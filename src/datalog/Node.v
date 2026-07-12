From Stdlib Require Import List Lia.
From Datalog Require Import List Datalog Smallstep.
From coqutil Require Import Map.Interface.
From coqutil Require Import Semantics.OmniSmallstepCombinators.
Import ListNotations.

Section __.
  Context {rel : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.
  Context {node_name : Type}.

  Implicit Types mf_rel : rel.
  Implicit Types mf_args : list (option T).
  Implicit Types nf_args : list T.

  Inductive dfact :=
  | normal_dfact (nf_rel : rel) (nf_args : list T)
  | meta_dfact (mf_rel : rel) (mf_args : list (option T)) (source : node_name) (expected_msgs : nat).

  Implicit Types known_facts sent_facts input_facts inputs : list dfact.
  Implicit Types nf result : dfact.

  Record node_state :=
    { known_facts : list dfact;
      sent_facts : list dfact }.

  Context (R_senders : rel -> list node_name).

  Definition expect_num_R_facts R mf_args known_facts num :=
    exists expected_msgss,
      Forall2 (fun n expected_msgs => In (meta_dfact R mf_args n expected_msgs) known_facts) (R_senders R) expected_msgss /\
        num = fold_left Nat.add expected_msgss O.

  Definition dfact_matches mf_rel mf_args nf :=
    exists nf_args,
      nf = normal_dfact mf_rel nf_args /\
        Forall2 matches mf_args nf_args.

  Definition knows_datalog_fact (dfacts : list dfact) (f : fact) :=
    match f with
    | normal_fact nf_rel nf_args =>
        In (normal_dfact nf_rel nf_args) dfacts
    | meta_fact mf_rel mf_args mf_set =>
        exists num,
        expect_num_R_facts mf_rel mf_args dfacts num /\
          Existsn (dfact_matches mf_rel mf_args) num dfacts /\
          (forall nf_args,
              Forall2 matches mf_args nf_args ->
              mf_set nf_args <-> In (normal_dfact mf_rel nf_args) dfacts)
    end.

  Definition can_deduce_normal_fact (r : rule) (known_facts : list dfact) nf_rel nf_args :=
    exists hyps,
      non_meta_rule_impl r nf_rel nf_args hyps /\
        Forall (knows_datalog_fact known_facts) hyps.

  Definition can_deduce_meta_fact (mf_concls mf_hyps : list meta_clause) (node : node_name) (sent_facts : list dfact) (result : dfact) (hyps : list fact) :=
    exists ctx mf_rel mf_args mf_cnt,
      result = meta_dfact mf_rel mf_args node mf_cnt /\
        Existsn (dfact_matches mf_rel mf_args) mf_cnt sent_facts /\
        Exists (fun c => interp_meta_clause ctx c (meta_fact mf_rel mf_args (fun _ => False))) mf_concls /\
        Forall2 (interp_meta_clause ctx) mf_hyps hyps.

  Definition ok_to_deduce_fact (r : rule) known sent f :=
    match f with
    | normal_dfact nf_rel nf_args => True
    | meta_dfact mf_rel mf_args source num_msgs =>
        forall nf_args,
          can_deduce_normal_fact r known mf_rel nf_args ->
          Forall2 matches mf_args nf_args ->
          In (normal_dfact mf_rel nf_args) sent
    end.

  Definition can_deduce_fact (r : rule) node known sent f :=
    match f with
    | normal_dfact nf_rel nf_args =>
        can_deduce_normal_fact r known nf_rel nf_args /\
          forall mf_args num,
            In (meta_dfact nf_rel mf_args node num) sent ->
            Forall2 matches mf_args nf_args ->
            False
    | meta_dfact mf_rel mf_args source num_msgs =>
        source = node /\
          exists mr_concls mr_hyps hyps,
            r = meta_rule mr_concls mr_hyps /\
              can_deduce_meta_fact mr_concls mr_hyps node sent f hyps /\
              Forall (knows_datalog_fact known) hyps
    end.

  Record node_prog :=
    { np_rules : list rule;
      np_name : node_name }.

  Definition new_facts (sp : node_prog) (rs : node_state) f :=
    Exists
      (fun r => can_deduce_fact r sp.(np_name) rs.(known_facts) rs.(sent_facts) f)
      sp.(np_rules) /\
      Forall
        (fun r => ok_to_deduce_fact r rs.(known_facts) rs.(sent_facts) f)
        sp.(np_rules).

  Variant node_label :=
    | nl_deduce (f : dfact).

  Local Notation IO_event := (Smallstep.IO_event node_label dfact).

  Inductive node_step (sp : node_prog) : node_state -> IO_event -> node_state -> Prop :=
  | node_deduce_step rs output :
    new_facts sp rs output ->
    node_step sp rs (O_event (nl_deduce output) [output])
                   {| known_facts := rs.(known_facts);
                     sent_facts := output :: rs.(sent_facts) |}
  | node_input_step rs input :
    node_step sp rs (I_event input)
                   {| known_facts := input :: rs.(known_facts);
                     sent_facts := rs.(sent_facts) |}.

  Definition allowed_inputs (input_facts : list dfact) :=
    (forall R mf_args k num num0,
        In (meta_dfact R mf_args k num) input_facts ->
        In (meta_dfact R mf_args k num0) input_facts -> num0 = num)
    /\
    (forall R mf_args expected_msgss,
        Forall2 (fun k e => In (meta_dfact R mf_args k e) input_facts)
                (R_senders R) expected_msgss ->
        exists num', num' <= fold_left Nat.add expected_msgss 0 /\
                     Existsn (dfact_matches R mf_args) num' input_facts).

  Definition dfact_equiv (f1 f2 : dfact) : Prop :=
    match f1, f2 with
    | meta_dfact R1 a1 s1 _, meta_dfact R2 a2 s2 _ => R1 = R2 /\ a1 = a2 /\ s1 = s2
    | _, _ => f1 = f2
    end.

  Definition dfact_consistent (c l : list dfact) : Prop :=
    forall R mf_args num,
      expect_num_R_facts R mf_args c num ->
      Existsn (dfact_matches R mf_args) num l.

  Definition node_init : node_state :=
    {| known_facts := []; sent_facts := [] |}.

  Definition nle (s1 s2 : node_state) :=
    submultiset s1.(known_facts) s2.(known_facts) /\
      incl_mod_weak dfact_equiv s1.(sent_facts) s2.(sent_facts).

  Context (np : node_prog).

  Local Notation node_will_step := (will_step (node_step np) allowed_inputs).

  Definition meta_facts_correct (s : node_state) : Prop :=
    forall R mf_args num,
      In (meta_dfact R mf_args np.(np_name) num) s.(sent_facts) ->
      exists mc mh hyps,
        In (meta_rule mc mh) np.(np_rules) /\
          can_deduce_meta_fact mc mh np.(np_name) s.(sent_facts)
            (meta_dfact R mf_args np.(np_name) num) hyps /\
          Forall (knows_datalog_fact s.(known_facts)) hyps
  (*not clear whether we need this next conjunct.  we could get it,
    by saying something like "inputs are consistent outputs from other nodes,
    plus the outputs of this node."
    not sure if that will later become necessary.
   *)
  (*/\
          (forall mf_set, ~ In (meta_fact R mf_args mf_set) hyps)*).

  Definition meta_facts_ok (s : node_state) : Prop :=
    forall r R mf_args num,
      In r np.(np_rules) ->
      In (meta_dfact R mf_args np.(np_name) num) s.(sent_facts) ->
      ok_to_deduce_fact r s.(known_facts) s.(sent_facts)
        (meta_dfact R mf_args np.(np_name) num).

  (* Adding an [allowed_inputs]-consistent fact to [known] preserves
     [knows_datalog_fact].  Normal facts are monotone by [in_cons]; for a meta
     fact the exact-count conditions could break if the new fact were a match,
     but [allowed_inputs] bounds matches by the declared total, so [x] cannot be
     a new match and the counts (and the iff) carry over. *)
  Lemma knows_datalog_fact_add_allowed x known h :
    allowed_inputs (x :: known) ->
    knows_datalog_fact known h ->
    knows_datalog_fact (x :: known) h.
  Proof.
    intros Hallow Hknows.
    destruct h as [R args | R margs mf_set].
    - apply in_cons. exact Hknows.
    - destruct Hknows as (num & Hexp & Hexn & Hiff).
      destruct Hexp as (ems & Hf2 & Hsum).
      assert (Hf2' : Forall2 (fun k e => In (meta_dfact R margs k e) (x :: known))
                             (R_senders R) ems).
      { clear -Hf2. induction Hf2; constructor; auto using in_cons. }
      assert (Hnm : ~ dfact_matches R margs x).
      { intro Hmatch. destruct Hallow as (_ & Hbound).
        destruct (Hbound R margs ems Hf2') as (num' & Hle & Hexn').
        assert (HexnS : Existsn (dfact_matches R margs) (S num) (x :: known))
          by (apply Existsn_yes; assumption).
        pose proof (Existsn_unique _ _ _ _ Hexn' HexnS) as Heq. lia. }
      exists num. split; [| split].
      + exists ems. split; [exact Hf2' | exact Hsum].
      + apply Existsn_no; assumption.
      + intros nfargs Hm. specialize (Hiff nfargs Hm). split; intros H.
        * apply in_cons. apply (proj1 Hiff). exact H.
        * cbn in H. destruct H as [Hx | Hin].
          -- exfalso. apply Hnm. exists nfargs. split; [exact Hx | exact Hm].
          -- apply (proj2 Hiff). exact Hin.
  Qed.

  Lemma step_preserves_meta_facts_correct s e s' :
    allowed_inputs s'.(known_facts) ->
    meta_facts_correct s ->
    node_step np s e s' ->
    meta_facts_correct s'.
  Proof.
    intros Hallow Hmfc Hstep.
    inversion Hstep as [s0 out Hnew | s0 inp]; subst; clear Hstep;
      intros R mf_args num Hin; cbn [known_facts sent_facts] in Hallow, Hin |- *.
    - (* deduce *)
      destruct Hnew as (Hex & Hok).
      destruct Hin as [Hhead | Hin_old].
      + (* out is the newly-deduced meta *)
        subst out.
        apply Exists_exists in Hex. destruct Hex as (r & Hr_in & Hcdf).
        cbn in Hcdf. destruct Hcdf as (_ & mc & mh & hyps & Hr_eq & Hcdm & Hhyps).
        destruct Hcdm as (ctx & mfr & mfa & mfc & Hres & HEx & Hconcl & Hinterp).
        exists mc, mh, hyps. subst r.
        split; [exact Hr_in | split; [| exact Hhyps]].
        exists ctx, mfr, mfa, mfc.
        split; [exact Hres | split; [| split; [exact Hconcl | exact Hinterp]]].
        apply Existsn_no; [intros (nfa & Hc & _); discriminate Hc | exact HEx].
      + (* existing meta in sent *)
        destruct (Hmfc R mf_args num Hin_old) as (mc & mh & hyps & Hrule & Hcdm & Hhyps).
        assert (Hnm : ~ dfact_matches R mf_args out).
        { intros (oargs & Hout & Hmatch). subst out.
          apply Exists_exists in Hex. destruct Hex as (r & Hr_in & Hcdf).
          cbn in Hcdf. destruct Hcdf as (_ & Hguard).
          exact (Hguard mf_args num Hin_old Hmatch). }
        destruct Hcdm as (ctx & mfr & mfa & mfc & Hres & HEx & Hconcl & Hinterp).
        exists mc, mh, hyps.
        split; [exact Hrule | split; [| exact Hhyps]].
        exists ctx, mfr, mfa, mfc.
        split; [exact Hres | split; [| split; [exact Hconcl | exact Hinterp]]].
        apply Existsn_no; [| exact HEx].
        assert (mfr = R) as -> by congruence.
        assert (mfa = mf_args) as -> by congruence.
        exact Hnm.
    - (* input *)
      destruct (Hmfc R mf_args num Hin) as (mc & mh & hyps & Hrule & Hcdm & Hhyps).
      exists mc, mh, hyps. split; [exact Hrule | split; [exact Hcdm |]].
      eapply Forall_impl; [| exact Hhyps].
      intros h Hh. apply knows_datalog_fact_add_allowed; [exact Hallow | exact Hh].
  Qed.

  Lemma step_preserves_meta_facts_ok s e s' :
    meta_rules_valid np.(np_rules) ->
    allowed_inputs s'.(known_facts) ->
    meta_facts_correct s ->
    meta_facts_ok s ->
    node_step np s e s' ->
    meta_facts_ok s'.
  Proof. Admitted.


  Lemma node_will_match' s1 lbl outs s1' s2 t2 :
    node_step np s1 (O_event lbl outs) s1' ->
    nle s1 s2 ->
    eventually (will_step (node_step np) allowed_inputs)
      (fun '(s2', _) => nle s1' s2') (s2, t2).
  Admitted.

  Lemma node_might_implies_will :
    meta_rules_valid np.(np_rules) ->
    might_implies_will_equiv (node_step np) dfact_equiv allowed_inputs node_init.
  Admitted.

End __.
