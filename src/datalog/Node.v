From Stdlib Require Import List Lia Permutation.
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

  Variant dfact_mod_count :=
    | normal_dfact_mc (nf_rel : rel) (nf_args : list T)
    | meta_dfact_mc (mf_rel : rel) (mf_args : list (option T)) (source : node_name).

  Definition mod_count (f : dfact) :=
    match f with
    | normal_dfact R args => normal_dfact_mc R args
    | meta_dfact R margs src _ => meta_dfact_mc R margs src
    end.

  Local Notation IO_event := (Smallstep.IO_event dfact_mod_count dfact).

  Inductive node_step (sp : node_prog) : node_state -> IO_event -> node_state -> Prop :=
  | node_deduce_step rs output :
    new_facts sp rs output ->
    node_step sp rs (O_event (mod_count output) [output])
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

  (* The good-state bundle carried through the demon's run: [known] is exactly
     the received inputs [inputs_of t] (queue-free, so equality, not just a
     permutation), those inputs are [allowed_inputs], and the two meta-fact
     invariants hold.  All four are preserved by [node_step] ([node_good_step]),
     so this is a genuine inductive invariant. *)
  Definition node_good (s : node_state) (t : list IO_event) : Prop :=
    s.(known_facts) = inputs_of t /\
    allowed_inputs (inputs_of t) /\
    meta_facts_correct s /\
    meta_facts_ok s.

  (* Monotonicity under submultiset, with [allowed_inputs] pinning the counts.
     [allowed_inputs] is downward-closed (a submultiset of allowed inputs is
     allowed).  [knows_datalog_fact] lifts upward into an allowed superset: the
     bound forces the extra part [rest] to contain no matches ([Existsn_split]
     decomposes the count of [l2 ~ l1 ++ rest]), so the exact-count [Existsn] and
     the set-characterising iff both carry over. *)
  Lemma allowed_inputs_submultiset l1 l2 :
    submultiset l1 l2 -> allowed_inputs l2 -> allowed_inputs l1.
  Proof.
    intros Hsub Hallow. pose proof (submultiset_incl _ _ Hsub) as Hincl.
    destruct Hsub as (rest & Hperm). destruct Hallow as (Huniq & Hbound). split.
    - intros R mf_args k num num0 H1 H2.
      apply (Huniq R mf_args k num num0); apply Hincl; assumption.
    - intros R mf_args ems Hf2.
      assert (Hf2' : Forall2 (fun k e => In (meta_dfact R mf_args k e) l2)
                             (R_senders R) ems)
        by (clear -Hf2 Hincl; induction Hf2; constructor;
              [apply Hincl; assumption | assumption]).
      destruct (Hbound R mf_args ems Hf2') as (num2 & Hle2 & Hexn2).
      pose proof (Existsn_perm _ _ _ _ Hexn2 Hperm) as Hexn2'.
      apply Existsn_split in Hexn2'. destruct Hexn2' as (n1 & n_rest & Hsum2 & Hex1 & _).
      exists n1. split; [lia | exact Hex1].
  Qed.

  Lemma knows_datalog_fact_submultiset l1 l2 h :
    submultiset l1 l2 -> allowed_inputs l2 ->
    knows_datalog_fact l1 h -> knows_datalog_fact l2 h.
  Proof.
    intros Hsub Hallow Hk. pose proof (submultiset_incl _ _ Hsub) as Hincl.
    destruct Hsub as (rest & Hperm).
    destruct h as [R args | R margs mf_set].
    - apply Hincl. exact Hk.
    - destruct Hk as (num & (ems & Hf2 & Hsum) & Hexn & Hiff).
      assert (Hf2' : Forall2 (fun k e => In (meta_dfact R margs k e) l2)
                             (R_senders R) ems)
        by (clear -Hf2 Hincl; induction Hf2; constructor;
              [apply Hincl; assumption | assumption]).
      destruct Hallow as (_ & Hbound).
      destruct (Hbound R margs ems Hf2') as (num2 & Hle2 & Hexn2).
      rewrite <- Hsum in Hle2.
      pose proof (Existsn_perm _ _ _ _ Hexn2 Hperm) as Hexn2'.
      apply Existsn_split in Hexn2'. destruct Hexn2' as (n1 & n_rest & Hsum2 & Hex1 & Hexr).
      pose proof (Existsn_unique _ _ _ _ Hex1 Hexn) as Hn1.
      assert (n_rest = 0) by lia. subst n_rest.
      assert (Hnum2 : num2 = num) by lia.
      pose proof (Existsn_0_Forall_not _ _ Hexr) as Hrest_no.
      exists num. split; [| split].
      + exists ems. split; [exact Hf2' | exact Hsum].
      + rewrite <- Hnum2. exact Hexn2.
      + intros nfa Hm. specialize (Hiff nfa Hm). split; intro H.
        * apply Hincl. apply (proj1 Hiff). exact H.
        * apply (proj2 Hiff).
          pose proof (Permutation_in _ Hperm H) as H'.
          apply in_app_or in H'. destruct H' as [Hin1 | Hinr]; [exact Hin1 |].
          exfalso. rewrite Forall_forall in Hrest_no.
          apply (Hrest_no _ Hinr). exists nfa. split; [reflexivity | exact Hm].
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
      intros h Hh. eapply knows_datalog_fact_submultiset;
        [apply submultiset_cons | exact Hallow | exact Hh].
  Qed.

  (* An [allowed_inputs]-consistent input cannot be a fresh match for a
     complete aggregate (one whose declared total is already realised in
     [known]).  Node analogue of Operational's [expect_num_R_facts_no_waiting]. *)
  Lemma not_match_of_complete R mf_args x known num :
    allowed_inputs (x :: known) ->
    expect_num_R_facts R mf_args known num ->
    Existsn (dfact_matches R mf_args) num known ->
    ~ dfact_matches R mf_args x.
  Proof.
    intros Hallow Hexp Hexn Hmatch.
    destruct Hexp as (ems & Hf2 & Hsum).
    assert (Hf2' : Forall2 (fun k e => In (meta_dfact R mf_args k e) (x :: known))
                           (R_senders R) ems).
    { clear -Hf2. induction Hf2; constructor; auto using in_cons. }
    destruct Hallow as (_ & Hbound).
    destruct (Hbound R mf_args ems Hf2') as (num' & Hle & Hexn').
    assert (HexnS : Existsn (dfact_matches R mf_args) (S num) (x :: known))
      by (apply Existsn_yes; assumption).
    pose proof (Existsn_unique _ _ _ _ Hexn' HexnS) as Heq. lia.
  Qed.

  (* If a hypothesis [h] is potentially supported by [hyps_d] (all of which are
     known at the old [known]), then [knows_datalog_fact] transfers back from the
     grown [inp :: known] to [known]: the added input cannot be the fresh piece
     that made [h] known, because it would be a fresh match for a complete
     aggregate in [hyps_d], contradicting [allowed_inputs]. *)
  Lemma knows_datalog_fact_transfer_down inp known hyps_d h :
    allowed_inputs (inp :: known) ->
    Forall (knows_datalog_fact known) hyps_d ->
    fact_potentially_supported hyps_d h ->
    knows_datalog_fact (inp :: known) h ->
    knows_datalog_fact known h.
  Proof.
    intros Hallow Hhyps_d Hsupp Hknow_new.
    destruct h as [Rh nfh | Rh mah msh].
    - cbn [fact_potentially_supported] in Hsupp.
      destruct Hsupp as (mah' & msh' & Hin_supp & Hmatch_supp).
      rewrite Forall_forall in Hhyps_d. specialize (Hhyps_d _ Hin_supp).
      cbn [knows_datalog_fact] in Hknow_new, Hhyps_d |- *.
      destruct Hknow_new as [Hinp | Hin]; [| exact Hin].
      exfalso. destruct Hhyps_d as (num_h & Hexp_h & Hex_h & _).
      apply (not_match_of_complete Rh mah' inp known num_h Hallow Hexp_h Hex_h).
      exists nfh. split; [exact Hinp | exact Hmatch_supp].
    - cbn [fact_potentially_supported] in Hsupp.
      destruct Hsupp as (msh' & Hin_supp).
      rewrite Forall_forall in Hhyps_d. specialize (Hhyps_d _ Hin_supp).
      cbn [knows_datalog_fact] in Hknow_new, Hhyps_d |- *.
      destruct Hhyps_d as (num_old & Hexp_old & Hex_old & _).
      destruct Hknow_new as (num_new & Hexp_new & Hex_new & Hiff_new).
      exists num_old. split; [exact Hexp_old | split; [exact Hex_old |]].
      intros nf Hm. specialize (Hiff_new nf Hm). split.
      + intro Hset. apply Hiff_new in Hset. destruct Hset as [Hinp | Hin]; [| exact Hin].
        exfalso. apply (not_match_of_complete Rh mah inp known num_old Hallow Hexp_old Hex_old).
        exists nf. split; [exact Hinp | exact Hm].
      + intro Hin. apply (proj2 Hiff_new). apply in_cons. exact Hin.
  Qed.

  Lemma step_preserves_meta_facts_ok s e s' :
    meta_rules_valid np.(np_rules) ->
    allowed_inputs s'.(known_facts) ->
    meta_facts_correct s ->
    meta_facts_ok s ->
    node_step np s e s' ->
    meta_facts_ok s'.
  Proof.
    intros Hmrv Hallow Hmfc Hmfok Hstep.
    inversion Hstep as [s0 out Hnew | s0 inp]; subst; clear Hstep;
      intros r R mf_args num Hr_in HIn;
      cbn [known_facts sent_facts] in Hallow, HIn |- *.
    - (* deduce: sent grows, known fixed *)
      cbn [ok_to_deduce_fact]. intros nfargs Hcdn Hmatch. apply in_cons.
      destruct HIn as [Hhead | HIn_old].
      + subst out. destruct Hnew as (_ & Hok). rewrite Forall_forall in Hok.
        specialize (Hok r Hr_in). cbn [ok_to_deduce_fact] in Hok.
        exact (Hok nfargs Hcdn Hmatch).
      + pose proof (Hmfok r R mf_args num Hr_in HIn_old) as Hok0.
        cbn [ok_to_deduce_fact] in Hok0. exact (Hok0 nfargs Hcdn Hmatch).
    - (* input: known grows *)
      cbn [ok_to_deduce_fact]. intros nfargs Hcdn Hmatch.
      destruct (Hmfc R mf_args num HIn) as (mc & mh & hyps_d & Hin_mr & Hcdmf & Hknown_mr).
      destruct Hcdn as (local_hyps & Hnmri & Hknown_local_new).
      destruct Hcdmf as (ctx & mfr & mfa & mfc & Hres & _ & Hconcl & Hinterp).
      assert (mfr = R) as -> by congruence.
      assert (mfa = mf_args) as -> by congruence.
      assert (Hri_meta : rule_impl (one_step_derives np.(np_rules)) (meta_rule mc mh)
                (meta_fact R mf_args (one_step_derives np.(np_rules) hyps_d R)) hyps_d).
      { eapply meta_rule_impl with (ctx := ctx).
        - eapply Exists_impl; [| exact Hconcl].
          intros c Hc. destruct Hc as (mfa0 & mfs0 & Hf2c & Heqc).
          injection Heqc as Hrel Hargs _.
          exists mfa0, (one_step_derives np.(np_rules) hyps_d R).
          split; [exact Hf2c |]. rewrite Hargs, Hrel. reflexivity.
        - exact Hinterp.
        - intros args'' _. reflexivity. }
      assert (Hri_normal : rule_impl (one_step_derives np.(np_rules)) r
                             (normal_fact R nfargs) local_hyps)
        by (apply simple_rule_impl; exact Hnmri).
      pose proof (Hmrv R mf_args (one_step_derives np.(np_rules) hyps_d R) hyps_d
                    (meta_rule mc mh) Hin_mr Hri_meta r nfargs local_hyps Hr_in
                    Hri_normal Hmatch) as Hpot.
      assert (Hknown_local_old : Forall (knows_datalog_fact s.(known_facts)) local_hyps).
      { rewrite Forall_forall in Hknown_local_new, Hpot |- *.
        intros h Hh. eapply knows_datalog_fact_transfer_down;
          [exact Hallow | exact Hknown_mr | exact (Hpot h Hh) | exact (Hknown_local_new h Hh)]. }
      pose proof (Hmfok r R mf_args num Hr_in HIn) as Hok0.
      cbn [ok_to_deduce_fact] in Hok0.
      apply Hok0; [| exact Hmatch].
      exists local_hyps. split; [exact Hnmri | exact Hknown_local_old].
  Qed.

  Lemma node_good_step s e s' t :
    meta_rules_valid np.(np_rules) ->
    node_good s t ->
    allowed_inputs (inputs_of (e :: t)) ->
    node_step np s e s' ->
    node_good s' (e :: t).
  Proof.
    intros Hmrv (Hkeq & _ & Hmfc & Hmfok) Hallow' Hstep.
    assert (Hkeq' : s'.(known_facts) = inputs_of (e :: t)).
    { inversion Hstep; subst; cbn [known_facts]; rewrite Hkeq; reflexivity. }
    assert (Hak : allowed_inputs s'.(known_facts)) by (rewrite Hkeq'; exact Hallow').
    split; [exact Hkeq' | split; [exact Hallow' | split]].
    - eapply step_preserves_meta_facts_correct; eassumption.
    - eapply step_preserves_meta_facts_ok; eassumption.
  Qed.

  Lemma node_good_init : node_good node_init [].
  Proof.
    split; [reflexivity | split; [| split]].
    - split.
      + intros R mf_args k num num0 H. destruct H.
      + intros R mf_args ems _. exists 0. split; [lia | constructor].
    - intros R mf_args num H. destruct H.
    - intros r R mf_args num Hr H. destruct H.
  Qed.

  Lemma node_good_star s t t' s' :
    meta_rules_valid np.(np_rules) ->
    allowed_inputs (inputs_of (t' ++ t)) ->
    node_good s t ->
    star (node_step np) s t' s' ->
    node_good s' (t' ++ t).
  Proof.
    intros Hmrv Hallow Hgood Hstar. revert Hallow.
    induction Hstar as [| t0 s'0 e s'' Hstar' IH Hstep]; intros Hallow.
    - exact Hgood.
    - assert (Hallow0 : allowed_inputs (inputs_of (t0 ++ t))).
      { destruct e as [m | lbl outs].
        - eapply allowed_inputs_submultiset; [apply submultiset_cons | exact Hallow].
        - exact Hallow. }
      exact (node_good_step s'0 e s'' (t0 ++ t) Hmrv (IH Hallow0) Hallow Hstep).
  Qed.

  Lemma node_will_match' s1 lbl outs s1' s2 t2 :
    meta_rules_valid np.(np_rules) ->
    node_good s2 t2 ->
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
