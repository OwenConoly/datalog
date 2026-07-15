From Stdlib Require Import List Lia Permutation Classical_Prop.
From Datalog Require Import List Datalog Smallstep Tactics.
From coqutil Require Import Map.Interface.
From coqutil Require Import Semantics.OmniSmallstepCombinators Tactics Tactics.fwd.
Import ListNotations.

Section __.
  Context {rel : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.
  Definition node_name := option nat.

  Inductive dfact :=
  | normal_dfact (nf_rel : rel) (nf_args : list T)
  | meta_dfact (mf_rel : rel) (mf_args : list (option T)) (source : node_name) (expected_msgs : nat).

  Definition dfact_rel (f : dfact) : rel :=
    match f with
    | normal_dfact R _ => R
    | meta_dfact R _ _ _ => R
    end.

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

  Definition node_init : node_state :=
    {| known_facts := []; sent_facts := [] |}.

  Definition nle (s1 s2 : node_state) :=
    submultiset s1.(known_facts) s2.(known_facts) /\
      incl_mod dfact_equiv s1.(sent_facts) s2.(sent_facts).

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

  Definition node_good (s : node_state) (t : list IO_event) : Prop :=
    s.(known_facts) = inputs_of t /\
    allowed_inputs (inputs_of t) /\
    meta_facts_correct s /\
    meta_facts_ok s.

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

  (* When [small] is a submultiset of an [allowed_inputs] multiset [big] and
     [small] already realises the full declared count of an aggregate [R/mf_args]
     ([expect_num] matched by [Existsn]), the extra part [rest] (with [big ~
     small ++ rest]) contains no further matches: [allowed_inputs] caps [big]'s
     matches at the declared total, which [small] alone already meets, so
     [Existsn_split] forces [rest]'s share to zero. *)
  (* Every list has some exact match-count (classically). *)
  Lemma Existsn_total (P : dfact -> Prop) l : exists n, Existsn P n l.
  Proof.
    induction l as [| x l IH].
    - exists 0. constructor.
    - destruct IH as (n & Hn). destruct (classic (P x)).
      + exists (S n). apply Existsn_yes; assumption.
      + exists n. apply Existsn_no; assumption.
  Qed.

  Lemma submultiset_rest_no_matches R mf_args small rest big num :
    Permutation big (small ++ rest) ->
    allowed_inputs big ->
    expect_num_R_facts R mf_args small num ->
    Existsn (dfact_matches R mf_args) num small ->
    Forall (fun x => ~ dfact_matches R mf_args x) rest.
  Proof.
    intros Hperm Hallow Hexp Hex.
    pose proof (submultiset_incl _ _ (ex_intro _ rest Hperm)) as Hincl.
    destruct Hexp as (ems & Hf2 & Hsum).
    assert (Hf2' : Forall2 (fun k e => In (meta_dfact R mf_args k e) big)
                           (R_senders R) ems)
      by (clear -Hf2 Hincl; induction Hf2; constructor;
            [apply Hincl; assumption | assumption]).
    destruct Hallow as (_ & Hbound).
    destruct (Hbound R mf_args ems Hf2') as (num' & Hle & Hexn').
    pose proof (Existsn_perm _ _ _ _ Hexn' Hperm) as Hexn''.
    apply Existsn_split in Hexn''.
    destruct Hexn'' as (n1 & n2 & Hsum' & Hex1 & Hex2).
    pose proof (Existsn_unique _ _ _ _ Hex1 Hex) as Hn1.
    assert (n2 = 0) by lia. subst n2.
    exact (Existsn_0_Forall_not _ _ Hex2).
  Qed.

  (* If [h] is potentially supported by [hyps_d] (all known at the small multiset)
     then [knows_datalog_fact] transfers down along a submultiset: the extra facts
     in the bigger multiset cannot be the fresh piece that made [h] known, since
     they would be fresh matches for a complete aggregate ([submultiset_rest_no_
     matches]).  The single-input step is the [submultiset_cons] instance. *)
  Lemma knows_datalog_fact_transfer_down_sub small big hyps_d h :
    submultiset small big ->
    allowed_inputs big ->
    Forall (knows_datalog_fact small) hyps_d ->
    fact_potentially_supported hyps_d h ->
    knows_datalog_fact big h ->
    knows_datalog_fact small h.
  Proof.
    intros Hsub Hallow Hhyps_d Hsupp Hknow_big.
    pose proof (submultiset_incl _ _ Hsub) as Hincl.
    destruct Hsub as (rest & Hperm).
    destruct h as [Rh nfh | Rh mah msh].
    - cbn [fact_potentially_supported] in Hsupp.
      destruct Hsupp as (mah' & msh' & Hin_supp & Hmatch_supp).
      rewrite Forall_forall in Hhyps_d. specialize (Hhyps_d _ Hin_supp).
      cbn [knows_datalog_fact] in Hknow_big, Hhyps_d |- *.
      pose proof (Permutation_in _ Hperm Hknow_big) as Hin_app.
      apply in_app_or in Hin_app. destruct Hin_app as [Hin | Hinr]; [exact Hin |].
      exfalso. destruct Hhyps_d as (num_h & Hexp_h & Hex_h & _).
      pose proof (submultiset_rest_no_matches Rh mah' small rest big num_h
                    Hperm Hallow Hexp_h Hex_h) as Hrest_no.
      rewrite Forall_forall in Hrest_no.
      apply (Hrest_no _ Hinr). exists nfh. split; [reflexivity | exact Hmatch_supp].
    - cbn [fact_potentially_supported] in Hsupp.
      destruct Hsupp as (msh' & Hin_supp).
      rewrite Forall_forall in Hhyps_d. specialize (Hhyps_d _ Hin_supp).
      cbn [knows_datalog_fact] in Hknow_big, Hhyps_d |- *.
      destruct Hhyps_d as (num_old & Hexp_old & Hex_old & _).
      destruct Hknow_big as (num_new & Hexp_new & Hex_new & Hiff_new).
      pose proof (submultiset_rest_no_matches Rh mah small rest big num_old
                    Hperm Hallow Hexp_old Hex_old) as Hrest_no.
      exists num_old. split; [exact Hexp_old | split; [exact Hex_old |]].
      intros nf Hm. specialize (Hiff_new nf Hm). split.
      + intro Hset. apply Hiff_new in Hset.
        pose proof (Permutation_in _ Hperm Hset) as Hin_app.
        apply in_app_or in Hin_app. destruct Hin_app as [Hin | Hinr]; [exact Hin |].
        exfalso. rewrite Forall_forall in Hrest_no.
        apply (Hrest_no _ Hinr). exists nf. split; [reflexivity | exact Hm].
      + intro Hin. apply (proj2 Hiff_new). apply Hincl. exact Hin.
  Qed.

  (* [interp_meta_clause] only fixes the rel and args of the produced meta-fact;
     its derivability set is unconstrained, so it can be swapped freely. *)
  Lemma interp_meta_clause_set_irrel ctx c (R : rel) (args : list (option T))
        (S1 S2 : list T -> Prop) :
    interp_meta_clause ctx c (meta_fact R args S1) ->
    interp_meta_clause ctx c (meta_fact R args S2).
  Proof.
    cbv [interp_meta_clause]. intros (mf_args & mf_set & Hf2 & Heq).
    injection Heq as -> -> _. exists mf_args, S2. split; [exact Hf2 | reflexivity].
  Qed.

  (* A [can_deduce_meta_fact]'s clauses really do witness that the meta-rule
     [meta_rule mc mh] derives the aggregate [R/mf_args] (with its derivability
     set), as a [rule_impl]. *)
  Lemma meta_concl_rule_impl mc mh ctx R mf_args hyps_d :
    Exists (fun c => interp_meta_clause ctx c (meta_fact R mf_args (fun _ => False))) mc ->
    Forall2 (interp_meta_clause ctx) mh hyps_d ->
    rule_impl (one_step_derives np.(np_rules)) (meta_rule mc mh)
      (meta_fact R mf_args (one_step_derives np.(np_rules) hyps_d R)) hyps_d.
  Proof.
    intros Hconcl Hinterp. eapply meta_rule_impl with (ctx := ctx).
    - eapply Exists_impl; [| exact Hconcl].
      intros c Hc. eapply interp_meta_clause_set_irrel. exact Hc.
    - exact Hinterp.
    - intros args'' _. reflexivity.
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
      destruct Hcdmf as (ctx & mfr & mfa & mfc & Hres & _ & Hconcl & Hinterp).
      assert (mfr = R) as -> by congruence.
      assert (mfa = mf_args) as -> by congruence.
      pose proof (Hmfok r R mf_args num Hr_in HIn) as Hok0.
      cbn [ok_to_deduce_fact] in Hok0.
      apply Hok0; [| exact Hmatch].
      (* [nfargs] is deducible from the grown [inp :: known]; since it matches the
         aggregate [R/mf_args] that meta-rule [mc/mh] derives, [meta_rules_valid]
         makes its hypotheses [fact_potentially_supported], so they transfer back
         down to [known], and [nfargs] is deducible there too. *)
      destruct Hcdn as (local_hyps & Hnmri & Hknown_local_new).
      exists local_hyps. split; [exact Hnmri |].
      pose proof (Hmrv _ _ _ _ _ Hin_mr
                    (meta_concl_rule_impl _ _ _ _ _ _ Hconcl Hinterp)
                    _ _ _ Hr_in (simple_rule_impl _ _ _ _ _ Hnmri) Hmatch) as Hpot.
      rewrite Forall_forall in Hknown_local_new, Hpot |- *.
      intros h Hh. eapply knows_datalog_fact_transfer_down_sub;
        [ apply submultiset_cons | exact Hallow | exact Hknown_mr
        | exact (Hpot h Hh) | exact (Hknown_local_new h Hh) ].
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

  Lemma node_step_star_mono s t' s' :
    star (node_step np) s t' s' ->
    submultiset s.(known_facts) s'.(known_facts) /\
    submultiset s.(sent_facts) s'.(sent_facts).
  Proof.
    intros Hstar. induction Hstar as [| t0 sa e sb Hstar' IH Hstep].
    - split; apply submultiset_refl.
    - destruct IH as (IHk & IHs).
      assert (submultiset sa.(known_facts) sb.(known_facts) /\
              submultiset sa.(sent_facts) sb.(sent_facts)) as (Hk & Hs).
      { inversion Hstep; subst; cbn [known_facts sent_facts];
          split; try apply submultiset_refl; apply submultiset_cons. }
      split; eapply submultiset_trans; eassumption.
  Qed.

  Lemma node_will_match s1 lbl outs s1' s2 t2 :
    meta_rules_valid np.(np_rules) ->
    node_good s2 t2 ->
    node_step np s1 (O_event lbl outs) s1' ->
    nle s1 s2 ->
    eventually (will_step (node_step np) allowed_inputs)
      (fun '(s2', _) => nle s1' s2') (s2, t2).
  Proof.
    intros Hmrv Hgood2 Hstep (Hknle & Hsnle).
    inversion Hstep as [rs o Hnf | rs inp]; subst.
    assert (Hmk : forall (X : node_state) o',
      submultiset s1.(known_facts) X.(known_facts) ->
      submultiset s2.(sent_facts) X.(sent_facts) ->
      In o' X.(sent_facts) -> dfact_equiv o o' ->
      nle {| known_facts := s1.(known_facts);
             sent_facts := o :: s1.(sent_facts) |} X).
    { intros X o' Hk Hs Ho'in Ho'eq. split.
      - cbn [known_facts]. exact Hk.
      - cbn [sent_facts]. intros a Ha. cbn [In] in Ha. destruct Ha as [Hao | Ha].
        + subst a. exists o'. split; [exact Ho'in | exact Ho'eq].
        + destruct (Hsnle a Ha) as (b & Hb & Hab). exists b. split; [| exact Hab].
          eapply submultiset_incl; [exact Hs | exact Hb]. }
    apply eventually_step_cps. cbn [will_step].
    exists (mod_count o). intros sdem tdem Hstar Hallowdem.
    pose proof (node_good_star s2 t2 tdem sdem Hmrv Hallowdem Hgood2 Hstar)
      as (Hkdem & Haldem & Hmfcdem & Hmfokdem).
    pose proof (node_step_star_mono s2 tdem sdem Hstar) as (Hkmono & Hsmono).
    assert (HsubK : submultiset s1.(known_facts) sdem.(known_facts))
      by (eapply submultiset_trans; [exact Hknle | exact Hkmono]).
    assert (Halk : allowed_inputs sdem.(known_facts))
      by (rewrite Hkdem; exact Haldem).
    destruct o as [Ro oargs | Ro margs osrc ocnt].
    - destruct Hnf as (Hex & _).
      apply Exists_exists in Hex. destruct Hex as (r & Hr_in & Hcdf).
      cbn [can_deduce_fact] in Hcdf. destruct Hcdf as (Hcdn1 & _).
      destruct Hcdn1 as (hyps & Hnmri & Hknows1).
      assert (Hcdn_dem : can_deduce_normal_fact r sdem.(known_facts) Ro oargs).
      { exists hyps. split; [exact Hnmri |].
        rewrite Forall_forall in Hknows1 |- *. intros h Hh.
        eapply knows_datalog_fact_submultiset;
          [exact HsubK | exact Halk | apply Hknows1; exact Hh]. }
      destruct (classic (In (normal_dfact Ro oargs) sdem.(sent_facts))) as [Hin | Hnin].
      + left. apply eventually_done. eapply Hmk; eauto. simpl. reflexivity.
      + right.
        exists {| known_facts := sdem.(known_facts);
                  sent_facts := normal_dfact Ro oargs :: sdem.(sent_facts) |},
               [normal_dfact Ro oargs].
        split.
        * apply node_deduce_step. split.
          -- apply Exists_exists. exists r. split; [exact Hr_in |].
             cbn [can_deduce_fact]. split; [exact Hcdn_dem |].
             intros margs' num' Hinmeta Hmatch'.
             pose proof (Hmfokdem r Ro margs' num' Hr_in Hinmeta) as Hok.
             cbn [ok_to_deduce_fact] in Hok.
             exact (Hnin (Hok oargs Hcdn_dem Hmatch')).
          -- apply Forall_forall. intros r'' _. cbn [ok_to_deduce_fact]. exact I.
        * apply eventually_done.
          apply (Hmk _ (normal_dfact Ro oargs)).
          -- cbn [known_facts]. exact HsubK.
          -- cbn [sent_facts]. eapply submultiset_trans; [exact Hsmono | apply submultiset_cons].
          -- cbn [sent_facts]. left. reflexivity.
          -- cbn [dfact_equiv]. reflexivity.
    - destruct Hnf as (Hex & Hokall).
      apply Exists_exists in Hex. destruct Hex as (r & Hr_in & Hcdf).
      cbn [can_deduce_fact] in Hcdf.
      destruct Hcdf as (Hsrc & mc & mh & hyps & Hrmr & Hcdmf & Hknows1).
      subst osrc.
      destruct Hcdmf as (ctx & mfr & mfa & mfc & Hres & _ & Hconcl & Hinterp).
      fwd.
      assert (Hin_mr : In (meta_rule mc mh) np.(np_rules))
        by (rewrite <- Hrmr; exact Hr_in).
      destruct (Existsn_total (dfact_matches mfr mfa) sdem.(sent_facts))
        as (num_d & Hexn_d).
      right.
      replace (mod_count (meta_dfact mfr mfa np.(np_name) mfc))
        with (mod_count (meta_dfact mfr mfa np.(np_name) num_d)) by reflexivity.
      exists {| known_facts := sdem.(known_facts);
                sent_facts := meta_dfact mfr mfa np.(np_name) num_d :: sdem.(sent_facts) |},
             [meta_dfact mfr mfa np.(np_name) num_d].
      split.
      + apply node_deduce_step. split.
        * apply Exists_exists. exists r. split; [exact Hr_in |].
          cbn [can_deduce_fact]. split; [reflexivity |].
          exists mc, mh, hyps. split; [exact Hrmr |]. split.
          -- cbv [can_deduce_meta_fact]. eauto 8.
          -- rewrite Forall_forall in Hknows1 |- *. intros h Hh.
             eauto using knows_datalog_fact_submultiset.
        * apply Forall_forall. intros r'' Hr''_in. cbn [ok_to_deduce_fact].
          intros nfargs Hcdn_dem Hmatch'.
          (* [nfargs] is deducible from the demon's grown [known]; matching the
             aggregate [mfr/mfa] that [mc/mh] derives, its hypotheses are
             [fact_potentially_supported] ([meta_rules_valid]) and hence transfer
             down to [s1]'s [known]. *)
          assert (Hcdn_s1 : can_deduce_normal_fact r'' s1.(known_facts) mfr nfargs).
          { destruct Hcdn_dem as (local_hyps & Hnmri & Hknown_local_new).
            exists local_hyps. split; [exact Hnmri |].
            pose proof (Hmrv _ _ _ _ _ Hin_mr
                          (meta_concl_rule_impl _ _ _ _ _ _ Hconcl Hinterp)
                          _ _ _ Hr''_in (simple_rule_impl _ _ _ _ _ Hnmri) Hmatch') as Hpot.
            rewrite Forall_forall in Hknown_local_new, Hpot |- *.
            intros h Hh. eapply knows_datalog_fact_transfer_down_sub;
              [ exact HsubK | exact Halk | exact Hknows1
              | exact (Hpot h Hh) | exact (Hknown_local_new h Hh) ]. }
          rewrite Forall_forall in Hokall.
          pose proof (Hokall r'' Hr''_in) as Hok1. cbn [ok_to_deduce_fact] in Hok1.
          pose proof (Hok1 nfargs Hcdn_s1 Hmatch') as Hin_s1.
          destruct (Hsnle _ Hin_s1) as (b & Hb & Hab).
          simpl in Hab. subst. eapply submultiset_incl; eassumption.
      + apply eventually_done. eapply Hmk; simpl; eauto.
        all: simpl; eauto.
        eauto using submultiset_trans, submultiset_cons.
  Qed.

  Lemma dfact_equiv_refl f : dfact_equiv f f.
  Proof. destruct f; simpl; auto. Qed.

  Lemma dfact_equiv_sym f1 f2 : dfact_equiv f1 f2 -> dfact_equiv f2 f1.
  Proof.
    destruct f1 as [R1 a1 | R1 m1 s1 c1], f2 as [R2 a2 | R2 m2 s2 c2];
      cbn [dfact_equiv]; try congruence.
    intros (HR & Ha & Hs); subst; auto.
  Qed.

  Lemma nle_refl s : nle s s.
  Proof.
    split; [apply submultiset_refl |].
    intros a Ha. exists a. split; [exact Ha | apply dfact_equiv_refl].
  Qed.

  Ltac inv_step :=
    match goal with
    | H: node_step _ _ _ _ |- _ => invert H
    end.

  Lemma sent_eq_outputs t s :
    star (node_step np) node_init t s -> s.(sent_facts) = outputs_of t.
  Proof.
    intros Hstar. induction Hstar; eauto.
    inv_step; simpl; eauto. f_equal. auto.
  Qed.

  Lemma reachable_node_good t s :
    meta_rules_valid np.(np_rules) ->
    allowed_inputs (inputs_of t) ->
    star (node_step np) node_init t s ->
    node_good s t.
  Proof.
    intros Hmrv Hallow Hstar.
    assert (node_good s (t ++ [])) as Hg.
    { eapply node_good_star;
        [ exact Hmrv | rewrite app_nil_r; exact Hallow | apply node_good_init | exact Hstar ]. }
    rewrite app_nil_r in Hg. exact Hg.
  Qed.

  Lemma node_drive_to_dominate t0 s0 t' sf :
    meta_rules_valid np.(np_rules) ->
    star (node_step np) node_init t0 s0 ->
    allowed_inputs (inputs_of t0) ->
    star (node_step np) s0 t' sf ->
    inputs_of t' = [] ->
    eventually (will_step (node_step np) allowed_inputs)
      (fun '(s2, _) => nle sf s2) (s0, t0).
  Proof.
    intros Hmrv Hstar0 Hga0 Hrun Hinp. revert Hinp.
    induction Hrun as [| T0 smid e sf' Hrun' IH Hstep]; intros Hinp.
    - apply eventually_done. apply nle_refl.
    - destruct e as [m | lbl outs].
      + cbn [inputs_of flat_map app] in Hinp. discriminate Hinp.
      + cbn [inputs_of flat_map app] in Hinp. specialize (IH Hinp).
        apply eventually_will_step_annotate in IH.
        eapply eventually_trans; [exact IH |].
        intros [s2 t2] (Hreach & Hle_mid).
        destruct Hreach as (tr & Hstar_s0s2 & -> & Hga_imp).
        specialize (Hga_imp Hga0).
        assert (Hstar2 : star (node_step np) node_init (tr ++ t0) s2) by eauto using star_app.
        eapply node_will_match;
          [ exact Hmrv
          | eapply reachable_node_good; [exact Hmrv | exact Hga_imp | exact Hstar2]
          | exact Hstep
          | exact Hle_mid ].
  Qed.

  Lemma node_might_implies_will :
    meta_rules_valid np.(np_rules) ->
    might_implies_will_equiv (node_step np) dfact_equiv allowed_inputs node_init.
  Proof.
    intros Hmrv t s o Hstar Hallow (t' & sf & Hrun & Hinp & Hino).
    assert (Hstarf : star (node_step np) node_init (t' ++ t) sf) by eauto using star_app.
    assert (Ho_sent : In o sf.(sent_facts))
      by (rewrite (sent_eq_outputs (t' ++ t) sf Hstarf); exact Hino).
    pose proof (node_drive_to_dominate t s t' sf Hmrv Hstar Hallow Hrun Hinp) as Hdrive.
    apply eventually_will_step_annotate in Hdrive.
    unfold will_output_equiv.
    eapply eventually_trans; [exact Hdrive |].
    intros [s2 t2] (Hreach & Hle).
    destruct Hle as (_ & Hsent_dom).
    destruct (Hsent_dom o Ho_sent) as (o' & Ho'_in & Ho'_eq).
    destruct Hreach as (tr & Hstar_s_s2 & -> & Hga_imp).
    specialize (Hga_imp Hallow).
    assert (Hstar2 : star (node_step np) node_init (tr ++ t) s2) by eauto using star_app.
    apply eventually_done.
    exists o'. split.
    - apply dfact_equiv_sym. exact Ho'_eq.
    - erewrite <- sent_eq_outputs by eassumption. eassumption.
  Qed.

End __.
