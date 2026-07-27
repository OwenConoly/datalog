From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.

From Datalog Require Import Map Tactics Fp List Dag Datalog.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List Datatypes.Option Eqb.

Import ListNotations.

Section RelMap.
  Context {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.

  Context {rel1 rel2} (f : rel1 -> rel2).

  Definition injective_on (x : rel1) : Prop :=
    forall y, f x = f y -> x = y.

  Definition rel_equiv R1 R2 := f R1 = f R2.

  Definition map_fact (fct : fact) : fact :=
    match fct with
    | normal_fact R args => normal_fact (f R) args
    | meta_fact R mf_args mf_set => meta_fact (f R) mf_args mf_set
    end.

  Definition fact_equiv f1 f2 := map_fact f1 = map_fact f2.

  Definition map_clause_rel (c : clause) : clause :=
    {| clause_rel := f c.(clause_rel);
      clause_args := c.(clause_args) |}.

  Lemma interp_clause_map_fw ctx c h :
    interp_clause ctx c h ->
    interp_clause ctx (map_clause_rel c) (map_fact h).
  Proof. intros. repeat invert_stuff. interp_exprs. Qed.

  Hint Unfold interp_clause rel_equiv fact_equiv : core.
  Lemma interp_clause_map_bw ctx c h :
    interp_clause ctx (map_clause_rel c) (map_fact h) ->
    exists h', fact_equiv h h' /\ interp_clause ctx c h'.
  Proof.
    intros H. cbv [interp_clause] in H. fwd.
    destruct h; simpl in *; repeat invert_stuff.
    eexists (normal_fact (clause_rel c) _). split.
    - cbv [fact_equiv]. simpl. f_equal. assumption.
    - eauto.
  Qed.

  Lemma Forall2_interp_clause_map_fw ctx hyps1 hyps2 :
    Forall2 (interp_clause ctx) hyps1 hyps2 ->
    Forall2 (interp_clause ctx) (map map_clause_rel hyps1) (map map_fact hyps2).
  Proof.
    intros.
    rewrite <- Forall2_map_l, <- Forall2_map_r.
    eapply Forall2_impl; [eassumption|].
    eauto using interp_clause_map_fw.
  Qed.

  Lemma Forall2_interp_clause_map_bw ctx hyps1 hyps2 :
    Forall2 (interp_clause ctx) (map map_clause_rel hyps1) (map map_fact hyps2) ->
    exists hyps2',
      Forall2 fact_equiv hyps2 hyps2' /\
      Forall2 (interp_clause ctx) hyps1 hyps2'.
  Proof.
    intros H. rewrite <- Forall2_map_l, <- Forall2_map_r in H.
    induction H.
    - eexists []. split; constructor.
    - apply interp_clause_map_bw in H. destruct H as [h' [Heq Hinterp]].
      destruct IHForall2 as [hyps2' [HForall_eq HForall_interp]].
      eexists (h' :: hyps2'). split; constructor; eauto.
  Qed.

  Lemma Forall2_interp_clause_map_bw' ctx hyps1 hyps2 :
    Forall2 (interp_clause ctx) (map map_clause_rel hyps1) (map map_fact hyps2) ->
    Forall2 (fun c h => exists h', fact_equiv h h' /\ interp_clause ctx c h') hyps1 hyps2.
  Proof.
    intros H. rewrite <- Forall2_map_l, <- Forall2_map_r in H.
    eapply Forall2_impl; [eassumption|].
    eauto using interp_clause_map_bw.
  Qed.

  Definition map_meta_clause_rel (c : meta_clause) : meta_clause :=
    {| meta_clause_rel := f c.(meta_clause_rel);
      meta_clause_args := c.(meta_clause_args) |}.

  Definition map_rule_rels (r : rule) : rule :=
    match r with
    | normal_rule concls hyps =>
        normal_rule (map (map_clause_rel) concls) (map (map_clause_rel) hyps)
    | meta_rule concls hyps =>
        meta_rule (map (map_meta_clause_rel) concls) (map (map_meta_clause_rel) hyps)
    | agg_rule concl agg hyp =>
        agg_rule (f concl) agg (f hyp)
    end.

  Lemma non_meta_rule_impl_map_fw r R args hyps :
    non_meta_rule_impl r R args hyps ->
    non_meta_rule_impl (map_rule_rels r) (f R) args (map map_fact hyps).
  Proof.
    invert 1.
    - econstructor.
      + apply Exists_map. eapply Exists_impl; [|eassumption].
        simpl. intros c Hc. eapply interp_clause_map_fw in Hc. eassumption.
      + apply Forall2_interp_clause_map_fw. eassumption.
    - simpl. eassert (meta_fact _ _ _ :: _ = _) as ->.
      2: { econstructor. eassumption. }
      f_equal. rewrite map_map. apply map_ext. intros [? ?]. reflexivity.
  Qed.

  Lemma interp_meta_clause_map_fw ctx c f0 :
    interp_meta_clause ctx c f0 ->
    interp_meta_clause ctx (map_meta_clause_rel c) (map_fact f0).
  Proof.
    cbv [interp_meta_clause]. intros. fwd. unfold map_fact. eauto.
  Qed.

  Lemma Forall2_interp_meta_clause_map_fw ctx hyps1 hyps2 :
    Forall2 (interp_meta_clause ctx) hyps1 hyps2 ->
    Forall2 (interp_meta_clause ctx) (map map_meta_clause_rel hyps1) (map map_fact hyps2).
  Proof.
    intros. rewrite <- Forall2_map_l, <- Forall2_map_r.
    eapply Forall2_impl; [eassumption|].
    eauto using interp_meta_clause_map_fw.
  Qed.

Lemma fact_matches_map_fw f1 f2 :
  fact_matches f1 f2 ->
  fact_matches (map_fact f1) (map_fact f2).
Proof.
  intros. cbv [fact_matches] in *. fwd. unfold map_fact. eauto 10.
Qed.

Lemma fact_matches_map_bw f1 f2 :
    fact_matches (map_fact f1) (map_fact f2) ->
    exists f1' f2',
      fact_equiv f1 f1' /\
      fact_equiv f2 f2' /\
      fact_matches f1' f2'.
  Proof.
    intros H. cbv [fact_matches] in H. fwd.
    destruct f1, f2; simpl in *; repeat invert_stuff.
    exists (normal_fact nf_rel nf_args), (meta_fact nf_rel mf_args mf_set).
    split; [|split].
    - cbv [fact_equiv]. simpl. f_equal.
    - cbv [fact_equiv]. simpl. f_equal. congruence.
    - cbv [fact_matches]. eauto 10.
  Qed.

  Hint Unfold interp_meta_clause : core.
  Lemma interp_meta_clause_map_bw ctx c h :
    interp_meta_clause ctx (map_meta_clause_rel c) (map_fact h) ->
    exists h', fact_equiv h h' /\ interp_meta_clause ctx c h'.
  Proof.
    intros H. cbv [interp_meta_clause] in H. fwd.
    destruct h; simpl in *; repeat invert_stuff.
    eexists (meta_fact (meta_clause_rel c) _ _). split.
    - cbv [fact_equiv]. simpl. f_equal. assumption.
    - eauto.
  Qed.

  Lemma Forall2_interp_meta_clause_map_bw' ctx hyps1 hyps2 :
    Forall2 (interp_meta_clause ctx) (map map_meta_clause_rel hyps1) (map map_fact hyps2) ->
    Forall2 (fun c h => exists h', fact_equiv h h' /\ interp_meta_clause ctx c h') hyps1 hyps2.
  Proof.
    intros H. rewrite <- Forall2_map_l, <- Forall2_map_r in H.
    eapply Forall2_impl; [eassumption|].
    eauto using interp_meta_clause_map_bw.
  Qed.

      Lemma rel_of_map_fact fct :
    rel_of (map_fact fct) = f (rel_of fct).
  Proof.
    destruct fct; reflexivity.
  Qed.

  Lemma args_of_map_fact fct :
    args_of (map_fact fct) = args_of fct.
  Proof.
    destruct fct; reflexivity.
  Qed.

  Lemma non_meta_rule_impl_map_bw r R args hyps :
    non_meta_rule_impl (map_rule_rels r) (f R) args (map map_fact hyps) ->
    exists R0 hyps0,
      rel_equiv R R0 /\
      Forall2 fact_equiv hyps hyps0 /\
        non_meta_rule_impl r R0 args hyps0.
  Proof.
    intros H. destruct r; invert H.
    - rewrite Exists_map in H2.
      apply Forall2_interp_clause_map_bw in H6.
      apply Exists_exists in H2. fwd.
      apply interp_clause_map_bw with (h := normal_fact _ _) in H2p1.
      fwd. cbv [fact_equiv] in H2p1p0. simpl in H2p1p0.
      destruct h'; simpl in H2p1p0; congruence || fwd.
      eexists nf_rel, _. ssplit; eauto.
      econstructor.
      + apply Exists_exists. eexists. split; [exact H2p0 |].
        eassumption.
      + eassumption.
    - destruct hyps as [|hyp hyps]; simpl in *; discriminate || fwd.
      destruct hyp; simpl in *; discriminate || fwd.
      do 2 eexists. split; [symmetry; eassumption|].
      split.
      2: { econstructor. eassumption. }
      constructor.
      { cbv [fact_equiv]. simpl. f_equal. auto. }
      rewrite <- Forall2_map_r.
      eapply Forall2_impl.
      1: { eapply map_eq_Forall2. symmetry. eassumption. }
      simpl. intros f' (?, ?) Hf'. destruct f'; simpl in Hf'; discriminate || fwd.
      cbv [fact_equiv]. simpl. f_equal. auto.
  Qed.

  Lemma non_meta_rule_invert_map r R args hyps :
    non_meta_rule_impl (map_rule_rels r) (f R) args hyps ->
    exists hyps0,
      hyps = map map_fact hyps0.
  Proof.
    intros H. destruct r; invert H.
    - rewrite Exists_map in *. rewrite <- Forall2_map_l in *.
      epose proof Forall_exists_r_Forall2 as H'. edestruct H' as [hyps0 Hhyps0].
      2: { eexists. apply Forall2_eq_map. apply Forall2_flip. eassumption. }
      apply Forall2_forget_l in H6. eapply Forall_impl; [|eassumption].
      simpl. intros. fwd. repeat invert_stuff. simpl.
      eexists (normal_fact _ _). reflexivity.
    - eexists (meta_fact _ _ _ ::
               map (fun '(x, y) => normal_fact hyp_rel (x :: y :: _)) _).
      simpl. f_equal. rewrite map_map.
      apply map_ext. intros [? ?]. reflexivity.
  Qed.

  Lemma extensionally_equal_map_fw f1 f2 :
    extensionally_equal f1 f2 ->
    extensionally_equal (map_fact f1) (map_fact f2).
  Proof.
    intros H. destruct f1, f2; cbv [extensionally_equal] in *; try contradiction; fwd.
    - split; [f_equal; auto | auto].
    - split; [f_equal; auto | split; auto].
  Qed.

  Lemma extensionally_equal_map_bw f1 f2 :
    extensionally_equal (map_fact f1) (map_fact f2) ->
    exists f1' f2',
      fact_equiv f1 f1' /\
      fact_equiv f2 f2' /\
      extensionally_equal f1' f2'.
  Proof.
    intros H. destruct f1 as [R1 args1 | R1 mf_args1 mf_set1],
                       f2 as [R2 args2 | R2 mf_args2 mf_set2];
    cbv [extensionally_equal] in H; try contradiction; fwd.
    - exists (normal_fact R1 args1), (normal_fact R1 args2).
      simpl in *. fwd.
      split; [|split].
      + cbv [fact_equiv]. reflexivity.
      + cbv [fact_equiv]. simpl in *. f_equal. congruence.
      + cbv [extensionally_equal]. auto.
    - exists (meta_fact R1 mf_args1 mf_set1), (meta_fact R1 mf_args2 mf_set2).
      simpl in *. fwd.
      split; [|split].
      + cbv [fact_equiv]. reflexivity.
      + cbv [fact_equiv]. simpl. f_equal. congruence.
      + cbv [extensionally_equal]. eauto.
  Qed.

  Definition meta_facts_consistent_with_map (meta_facts : list fact) :=
    forall R1 args1 S1 R2 args2 S2,
      In (meta_fact R1 args1 S1) meta_facts ->
      In (meta_fact R2 args2 S2) meta_facts ->
      f R1 = f R2 ->
      forall nf_args,
        Forall2 matches args1 nf_args ->
        Forall2 matches args2 nf_args ->
        S1 nf_args <-> S2 nf_args.

  Lemma meta_cond_map_iff mr mf_args mf_set p R (args : list T) meta_hyps :
    meta_rules_valid p ->
    In mr p ->
    rule_impl (one_step_derives p) mr (meta_fact R mf_args mf_set) meta_hyps ->
    Forall2 matches mf_args args ->
    meta_facts_consistent_with_map meta_hyps ->
    injective_on R ->
    one_step_derives p meta_hyps R args <->
      one_step_derives (map map_rule_rels p) (map map_fact meta_hyps) (f R) args.
  Proof.
    intros Hvalid HIn Hmr Hmf_args Hmfs_consistent Hinj.
    cbv [one_step_derives one_step_derives0].
    pose proof Hmr as Hmh.
    apply meta_hyps_are_meta_facts in Hmh.
    apply Hvalid in Hmr; [|assumption].
    clear Hvalid HIn.
    split; intros H; fwd.
    - eexists. split.
      { apply Exists_map. eapply Exists_impl; [|eassumption]. simpl.
        intros. apply non_meta_rule_impl_map_fw. eassumption. }
      rewrite Lists.List.Forall_map. eapply Forall_impl; [|eassumption].
      intros f' Hex. apply Exists_exists in Hex. fwd.
      apply Exists_exists. eexists. split; [apply in_map; eassumption |].
      destruct Hexp1 as [Hext | Hmatch].
      + left. apply extensionally_equal_map_fw. eassumption.
      + right. apply fact_matches_map_fw. eassumption.
    - apply Exists_map in Hp0. apply Exists_exists in Hp0. fwd.
      pose proof Hp0p1 as Hp1'.
      apply non_meta_rule_invert_map in Hp0p1. fwd.
      eapply non_meta_rule_impl_map_bw in Hp1'. fwd.
      apply Hinj in Hp1'p0. subst.
      specialize (Hmr _ _ _ ltac:(eassumption) ltac:(eauto) ltac:(eassumption)).
      eexists. split; [apply Exists_exists; eauto |].
      clear Hp1'p2.
      rewrite Lists.List.Forall_map in Hp1.
      apply Forall2_forget_l in Hp1'p1. apply Forall_forall.
      intros f' Hf'. rewrite Forall_forall in Hp1'p1.
      specialize (Hp1'p1 _ Hf'). fwd.
      rewrite Forall_forall in Hp1.
      specialize (Hp1 _ ltac:(eassumption)). apply Exists_map in Hp1.
      apply Exists_exists in Hp1. fwd.
      rewrite Forall_forall in Hmr. specialize (Hmr _ Hf').
      cbv [fact_potentially_supported] in Hmr.
      rewrite Forall_forall in Hmh. specialize (Hmh _ ltac:(eassumption)).
      destruct Hp1p1 as [Hext | Hmatch].
      * apply extensionally_equal_map_bw in Hext. fwd.
        destruct f'.
        { (*gross*)
          exfalso.
          destruct x0, x1, f1', f2';
            cbv [is_meta] in Hmh; try contradiction;
            cbv [fact_equiv map_fact] in Hp1'p1p1; try discriminate Hp1'p1p1;
            cbv [fact_equiv map_fact] in Hextp0; try discriminate Hextp0;
            cbv [fact_equiv map_fact] in Hextp1; try discriminate Hextp1;
            cbv [extensionally_equal] in Hextp2; try contradiction. }
        fwd.
        apply Exists_exists. eexists. split; [exact Hmr|].
        left. simpl. ssplit; auto.
        intros args' Hargs'.
        cbv [fact_equiv map_fact] in Hp1'p1p1, Hextp0, Hextp1.
        destruct x0 as [| R_x0 args_x0 S_x0]; try discriminate.
        destruct f1' as [| R_f1 args_f1 S_f1]; try discriminate.
        destruct f2' as [| R_f2 args_f2 S_f2]; try contradiction.
        destruct x1 as [| R_x1 args_x1 S_x1]; try discriminate.
        simpl in Hextp2. fwd.
        rewrite Hextp2p2 by assumption.
        eapply Hmfs_consistent; try eassumption.
        congruence.
      * apply fact_matches_map_bw in Hmatch. fwd.
        destruct f'.
        2: { exfalso.
             cbv [fact_matches] in Hmatchp2. fwd.
             cbv [fact_equiv map_fact] in Hmatchp0, Hp1'p1p1.
             destruct x0; congruence. }
        fwd. apply Exists_exists. eexists. split; [exact Hmrp0|].
        right. cbv [fact_matches]. do 4 eexists. ssplit; try reflexivity.
        1: assumption.
        cbv [fact_matches] in Hmatchp2.
        destruct Hmatchp2 as [R_f [nf_args_f [mf_args_f [mf_set_f [H_match_args [H_set_eval [H_f1' H_f2']]]]]]].
        subst f1' f2'.

        cbv [fact_equiv map_fact] in Hp1'p1p1, Hmatchp0, Hmatchp1.
        destruct x0 as [R_x0 args_x0 | ]; try discriminate.
        destruct x1 as [ | R_x1 mf_args_x1 S_x1]; try contradiction.
        fwd.
        fwd. cbv [meta_facts_consistent_with_map] in Hmfs_consistent.
        rewrite Hmfs_consistent; eauto. congruence.
  Qed.

  Lemma rule_impl_map_rule_rels_fw p r f0 hyps :
    meta_rules_valid p ->
    In r p ->
    injective_on (rel_of f0) ->
    meta_facts_consistent_with_map hyps ->
    rule_impl (one_step_derives p) r f0 hyps ->
    rule_impl (one_step_derives (map map_rule_rels p))
      (map_rule_rels r)
      (map_fact f0)
      (map map_fact hyps).
  Proof.
    intros Hvalid Hr Hinj Hcon Himpl. pose proof Himpl as Himpl0. invert Himpl.
    - econstructor. apply non_meta_rule_impl_map_fw. eassumption.
    - simpl. econstructor.
      + rewrite Exists_map. eapply Exists_impl; [|eassumption].
        simpl. intros c Hc. eapply interp_meta_clause_map_fw in Hc. eassumption.
      + apply Forall2_interp_meta_clause_map_fw. eassumption.
      + intros args'' Hargs. rewrite H1 by assumption.
        eapply meta_cond_map_iff; eassumption.
  Qed.

  Lemma Forall2_interp_meta_clause_map_bw ctx hyps1 hyps2 :
    Forall2 (interp_meta_clause ctx) (map map_meta_clause_rel hyps1) (map map_fact hyps2) ->
    exists hyps2',
      Forall2 fact_equiv hyps2 hyps2' /\
      Forall2 (interp_meta_clause ctx) hyps1 hyps2'.
  Proof.
    intros H. rewrite <- Forall2_map_l, <- Forall2_map_r in H.
    induction H.
    - eexists []. split; constructor.
    - apply interp_meta_clause_map_bw in H. destruct H as [h' [Heq Hinterp]].
      destruct IHForall2 as [hyps2' [HForall_eq HForall_interp]].
      eexists (h' :: hyps2'). split; constructor; eauto.
  Qed.

  Lemma meta_facts_consistent_with_map_equiv hyps hyps' :
    meta_facts_consistent_with_map hyps ->
    Forall2 fact_equiv hyps hyps' ->
    meta_facts_consistent_with_map hyps'.
  Proof.
    intros Hcon Heq.
    cbv [meta_facts_consistent_with_map].
    intros R1 args1 S1 R2 args2 S2 Hin1 Hin2 Hf_eq nf_args Hmatch1 Hmatch2.

    apply Forall2_forget_l in Heq. rewrite Forall_forall in Heq.
    apply Heq in Hin1, Hin2. fwd.

    cbv [fact_equiv map_fact] in Hin1p1, Hin2p1.
    destruct x as [| R1' args1' S1']; try discriminate.
    destruct x0 as [| R2' args2' S2']; try discriminate.
    fwd. eauto using eq_trans.
  Qed.

  Lemma rule_impl_map_rule_rels_bw p r f0 hyps :
    meta_rules_valid p ->
    In r p ->
    injective_on (rel_of f0) ->
    meta_facts_consistent_with_map hyps ->
    rule_impl (one_step_derives (map map_rule_rels p))
      (map_rule_rels r)
      (map_fact f0)
      (map map_fact hyps) ->
    exists f0' hyps',
      fact_equiv f0 f0' /\
      Forall2 fact_equiv hyps hyps' /\
      rule_impl (one_step_derives p) r f0' hyps'.
  Proof.
    intros Hvalid Hr Hinj Hcon Himpl. invert Himpl.
    - destruct f0; simpl in *; repeat invert_stuff.
      eassert (H':_) by (eapply non_meta_rule_impl_map_bw; eassumption).
      fwd. apply Hinj in H'p0. subst. eauto 7.
    - destruct f0; simpl in *; congruence || fwd.
      destruct r; simpl in *; congruence || fwd.
      apply Forall2_interp_meta_clause_map_bw in H2. fwd.
      rewrite Exists_map in H1. apply Exists_exists in H1. fwd.
      apply interp_meta_clause_map_bw with (h := meta_fact _ _ _) in H1p1. fwd.
      do 2 eexists. split; [eassumption|]. split; [eassumption|].
      cbv [fact_equiv] in H1p1p0. simpl in H1p1p0.
      destruct h'; simpl in H1p1p0; try discriminate. fwd.
      econstructor.
      + apply Exists_exists. eauto.
      + assumption.
      + intros. rewrite H3 by assumption. symmetry.
        apply Hinj in H1. subst.
        replace (map map_fact hyps) with (map map_fact hyps2').
        2: { apply Forall2_eq_map. rewrite <- Forall2_map_r.
             eapply Forall2_impl; [eassumption|].
             auto. }
        eapply meta_cond_map_iff; try eassumption.
        2: { eauto using meta_facts_consistent_with_map_equiv. }
        econstructor.
        -- apply Exists_exists. eexists. split; [eassumption|].
           cbv [interp_meta_clause]. cbv [interp_meta_clause] in H1p1p1.
           fwd. eauto.
        -- assumption.
        -- intros. reflexivity.
  Qed.

  Lemma rule_impl_map_rule_rels_f_target blah r f_target hyps :
    rule_impl blah (map_rule_rels r) f_target hyps ->
    exists f0, f_target = map_fact f0 /\ In (rel_of f0) (concl_rels r).
  Proof.
    invert 1.
    - destruct r; simpl in H0; invert H0.
      + rewrite Exists_map in H2. apply Exists_exists in H2. fwd.
        cbv [interp_clause] in H2p1. fwd.
        eexists (normal_fact _ _). simpl. auto using in_map.
      + eexists (normal_fact _ _). simpl. auto using in_map.
    - destruct r; simpl in H0; invert H0.
      rewrite Exists_map in H1. apply Exists_exists in H1. fwd.
      cbv [interp_meta_clause] in H1p1. fwd.
      eexists (meta_fact _ _ _). simpl. auto using in_map.
  Qed.

  Lemma prog_impl_fact_equiv (p : list rule) Q f1 f2 :
    Forall injective_on (flat_map concl_rels p) ->
    (forall f1' f2', fact_equiv f1' f2' -> Q f1' <-> Q f2') ->
    fact_equiv f1 f2 ->
    prog_impl p Q f1 <-> prog_impl p Q f2.
  Proof.
    intros Hinj HQ Heq. split; intros Hprog.
    - pose proof Hprog as Hprog_copy. apply prog_impl_rel_of in Hprog_copy.
      destruct Hprog_copy as [HQ1 | Hconcl].
      + apply prog_impl_leaf. apply (proj1 (HQ _ _ Heq)). exact HQ1.
      + rewrite Forall_forall in Hinj. apply Hinj in Hconcl. cbv [injective_on] in Hconcl.
        destruct f1 as [R1 args1 | R1 mf_args1 S1], f2 as [R2 args2 | R2 mf_args2 S2];
          cbv [fact_equiv map_fact] in Heq; try discriminate;
          inversion Heq;
          assert (f R1 = f R2) by congruence;
          apply Hconcl in H; subst; exact Hprog.
    - pose proof Hprog as Hprog_copy. apply prog_impl_rel_of in Hprog_copy.
      destruct Hprog_copy as [HQ2 | Hconcl].
      + apply prog_impl_leaf. apply (proj2 (HQ _ _ Heq)). exact HQ2.
      + rewrite Forall_forall in Hinj. apply Hinj in Hconcl. cbv [injective_on] in Hconcl.
        destruct f1 as [R1 args1 | R1 mf_args1 S1], f2 as [R2 args2 | R2 mf_args2 S2];
          cbv [fact_equiv map_fact] in Heq; try discriminate;
          inversion Heq;
          assert (f R2 = f R1) by congruence;
          apply Hconcl in H; subst; exact Hprog.
  Qed.

  Lemma prog_impl_map_rule_rels_fw p Q f0 :
    meta_rules_valid p ->
    (forall f, Q f -> ~ In (rel_of f) (flat_map concl_rels p)) ->
    doesnt_lie Q ->
    (forall f1 f2, fact_equiv f1 f2 -> Q f1 <-> Q f2) ->
    Forall injective_on (flat_map concl_rels p) ->
    prog_impl p Q f0 ->
    prog_impl (map map_rule_rels p) (fun f' => exists f, f' = map_fact f /\ Q f) (map_fact f0).
  Proof.
    intros Hvalid Hinp Hlie HQ Hinj Hprog.
    induction Hprog.
    - apply prog_impl_leaf. eexists; eauto.
    - apply Exists_exists in H. destruct H as [r [Hr_in Hr_impl]].
      eapply prog_impl_step.
      + apply Exists_map. apply Exists_exists. exists r. split; [exact Hr_in|].
        eapply rule_impl_map_rule_rels_fw; try eassumption.
        * rewrite Forall_forall in Hinj. apply Hinj. apply in_flat_map.
          eexists. split; [eassumption|].
          eapply rule_impl_concl_relname_in. eassumption.
        * intros R1 args1 S1 R2 args2 S2 Hin1 Hin2 Heq nf_args Hmatch1 Hmatch2.
          rewrite Forall_forall in H0.
          eapply meta_facts_consistent.
          -- eassumption.
          -- intros R' args1' args2' S1' S2' HQ1 HQ2 nf_args' Hmatch1' Hmatch2'.
             cbv [doesnt_lie consistent] in Hlie.
             rewrite (Hlie _ _ _ HQ1 _ Hmatch1'), (Hlie _ _ _ HQ2 _ Hmatch2').
             reflexivity.
          -- eassumption.
          -- apply H0. exact Hin1.
          -- rewrite prog_impl_fact_equiv; try eassumption.
             ++ apply H0. exact Hin2.
             ++ cbv [fact_equiv]. simpl. f_equal. congruence.
          -- eassumption.
          -- eassumption.
      + rewrite Lists.List.Forall_map. eapply Forall_impl; [|eassumption].
        simpl. auto.
  Qed.

  Hint Resolve prog_impl_leaf : core.
  Lemma prog_impl_map_rule_rels_bw' p Q f_target :
    meta_rules_valid p ->
    (forall f, Q f -> ~ In (rel_of f) (flat_map concl_rels p)) ->
    doesnt_lie Q ->
    (forall f1 f2, fact_equiv f1 f2 -> Q f1 <-> Q f2) ->
    Forall injective_on (flat_map concl_rels p) ->
    prog_impl (map map_rule_rels p) (fun f' => exists f, f' = map_fact f /\ Q f) f_target ->
    exists f0, f_target = map_fact f0 /\ prog_impl p Q f0.
  Proof.
    intros Hvalid Hinp Hlie HQ Hinj Hprog.
    induction Hprog.
    - fwd. eauto.
    - apply Exists_map in H. apply Exists_exists in H. fwd.
      pose proof Hp1 as H'. apply rule_impl_map_rule_rels_f_target in H'.
      fwd.
      apply Forall_exists_r_Forall2 in H1. fwd.
      pose proof H1 as H1'.
      apply Forall2_flip in H1'. eapply Forall2_impl in H1'.
      1: eapply Forall2_eq_map in H1'.
      2: { intros. fwd. eauto. }
      subst.
      eassert (H':_).
      { eapply rule_impl_map_rule_rels_bw; try eassumption.
        - rewrite Forall_forall in Hinj. apply Hinj. apply in_flat_map.
          eexists. split; [eassumption|]. assumption.
        - intros R1 args1 S1 R2 args2 S2 Hin1 Hin2 Heq nf_args Hmatch1 Hmatch2.
          rewrite Forall_forall in H0. Check meta_facts_consistent.
          eapply meta_facts_consistent.
          -- eassumption.
          -- intros R' args1' args2' S1' S2' HQ1 HQ2 nf_args' Hmatch1' Hmatch2'.
             cbv [doesnt_lie consistent] in Hlie.
             rewrite (Hlie _ _ _ HQ1 _ Hmatch1'), (Hlie _ _ _ HQ2 _ Hmatch2').
             reflexivity.
          -- eassumption.
          -- apply Forall2_forget_l in H1. rewrite Forall_forall in H1.
             apply H1 in Hin1. fwd. eassumption.
          -- rewrite prog_impl_fact_equiv; try eassumption.
             ++ apply Forall2_forget_l in H1. rewrite Forall_forall in H1.
                apply H1 in Hin2. fwd. eassumption.
             ++ cbv [fact_equiv]. simpl. f_equal. congruence.
          -- eassumption.
          -- eassumption. }
      fwd.
      eexists. split; [eassumption|].
      eapply prog_impl_step.
      { apply Exists_exists. eauto. }
      apply Forall2_forget_l in H'p2, H1. rewrite Forall_forall in H1, H'p2.
      apply Forall_forall. intros f' Hf'. apply H'p2 in Hf'. fwd.
      apply H1 in Hf'p0. fwd.
      rewrite <- prog_impl_fact_equiv; eassumption.
  Qed.

  Lemma map_fact_inj f0 f0' :
    injective_on (rel_of f0) ->
    map_fact f0 = map_fact f0' ->
    f0 = f0'.
  Proof.
    intros Hinj Heq.
    destruct f0 as [R1 args1 | R1 mf_args1 S1],
             f0' as [R2 args2 | R2 mf_args2 S2];
      cbv [map_fact rel_of] in *; try discriminate.
    - (* Case: normal_fact *)
      inversion Heq; subst.
      assert (R1 = R2) by (apply Hinj; congruence).
      subst. reflexivity.
    - (* Case: meta_fact *)
      inversion Heq; subst.
      assert (R1 = R2) by (apply Hinj; congruence).
      subst. reflexivity.
  Qed.

  Lemma prog_impl_map_rule_rels_iff p Q f0 :
    meta_rules_valid p ->
    (forall f, Q f -> ~ In (rel_of f) (flat_map concl_rels p)) ->
    doesnt_lie Q ->
    (forall f1 f2, fact_equiv f1 f2 -> Q f1 <-> Q f2) ->
    Forall injective_on (flat_map concl_rels p) ->
    injective_on (rel_of f0) ->
    prog_impl p Q f0 <->
    prog_impl (map map_rule_rels p) (fun f' => exists f, f' = map_fact f /\ Q f) (map_fact f0).
  Proof.
    intros. split; intros H'.
    - apply prog_impl_map_rule_rels_fw; assumption.
    - eapply prog_impl_map_rule_rels_bw' in H'; try assumption.
      destruct H' as [f0' [Heq Hprog]].
      eapply map_fact_inj in Heq; try assumption. subst. assumption.
  Qed.

  Lemma concl_rels_map_rule_rels r :
    concl_rels (map_rule_rels r) = map f (concl_rels r).
  Proof.
    destruct r; simpl.
    - do 2 rewrite map_map. reflexivity.
    - do 2 rewrite map_map. reflexivity.
    - reflexivity.
  Qed.

  Lemma hyp_rels_map_rule_rels r :
    hyp_rels (map_rule_rels r) = map f (hyp_rels r).
  Proof.
    destruct r; simpl.
    - do 2 rewrite map_map. reflexivity.
    - do 2 rewrite map_map. reflexivity.
    - reflexivity.
  Qed.

  Lemma all_rels_map_rule_rels r :
    all_rels (map_rule_rels r) = map f (all_rels r).
  Proof.
    cbv [all_rels].
    rewrite concl_rels_map_rule_rels, hyp_rels_map_rule_rels.
    rewrite map_app. reflexivity.
  Qed.

  Lemma fact_of_g_args_of fct :
    fact_of (f (rel_of fct)) (args_of fct) = map_fact fct.
  Proof. destruct fct; reflexivity. Qed.

  Lemma map_fact_fact_of R args :
    map_fact (fact_of R args) = fact_of (f R) args.
  Proof.
    destruct args; reflexivity.
  Qed.

  Lemma map_fact_eq_fact_of f0 :
    map_fact f0 = fact_of (f (rel_of f0)) (args_of f0).
  Proof.
    destruct f0; reflexivity.
  Qed.

  (*now an easier theorem: if f happens to be injective, then the renaming is automatically correct*)
  Context (f_inj : forall x y, f x = f y -> x = y).

  Lemma map_fact_inj_g a b :
    map_fact a = map_fact b -> a = b.
  Proof.
    intros H. eapply map_fact_inj; [|exact H].
    intros y Hy. apply f_inj. exact Hy.
  Qed.

  Lemma Forall2_fact_equiv_eq l1 l2 :
    Forall2 fact_equiv l1 l2 -> l1 = l2.
  Proof.
    induction 1; [reflexivity|].
    f_equal; [apply map_fact_inj_g; exact H | exact IHForall2].
  Qed.

  Lemma non_meta_rule_impl_map_bw_inj r R args hyps :
    non_meta_rule_impl (map_rule_rels r) (f R) args (map map_fact hyps) ->
    non_meta_rule_impl r R args hyps.
  Proof.
    intros H. apply non_meta_rule_impl_map_bw in H. fwd.
    cbv [rel_equiv] in Hp0. apply f_inj in Hp0. subst.
    apply Forall2_fact_equiv_eq in Hp1. subst. exact Hp2.
  Qed.

  Lemma fact_supported_map_iff_inj meta_facts g :
    fact_supported meta_facts g <->
    fact_supported (map map_fact meta_facts) (map_fact g).
  Proof.
    cbv [fact_supported]. rewrite Exists_map. split; intros H.
    - eapply Exists_impl; [|exact H]. simpl. intros hyp [Hh|Hh].
      + left. apply extensionally_equal_map_fw. exact Hh.
      + right. apply fact_matches_map_fw. exact Hh.
    - eapply Exists_impl; [|exact H]. simpl. intros hyp [Hh|Hh].
      + left. apply extensionally_equal_map_bw in Hh. fwd.
        cbv [fact_equiv] in Hhp0, Hhp1.
        apply map_fact_inj_g in Hhp0, Hhp1. subst. exact Hhp2.
      + right. apply fact_matches_map_bw in Hh. fwd.
        cbv [fact_equiv] in Hhp0, Hhp1.
        apply map_fact_inj_g in Hhp0, Hhp1. subst. exact Hhp2.
  Qed.

  Lemma one_step_derives_map_iff_inj p meta_facts R args :
    one_step_derives p meta_facts R args <->
    one_step_derives (map map_rule_rels p) (map map_fact meta_facts) (f R) args.
  Proof.
    cbv [one_step_derives one_step_derives0]. split; intros H; fwd.
    - exists (map map_fact hyps). split.
      + apply Exists_map. eapply Exists_impl; [|exact Hp0]. simpl.
        intros r Hr. apply non_meta_rule_impl_map_fw. exact Hr.
      + rewrite Lists.List.Forall_map. eapply Forall_impl; [|exact Hp1]. simpl.
        intros x Hx. apply fact_supported_map_iff_inj. exact Hx.
    - apply Exists_map in Hp0. apply Exists_exists in Hp0. fwd.
      pose proof Hp0p1 as Hinv. apply non_meta_rule_invert_map in Hinv. fwd. subst.
      apply non_meta_rule_impl_map_bw_inj in Hp0p1.
      exists hyps0. split.
      + apply Exists_exists. eexists. split; [exact Hp0p0|]. exact Hp0p1.
      + rewrite Lists.List.Forall_map in Hp1. eapply Forall_impl; [|exact Hp1]. simpl.
        intros fct Hfct. apply fact_supported_map_iff_inj. exact Hfct.
  Qed.

  Lemma rule_impl_map_iff_inj p r f0 hyps :
    rule_impl (one_step_derives p) r f0 hyps <->
    rule_impl (one_step_derives (map map_rule_rels p))
      (map_rule_rels r) (map_fact f0) (map map_fact hyps).
  Proof.
    split; intros H.
    - invert H.
      + simpl. apply simple_rule_impl. apply non_meta_rule_impl_map_fw. exact H0.
      + simpl. eapply meta_rule_impl.
        * rewrite Exists_map. eapply Exists_impl; [|exact H0]. simpl.
          intros c Hc. apply interp_meta_clause_map_fw in Hc. exact Hc.
        * apply Forall2_interp_meta_clause_map_fw. exact H1.
        * intros args'' Hargs. rewrite (H2 args'' Hargs).
          apply one_step_derives_map_iff_inj.
    - invert H.
      + destruct f0; simpl in *; repeat invert_stuff.
        apply simple_rule_impl. apply non_meta_rule_impl_map_bw_inj. eassumption.
      + destruct f0; simpl in *; congruence || fwd.
        destruct r; simpl in *; congruence || fwd.
        apply Forall2_interp_meta_clause_map_bw in H3. fwd.
        apply Forall2_fact_equiv_eq in H3p0. subst.
        rewrite Exists_map in H2. apply Exists_exists in H2. fwd.
        apply interp_meta_clause_map_bw with (h := meta_fact _ _ _) in H2p1. fwd.
        cbv [fact_equiv] in H2p1p0. apply map_fact_inj_g in H2p1p0. subst.
        eapply meta_rule_impl.
        * apply Exists_exists. eexists. split; [exact H2p0|]. exact H2p1p1.
        * exact H3p1.
        * intros args'' Hargs. rewrite (H4 args'' Hargs). symmetry.
          apply one_step_derives_map_iff_inj.
  Qed.

  Lemma prog_impl_map_fw_inj p Q f0 :
    prog_impl p Q f0 ->
    prog_impl (map map_rule_rels p)
      (fun f' => exists f, f' = map_fact f /\ Q f) (map_fact f0).
  Proof.
    intros Hprog. induction Hprog.
    - apply prog_impl_leaf. eexists; eauto.
    - apply Exists_exists in H. destruct H as [r [Hr_in Hr_impl]].
      eapply prog_impl_step.
      + apply Exists_map. apply Exists_exists. exists r. split; [exact Hr_in|].
        apply rule_impl_map_iff_inj. exact Hr_impl.
      + rewrite Lists.List.Forall_map. eapply Forall_impl; [|eassumption]. simpl. auto.
  Qed.

  Lemma prog_impl_map_bw_inj p Q f_target :
    prog_impl (map map_rule_rels p)
      (fun f' => exists f, f' = map_fact f /\ Q f) f_target ->
    exists f0, f_target = map_fact f0 /\ prog_impl p Q f0.
  Proof.
    intros Hprog. induction Hprog.
    - fwd. eauto.
    - apply Exists_map in H. apply Exists_exists in H. fwd.
      pose proof Hp1 as Htgt. apply rule_impl_map_rule_rels_f_target in Htgt. fwd. subst.
      apply Forall_exists_r_Forall2 in H1. fwd.
      pose proof H1 as H1'.
      apply Forall2_flip in H1'. eapply Forall2_impl in H1'.
      1: eapply Forall2_eq_map in H1'.
      2: { intros. fwd. eauto. }
      subst.
      apply rule_impl_map_iff_inj in Hp1.
      eexists. split; [reflexivity|].
      eapply prog_impl_step.
      { apply Exists_exists. eexists. split; [exact Hp0|]. exact Hp1. }
      apply Forall2_forget_l in H1. eapply Forall_impl; [|exact H1].
      simpl. intros g0 Hg0. fwd. assumption.
  Qed.

  Lemma prog_impl_map_rule_rels_iff_inj p Q f0 :
    prog_impl p Q f0 <->
    prog_impl (map map_rule_rels p) (fun f' => exists f, f' = map_fact f /\ Q f) (map_fact f0).
  Proof.
    split; intros H.
    - apply prog_impl_map_fw_inj. exact H.
    - apply prog_impl_map_bw_inj in H. fwd.
      apply map_fact_inj_g in Hp0. subst. exact Hp1.
  Qed.
End RelMap.
