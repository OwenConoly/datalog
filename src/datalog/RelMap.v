From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.

From Datalog Require Import Map Tactics Fp List Datalog.
From GraphSearch Require Import Dag.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List Datatypes.Option Eqb.

Import ListNotations.

Section RelMap.
  Context {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context {semantics : datalog_semantics fn aggregator T}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.

  Context {rel1 rel2} (f : rel1 -> rel2).

  Definition inj_on_elt (x : rel1) : Prop :=
    forall y, f x = f y -> x = y.

  Definition rel_equiv R1 R2 := f R1 = f R2.

  Definition map_normal_fact (nf : normal_fact) : normal_fact :=
    {| normal_fact.rel := f nf.(normal_fact.rel);
      normal_fact.args := nf.(normal_fact.args) |}.

  Definition map_fact_pattern (fp : fact_pattern) : fact_pattern :=
    {| fact_pattern.rel := f fp.(fact_pattern.rel);
      fact_pattern.args := fp.(fact_pattern.args) |}.

  Definition map_meta_fact (mf : meta_fact) : meta_fact :=
    {| meta_fact.pattern := map_fact_pattern mf.(meta_fact.pattern);
      meta_fact.set := mf.(meta_fact.set) |}.

  Definition map_fact (fct : fact) : fact :=
    match fct with
    | fact.normal nf => fact.normal (map_normal_fact nf)
    | fact.meta mf => fact.meta (map_meta_fact mf)
    end.

  Lemma map_fact_normal l :
    map map_fact (map fact.normal l) = map fact.normal (map map_normal_fact l).
  Proof. rewrite !map_map. apply map_ext. intros. reflexivity. Qed.

  Lemma map_fact_normal_inv l1 l2 :
    map fact.normal l1 = map map_fact l2 ->
    exists l2', l2 = map fact.normal l2' /\ l1 = map map_normal_fact l2'.
  Proof.
    revert l2. induction l1; intros [|b l2] H; simpl in H; try discriminate.
    - exists nil. auto.
    - destruct b; simpl in H; [|discriminate]. invert H.
      apply IHl1 in H2. fwd. exists (n :: l2'). auto.
  Qed.

  Definition fact_equiv f1 f2 := map_fact f1 = map_fact f2.

  Definition normal_fact_equiv n1 n2 := map_normal_fact n1 = map_normal_fact n2.

  Definition map_clause_rel (c : clause) : clause :=
    {| clause.rel := f c.(clause.rel);
      clause.args := c.(clause.args) |}.

  Lemma interp_clause_map_fw ctx c h :
    clause.interp ctx c h ->
    clause.interp ctx (map_clause_rel c) (map_normal_fact h).
  Proof. intros. repeat invert_stuff. interp_exprs. Qed.

  Hint Unfold clause.interp rel_equiv fact_equiv normal_fact_equiv : core.
  Lemma interp_clause_map_bw ctx c h :
    clause.interp ctx (map_clause_rel c) (map_normal_fact h) ->
    exists h', normal_fact_equiv h h' /\ clause.interp ctx c h'.
  Proof.
    intros H. cbv [clause.interp] in H. fwd.
    eexists {| normal_fact.rel := clause.rel c; normal_fact.args := _ |}. split.
    - cbv [normal_fact_equiv map_normal_fact]. simpl. f_equal. simpl in *. congruence.
    - eauto.
  Qed.

  Lemma Forall2_interp_clause_map_fw ctx hyps1 hyps2 :
    Forall2 (clause.interp ctx) hyps1 hyps2 ->
    Forall2 (clause.interp ctx) (map map_clause_rel hyps1) (map map_normal_fact hyps2).
  Proof.
    intros.
    rewrite <- Forall2_map_l, <- Forall2_map_r.
    eapply Forall2_impl; [eassumption|].
    eauto using interp_clause_map_fw.
  Qed.

  Lemma Forall2_interp_clause_map_bw ctx hyps1 hyps2 :
    Forall2 (clause.interp ctx) (map map_clause_rel hyps1) (map map_normal_fact hyps2) ->
    exists hyps2',
      Forall2 normal_fact_equiv hyps2 hyps2' /\
      Forall2 (clause.interp ctx) hyps1 hyps2'.
  Proof.
    intros H. rewrite <- Forall2_map_l, <- Forall2_map_r in H.
    induction H.
    - eexists []. split; constructor.
    - apply interp_clause_map_bw in H. destruct H as [h' [Heq Hinterp]].
      destruct IHForall2 as [hyps2' [HForall_eq HForall_interp]].
      eexists (h' :: hyps2'). split; constructor; eauto.
  Qed.

  Lemma Forall2_interp_clause_map_bw' ctx hyps1 hyps2 :
    Forall2 (clause.interp ctx) (map map_clause_rel hyps1) (map map_normal_fact hyps2) ->
    Forall2 (fun c h => exists h', normal_fact_equiv h h' /\ clause.interp ctx c h') hyps1 hyps2.
  Proof.
    intros H. rewrite <- Forall2_map_l, <- Forall2_map_r in H.
    eapply Forall2_impl; [eassumption|].
    eauto using interp_clause_map_bw.
  Qed.

  Definition map_clause_pattern_rel (c : clause_pattern) : clause_pattern :=
    {| clause_pattern.rel := f c.(clause_pattern.rel);
      clause_pattern.args := c.(clause_pattern.args) |}.

  Definition map_rule_rels (r : rule) : rule :=
    match r with
    | rule.impl concls hyps =>
        rule.impl (map map_clause_rel concls) (map map_clause_rel hyps)
    | rule.agg concl agg hyp =>
        rule.agg (f concl) agg (f hyp)
    end.

  Definition map_meta_rule_rels (r : meta_rule) : meta_rule :=
    {| meta_rule.concls := map map_clause_pattern_rel r.(meta_rule.concls);
      meta_rule.hyps := map map_clause_pattern_rel r.(meta_rule.hyps) |}.

  Lemma rule_interp_map_fw r nf hyps :
    rule.interp r nf hyps ->
    rule.interp (map_rule_rels r) (map_normal_fact nf) (map map_fact hyps).
  Proof.
    invert 1.
    - simpl. rewrite map_fact_normal. econstructor.
      + apply Exists_map. eapply Exists_impl; [|eassumption].
        simpl. eauto using interp_clause_map_fw.
      + apply Forall2_interp_clause_map_fw. assumption.
    - simpl. rewrite map_map.
      eassert (map _ vals = _) as ->.
      2: { constructor. eassumption. }
      apply map_ext. intros [? ?]. reflexivity.
  Qed.

  Definition fact_pattern_equiv p1 p2 := map_fact_pattern p1 = map_fact_pattern p2.

  Lemma interp_clause_pattern_map_fw ctx c fp :
    clause_pattern.interp ctx c fp ->
    clause_pattern.interp ctx (map_clause_pattern_rel c) (map_fact_pattern fp).
  Proof. intros. repeat invert_stuff. interp_exprs. Qed.

  Lemma Forall2_interp_clause_pattern_map_fw ctx hyps1 hyps2 :
    Forall2 (clause_pattern.interp ctx) hyps1 hyps2 ->
    Forall2 (clause_pattern.interp ctx)
      (map map_clause_pattern_rel hyps1) (map map_fact_pattern hyps2).
  Proof.
    intros. rewrite <- Forall2_map_l, <- Forall2_map_r.
    eapply Forall2_impl; [eassumption|].
    eauto using interp_clause_pattern_map_fw.
  Qed.

  Lemma meta_fact_matches_map_fw mf nf :
    meta_fact.matches mf nf ->
    meta_fact.matches (map_meta_fact mf) (map_normal_fact nf).
  Proof.
    cbv [meta_fact.matches fact_pattern.matches map_meta_fact map_fact_pattern
           map_normal_fact]. simpl. intros. fwd. ssplit; auto. congruence.
  Qed.

  Hint Unfold clause_pattern.interp : core.
  Lemma interp_clause_pattern_map_bw ctx c fp :
    clause_pattern.interp ctx (map_clause_pattern_rel c) (map_fact_pattern fp) ->
    exists fp', fact_pattern_equiv fp fp' /\ clause_pattern.interp ctx c fp'.
  Proof.
    intros H. cbv [clause_pattern.interp] in H. fwd.
    eexists {| fact_pattern.rel := clause_pattern.rel c; fact_pattern.args := _ |}. split.
    - cbv [fact_pattern_equiv map_fact_pattern]. simpl. f_equal. simpl in *. congruence.
    - eauto.
  Qed.

  Lemma Forall2_interp_clause_pattern_map_bw' ctx hyps1 hyps2 :
    Forall2 (clause_pattern.interp ctx)
      (map map_clause_pattern_rel hyps1) (map map_fact_pattern hyps2) ->
    Forall2 (fun c fp => exists fp', fact_pattern_equiv fp fp' /\
                                    clause_pattern.interp ctx c fp') hyps1 hyps2.
  Proof.
    intros H. rewrite <- Forall2_map_l, <- Forall2_map_r in H.
    eapply Forall2_impl; [eassumption|].
    eauto using interp_clause_pattern_map_bw.
  Qed.

  Lemma rel_map_fact fct :
    fact.rel (map_fact fct) = f (fact.rel fct).
  Proof. destruct fct; reflexivity. Qed.

  Lemma args_of_map_fact fct :
    fact.args_of (map_fact fct) = fact.args_of fct.
  Proof. destruct fct; simp; reflexivity. Qed.

  Lemma Forall2_fact_equiv_normal l1 l2 :
    Forall2 normal_fact_equiv l1 l2 ->
    Forall2 fact_equiv (map fact.normal l1) (map fact.normal l2).
  Proof.
    intros. rewrite <- Forall2_map_l, <- Forall2_map_r.
    eapply Forall2_impl; [eassumption|]. cbv [fact_equiv normal_fact_equiv]. simpl.
    intros. f_equal. assumption.
  Qed.

  Lemma rule_interp_map_bw r nf hyps :
    rule.interp (map_rule_rels r) (map_normal_fact nf) (map map_fact hyps) ->
    exists nf' hyps',
      normal_fact_equiv nf nf' /\
      Forall2 fact_equiv hyps hyps' /\
      rule.interp r nf' hyps'.
  Proof.
    intros H. destruct r; invert H.
    - apply map_fact_normal_inv in H2. fwd.
      apply Forall2_interp_clause_map_bw in H5. fwd.
      apply in_map_iff in H4p0. fwd.
      apply interp_clause_map_bw in H4p1. fwd.
      eexists _, (map fact.normal hyps2'). ssplit.
      + eassumption.
      + apply Forall2_fact_equiv_normal. eassumption.
      + econstructor; [apply Exists_exists; eauto | eassumption].
    - destruct hyps as [|h0 hyps]; simpl in H6; [discriminate|]. invert H6.
      destruct h0; simpl in *; [discriminate|].
      eexists _, _. ssplit.
      3: { econstructor. eassumption. }
      1: { cbv [normal_fact_equiv map_normal_fact]. simpl. f_equal; congruence. }
      constructor.
      + symmetry. assumption.
      + apply map_eq_Forall2 in H2. rewrite <- Forall2_map_r, <- Forall2_flip_iff.
        eapply Forall2_impl; [eassumption|].
        intros [? ?] ?. cbv [fact_equiv]. auto.
  Qed.

  Lemma interp_clause_map_image ctx c h :
    clause.interp ctx (map_clause_rel c) h ->
    exists h', h = map_normal_fact h'.
  Proof.
    intros. exists {| normal_fact.rel := c.(clause.rel);
                     normal_fact.args := h.(normal_fact.args) |}.
    cbv [clause.interp map_clause_rel map_normal_fact] in *. simpl in *. fwd. simp.
    reflexivity.
  Qed.

  Lemma Forall2_interp_clause_map_image ctx cs hs :
    Forall2 (clause.interp ctx) (map map_clause_rel cs) hs ->
    exists hs', hs = map map_normal_fact hs'.
  Proof.
    intros H. apply Forall_ex_eq_map. rewrite <- Forall2_map_l in H.
    apply Forall2_forget_l in H. eapply Forall_impl; [eassumption|].
    simpl. intros. fwd. eauto using interp_clause_map_image.
  Qed.

  Lemma rule_interp_invert_map r nf hyps :
    rule.interp (map_rule_rels r) nf hyps ->
    exists hyps0, hyps = map map_fact hyps0.
  Proof.
    intros H. destruct r; invert H.
    - apply Forall2_interp_clause_map_image in H5. fwd.
      exists (map fact.normal hs'). symmetry. apply map_fact_normal.
    - exists (fact.meta {| meta_fact.pattern :=
                            {| fact_pattern.rel := hyp;
                              fact_pattern.args := value_pattern.any :: value_pattern.any
                                                     :: map value_pattern.exactly args |};
                          meta_fact.set := S |}
                :: map (fun '(i, x_i) =>
                          fact.normal {| normal_fact.rel := hyp;
                                        normal_fact.args := i :: x_i :: args |}) vals).
      simpl. f_equal. rewrite map_map. apply map_ext. intros [? ?]. reflexivity.
  Qed.

  Lemma fact_pattern_matches_map_fw fp nf :
    fact_pattern.matches fp nf ->
    fact_pattern.matches (map_fact_pattern fp) (map_normal_fact nf).
  Proof.
    cbv [fact_pattern.matches map_fact_pattern map_normal_fact]. simpl. intros. fwd.
    split; [congruence | assumption].
  Qed.

  Lemma meta_fact_equiv_map_fw mf1 mf2 :
    meta_fact.equiv mf1 mf2 ->
    meta_fact.equiv (map_meta_fact mf1) (map_meta_fact mf2).
  Proof.
    cbv [meta_fact.equiv map_meta_fact map_fact_pattern]. simpl. intros. fwd.
    split; [congruence|]. assumption.
  Qed.

  Lemma implied_by_mf_map_fw fct mf :
    fact.implied_by_mf fct mf ->
    fact.implied_by_mf (map_fact fct) (map_meta_fact mf).
  Proof.
    destruct fct; simpl; auto using meta_fact_matches_map_fw, meta_fact_equiv_map_fw.
  Qed.

  Lemma implied_by_mfs_map_fw mfs fct :
    fact.implied_by_mfs mfs fct ->
    fact.implied_by_mfs (map map_meta_fact mfs) (map_fact fct).
  Proof.
    cbv [fact.implied_by_mfs]. rewrite Exists_map. intros.
    eapply Exists_impl; [|eassumption]. auto using implied_by_mf_map_fw.
  Qed.

  Definition meta_facts_agree_under_map (mhyps : list meta_fact) :=
    forall mf1 mf2,
      In mf1 mhyps ->
      In mf2 mhyps ->
      meta_fact.agree (map_meta_fact mf1) (map_meta_fact mf2).

  Hint Unfold fact_pattern.matches : core.
  Lemma matches_map_fact_pattern fp R args :
    f fp.(fact_pattern.rel) = R ->
    Forall2 value_pattern.matches fp.(fact_pattern.args) args ->
    fact_pattern.matches (map_fact_pattern fp)
      {| normal_fact.rel := R; normal_fact.args := args |}.
  Proof. cbv [fact_pattern.matches map_fact_pattern]. simpl. auto. Qed.

  Lemma implied_by_mf_agree fct mf1 mf2 :
    fact.implied_by_mf (map_fact fct) (map_meta_fact mf1) ->
    meta_fact.agree (map_meta_fact mf1) (map_meta_fact mf2) ->
    fact.covered_by fct mf2.(meta_fact.pattern) ->
    fact.implied_by_mf fct mf2.
  Proof.
    cbv [meta_fact.agree]. intros Himp Hagree Hcov. destruct fct as [nf|m].
    - cbv [fact.implied_by_mf fact.covered_by meta_fact.matches map_fact
             map_meta_fact] in *. simpl in *. fwd.
      split; [assumption|].
      apply (Hagree (map_normal_fact nf)); auto using fact_pattern_matches_map_fw.
    - cbv [fact.implied_by_mf fact.covered_by meta_fact.equiv map_fact map_meta_fact
             map_fact_pattern] in *. simp. fwd.
      split; [reflexivity|]. intros args Hargs.
      rewrite Himpp1 by assumption.
      apply (Hagree {| normal_fact.rel := f rel0; normal_fact.args := args |}); auto.
  Qed.

  Lemma implied_by_mfs_covered_bw mhyps fct :
    meta_facts_agree_under_map mhyps ->
    fact.implied_by_mfs (map map_meta_fact mhyps) (map_fact fct) ->
    fact.covered_by_pats (map meta_fact.pattern mhyps) fct ->
    fact.implied_by_mfs mhyps fct.
  Proof.
    cbv [fact.implied_by_mfs fact.covered_by_pats meta_facts_agree_under_map].
    rewrite !Exists_map, !Exists_exists. intros Hagree H1 H2. fwd.
    exists x. split; [assumption|]. eapply implied_by_mf_agree; eauto.
  Qed.

  (* --- ported above this line; the rest is still the old API --- *)

  Lemma meta_cond_map_iff mr mf_args mf_set p R (args : list T) meta_hyps :
    meta_rules_valid p ->
    In mr p ->
    rule_impl (one_step_derives p) mr (meta_fact R mf_args mf_set) meta_hyps ->
    Forall2 matches mf_args args ->
    meta_facts_consistent_with_map meta_hyps ->
    inj_on_elt R ->
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
    inj_on_elt (rel_of f0) ->
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
    Forall2 (meta_clause.interp ctx) (map map_meta_clause_rel hyps1) (map map_fact hyps2) ->
    exists hyps2',
      Forall2 fact_equiv hyps2 hyps2' /\
      Forall2 (meta_clause.interp ctx) hyps1 hyps2'.
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
    inj_on_elt (rel_of f0) ->
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
           cbv [meta_clause.interp]. cbv [meta_clause.interp] in H1p1p1.
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
        cbv [clause.interp] in H2p1. fwd.
        eexists (normal_fact _ _). simpl. auto using in_map.
      + eexists (normal_fact _ _). simpl. auto using in_map.
    - destruct r; simpl in H0; invert H0.
      rewrite Exists_map in H1. apply Exists_exists in H1. fwd.
      cbv [meta_clause.interp] in H1p1. fwd.
      eexists (meta_fact _ _ _). simpl. auto using in_map.
  Qed.

  Lemma prog_impl_fact_equiv (p : list rule) Q f1 f2 :
    Forall inj_on_elt (flat_map concl_rels p) ->
    (forall f1' f2', fact_equiv f1' f2' -> Q f1' <-> Q f2') ->
    fact_equiv f1 f2 ->
    prog_impl p Q f1 <-> prog_impl p Q f2.
  Proof.
    intros Hinj HQ Heq. split; intros Hprog.
    - pose proof Hprog as Hprog_copy. apply prog_impl_rel_of in Hprog_copy.
      destruct Hprog_copy as [HQ1 | Hconcl].
      + apply prog_impl_leaf. apply (proj1 (HQ _ _ Heq)). exact HQ1.
      + rewrite Forall_forall in Hinj. apply Hinj in Hconcl. cbv [inj_on_elt] in Hconcl.
        destruct f1 as [R1 args1 | R1 mf_args1 S1], f2 as [R2 args2 | R2 mf_args2 S2];
          cbv [fact_equiv map_fact] in Heq; try discriminate;
          inversion Heq;
          assert (f R1 = f R2) by congruence;
          apply Hconcl in H; subst; exact Hprog.
    - pose proof Hprog as Hprog_copy. apply prog_impl_rel_of in Hprog_copy.
      destruct Hprog_copy as [HQ2 | Hconcl].
      + apply prog_impl_leaf. apply (proj2 (HQ _ _ Heq)). exact HQ2.
      + rewrite Forall_forall in Hinj. apply Hinj in Hconcl. cbv [inj_on_elt] in Hconcl.
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
    Forall inj_on_elt (flat_map concl_rels p) ->
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
    Forall inj_on_elt (flat_map concl_rels p) ->
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
    inj_on_elt (rel_of f0) ->
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
    Forall inj_on_elt (flat_map concl_rels p) ->
    inj_on_elt (rel_of f0) ->
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

  Lemma concl_in_all (r : @rule rel1 exprvar fn aggregator) x :
    In x (concl_rels r) -> In x (all_rels r).
  Proof. cbv [all_rels]. intros. apply in_or_app. auto. Qed.

  Lemma hyp_in_all (r : @rule rel1 exprvar fn aggregator) x :
    In x (hyp_rels r) -> In x (all_rels r).
  Proof. cbv [all_rels]. intros. apply in_or_app. auto. Qed.

  Lemma map_fact_inj_g a b :
    (f (rel_of a) = f (rel_of b) -> rel_of a = rel_of b) ->
    map_fact a = map_fact b -> a = b.
  Proof.
    intros Hinj H.
    destruct a as [Ra ? | Ra ? ?], b as [Rb ? | Rb ? ?];
      cbv [map_fact rel_of] in *; inversion H; subst;
      assert (Ra = Rb) by (apply Hinj; assumption); subst; reflexivity.
  Qed.

  Lemma Forall2_fact_equiv_map_eq l1 l2 :
    Forall2 fact_equiv l1 l2 -> map map_fact l1 = map map_fact l2.
  Proof.
    induction 1; simpl; [reflexivity|]. cbv [fact_equiv] in H. congruence.
  Qed.

  Lemma non_meta_rule_impl_map_bw_recover r Rimg args hyps_m :
    non_meta_rule_impl (map_rule_rels r) Rimg args hyps_m ->
    exists R0 hyps0,
      Rimg = f R0 /\ In R0 (concl_rels r) /\ hyps_m = map map_fact hyps0 /\
      non_meta_rule_impl r R0 args hyps0.
  Proof.
    intros H.
    pose proof (non_meta_rule_impl_concl_relname_in _ _ _ _ H) as Hin.
    rewrite concl_rels_map_rule_rels in Hin. apply in_map_iff in Hin.
    destruct Hin as (R0 & HR0eq & HR0in). subst Rimg.
    pose proof H as Hinv. apply non_meta_rule_invert_map in Hinv.
    destruct Hinv as [hyps_pre Hpre]. subst hyps_m.
    apply non_meta_rule_impl_map_bw in H.
    destruct H as (R0' & hyps0 & Hrel & Hfe & Hnm).
    cbv [rel_equiv] in Hrel.
    exists R0', hyps0. ssplit.
    - exact Hrel.
    - eapply non_meta_rule_impl_concl_relname_in. exact Hnm.
    - apply Forall2_fact_equiv_map_eq. exact Hfe.
    - exact Hnm.
  Qed.

  Lemma Forall2_interp_meta_clause_recover ctx cs hs :
    Forall2 (meta_clause.interp ctx) (map map_meta_clause_rel cs) hs ->
    exists hs0, hs = map map_fact hs0 /\ Forall2 (meta_clause.interp ctx) cs hs0.
  Proof.
    revert hs. induction cs as [|c cs IH]; intros hs H; simpl in H.
    - invert H. exists []. split; constructor.
    - invert H. cbv [meta_clause.interp] in H2. fwd.
      apply IH in H4. destruct H4 as (hs0 & Hhs0 & Hok). subst.
      exists (meta_fact (meta_clause.rel c) mf_args mf_set :: hs0).
      split; [reflexivity|]. constructor; [|exact Hok].
      cbv [meta_clause.interp]. eauto.
  Qed.

  Lemma Forall2_interp_meta_clause_rel ctx (cs : list (@meta_clause rel1 exprvar fn))
    (hs : list (@fact rel1 T)) :
    Forall2 (meta_clause.interp ctx) cs hs ->
    Forall (fun h => In (rel_of h) (map meta_clause.rel cs)) hs.
  Proof.
    induction 1 as [| c hh cs' hs' Hc Hrest IH]; simpl; constructor.
    - cbv [meta_clause.interp] in Hc. fwd. subst. simpl. left. reflexivity.
    - eapply Forall_impl; [|exact IH]. simpl. intros a Ha. right. exact Ha.
  Qed.

  Lemma extensionally_equal_map_bw_inj g mf :
    (f (rel_of g) = f (rel_of mf) -> rel_of g = rel_of mf) ->
    extensionally_equal (map_fact g) (map_fact mf) ->
    extensionally_equal g mf.
  Proof.
    intros Hinj H.
    destruct g as [Rg ag | Rg mg sg], mf as [Rm am | Rm mm sm];
      cbv [extensionally_equal map_fact rel_of] in *; try contradiction; fwd;
      assert (Rg = Rm) by (apply Hinj; assumption); subst; auto.
  Qed.

  Lemma fact_matches_map_bw_inj g mf :
    (f (rel_of g) = f (rel_of mf) -> rel_of g = rel_of mf) ->
    fact_matches (map_fact g) (map_fact mf) ->
    fact_matches g mf.
  Proof.
    intros Hinj H. cbv [fact_matches] in H. fwd.
    destruct g as [Rg ag | Rg mg sg]; cbv [map_fact] in Hp0; try discriminate.
    destruct mf as [Rm am | Rm mm sm]; cbv [map_fact] in Hp1; try discriminate.
    cbv [rel_of] in Hinj. invert Hp0. invert Hp1.
    assert (Rg = Rm) by (apply Hinj; congruence). subst.
    cbv [fact_matches]. do 4 eexists. ssplit; try reflexivity; eassumption.
  Qed.

  Lemma fact_supported_map_fw meta_facts g :
    fact_supported meta_facts g ->
    fact_supported (map map_fact meta_facts) (map_fact g).
  Proof.
    cbv [fact_supported]. rewrite Exists_map. intros H.
    eapply Exists_impl; [|exact H]. simpl. intros hyp [Hh|Hh].
    - left. apply extensionally_equal_map_fw. exact Hh.
    - right. apply fact_matches_map_fw. exact Hh.
  Qed.

  Lemma fact_supported_map_bw_inj meta_facts g :
    injective_on f (rel_of g :: map rel_of meta_facts) ->
    fact_supported (map map_fact meta_facts) (map_fact g) ->
    fact_supported meta_facts g.
  Proof.
    intros Hinj H. cbv [fact_supported] in *. rewrite Exists_map in H.
    apply Exists_exists in H. destruct H as (mf & Hin & Hdisj).
    apply Exists_exists. exists mf. split; [exact Hin|].
    assert (f (rel_of g) = f (rel_of mf) -> rel_of g = rel_of mf) as Hpair.
    { intros Hfe. apply Hinj; [left; reflexivity | right; apply in_map; exact Hin | exact Hfe]. }
    destruct Hdisj as [Hh|Hh].
    - left. eapply extensionally_equal_map_bw_inj; [exact Hpair | exact Hh].
    - right. eapply fact_matches_map_bw_inj; [exact Hpair | exact Hh].
  Qed.

  Context
    (p : list rule)
      (f_inj : injective_on f (flat_map all_rels p)).

  Lemma rel_in_flat_map r x :
    In r p -> In x (all_rels r) -> In x (flat_map all_rels p).
  Proof. intros. apply in_flat_map. eauto. Qed.

  Lemma prog_impl_bridge Q h g :
    (forall f1 f2, fact_equiv f1 f2 -> Q f1 <-> Q f2) ->
    injective_on f (rel_of h :: flat_map all_rels p) ->
    fact_equiv h g ->
    prog_impl p Q g ->
    prog_impl p Q h.
  Proof.
    intros HQ Hh Hfe Hg.
    pose proof Hg as Hg'. apply prog_impl_rel_of in Hg'.
    destruct Hg' as [HQg | Hconcl].
    - apply prog_impl_leaf. apply (proj2 (HQ h g Hfe)). exact HQg.
    - assert (In (rel_of g) (flat_map all_rels p)) as Hgmem.
      { apply in_flat_map in Hconcl. fwd. apply in_flat_map.
        eexists. split; [eassumption|]. apply concl_in_all. assumption. }
      assert (h = g) as ->; [|exact Hg].
      apply map_fact_inj_g; [|exact Hfe]. intros Hfe2.
      apply Hh; [ left; reflexivity | right; exact Hgmem | exact Hfe2 ].
  Qed.

  Lemma one_step_derives_map_iff_inj meta_facts R args :
    In R (flat_map all_rels p) ->
    Forall (fun mf => In (rel_of mf) (flat_map all_rels p)) meta_facts ->
    one_step_derives p meta_facts R args <->
    one_step_derives (map map_rule_rels p) (map map_fact meta_facts) (f R) args.
  Proof.
    intros HR Hmf. cbv [one_step_derives one_step_derives0]. split; intros H; fwd.
    - exists (map map_fact hyps). split.
      + apply Exists_map. eapply Exists_impl; [|exact Hp0]. simpl.
        intros r Hr. apply non_meta_rule_impl_map_fw. exact Hr.
      + rewrite Lists.List.Forall_map. eapply Forall_impl; [|exact Hp1]. simpl.
        intros x Hx. apply fact_supported_map_fw. exact Hx.
    - apply Exists_map in Hp0. apply Exists_exists in Hp0. fwd.
      apply non_meta_rule_impl_map_bw_recover in Hp0p1.
      destruct Hp0p1 as (R0 & hyps0 & Hrel & HR0c & Heq & Hnm). subst.
      assert (In R0 (flat_map all_rels p)) as HR0.
      { eapply rel_in_flat_map; [exact Hp0p0|]. apply concl_in_all. exact HR0c. }
      assert (R = R0) by (apply f_inj; assumption). subst R0.
      exists hyps0. split.
      + apply Exists_exists. eexists. split; [exact Hp0p0|]. exact Hnm.
      + rewrite Lists.List.Forall_map in Hp1.
        pose proof (non_meta_rule_impl_hyp_relname_in _ _ _ _ Hnm) as Hhr.
        apply Forall_forall. intros h Hh_in.
        eapply fact_supported_map_bw_inj;
          [| rewrite Forall_forall in Hp1; apply Hp1; exact Hh_in ].
        eapply injective_on_incl; [| exact f_inj ].
        intros z Hz. destruct Hz as [Heq | Hz];
          [ subst z; eapply rel_in_flat_map; [exact Hp0p0|]; apply hyp_in_all;
            rewrite Forall_forall in Hhr; apply Hhr; exact Hh_in
          | apply in_map_iff in Hz; destruct Hz as (mf & Hmfeq & Hmfin); subst z;
            rewrite Forall_forall in Hmf; apply Hmf; exact Hmfin ].
  Qed.

  Lemma rule_impl_map_fw_inj r f0 hyps :
    In r p ->
    In (rel_of f0) (flat_map all_rels p) ->
    Forall (fun h => In (rel_of h) (flat_map all_rels p)) hyps ->
    rule_impl (one_step_derives p) r f0 hyps ->
    rule_impl (one_step_derives (map map_rule_rels p))
      (map_rule_rels r) (map_fact f0) (map map_fact hyps).
  Proof.
    intros Hr Hf0 Hhyps H. invert H.
    - simpl. apply simple_rule_impl. apply non_meta_rule_impl_map_fw. exact H0.
    - simpl. eapply meta_rule_impl.
      + rewrite Exists_map. eapply Exists_impl; [|exact H0]. simpl.
        intros c Hc. apply interp_meta_clause_map_fw in Hc. exact Hc.
      + apply Forall2_interp_meta_clause_map_fw. exact H1.
      + intros args'' Hargs. rewrite (H2 args'' Hargs).
        apply one_step_derives_map_iff_inj; [exact Hf0 | exact Hhyps].
  Qed.

  Lemma rule_impl_map_bw_recover r f_target hyps_m :
    In r p ->
    rule_impl (one_step_derives (map map_rule_rels p))
      (map_rule_rels r) f_target hyps_m ->
    exists f0 hyps0,
      f_target = map_fact f0 /\
      hyps_m = map map_fact hyps0 /\
      In (rel_of f0) (flat_map all_rels p) /\
      Forall (fun h => In (rel_of h) (flat_map all_rels p)) hyps0 /\
      rule_impl (one_step_derives p) r f0 hyps0.
  Proof.
    intros Hr H. invert H.
    - apply non_meta_rule_impl_map_bw_recover in H0.
      destruct H0 as (R0 & hyps0 & Hrel & HR0c & Heq & Hnm).
      exists (normal_fact R0 args), hyps0. ssplit.
      + simpl. rewrite Hrel. reflexivity.
      + exact Heq.
      + simpl. eapply rel_in_flat_map; [exact Hr|]. apply concl_in_all. exact HR0c.
      + pose proof (non_meta_rule_impl_hyp_relname_in _ _ _ _ Hnm) as Hhr.
        eapply Forall_impl; [|exact Hhr]. simpl. intros h Hh.
        eapply rel_in_flat_map; [exact Hr|]. apply hyp_in_all. exact Hh.
      + apply simple_rule_impl. exact Hnm.
    - destruct r as [rc rh | rc rh | cr ag hr]; simpl in *; try discriminate; fwd.
      apply Forall2_interp_meta_clause_recover in H2.
      destruct H2 as (hyps0 & Hhm & Hok). subst.
      assert (Forall (fun h => In (rel_of h) (flat_map all_rels p)) hyps0) as Hhyps0.
      { pose proof (Forall2_interp_meta_clause_rel _ _ _ Hok) as Hr0.
        eapply Forall_impl; [|exact Hr0]. simpl. intros h Hh.
        eapply rel_in_flat_map; [exact Hr|]. apply hyp_in_all. exact Hh. }
      rewrite Exists_map in H1. apply Exists_exists in H1.
      destruct H1 as (c & Hc & H1i).
      cbv [meta_clause.interp] in H1i. destruct H1i as (mfa & mfs & Hae & Heq2).
      invert Heq2.
      assert (In (meta_clause.rel c) (flat_map all_rels p)) as HR0.
      { eapply rel_in_flat_map; [exact Hr|]. apply concl_in_all. apply in_map_iff. eauto. }
      exists (meta_fact (meta_clause.rel c) mfa S), hyps0. ssplit.
      + reflexivity.
      + reflexivity.
      + exact HR0.
      + exact Hhyps0.
      + eapply meta_rule_impl.
        * apply Exists_exists. exists c. split; [exact Hc|].
          cbv [meta_clause.interp]. exists mfa, S. split; [exact Hae | reflexivity].
        * exact Hok.
        * intros args'' Hargs. rewrite (H3 args'' Hargs). symmetry.
          apply one_step_derives_map_iff_inj; [exact HR0 | exact Hhyps0].
  Qed.

  Lemma prog_impl_map_fw_inj Q f0 :
    prog_impl p Q f0 ->
    prog_impl (map map_rule_rels p)
      (fun f' => exists f, f' = map_fact f /\ Q f) (map_fact f0).
  Proof.
    intros Hprog. induction Hprog.
    - apply prog_impl_leaf. eexists; eauto.
    - apply Exists_exists in H. destruct H as [r [Hr_in Hr_impl]].
      eapply prog_impl_step.
      + apply Exists_map. apply Exists_exists. exists r. split; [exact Hr_in|].
        eapply rule_impl_map_fw_inj; [exact Hr_in | | | exact Hr_impl].
        * eapply rel_in_flat_map; [exact Hr_in|]. apply concl_in_all.
          eapply rule_impl_concl_relname_in. exact Hr_impl.
        * pose proof (rule_impl_hyp_relname_in _ _ _ _ Hr_impl) as Hhr.
          eapply Forall_impl; [|exact Hhr]. simpl. intros h Hh.
          eapply rel_in_flat_map; [exact Hr_in|]. apply hyp_in_all. exact Hh.
      + rewrite Lists.List.Forall_map. eapply Forall_impl; [|eassumption]. simpl. auto.
  Qed.

  Lemma prog_impl_map_bw_inj Q f_target :
    (forall f1 f2, fact_equiv f1 f2 -> Q f1 <-> Q f2) ->
    prog_impl (map map_rule_rels p)
      (fun f' => exists f, f' = map_fact f /\ Q f) f_target ->
    exists f0, f_target = map_fact f0 /\ prog_impl p Q f0.
  Proof.
    intros HQ Hprog. induction Hprog.
    - fwd. eauto.
    - apply Exists_map in H. apply Exists_exists in H. fwd.
      eapply rule_impl_map_bw_recover in Hp1; [|exact Hp0].
      destruct Hp1 as (f0 & hyps0 & Hxeq & Hleq & Hf0mem & Hhypsmem & Hnm). subst.
      exists f0. split; [reflexivity|].
      eapply prog_impl_step.
      { apply Exists_exists. eexists. split; [exact Hp0|]. exact Hnm. }
      rewrite Lists.List.Forall_map in H1.
      apply Forall_forall. intros h Hh_in.
      rewrite Forall_forall in H1, Hhypsmem.
      specialize (H1 _ Hh_in). destruct H1 as (g & Hgeq & Hgprog).
      eapply prog_impl_bridge;
        [ exact HQ
        | apply injective_on_cons_in; [ apply Hhypsmem; exact Hh_in | exact f_inj ]
        | | exact Hgprog ].
      cbv [fact_equiv]. exact Hgeq.
  Qed.

  Lemma prog_impl_map_rule_rels_iff_inj Q f0 :
    injective_on f (rel_of f0 :: flat_map all_rels p) ->
    (forall f1 f2, fact_equiv f1 f2 -> Q f1 <-> Q f2) ->
    prog_impl p Q f0 <->
    prog_impl (map map_rule_rels p) (fun f' => exists f, f' = map_fact f /\ Q f) (map_fact f0).
  Proof.
    intros Hf0 HQ. split; intros H.
    - apply prog_impl_map_fw_inj. exact H.
    - apply prog_impl_map_bw_inj in H; [|exact HQ]. fwd.
      eapply prog_impl_bridge; [exact HQ | exact Hf0 | | exact Hp1].
      cbv [fact_equiv]. exact Hp0.
  Qed.
End RelMap.
