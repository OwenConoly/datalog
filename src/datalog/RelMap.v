From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.

From Datalog Require Import Map Tactics Fp List Pftree Datalog.
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
    h = map_normal_fact {| normal_fact.rel := c.(clause.rel);
                          normal_fact.args := h.(normal_fact.args) |}.
  Proof.
    cbv [clause.interp map_clause_rel map_normal_fact]. simpl. intros. fwd. simp.
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

  Lemma interp_clause_pattern_map_image ctx c fp :
    clause_pattern.interp ctx (map_clause_pattern_rel c) fp ->
    fp = map_fact_pattern {| fact_pattern.rel := c.(clause_pattern.rel);
                            fact_pattern.args := fp.(fact_pattern.args) |}.
  Proof.
    cbv [clause_pattern.interp map_clause_pattern_rel map_fact_pattern]. simpl.
    intros. fwd. simp. reflexivity.
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

  Lemma normal_fact_equiv_inj nf nf' :
    inj_on_elt nf.(normal_fact.rel) ->
    normal_fact_equiv nf nf' ->
    nf = nf'.
  Proof.
    intros Hinj H. cbv [normal_fact_equiv map_normal_fact] in H. simp. fwd.
    f_equal. auto.
  Qed.

  Lemma one_step_derives_map_iff p mr pat mhyps nf :
    program.meta_rules_valid p ->
    In mr p.(program.meta_rules) ->
    meta_rule.pattern_interp mr pat (map meta_fact.pattern mhyps) ->
    fact_pattern.matches pat nf ->
    meta_facts_agree_under_map mhyps ->
    inj_on_elt nf.(normal_fact.rel) ->
    rule.one_step_derives p.(program.rules) mhyps nf <->
      rule.one_step_derives (map map_rule_rels p.(program.rules))
        (map map_meta_fact mhyps) (map_normal_fact nf).
  Proof.
    intros Hvalid Hmr Hpat Hmatch Hagree Hinj. cbv [rule.one_step_derives].
    split; intros H; fwd.
    - exists (map map_fact hyps). split.
      + apply Exists_map, Exists_exists. eauto using rule_interp_map_fw.
      + apply Forall_forall. intros h Hh. apply in_map_iff in Hh. fwd.
        apply implied_by_mfs_map_fw. rewrite Forall_forall in Hp1. auto.
    - apply in_map_iff in Hp0p0. fwd.
      pose proof Hp0p1 as Hinv. apply rule_interp_invert_map in Hinv. fwd.
      apply rule_interp_map_bw in Hp0p1. fwd.
      apply normal_fact_equiv_inj in Hp0p1p0; [|assumption]. subst.
      exists hyps'. split; [apply Exists_exists; eauto|].
      pose proof (Hvalid _ _ Hmr Hp0p0p1 _ _ _ _ Hpat Hp0p1p2 Hmatch) as Hcov.
      apply Forall2_forget_l in Hp0p1p1.
      rewrite Forall_forall in Hp0p1p1, Hcov, Hp1.
      apply Forall_forall. intros h' Hh'.
      specialize (Hp0p1p1 _ Hh'). fwd.
      eapply implied_by_mfs_covered_bw; [assumption| |auto].
      cbv [fact_equiv] in *. rewrite <- Hp0p1p1p1.
      apply Hp1. apply in_map. assumption.
  Qed.

  Lemma map_fact_meta l :
    map map_fact (map fact.meta l) = map fact.meta (map map_meta_fact l).
  Proof. rewrite !map_map. apply map_ext. intros. reflexivity. Qed.

  Lemma map_pattern_map_meta_fact l :
    map meta_fact.pattern (map map_meta_fact l) =
      map map_fact_pattern (map meta_fact.pattern l).
  Proof. rewrite !map_map. apply map_ext. intros. reflexivity. Qed.

  Lemma pattern_interp_map_fw mr pat pats :
    meta_rule.pattern_interp mr pat pats ->
    meta_rule.pattern_interp (map_meta_rule_rels mr) (map_fact_pattern pat)
      (map map_fact_pattern pats).
  Proof.
    cbv [meta_rule.pattern_interp map_meta_rule_rels]. simpl. intros. fwd.
    exists ctx. split.
    - apply Exists_map, Exists_exists. eauto using interp_clause_pattern_map_fw.
    - apply Forall2_interp_clause_pattern_map_fw. assumption.
  Qed.

  Lemma meta_rule_interp_map_fw p mr mf mhyps :
    program.meta_rules_valid p ->
    In mr p.(program.meta_rules) ->
    meta_facts_agree_under_map mhyps ->
    inj_on_elt (meta_fact.rel mf) ->
    meta_rule.interp p.(program.rules) mr mf mhyps ->
    meta_rule.interp (map map_rule_rels p.(program.rules)) (map_meta_rule_rels mr)
      (map_meta_fact mf) (map map_meta_fact mhyps).
  Proof.
    intros Hvalid Hmr Hagree Hinj H.
    cbv [meta_rule.interp meta_fact.equiv meta_fact.rel] in *. fwd.
    destruct mf. simpl in *. subst.
    exists (map_fact_pattern pat). rewrite map_pattern_map_meta_fact.
    split; [auto using pattern_interp_map_fw|].
    cbv [map_meta_fact map_fact_pattern]. simpl. split; [reflexivity|].
    intros args Hargs. rewrite Hp2 by assumption.
    apply (one_step_derives_map_iff p mr pat mhyps
             {| normal_fact.rel := pat.(fact_pattern.rel); normal_fact.args := args |}); auto.
  Qed.

  Definition map_program (p : program) : program :=
    {| program.rules := map map_rule_rels p.(program.rules);
      program.meta_rules := map map_meta_rule_rels p.(program.meta_rules) |}.

  Definition facts_agree_under_map (hyps : list fact) :=
    forall mf1 mf2,
      In (fact.meta mf1) hyps ->
      In (fact.meta mf2) hyps ->
      meta_fact.agree (map_meta_fact mf1) (map_meta_fact mf2).

  Lemma facts_agree_under_map_meta mhyps :
    facts_agree_under_map (map fact.meta mhyps) ->
    meta_facts_agree_under_map mhyps.
  Proof.
    cbv [facts_agree_under_map meta_facts_agree_under_map]. auto using in_map.
  Qed.

  Lemma interp_step_map_fw p fct hyps :
    program.meta_rules_valid p ->
    inj_on_elt (fact.rel fct) ->
    facts_agree_under_map hyps ->
    program.interp_step p fct hyps ->
    program.interp_step (map_program p) (map_fact fct) (map map_fact hyps).
  Proof.
    intros Hvalid Hinj Hagree H. invert H; simpl in *.
    - constructor. simpl. apply Exists_map, Exists_exists. fwd.
      eauto using rule_interp_map_fw.
    - rewrite map_fact_meta. constructor. simpl.
      apply Exists_map, Exists_exists. fwd.
      eexists. split; [eassumption|].
      apply meta_rule_interp_map_fw; auto using facts_agree_under_map_meta.
  Qed.

  Lemma Forall2_interp_clause_pattern_map_bw ctx hyps1 hyps2 :
    Forall2 (clause_pattern.interp ctx)
      (map map_clause_pattern_rel hyps1) (map map_fact_pattern hyps2) ->
    exists hyps2',
      Forall2 fact_pattern_equiv hyps2 hyps2' /\
      Forall2 (clause_pattern.interp ctx) hyps1 hyps2'.
  Proof.
    intros H. rewrite <- Forall2_map_l, <- Forall2_map_r in H.
    induction H.
    - eexists []. split; constructor.
    - apply interp_clause_pattern_map_bw in H. fwd.
      eexists (_ :: _). split; constructor; eauto.
  Qed.

  Lemma pattern_interp_map_bw mr pat pats :
    meta_rule.pattern_interp (map_meta_rule_rels mr) (map_fact_pattern pat)
      (map map_fact_pattern pats) ->
    exists pat0 pats0,
      fact_pattern_equiv pat pat0 /\
      Forall2 fact_pattern_equiv pats pats0 /\
      meta_rule.pattern_interp mr pat0 pats0.
  Proof.
    cbv [meta_rule.pattern_interp map_meta_rule_rels]. simpl. intros. fwd.
    apply in_map_iff in Hp0p0. fwd.
    apply interp_clause_pattern_map_bw in Hp0p1.
    apply Forall2_interp_clause_pattern_map_bw in Hp1. fwd.
    eexists _, _. ssplit; [eassumption|eassumption|].
    exists ctx. split; [apply Exists_exists; eauto | assumption].
  Qed.

  Definition meta_fact_equiv m1 m2 := map_meta_fact m1 = map_meta_fact m2.

  Lemma meta_facts_of_patterns mhyps pats :
    Forall2 fact_pattern_equiv (map meta_fact.pattern mhyps) pats ->
    exists mhyps',
      Forall2 meta_fact_equiv mhyps mhyps' /\
      map meta_fact.pattern mhyps' = pats.
  Proof.
    rewrite <- Forall2_map_l. induction 1; [now exists []|]. fwd.
    eexists ({| meta_fact.pattern := y; meta_fact.set := x.(meta_fact.set) |} :: _).
    split.
    - constructor; [|eassumption]. cbv [meta_fact_equiv map_meta_fact]. simpl.
      f_equal. assumption.
    - simpl. f_equal.
  Qed.

  Lemma fact_pattern_equiv_inj fp fp' :
    inj_on_elt fp.(fact_pattern.rel) ->
    fact_pattern_equiv fp fp' ->
    fp = fp'.
  Proof.
    intros Hinj H. cbv [fact_pattern_equiv map_fact_pattern] in H. simp. fwd.
    f_equal. auto.
  Qed.

  Lemma meta_facts_agree_under_map_equiv mhyps mhyps' :
    meta_facts_agree_under_map mhyps ->
    Forall2 meta_fact_equiv mhyps mhyps' ->
    meta_facts_agree_under_map mhyps'.
  Proof.
    cbv [meta_facts_agree_under_map meta_fact_equiv]. intros Hagree Heq mf1 mf2 H1 H2.
    apply Forall2_forget_l in Heq. rewrite Forall_forall in Heq.
    apply Heq in H1, H2. fwd. rewrite <- H1p1, <- H2p1. auto.
  Qed.

  Lemma meta_rule_interp_map_bw p mr mf mhyps :
    program.meta_rules_valid p ->
    In mr p.(program.meta_rules) ->
    meta_facts_agree_under_map mhyps ->
    inj_on_elt (meta_fact.rel mf) ->
    meta_rule.interp (map map_rule_rels p.(program.rules)) (map_meta_rule_rels mr)
      (map_meta_fact mf) (map map_meta_fact mhyps) ->
    exists mhyps',
      Forall2 meta_fact_equiv mhyps mhyps' /\
      meta_rule.interp p.(program.rules) mr mf mhyps'.
  Proof.
    intros Hvalid Hmr Hagree Hinj H.
    cbv [meta_rule.interp meta_fact.equiv meta_fact.rel] in *. fwd.
    destruct mf. simpl in *. subst.
    rewrite map_pattern_map_meta_fact in Hp0.
    apply pattern_interp_map_bw in Hp0. fwd.
    apply fact_pattern_equiv_inj in Hp0p0; [|assumption]. subst.
    apply meta_facts_of_patterns in Hp0p1. fwd.
    rewrite (Forall2_map_eq _ _ _ _ Hp0p1p0) in Hp2.
    exists mhyps'. split; [assumption|].
    exists pat0. ssplit; [assumption|reflexivity|].
    intros args Hargs. rewrite Hp2 by assumption. symmetry.
    apply (one_step_derives_map_iff p mr pat0 mhyps'
             {| normal_fact.rel := pat0.(fact_pattern.rel); normal_fact.args := args |});
      eauto using meta_facts_agree_under_map_equiv.
  Qed.

  Lemma map_fact_meta_inv l1 l2 :
    map fact.meta l1 = map map_fact l2 ->
    exists l2', l2 = map fact.meta l2' /\ l1 = map map_meta_fact l2'.
  Proof.
    revert l2. induction l1; intros [|b l2] H; simpl in H; try discriminate.
    - exists nil. auto.
    - destruct b; simpl in H; [discriminate|]. invert H.
      apply IHl1 in H2. fwd. exists (m :: l2'). auto.
  Qed.

  Lemma Forall2_fact_equiv_meta l1 l2 :
    Forall2 meta_fact_equiv l1 l2 ->
    Forall2 fact_equiv (map fact.meta l1) (map fact.meta l2).
  Proof.
    intros. rewrite <- Forall2_map_l, <- Forall2_map_r.
    eapply Forall2_impl; [eassumption|]. cbv [fact_equiv meta_fact_equiv]. simpl.
    intros. f_equal. assumption.
  Qed.

  Lemma interp_step_map_bw p fct hyps :
    program.meta_rules_valid p ->
    inj_on_elt (fact.rel fct) ->
    facts_agree_under_map hyps ->
    program.interp_step (map_program p) (map_fact fct) (map map_fact hyps) ->
    exists hyps', Forall2 fact_equiv hyps hyps' /\ program.interp_step p fct hyps'.
  Proof.
    intros Hvalid Hinj Hagree H. cbv [map_program] in H.
    destruct fct as [nf|mf]; simpl in *; invert H; fwd.
    - apply in_map_iff in H1p0. fwd.
      apply rule_interp_map_bw in H1p1. fwd.
      apply normal_fact_equiv_inj in H1p1p0; [|assumption]. subst.
      eexists. split; [eassumption|]. constructor. apply Exists_exists. eauto.
    - apply map_fact_meta_inv in H1. fwd.
      apply in_map_iff in H2p0. fwd.
      apply facts_agree_under_map_meta in Hagree.
      eapply meta_rule_interp_map_bw in H2p1; try assumption.
      fwd. exists (map fact.meta mhyps'). split.
      + apply Forall2_fact_equiv_meta. assumption.
      + constructor. apply Exists_exists. eauto.
  Qed.

  Lemma rule_interp_map_target r nf hyps :
    rule.interp (map_rule_rels r) nf hyps ->
    exists nf0, nf = map_normal_fact nf0 /\ In nf0.(normal_fact.rel) (rule.concl_rels r).
  Proof.
    intros H. destruct r; invert H; fwd.
    - apply in_map_iff in H2p0. fwd.
      apply interp_clause_map_image in H2p1.
      eexists. split; [eassumption|]. simpl. apply in_map. assumption.
    - eexists {| normal_fact.rel := concl; normal_fact.args := _ |}.
      split; [reflexivity|]. simpl. auto.
  Qed.

  Lemma meta_rule_interp_map_target prog mr mf hyps :
    meta_rule.interp prog (map_meta_rule_rels mr) mf hyps ->
    exists mf0, mf = map_meta_fact mf0 /\
                 In (meta_fact.rel mf0) (meta_rule.concl_rels mr).
  Proof.
    cbv [meta_rule.interp meta_rule.pattern_interp map_meta_rule_rels
           meta_fact.equiv meta_fact.rel meta_rule.concl_rels]. simpl.
    intros. fwd. apply in_map_iff in Hp0p0p0. fwd.
    apply interp_clause_pattern_map_image in Hp0p0p1.
    destruct mf as [mf_pat mf_set]. simpl in *.
    exists {| meta_fact.pattern :=
               {| fact_pattern.rel := x0.(clause_pattern.rel);
                 fact_pattern.args := mf_pat.(fact_pattern.args) |};
             meta_fact.set := mf_set |}.
    split.
    - cbv [map_meta_fact map_fact_pattern] in *. simpl in *. congruence.
    - simpl. apply in_map. assumption.
  Qed.

  Lemma interp_step_map_target p fct hyps :
    program.interp_step (map_program p) fct hyps ->
    exists fct0, fct = map_fact fct0 /\ In (fact.rel fct0) (program.concl_rels p).
  Proof.
    cbv [map_program program.concl_rels]. intros H. invert H; simpl in *; fwd.
    - apply in_map_iff in H0p0. fwd.
      apply rule_interp_map_target in H0p1. fwd.
      eexists (fact.normal _). split; [reflexivity|].
      simpl. apply in_or_app. left. apply in_flat_map. eauto.
    - apply in_map_iff in H0p0. fwd.
      apply meta_rule_interp_map_target in H0p1. fwd.
      eexists (fact.meta _). split; [reflexivity|].
      simpl. apply in_or_app. right. apply in_flat_map. eauto.
  Qed.

  Lemma meta_fact_equiv_inj mf mf' :
    inj_on_elt (meta_fact.rel mf) ->
    meta_fact_equiv mf mf' ->
    mf = mf'.
  Proof.
    cbv [meta_fact_equiv map_meta_fact meta_fact.rel]. intros Hinj H. simp. fwd.
    f_equal. apply fact_pattern_equiv_inj; assumption.
  Qed.

  Lemma map_fact_inj fct fct' :
    inj_on_elt (fact.rel fct) ->
    fact_equiv fct fct' ->
    fct = fct'.
  Proof.
    destruct fct, fct'; cbv [fact_equiv]; simpl; intros Hinj H; try discriminate.
    - f_equal. apply normal_fact_equiv_inj; [assumption|]. cbv [normal_fact_equiv]. congruence.
    - f_equal. apply meta_fact_equiv_inj; [assumption|]. cbv [meta_fact_equiv]. congruence.
  Qed.

  Lemma interp_fact_equiv p Q f1 f2 :
    Forall inj_on_elt (program.concl_rels p) ->
    (forall f1' f2', fact_equiv f1' f2' -> Q f1' <-> Q f2') ->
    fact_equiv f1 f2 ->
    program.interp p Q f1 <-> program.interp p Q f2.
  Proof.
    intros Hinj HQ Heq. rewrite Forall_forall in Hinj.
    assert (H: forall a b, fact_equiv a b -> program.interp p Q a -> program.interp p Q b).
    { intros a b Hab Ha. destruct (program.interp_rel_of _ _ _ Ha) as [HQa|Hin].
      - apply pftree.leaf. apply (HQ _ _ Hab). assumption.
      - apply Hinj in Hin. apply map_fact_inj in Hab; [|assumption]. subst. assumption. }
    split; intros Hi.
    - eapply H; eassumption.
    - eapply H; [|eassumption]. cbv [fact_equiv] in *. congruence.
  Qed.

  Lemma facts_agree_under_map_of_interp p Q hyps :
    program.meta_rules_valid p ->
    (forall fct, Q fct -> ~ In (fact.rel fct) (program.concl_rels p)) ->
    fact.set_doesnt_lie Q ->
    (forall f1 f2, fact_equiv f1 f2 -> Q f1 <-> Q f2) ->
    Forall inj_on_elt (program.concl_rels p) ->
    Forall (program.interp p Q) hyps ->
    facts_agree_under_map hyps.
  Proof.
    intros Hvalid Hinp Hlie HQ Hinj Hderiv mf1 mf2 H1 H2.
    rewrite Forall_forall in Hderiv. apply Hderiv in H1, H2.
    cbv [meta_fact.agree map_meta_fact map_fact_pattern fact_pattern.matches]. simpl.
    intros nf Hm1 Hm2. fwd.
    assert (Hd2: program.interp p Q
                   (fact.meta {| meta_fact.pattern :=
                                  {| fact_pattern.rel := meta_fact.rel mf1;
                                    fact_pattern.args :=
                                      mf2.(meta_fact.pattern).(fact_pattern.args) |};
                               meta_fact.set := mf2.(meta_fact.set) |})).
    { apply (interp_fact_equiv p Q (fact.meta mf2)); auto.
      cbv [fact_equiv map_fact map_meta_fact map_fact_pattern meta_fact.rel]. simp. congruence. }
    pose proof (program.meta_facts_consistent p Q mf1 _ Hinp
                  ltac:(eauto using fact.set_doesnt_lie_agree) Hvalid H1 Hd2) as Hagree.
    apply (Hagree {| normal_fact.rel := meta_fact.rel mf1;
                    normal_fact.args := nf.(normal_fact.args) |}); auto.
  Qed.

  Lemma interp_map_fw p Q fct :
    program.meta_rules_valid p ->
    (forall f', Q f' -> ~ In (fact.rel f') (program.concl_rels p)) ->
    fact.set_doesnt_lie Q ->
    (forall f1 f2, fact_equiv f1 f2 -> Q f1 <-> Q f2) ->
    Forall inj_on_elt (program.concl_rels p) ->
    program.interp p Q fct ->
    program.interp (map_program p)
      (fun f' => exists g, f' = map_fact g /\ Q g) (map_fact fct).
  Proof.
    intros Hvalid Hinp Hlie HQ Hinj Hprog. induction Hprog.
    - apply pftree.leaf. eauto.
    - eapply pftree.step.
      + eapply interp_step_map_fw; try eassumption.
        * rewrite Forall_forall in Hinj. apply Hinj.
          eauto using program.interp_step_concl_relname_in.
        * eapply facts_agree_under_map_of_interp; eassumption.
      + apply Forall_forall. intros h Hh. apply in_map_iff in Hh. fwd.
        rewrite Forall_forall in H1. auto.
  Qed.

  Lemma interp_map_bw p Q f_target :
    program.meta_rules_valid p ->
    (forall f', Q f' -> ~ In (fact.rel f') (program.concl_rels p)) ->
    fact.set_doesnt_lie Q ->
    (forall f1 f2, fact_equiv f1 f2 -> Q f1 <-> Q f2) ->
    Forall inj_on_elt (program.concl_rels p) ->
    program.interp (map_program p)
      (fun f' => exists g, f' = map_fact g /\ Q g) f_target ->
    exists fct, f_target = map_fact fct /\ program.interp p Q fct.
  Proof.
    intros Hvalid Hinp Hlie HQ Hinj Hprog. induction Hprog.
    - fwd. eauto using pftree.leaf.
    - apply Forall_exists_r_Forall2 in H1. fwd.
      assert (Hl: l = map map_fact ys).
      { apply Forall2_eq_map. rewrite <- Forall2_flip_iff.
        eapply Forall2_impl; [eassumption|]. simpl. intros. fwd. auto. }
      assert (Hys: Forall (program.interp p Q) ys).
      { apply Forall2_forget_l in H1. eapply Forall_impl; [eassumption|].
        simpl. intros. fwd. auto. }
      subst l. pose proof H as Ht. apply interp_step_map_target in Ht. fwd.
      eapply interp_step_map_bw in H; try eassumption.
      2: { rewrite Forall_forall in Hinj. auto. }
      2: { eapply facts_agree_under_map_of_interp; eassumption. }
      fwd. eexists. split; [reflexivity|]. eapply pftree.step; [eassumption|].
      apply Forall2_forget_l in Hp0. rewrite Forall_forall in Hp0, Hys.
      apply Forall_forall. intros h Hh. apply Hp0 in Hh. fwd.
      apply (interp_fact_equiv p Q x); auto.
  Qed.

  Lemma interp_map_iff p Q fct :
    program.meta_rules_valid p ->
    (forall f', Q f' -> ~ In (fact.rel f') (program.concl_rels p)) ->
    fact.set_doesnt_lie Q ->
    (forall f1 f2, fact_equiv f1 f2 -> Q f1 <-> Q f2) ->
    Forall inj_on_elt (program.concl_rels p) ->
    inj_on_elt (fact.rel fct) ->
    program.interp p Q fct <->
      program.interp (map_program p)
        (fun f' => exists g, f' = map_fact g /\ Q g) (map_fact fct).
  Proof.
    intros. split; intros H'.
    - apply interp_map_fw; assumption.
    - eapply interp_map_bw in H'; try assumption. fwd.
      apply map_fact_inj in H'p0; [|assumption]. subst. assumption.
  Qed.

  Lemma concl_rels_map_rule_rels r :
    rule.concl_rels (map_rule_rels r) = map f (rule.concl_rels r).
  Proof. destruct r; simpl; [rewrite !map_map|]; reflexivity. Qed.

  Lemma hyp_rels_map_rule_rels r :
    rule.hyp_rels (map_rule_rels r) = map f (rule.hyp_rels r).
  Proof. destruct r; simpl; [rewrite !map_map|]; reflexivity. Qed.

  Lemma concl_rels_map_meta_rule_rels mr :
    meta_rule.concl_rels (map_meta_rule_rels mr) = map f (meta_rule.concl_rels mr).
  Proof. cbv [meta_rule.concl_rels map_meta_rule_rels]. simpl. rewrite !map_map. reflexivity. Qed.

  Lemma hyp_rels_map_meta_rule_rels mr :
    meta_rule.hyp_rels (map_meta_rule_rels mr) = map f (meta_rule.hyp_rels mr).
  Proof. cbv [meta_rule.hyp_rels map_meta_rule_rels]. simpl. rewrite !map_map. reflexivity. Qed.

  Lemma concl_rels_map_program p :
    program.concl_rels (map_program p) = map f (program.concl_rels p).
  Proof.
    cbv [program.concl_rels map_program]. simpl.
    rewrite map_app, !map_flat_map, !flat_map_map. f_equal.
    - apply flat_map_ext. apply concl_rels_map_rule_rels.
    - apply flat_map_ext. apply concl_rels_map_meta_rule_rels.
  Qed.

  Lemma hyp_rels_map_program p :
    program.hyp_rels (map_program p) = map f (program.hyp_rels p).
  Proof.
    cbv [program.hyp_rels map_program]. simpl.
    rewrite map_app, !map_flat_map, !flat_map_map. f_equal.
    - apply flat_map_ext. apply hyp_rels_map_rule_rels.
    - apply flat_map_ext. apply hyp_rels_map_meta_rule_rels.
  Qed.

  Lemma all_rels_map_program p :
    program.all_rels (map_program p) = map f (program.all_rels p).
  Proof.
    cbv [program.all_rels]. rewrite concl_rels_map_program, hyp_rels_map_program.
    rewrite map_app. reflexivity.
  Qed.

  Lemma map_fact_of_args R args :
    map_fact (fact.of_args R args) = fact.of_args (f R) args.
  Proof. destruct args; reflexivity. Qed.

  Lemma map_fact_eq_of_args fct :
    map_fact fct = fact.of_args (f (fact.rel_of fct)) (fact.args_of fct).
  Proof. destruct fct; simp; reflexivity. Qed.

  Lemma implied_by_mf_map_bw_inj fct mf :
    (f (fact.rel fct) = f (meta_fact.rel mf) -> fact.rel fct = meta_fact.rel mf) ->
    fact.implied_by_mf (map_fact fct) (map_meta_fact mf) ->
    fact.implied_by_mf fct mf.
  Proof.
    cbv [fact.implied_by_mf fact.rel meta_fact.rel meta_fact.matches meta_fact.equiv
           map_fact map_normal_fact map_meta_fact map_fact_pattern fact_pattern.matches].
    destruct fct; simp; intros Hinj H; fwd.
    - ssplit; auto. symmetry. apply Hinj. congruence.
    - split; [|assumption]. f_equal. auto.
  Qed.

  Lemma implied_by_mfs_map_bw_inj mfs fct :
    (forall mf, In mf mfs ->
                f (fact.rel fct) = f (meta_fact.rel mf) ->
                fact.rel fct = meta_fact.rel mf) ->
    fact.implied_by_mfs (map map_meta_fact mfs) (map_fact fct) ->
    fact.implied_by_mfs mfs fct.
  Proof.
    cbv [fact.implied_by_mfs]. rewrite Exists_map, !Exists_exists.
    intros Hinj H. fwd. eauto using implied_by_mf_map_bw_inj.
  Qed.

  Lemma Forall2_interp_clause_pattern_map_image ctx cs hs :
    Forall2 (clause_pattern.interp ctx) (map map_clause_pattern_rel cs) hs ->
    exists hs', hs = map map_fact_pattern hs'.
  Proof.
    intros H. apply Forall_ex_eq_map. rewrite <- Forall2_map_l in H.
    apply Forall2_forget_l in H. eapply Forall_impl; [eassumption|].
    simpl. intros. fwd. eauto using interp_clause_pattern_map_image.
  Qed.

  Lemma meta_fact_map_image mh pat :
    mh.(meta_fact.pattern) = map_fact_pattern pat ->
    mh = map_meta_fact {| meta_fact.pattern := pat; meta_fact.set := mh.(meta_fact.set) |}.
  Proof. destruct mh. cbv [map_meta_fact]. simpl. intros. congruence. Qed.

  Lemma meta_facts_map_image mhyps pats :
    map meta_fact.pattern mhyps = map map_fact_pattern pats ->
    exists mhyps0, mhyps = map map_meta_fact mhyps0.
  Proof.
    intros H. apply Forall_ex_eq_map. apply map_eq_Forall2 in H.
    eapply Forall_impl; [eapply Forall2_forget_r; eassumption|].
    simpl. intros. fwd. eauto using meta_fact_map_image.
  Qed.

  (*now an easier theorem: if f happens to be injective, then the renaming is
    automatically correct*)

  Section inj.
    Context (p : program) (f_inj : injective_on f (program.all_rels p)).

    Lemma rule_concl_rel_in r x :
      In r p.(program.rules) ->
      In x (rule.concl_rels r) ->
      In x (program.all_rels p).
    Proof.
      cbv [program.all_rels program.concl_rels]. intros.
      apply in_or_app. left. apply in_or_app. left. apply in_flat_map. eauto.
    Qed.

    Lemma rule_hyp_rel_in r x :
      In r p.(program.rules) ->
      In x (rule.hyp_rels r) ->
      In x (program.all_rels p).
    Proof.
      cbv [program.all_rels program.hyp_rels]. intros.
      apply in_or_app. right. apply in_or_app. left. apply in_flat_map. eauto.
    Qed.

    Lemma meta_rule_concl_rel_in mr x :
      In mr p.(program.meta_rules) ->
      In x (meta_rule.concl_rels mr) ->
      In x (program.all_rels p).
    Proof.
      cbv [program.all_rels program.concl_rels]. intros.
      apply in_or_app. left. apply in_or_app. right. apply in_flat_map. eauto.
    Qed.

    Lemma meta_rule_hyp_rel_in mr x :
      In mr p.(program.meta_rules) ->
      In x (meta_rule.hyp_rels mr) ->
      In x (program.all_rels p).
    Proof.
      cbv [program.all_rels program.hyp_rels]. intros.
      apply in_or_app. right. apply in_or_app. right. apply in_flat_map. eauto.
    Qed.

    Lemma normal_fact_equiv_eq nf nf' :
      In nf.(normal_fact.rel) (program.all_rels p) ->
      In nf'.(normal_fact.rel) (program.all_rels p) ->
      normal_fact_equiv nf nf' ->
      nf = nf'.
    Proof.
      cbv [normal_fact_equiv map_normal_fact]. intros. simp. fwd. f_equal. auto.
    Qed.

    Lemma fact_equiv_eq a b :
      In (fact.rel a) (program.all_rels p) ->
      In (fact.rel b) (program.all_rels p) ->
      fact_equiv a b ->
      a = b.
    Proof.
      destruct a, b; cbv [fact_equiv fact.rel]; simpl; intros ? ? Heq;
        try discriminate.
      - f_equal. apply normal_fact_equiv_eq; auto. cbv [normal_fact_equiv]. congruence.
      - f_equal. cbv [map_meta_fact map_fact_pattern meta_fact.rel] in *. simp. fwd.
        f_equal. f_equal. auto.
    Qed.
  End inj.

  (*not yet ported to the current API:
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
   *)

End RelMap.
