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

  Definition inj_at (x y : rel1) : Prop := f x = f y -> x = y.

  Definition inj_on_elt (x : rel1) : Prop := forall y, inj_at x y.

  Lemma inj_on_elt_at x y :
    inj_on_elt x ->
    inj_at x y.
  Proof. auto. Qed.
  Hint Resolve inj_on_elt_at : core.

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

  Lemma map_fact_meta l :
    map map_fact (map fact.meta l) = map fact.meta (map map_meta_fact l).
  Proof. rewrite !map_map. apply map_ext. intros. reflexivity. Qed.

  Lemma map_pattern_map_meta_fact l :
    map meta_fact.pattern (map map_meta_fact l) =
      map map_fact_pattern (map meta_fact.pattern l).
  Proof. rewrite !map_map. apply map_ext. intros. reflexivity. Qed.

  Lemma map_fact_meta_inv l1 l2 :
    map fact.meta l1 = map map_fact l2 ->
    exists l2', l2 = map fact.meta l2' /\ l1 = map map_meta_fact l2'.
  Proof.
    revert l2. induction l1; intros [|b l2] H; simpl in H; try discriminate.
    - exists nil. auto.
    - destruct b; simpl in H; [discriminate|]. invert H.
      apply IHl1 in H2. fwd. exists (m :: l2'). auto.
  Qed.

  Lemma rel_map_fact fct :
    fact.rel (map_fact fct) = f (fact.rel fct).
  Proof. destruct fct; reflexivity. Qed.

  Lemma args_of_map_fact fct :
    fact.args_of (map_fact fct) = fact.args_of fct.
  Proof. destruct fct; simp; reflexivity. Qed.

  Lemma map_fact_of_args R args :
    map_fact (fact.of_args R args) = fact.of_args (f R) args.
  Proof. destruct args; reflexivity. Qed.

  Lemma map_fact_eq_of_args fct :
    map_fact fct = fact.of_args (f (fact.rel fct)) (fact.args_of fct).
  Proof. destruct fct; simp; reflexivity. Qed.

  Definition fact_equiv f1 f2 := map_fact f1 = map_fact f2.

  Definition normal_fact_equiv n1 n2 := map_normal_fact n1 = map_normal_fact n2.

  Definition fact_pattern_equiv p1 p2 := map_fact_pattern p1 = map_fact_pattern p2.

  Definition meta_fact_equiv m1 m2 := map_meta_fact m1 = map_meta_fact m2.

  Hint Unfold clause.interp clause_pattern.interp fact_pattern.matches
    fact_equiv normal_fact_equiv : core.

  Lemma Forall2_fact_equiv_meta l1 l2 :
    Forall2 meta_fact_equiv l1 l2 ->
    Forall2 fact_equiv (map fact.meta l1) (map fact.meta l2).
  Proof.
    intros. rewrite <- Forall2_map_l, <- Forall2_map_r.
    eapply Forall2_impl; [eassumption|]. cbv [fact_equiv meta_fact_equiv]. simpl.
    intros. f_equal. assumption.
  Qed.

  Definition map_clause_rel (c : clause) : clause :=
    {| clause.rel := f c.(clause.rel);
      clause.args := c.(clause.args) |}.

  Lemma clause_interp_map_fw ctx c h :
    clause.interp ctx c h ->
    clause.interp ctx (map_clause_rel c) (map_normal_fact h).
  Proof. intros. repeat invert_stuff. interp_exprs. Qed.

  Lemma Forall2_clause_interp_map_fw ctx hyps1 hyps2 :
    Forall2 (clause.interp ctx) hyps1 hyps2 ->
    Forall2 (clause.interp ctx) (map map_clause_rel hyps1) (map map_normal_fact hyps2).
  Proof.
    intros.
    rewrite <- Forall2_map_l, <- Forall2_map_r.
    eapply Forall2_impl; [eassumption|].
    eauto using clause_interp_map_fw.
  Qed.

  Lemma clause_interp_map_inv ctx c h :
    clause.interp ctx (map_clause_rel c) h ->
    exists h0, h = map_normal_fact h0 /\ clause.interp ctx c h0.
  Proof.
    cbv [clause.interp map_clause_rel map_normal_fact]. simpl. intros. fwd.
    exists {| normal_fact.rel := c.(clause.rel);
             normal_fact.args := h.(normal_fact.args) |}.
    simpl. ssplit; auto. simp. reflexivity.
  Qed.

  Lemma Forall2_clause_interp_map_inv ctx cs hs :
    Forall2 (clause.interp ctx) (map map_clause_rel cs) hs ->
    exists hs0, hs = map map_normal_fact hs0 /\ Forall2 (clause.interp ctx) cs hs0.
  Proof.
    intros H. rewrite <- Forall2_map_l in H.
    eapply Forall2_exists_r_map; [eassumption|]. eauto using clause_interp_map_inv.
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
        simpl. eauto using clause_interp_map_fw.
      + apply Forall2_clause_interp_map_fw. assumption.
    - simpl. rewrite map_map.
      (*the second goal pins the evar, so it must be solved first*)
      eassert (map _ vals = _) as ->.
      2: { constructor. eassumption. }
      apply map_ext. intros [? ?]. reflexivity.
  Qed.

  Lemma rule_interp_map_inv r nf hyps :
    rule.interp (map_rule_rels r) nf hyps ->
    exists nf0 hyps0,
      nf = map_normal_fact nf0 /\
      hyps = map map_fact hyps0 /\
      rule.interp r nf0 hyps0.
  Proof.
    intros H. destruct r; invert H.
    - apply Exists_exists in H2. fwd. apply in_map_iff in H2p0. fwd.
      apply clause_interp_map_inv in H2p1. fwd.
      apply Forall2_clause_interp_map_inv in H5. fwd.
      exists h0, (map fact.normal hs0). ssplit.
      + reflexivity.
      + symmetry. apply map_fact_normal.
      + econstructor; [apply Exists_exists; eauto | eassumption].
    - exists {| normal_fact.rel := concl;
               normal_fact.args := interp_agg agg vals :: args |},
        (fact.meta {| meta_fact.pattern :=
                       {| fact_pattern.rel := hyp;
                         fact_pattern.args := value_pattern.any :: value_pattern.any
                                                :: map value_pattern.exactly args |};
                     meta_fact.set := S |}
           :: map (fun '(i, x_i) =>
                     fact.normal {| normal_fact.rel := hyp;
                                   normal_fact.args := i :: x_i :: args |}) vals).
      ssplit.
      + reflexivity.
      + simpl. f_equal. rewrite map_map. apply map_ext. intros [? ?]. reflexivity.
      + constructor. assumption.
  Qed.

  Lemma clause_pattern_interp_map_fw ctx c fp :
    clause_pattern.interp ctx c fp ->
    clause_pattern.interp ctx (map_clause_pattern_rel c) (map_fact_pattern fp).
  Proof. intros. repeat invert_stuff. interp_exprs. Qed.

  Lemma Forall2_clause_pattern_interp_map_fw ctx hyps1 hyps2 :
    Forall2 (clause_pattern.interp ctx) hyps1 hyps2 ->
    Forall2 (clause_pattern.interp ctx)
      (map map_clause_pattern_rel hyps1) (map map_fact_pattern hyps2).
  Proof.
    intros. rewrite <- Forall2_map_l, <- Forall2_map_r.
    eapply Forall2_impl; [eassumption|].
    eauto using clause_pattern_interp_map_fw.
  Qed.

  Lemma clause_pattern_interp_map_inv ctx c fp :
    clause_pattern.interp ctx (map_clause_pattern_rel c) fp ->
    exists fp0, fp = map_fact_pattern fp0 /\ clause_pattern.interp ctx c fp0.
  Proof.
    cbv [clause_pattern.interp map_clause_pattern_rel map_fact_pattern]. simpl.
    intros. fwd.
    exists {| fact_pattern.rel := c.(clause_pattern.rel);
             fact_pattern.args := fp.(fact_pattern.args) |}.
    simpl. ssplit; auto. simp. reflexivity.
  Qed.

  Lemma Forall2_clause_pattern_interp_map_inv ctx cs fps :
    Forall2 (clause_pattern.interp ctx) (map map_clause_pattern_rel cs) fps ->
    exists fps0,
      fps = map map_fact_pattern fps0 /\
      Forall2 (clause_pattern.interp ctx) cs fps0.
  Proof.
    intros H. rewrite <- Forall2_map_l in H.
    eapply Forall2_exists_r_map; [eassumption|].
    eauto using clause_pattern_interp_map_inv.
  Qed.

  Lemma meta_fact_matches_map_fw mf nf :
    meta_fact.matches mf nf ->
    meta_fact.matches (map_meta_fact mf) (map_normal_fact nf).
  Proof.
    cbv [meta_fact.matches fact_pattern.matches map_meta_fact map_fact_pattern
           map_normal_fact]. simpl. intros. fwd. ssplit; auto. congruence.
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

  Lemma normal_fact_equiv_eq nf nf' :
    inj_at nf.(normal_fact.rel) nf'.(normal_fact.rel) ->
    normal_fact_equiv nf nf' ->
    nf = nf'.
  Proof.
    intros Hinj H. cbv [normal_fact_equiv map_normal_fact] in H. simp. fwd.
    f_equal. auto.
  Qed.

  Lemma fact_pattern_equiv_eq fp fp' :
    inj_at fp.(fact_pattern.rel) fp'.(fact_pattern.rel) ->
    fact_pattern_equiv fp fp' ->
    fp = fp'.
  Proof.
    intros Hinj H. cbv [fact_pattern_equiv map_fact_pattern] in H. simp. fwd.
    f_equal. auto.
  Qed.

  Lemma meta_fact_equiv_eq mf mf' :
    inj_at (meta_fact.rel mf) (meta_fact.rel mf') ->
    meta_fact_equiv mf mf' ->
    mf = mf'.
  Proof.
    cbv [meta_fact_equiv map_meta_fact meta_fact.rel]. intros Hinj H. simp. fwd.
    f_equal. apply fact_pattern_equiv_eq; assumption.
  Qed.

  Lemma fact_equiv_eq a b :
    inj_at (fact.rel a) (fact.rel b) ->
    fact_equiv a b ->
    a = b.
  Proof.
    destruct a, b; cbv [fact_equiv]; simpl; intros Hinj H; try discriminate.
    - f_equal. apply normal_fact_equiv_eq; [assumption|]. cbv [normal_fact_equiv]. congruence.
    - f_equal. apply meta_fact_equiv_eq; [assumption|]. cbv [meta_fact_equiv]. congruence.
  Qed.

  Hint Resolve program.rule_concl_rel_in program.rule_hyp_rel_in
    program.meta_rule_concl_rel_in program.meta_rule_hyp_rel_in
    program.concl_rel_all program.hyp_rel_all : core.

  Lemma one_step_derives_map_fw rules mhyps nf :
    rule.one_step_derives rules mhyps nf ->
    rule.one_step_derives (map map_rule_rels rules) (map map_meta_fact mhyps)
      (map_normal_fact nf).
  Proof.
    cbv [rule.one_step_derives]. intros H. fwd. exists (map map_fact hyps). split.
    - apply Exists_map, Exists_exists. eauto using rule_interp_map_fw.
    - apply Forall_forall. intros h Hh. apply in_map_iff in Hh. fwd.
      apply implied_by_mfs_map_fw. rewrite Forall_forall in Hp1. auto.
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
    intros Hvalid Hmr Hpat Hmatch Hagree Hinj. split; intros H.
    - apply one_step_derives_map_fw. assumption.
    - cbv [rule.one_step_derives] in *. fwd. apply in_map_iff in Hp0p0. fwd.
      apply rule_interp_map_inv in Hp0p1. fwd.
      apply normal_fact_equiv_eq in Hp0p1p0; [|auto]. subst.
      exists hyps0. split; [apply Exists_exists; eauto|].
      pose proof (Hvalid _ _ Hmr Hp0p0p1 _ _ _ _ Hpat Hp0p1p2 Hmatch) as Hcov.
      rewrite Forall_forall in Hcov, Hp1 |- *. intros h' Hh'.
      eapply implied_by_mfs_covered_bw; [assumption| |auto].
      apply Hp1. apply in_map. assumption.
  Qed.

  Lemma pattern_interp_map_fw mr pat pats :
    meta_rule.pattern_interp mr pat pats ->
    meta_rule.pattern_interp (map_meta_rule_rels mr) (map_fact_pattern pat)
      (map map_fact_pattern pats).
  Proof.
    cbv [meta_rule.pattern_interp map_meta_rule_rels]. simpl. intros. fwd.
    exists ctx. split.
    - apply Exists_map, Exists_exists. eauto using clause_pattern_interp_map_fw.
    - apply Forall2_clause_pattern_interp_map_fw. assumption.
  Qed.

  Lemma meta_fact_map_image mh pat :
    mh.(meta_fact.pattern) = map_fact_pattern pat ->
    mh = map_meta_fact {| meta_fact.pattern := pat; meta_fact.set := mh.(meta_fact.set) |}.
  Proof. destruct mh. cbv [map_meta_fact]. simpl. intros. congruence. Qed.

  Lemma meta_facts_map_image mhyps pats :
    map meta_fact.pattern mhyps = map map_fact_pattern pats ->
    exists mhyps0,
      mhyps = map map_meta_fact mhyps0 /\
      map meta_fact.pattern mhyps0 = pats.
  Proof.
    revert pats. induction mhyps; intros [|pat pats] H; simpl in H; try discriminate.
    - now exists [].
    - invert H. apply IHmhyps in H2. fwd.
      eexists ({| meta_fact.pattern := pat;
                 meta_fact.set := a.(meta_fact.set) |} :: _).
      split.
      + simpl. f_equal; auto using meta_fact_map_image.
      + simpl. f_equal; assumption.
  Qed.

  Lemma pattern_interp_map_inv mr pat pats :
    meta_rule.pattern_interp (map_meta_rule_rels mr) pat pats ->
    exists pat0 pats0,
      pat = map_fact_pattern pat0 /\
      pats = map map_fact_pattern pats0 /\
      meta_rule.pattern_interp mr pat0 pats0.
  Proof.
    cbv [meta_rule.pattern_interp map_meta_rule_rels]. simpl. intros. fwd.
    apply in_map_iff in Hp0p0. fwd.
    apply clause_pattern_interp_map_inv in Hp0p1. fwd.
    apply Forall2_clause_pattern_interp_map_inv in Hp1. fwd.
    exists fp0, fps0. ssplit; auto.
    exists ctx. split; [apply Exists_exists; eauto | assumption].
  Qed.

  Lemma meta_rule_interp_map_inv prog mr mf mhyps :
    meta_rule.interp prog (map_meta_rule_rels mr) mf mhyps ->
    exists mf0 mhyps0,
      mf = map_meta_fact mf0 /\
      mhyps = map map_meta_fact mhyps0 /\
      In (meta_fact.rel mf0) (meta_rule.concl_rels mr) /\
      Forall (fun mh => In (meta_fact.rel mh) (meta_rule.hyp_rels mr)) mhyps0.
  Proof.
    cbv [meta_rule.interp]. intros. fwd.
    apply pattern_interp_map_inv in Hp0. fwd.
    apply meta_facts_map_image in Hp0p1. fwd.
    cbv [meta_fact.equiv] in Hp1. fwd.
    exists {| meta_fact.pattern := pat0; meta_fact.set := mf.(meta_fact.set) |}, mhyps0.
    ssplit.
    - auto using meta_fact_map_image.
    - reflexivity.
    - cbv [meta_fact.rel]. simpl.
      eauto using meta_rule.pattern_interp_concl_relname_in.
    - pose proof (meta_rule.pattern_interp_hyp_relname_in _ _ _ Hp0p2) as Hhr.
      rewrite Lists.List.Forall_map in Hhr.
      eapply Forall_impl; [eassumption|]. auto.
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

  Lemma pattern_interp_map_bw mr pat pats :
    meta_rule.pattern_interp (map_meta_rule_rels mr) (map_fact_pattern pat)
      (map map_fact_pattern pats) ->
    exists pat0 pats0,
      fact_pattern_equiv pat pat0 /\
      Forall2 fact_pattern_equiv pats pats0 /\
      meta_rule.pattern_interp mr pat0 pats0.
  Proof.
    intros H. apply pattern_interp_map_inv in H. fwd.
    eexists _, _. ssplit; [eassumption| |eassumption].
    apply map_eq_Forall2. assumption.
  Qed.

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
    apply fact_pattern_equiv_eq in Hp0p0; [|auto]. subst.
    apply meta_facts_of_patterns in Hp0p1. fwd.
    rewrite (Forall2_map_eq _ _ _ _ Hp0p1p0) in Hp2.
    exists mhyps'. split; [assumption|].
    exists pat0. ssplit; [assumption|reflexivity|].
    intros args Hargs. rewrite Hp2 by assumption. symmetry.
    apply (one_step_derives_map_iff p mr pat0 mhyps'
             {| normal_fact.rel := pat0.(fact_pattern.rel); normal_fact.args := args |});
      eauto using meta_facts_agree_under_map_equiv.
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
    Forall inj_on_elt (program.concl_rels p) ->
    facts_agree_under_map hyps ->
    program.interp_step p fct hyps ->
    program.interp_step (map_program p) (map_fact fct) (map map_fact hyps).
  Proof.
    intros Hvalid Hinj Hagree H. rewrite Forall_forall in Hinj.
    pose proof (program.interp_step_concl_relname_in _ _ _ H) as Hin.
    invert H; simpl in *.
    - constructor. simpl. apply Exists_map, Exists_exists. fwd.
      eauto using rule_interp_map_fw.
    - rewrite map_fact_meta. constructor. simpl.
      apply Exists_map, Exists_exists. fwd.
      eexists. split; [eassumption|].
      apply meta_rule_interp_map_fw; auto using facts_agree_under_map_meta.
  Qed.

  Lemma interp_step_map_bw p fct_img hyps :
    program.meta_rules_valid p ->
    Forall inj_on_elt (program.concl_rels p) ->
    facts_agree_under_map hyps ->
    program.interp_step (map_program p) fct_img (map map_fact hyps) ->
    exists fct hyps',
      fct_img = map_fact fct /\
      Forall2 fact_equiv hyps hyps' /\
      program.interp_step p fct hyps'.
  Proof.
    intros Hvalid Hinj Hagree H. rewrite Forall_forall in Hinj.
    cbv [map_program] in H. invert H; simpl in *; fwd.
    - apply in_map_iff in H0p0. fwd.
      apply rule_interp_map_inv in H0p1. fwd.
      exists (fact.normal nf0). eexists. ssplit.
      + reflexivity.
      + apply map_eq_Forall2. eassumption.
      + constructor. apply Exists_exists. eauto.
    - apply map_fact_meta_inv in H0. fwd.
      apply in_map_iff in H2p0. fwd.
      pose proof H2p1 as Hinv. apply meta_rule_interp_map_inv in Hinv. fwd.
      eapply meta_rule_interp_map_bw in H2p1; try eassumption.
      2: eauto using facts_agree_under_map_meta.
      2: eauto.
      fwd. exists (fact.meta mf0), (map fact.meta mhyps'). ssplit.
      + reflexivity.
      + apply Forall2_fact_equiv_meta. assumption.
      + constructor. apply Exists_exists. eauto.
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
      - apply Hinj in Hin. apply fact_equiv_eq in Hab; [|auto]. subst. assumption. }
    split; intros Hi.
    - eapply H; eassumption.
    - eapply H; [|eassumption]. cbv [fact_equiv] in *. congruence.
  Qed.

  Lemma facts_agree_under_map_of_interp p Q hyps :
    program.meta_rules_valid p ->
    program.good_input_set p Q ->
    (forall f1 f2, fact_equiv f1 f2 -> Q f1 <-> Q f2) ->
    Forall inj_on_elt (program.concl_rels p) ->
    Forall (program.interp p Q) hyps ->
    facts_agree_under_map hyps.
  Proof.
    intros Hvalid [Hinp Hlie] HQ Hinj Hderiv mf1 mf2 H1 H2.
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
    program.good_input_set p Q ->
    (forall f1 f2, fact_equiv f1 f2 -> Q f1 <-> Q f2) ->
    Forall inj_on_elt (program.concl_rels p) ->
    program.interp p Q fct ->
    program.interp (map_program p)
      (fun f' => exists g, f' = map_fact g /\ Q g) (map_fact fct).
  Proof.
    intros Hvalid Hgood HQ Hinj Hprog. induction Hprog.
    - apply pftree.leaf. eauto.
    - eapply pftree.step.
      + eapply interp_step_map_fw; try eassumption.
        eapply facts_agree_under_map_of_interp; eassumption.
      + apply Forall_forall. intros h Hh. apply in_map_iff in Hh. fwd.
        rewrite Forall_forall in H1. auto.
  Qed.

  Lemma interp_map_hyps_image p Q l :
    Forall (fun y => exists fct, y = map_fact fct /\ program.interp p Q fct) l ->
    exists ys, l = map map_fact ys /\ Forall (program.interp p Q) ys.
  Proof.
    intros H. apply Forall_exists_r_Forall2 in H. fwd. exists ys. split.
    - apply Forall2_eq_map. rewrite <- Forall2_flip_iff.
      eapply Forall2_impl; [eassumption|]. simpl. intros. fwd. auto.
    - apply Forall2_forget_l in H. eapply Forall_impl; [eassumption|].
      simpl. intros. fwd. auto.
  Qed.

  Lemma interp_map_bw p Q f_target :
    program.meta_rules_valid p ->
    program.good_input_set p Q ->
    (forall f1 f2, fact_equiv f1 f2 -> Q f1 <-> Q f2) ->
    Forall inj_on_elt (program.concl_rels p) ->
    program.interp (map_program p)
      (fun f' => exists g, f' = map_fact g /\ Q g) f_target ->
    exists fct, f_target = map_fact fct /\ program.interp p Q fct.
  Proof.
    intros Hvalid Hgood HQ Hinj Hprog. induction Hprog.
    - fwd. eauto using pftree.leaf.
    - apply interp_map_hyps_image in H1. fwd.
      eapply interp_step_map_bw in H; try eassumption.
      2: { eapply facts_agree_under_map_of_interp; eassumption. }
      fwd. eexists. split; [reflexivity|]. eapply pftree.step; [eassumption|].
      apply Forall2_forget_l in Hp1. rewrite Forall_forall in Hp1, H1p1.
      apply Forall_forall. intros h Hh. apply Hp1 in Hh. fwd.
      apply (interp_fact_equiv p Q x); auto.
  Qed.

  Lemma interp_map_iff p Q fct :
    program.meta_rules_valid p ->
    program.good_input_set p Q ->
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
      apply fact_equiv_eq in H'p0; [|auto]. subst. assumption.
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

  Lemma implied_by_mf_map_bw_inj fct mf :
    inj_at (fact.rel fct) (meta_fact.rel mf) ->
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
    (forall mf, In mf mfs -> inj_at (fact.rel fct) (meta_fact.rel mf)) ->
    fact.implied_by_mfs (map map_meta_fact mfs) (map_fact fct) ->
    fact.implied_by_mfs mfs fct.
  Proof.
    cbv [fact.implied_by_mfs]. rewrite Exists_map, !Exists_exists.
    intros Hinj H. fwd. eauto using implied_by_mf_map_bw_inj.
  Qed.

  (*now an easier theorem: if f happens to be injective, then the renaming is
    automatically correct*)

  Section inj.
    Context (p : program) (f_inj : injective_on f (program.all_rels p)).

    Lemma f_inj_at x y :
      In x (program.all_rels p) ->
      In y (program.all_rels p) ->
      inj_at x y.
    Proof. cbv [inj_at]. auto. Qed.
    Hint Resolve f_inj_at : core.

    Lemma one_step_derives_map_iff_inj mhyps nf :
      In nf.(normal_fact.rel) (program.all_rels p) ->
      Forall (fun mf => In (meta_fact.rel mf) (program.all_rels p)) mhyps ->
      rule.one_step_derives p.(program.rules) mhyps nf <->
        rule.one_step_derives (map map_rule_rels p.(program.rules))
          (map map_meta_fact mhyps) (map_normal_fact nf).
    Proof.
      intros Hnf Hmhyps. split; intros H.
      - apply one_step_derives_map_fw. assumption.
      - cbv [rule.one_step_derives] in *. fwd. apply in_map_iff in Hp0p0. fwd.
        apply rule_interp_map_inv in Hp0p1. fwd.
        assert (nf = nf0) as ->.
        { apply normal_fact_equiv_eq; [|assumption].
          apply f_inj_at; eauto using rule.interp_concl_relname_in. }
        exists hyps0. split; [apply Exists_exists; eauto|].
        pose proof (rule.interp_hyp_relname_in _ _ _ Hp0p1p2) as Hhr.
        rewrite Forall_forall in Hp1, Hhr, Hmhyps |- *. intros h' Hh'.
        apply implied_by_mfs_map_bw_inj.
        + intros mf Hmf Heq. apply f_inj; eauto.
        + apply Hp1. apply in_map. assumption.
    Qed.

    Lemma Forall2_fact_pattern_equiv_eq l1 l2 :
      Forall (fun fp => In fp.(fact_pattern.rel) (program.all_rels p)) l1 ->
      Forall (fun fp => In fp.(fact_pattern.rel) (program.all_rels p)) l2 ->
      Forall2 fact_pattern_equiv l1 l2 ->
      l1 = l2.
    Proof.
      intros Hl1 Hl2 H. revert Hl1 Hl2. induction H; intros Hl1 Hl2; [reflexivity|].
      invert Hl1. invert Hl2. f_equal; auto using fact_pattern_equiv_eq.
    Qed.

    Lemma meta_rule_interp_map_bw_inj mr mf mhyps :
      In mr p.(program.meta_rules) ->
      In (meta_fact.rel mf) (program.all_rels p) ->
      Forall (fun mh => In (meta_fact.rel mh) (program.all_rels p)) mhyps ->
      meta_rule.interp (map map_rule_rels p.(program.rules)) (map_meta_rule_rels mr)
        (map_meta_fact mf) (map map_meta_fact mhyps) ->
      meta_rule.interp p.(program.rules) mr mf mhyps.
    Proof.
      intros Hmr Hmf Hmhyps H.
      cbv [meta_rule.interp meta_fact.equiv meta_fact.rel] in *. fwd.
      destruct mf. simpl in *. subst.
      rewrite map_pattern_map_meta_fact in Hp0.
      apply pattern_interp_map_bw in Hp0. fwd.
      assert (pattern = pat0) as <-.
      { apply fact_pattern_equiv_eq; [|assumption].
        apply f_inj_at; eauto using meta_rule.pattern_interp_concl_relname_in. }
      assert (map meta_fact.pattern mhyps = pats0) as <-.
      { apply Forall2_fact_pattern_equiv_eq; auto.
        - apply List.Forall_map. assumption.
        - eapply Forall_impl;
            [eapply meta_rule.pattern_interp_hyp_relname_in; eassumption|].
          simpl. eauto. }
      exists pattern. ssplit; [assumption|reflexivity|].
      intros args Hargs. rewrite Hp2 by assumption. symmetry.
      apply (one_step_derives_map_iff_inj mhyps
               {| normal_fact.rel := fact_pattern.rel pattern;
                 normal_fact.args := args |}); assumption.
    Qed.

    Lemma meta_rule_interp_map_fw_inj mr mf mhyps :
      In mr p.(program.meta_rules) ->
      meta_rule.interp p.(program.rules) mr mf mhyps ->
      meta_rule.interp (map map_rule_rels p.(program.rules)) (map_meta_rule_rels mr)
        (map_meta_fact mf) (map map_meta_fact mhyps).
    Proof.
      intros Hmr H. pose proof (meta_rule.interp_hyp_relname_in _ _ _ _ H) as Hhr.
      cbv [meta_rule.interp meta_fact.equiv meta_fact.rel] in *. fwd.
      destruct mf. simpl in *. subst.
      exists (map_fact_pattern pat). rewrite map_pattern_map_meta_fact.
      split; [auto using pattern_interp_map_fw|].
      cbv [map_meta_fact map_fact_pattern]. simpl. split; [reflexivity|].
      intros args Hargs. rewrite Hp2 by assumption.
      apply (one_step_derives_map_iff_inj mhyps
               {| normal_fact.rel := pat.(fact_pattern.rel); normal_fact.args := args |}).
      - simpl. eauto using meta_rule.pattern_interp_concl_relname_in.
      - eapply Forall_impl; [eassumption|]. simpl. eauto.
    Qed.

    Lemma interp_step_map_fw_inj fct hyps :
      program.interp_step p fct hyps ->
      program.interp_step (map_program p) (map_fact fct) (map map_fact hyps).
    Proof.
      intros H. invert H; simpl in *.
      - constructor. simpl. apply Exists_map, Exists_exists. fwd.
        eauto using rule_interp_map_fw.
      - rewrite map_fact_meta. constructor. simpl.
        apply Exists_map, Exists_exists. fwd.
        eauto using meta_rule_interp_map_fw_inj.
    Qed.

    Lemma interp_step_map_bw_inj f_target hyps_m :
      program.interp_step (map_program p) f_target hyps_m ->
      exists fct hyps,
        f_target = map_fact fct /\
        hyps_m = map map_fact hyps /\
        In (fact.rel fct) (program.all_rels p) /\
        Forall (fun h => In (fact.rel h) (program.all_rels p)) hyps /\
        program.interp_step p fct hyps.
    Proof.
      cbv [map_program]. intros H. invert H; simpl in *; fwd.
      - apply in_map_iff in H0p0. fwd.
        apply rule_interp_map_inv in H0p1. fwd.
        exists (fact.normal nf0), hyps0. ssplit.
        + reflexivity.
        + reflexivity.
        + simpl. eauto using rule.interp_concl_relname_in.
        + eapply Forall_impl; [eapply rule.interp_hyp_relname_in; eassumption|].
          simpl. eauto.
        + constructor. apply Exists_exists. eauto.
      - apply in_map_iff in H0p0. fwd.
        pose proof H0p1 as Hinv. apply meta_rule_interp_map_inv in Hinv. fwd.
        exists (fact.meta mf0), (map fact.meta mhyps0). ssplit.
        + reflexivity.
        + symmetry. apply map_fact_meta.
        + simpl. eauto.
        + apply List.Forall_map. eapply Forall_impl; [eassumption|]. simpl. eauto.
        + constructor. apply Exists_exists. eexists. split; [eassumption|].
          apply meta_rule_interp_map_bw_inj; try assumption.
          * eauto.
          * eapply Forall_impl; [eassumption|]. simpl. eauto.
    Qed.

    Lemma interp_bridge Q h g :
      (forall f1 f2, fact_equiv f1 f2 -> Q f1 <-> Q f2) ->
      injective_on f (fact.rel h :: program.all_rels p) ->
      fact_equiv h g ->
      program.interp p Q g ->
      program.interp p Q h.
    Proof.
      intros HQ Hinj Heq Hg. destruct (program.interp_rel_of _ _ _ Hg) as [HQg|Hin].
      - apply pftree.leaf. apply (HQ _ _ Heq). assumption.
      - assert (h = g) as ->; [|assumption].
        apply fact_equiv_eq; [|assumption].
        intros He. eapply injective_on_cons_head; eauto.
    Qed.

    Lemma interp_map_fw_inj Q fct :
      program.interp p Q fct ->
      program.interp (map_program p)
        (fun f' => exists g, f' = map_fact g /\ Q g) (map_fact fct).
    Proof.
      induction 1.
      - apply pftree.leaf. eauto.
      - eapply pftree.step; [apply interp_step_map_fw_inj; eassumption|].
        apply Forall_forall. intros h Hh. apply in_map_iff in Hh. fwd.
        rewrite Forall_forall in H1. auto.
    Qed.

    Lemma interp_map_bw_inj Q f_target :
      (forall f1 f2, fact_equiv f1 f2 -> Q f1 <-> Q f2) ->
      program.interp (map_program p)
        (fun f' => exists g, f' = map_fact g /\ Q g) f_target ->
      exists fct, f_target = map_fact fct /\ program.interp p Q fct.
    Proof.
      intros HQ Hprog. induction Hprog.
      - fwd. eauto using pftree.leaf.
      - apply interp_map_hyps_image in H1. fwd.
        apply interp_step_map_bw_inj in H. fwd.
        exists fct. split; [reflexivity|]. eapply pftree.step; [eassumption|].
        apply map_eq_Forall2 in Hp1. apply Forall2_forget_l in Hp1.
        rewrite Forall_forall in Hp1, H1p1, Hp3.
        apply Forall_forall. intros h Hh. specialize (Hp1 _ Hh). fwd.
        eapply interp_bridge.
        + assumption.
        + apply injective_on_cons_in; auto.
        + cbv [fact_equiv]. symmetry. eassumption.
        + auto.
    Qed.

    Lemma interp_map_iff_inj Q fct :
      injective_on f (fact.rel fct :: program.all_rels p) ->
      (forall f1 f2, fact_equiv f1 f2 -> Q f1 <-> Q f2) ->
      program.interp p Q fct <->
        program.interp (map_program p)
          (fun f' => exists g, f' = map_fact g /\ Q g) (map_fact fct).
    Proof.
      intros Hfct HQ. split; intros H.
      - apply interp_map_fw_inj. assumption.
      - apply interp_map_bw_inj in H; [|assumption]. fwd.
        eapply interp_bridge; eauto.
    Qed.
  End inj.
End RelMap.
