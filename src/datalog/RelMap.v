From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.

From Datalog Require Import Map Tactics Fp List Pftree Datalog.
From GraphSearch Require Import Dag.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List Datatypes.Option Eqb.

Import ListNotations.

Module normal_fact.
  Section __.
    Context `{params : datalog_params} {rel1 rel2 : Type}.

    Definition map_rel (g : rel1 -> rel2) (nf : normal_fact (relt := rel1)) : normal_fact (relt := rel2) :=
      {| normal_fact.rel := g nf.(normal_fact.rel);
        normal_fact.args := nf.(normal_fact.args) |}.

    Definition wf (wf_rel : rel1 -> rel2 -> Prop) (nf1 : normal_fact (relt := rel1)) (nf2 : normal_fact (relt := rel2)) :=
      wf_rel nf1.(normal_fact.rel) nf2.(normal_fact.rel) /\
        nf1.(normal_fact.args) = nf2.(normal_fact.args).
  End __.
End normal_fact.

Module fact_pattern.
  Section __.
    Context `{params : datalog_params} {rel1 rel2 : Type}.

    Definition map_rel (g : rel1 -> rel2) (fp : fact_pattern (relt := rel1)) : fact_pattern (relt := rel2) :=
      {| fact_pattern.rel := g fp.(fact_pattern.rel);
        fact_pattern.args := fp.(fact_pattern.args) |}.

    Definition wf (wf_rel : rel1 -> rel2 -> Prop) (fp1 : fact_pattern (relt := rel1)) (fp2 : fact_pattern (relt := rel2)) :=
      wf_rel fp1.(fact_pattern.rel) fp2.(fact_pattern.rel) /\
        fp1.(fact_pattern.args) = fp2.(fact_pattern.args).
  End __.
End fact_pattern.

Module meta_fact.
  Section __.
    Context `{params : datalog_params} {rel1 rel2 : Type}.

    Definition map_rel (g : rel1 -> rel2) (mf : meta_fact (_rel := rel1)) : meta_fact (_rel := rel2) :=
      {| meta_fact.pattern := fact_pattern.map_rel g mf.(meta_fact.pattern);
        meta_fact.set := mf.(meta_fact.set);
        meta_fact._pf := mf.(meta_fact._pf) |}.

    Definition wf (wf_rel : rel1 -> rel2 -> Prop) (mf1 : meta_fact (_rel := rel1)) (mf2 : meta_fact (_rel := rel2)) :=
      fact_pattern.wf wf_rel mf1.(meta_fact.pattern) mf2.(meta_fact.pattern) /\
        mf1.(meta_fact.set) = mf2.(meta_fact.set).
  End __.
End meta_fact.

Module fact.
  Section __.
    Context `{params : datalog_params} {rel1 rel2 : Type}.

    Definition map_rel (g : rel1 -> rel2) (f : fact (_rel := rel1)) : fact (_rel := rel2) :=
      match f with
      | fact.normal nf => fact.normal (normal_fact.map_rel g nf)
      | fact.meta mf => fact.meta (meta_fact.map_rel g mf)
      end.

    Definition wf (wf_rel : rel1 -> rel2 -> Prop) (f1 : fact (_rel := rel1)) (f2 : fact (_rel := rel2)) :=
      match f1, f2 with
      | fact.normal nf1, fact.normal nf2 => normal_fact.wf wf_rel nf1 nf2
      | fact.meta mf1, fact.meta mf2 => meta_fact.wf wf_rel mf1 mf2
      | _, _ => False
      end.
  End __.
End fact.

Module clause.
  Section __.
    Context `{params : datalog_params} {rel1 rel2 : Type}.

    Definition map_rel (g : rel1 -> rel2) (c : clause (relt := rel1)) : clause (relt := rel2) :=
      {| clause.rel := g c.(clause.rel);
        clause.args := c.(clause.args) |}.

    Definition wf (wf_rel : rel1 -> rel2 -> Prop) (c1 : clause (relt := rel1)) (c2 : clause (relt := rel2)) :=
      wf_rel c1.(clause.rel) c2.(clause.rel) /\ c1.(clause.args) = c2.(clause.args).
  End __.
End clause.

Module rule.
  Section __.
    Context `{params : datalog_params} {rel1 rel2 : Type}.

    Definition map_rel (g : rel1 -> rel2) (r : rule (_rel := rel1)) : rule (_rel := rel2) :=
      match r with
      | rule.impl concls hyps =>
          rule.impl (map (clause.map_rel g) concls) (map (clause.map_rel g) hyps)
      | rule.agg concl agg hyp =>
          rule.agg (g concl) agg (g hyp)
      end.

    Variant wf (wf_rel : rel1 -> rel2 -> Prop) : rule (_rel := rel1) -> rule (_rel := rel2) -> Prop :=
      | wf_impl concls1 hyps1 concls2 hyps2 :
        Forall2 (clause.wf wf_rel) concls1 concls2 ->
        Forall2 (clause.wf wf_rel) hyps1 hyps2 ->
        wf _ (rule.impl concls1 hyps1) (rule.impl concls2 hyps2)
      | wf_agg concl1 concl2 a hyp1 hyp2 :
        wf_rel concl1 concl2 ->
        wf_rel hyp1 hyp2 ->
        wf _ (rule.agg concl1 a hyp1) (rule.agg concl2 a hyp2).
  End __.
End rule.

Module clause_pattern.
  Section __.
    Context `{params : datalog_params} {rel1 rel2 : Type}.

    Definition map_rel (g : rel1 -> rel2) (cp : clause_pattern (relt := rel1)) : clause_pattern (relt := rel2) :=
      {| clause_pattern.rel := g cp.(clause_pattern.rel);
        clause_pattern.args := cp.(clause_pattern.args) |}.

    Definition wf (wf_rel : rel1 -> rel2 -> Prop) (cp1 : clause_pattern (relt := rel1)) (cp2 : clause_pattern (relt := rel2)) :=
      wf_rel cp1.(clause_pattern.rel) cp2.(clause_pattern.rel) /\
        cp1.(clause_pattern.args) = cp2.(clause_pattern.args).
  End __.
End clause_pattern.

Module meta_rule.
  Section __.
    Context `{params : datalog_params} {rel1 rel2 : Type}.

    Definition map_rel (g : rel1 -> rel2) (mr : meta_rule (relt := rel1)) : meta_rule (relt := rel2) :=
      {| meta_rule.concls := map (clause_pattern.map_rel g) mr.(meta_rule.concls);
        meta_rule.hyps := map (clause_pattern.map_rel g) mr.(meta_rule.hyps) |}.

    Definition wf (wf_rel : rel1 -> rel2 -> Prop) (mr1 : meta_rule (relt := rel1)) (mr2 : meta_rule (relt := rel2)) :=
      Forall2 (clause_pattern.wf wf_rel) mr1.(meta_rule.concls) mr2.(meta_rule.concls) /\
        Forall2 (clause_pattern.wf wf_rel) mr1.(meta_rule.hyps) mr2.(meta_rule.hyps).
  End __.
End meta_rule.

Module program.
  Section __.
    Context `{params : datalog_params} {rel1 rel2 : Type}.

    Definition map_rel (g : rel1 -> rel2) (p : program (relt := rel1)) : program (relt := rel2) :=
      {| program.rules := map (rule.map_rel g) p.(program.rules);
        program.meta_rules := map (meta_rule.map_rel g) p.(program.meta_rules) |}.

    Definition wf (wf_rel : rel1 -> rel2 -> Prop) (p1 : program (relt := rel1)) (p2 : program (relt := rel2)) :=
      Forall2 (rule.wf wf_rel) p1.(program.rules) p2.(program.rules) /\
        Forall2 (meta_rule.wf wf_rel) p1.(program.meta_rules) p2.(program.meta_rules).
  End __.
End program.

Section RelMap.
  Context {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context {semantics : datalog_semantics fn aggregator T}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.
  Context {value_eqb : Eqb T} {value_eqb_ok : Eqb_ok value_eqb}.
  Context {value_set : map.map (list T) unit} {value_set_ok : map.ok value_set}.

  Hint Resolve program.rule_concl_rel_in program.rule_hyp_rel_in
    program.meta_rule_concl_rel_in program.meta_rule_hyp_rel_in
    program.concl_rel_all program.hyp_rel_all in_combine_l in_combine_r : core.

  Section Wf.
    Context {rel1 rel2} (wf_rel : rel1 -> rel2 -> Prop).

    Definition meta_facts_agree (mhyps : list (meta_fact (_rel := rel2))) :=
      forall mf mf', In mf mhyps -> In mf' mhyps -> meta_fact.agree mf mf'.

    Definition facts_agree (hyps : list (fact (_rel := rel2))) :=
      forall mf mf', In (fact.meta mf) hyps -> In (fact.meta mf') hyps -> meta_fact.agree mf mf'.

    Lemma facts_agree_meta mhyps :
      facts_agree (map fact.meta mhyps) ->
      meta_facts_agree mhyps.
    Proof. cbv [facts_agree meta_facts_agree]. auto using in_map. Qed.

    Definition functional_at x := forall y y', wf_rel x y -> wf_rel x y' -> y = y'.

    Definition inj_at x x' := forall y, wf_rel x y -> wf_rel x' y -> x = x'.

    Definition inj_on_elt x := forall x', inj_at x x'.

    Definition inj_on l := forall x x', In x l -> In x' l -> inj_at x x'.

    Lemma inj_on_elt_at x x' :
      inj_on_elt x ->
      inj_at x x'.
    Proof. auto. Qed.

    Lemma inj_on_at l x x' :
      inj_on l ->
      In x l ->
      In x' l ->
      inj_at x x'.
    Proof. auto. Qed.
    Hint Resolve inj_on_elt_at inj_on_at : core.

    Lemma wf_fact_map_rel_r g h :
      fact.wf wf_rel h (fact.map_rel g h) <-> wf_rel (fact.rel h) (g (fact.rel h)).
    Proof.
      destruct h; cbv [fact.wf normal_fact.wf meta_fact.wf fact_pattern.wf fact.rel meta_fact.rel
                       fact.map_rel normal_fact.map_rel meta_fact.map_rel fact_pattern.map_rel];
        simpl; intuition.
    Qed.

    Lemma wf_fact_map_rel_l g h :
      fact.wf wf_rel (fact.map_rel g h) h <-> wf_rel (g (fact.rel h)) (fact.rel h).
    Proof.
      destruct h; cbv [fact.wf normal_fact.wf meta_fact.wf fact_pattern.wf fact.rel meta_fact.rel
                       fact.map_rel normal_fact.map_rel meta_fact.map_rel fact_pattern.map_rel];
        simpl; intuition.
    Qed.

    Lemma wf_fact_rel f1 f2 :
      fact.wf wf_rel f1 f2 ->
      wf_rel (fact.rel f1) (fact.rel f2).
    Proof.
      destruct f1, f2; cbv [fact.wf normal_fact.wf meta_fact.wf fact_pattern.wf meta_fact.rel];
        simpl; intuition.
    Qed.

    Lemma wf_normal_fact_fun nf1 nf2 nf2' :
      functional_at nf1.(normal_fact.rel) ->
      normal_fact.wf wf_rel nf1 nf2 ->
      normal_fact.wf wf_rel nf1 nf2' ->
      nf2 = nf2'.
    Proof.
      destruct nf2, nf2'. cbv [functional_at normal_fact.wf]. simpl. intros. fwd.
      f_equal; solve [eauto | congruence].
    Qed.

    Lemma wf_normal_fact_inj nf1 nf1' nf2 :
      inj_at nf1.(normal_fact.rel) nf1'.(normal_fact.rel) ->
      normal_fact.wf wf_rel nf1 nf2 ->
      normal_fact.wf wf_rel nf1' nf2 ->
      nf1 = nf1'.
    Proof.
      destruct nf1, nf1'. cbv [inj_at normal_fact.wf]. simpl. intros. fwd.
      f_equal; solve [eauto | congruence].
    Qed.

    Lemma wf_fact_pattern_fun fp1 fp2 fp2' :
      functional_at fp1.(fact_pattern.rel) ->
      fact_pattern.wf wf_rel fp1 fp2 ->
      fact_pattern.wf wf_rel fp1 fp2' ->
      fp2 = fp2'.
    Proof.
      destruct fp2, fp2'. cbv [functional_at fact_pattern.wf]. simpl. intros. fwd.
      f_equal; solve [eauto | congruence].
    Qed.

    Lemma wf_fact_pattern_inj fp1 fp1' fp2 :
      inj_at fp1.(fact_pattern.rel) fp1'.(fact_pattern.rel) ->
      fact_pattern.wf wf_rel fp1 fp2 ->
      fact_pattern.wf wf_rel fp1' fp2 ->
      fp1 = fp1'.
    Proof.
      destruct fp1, fp1'. cbv [inj_at fact_pattern.wf]. simpl. intros. fwd.
      f_equal; solve [eauto | congruence].
    Qed.

    Lemma wf_meta_fact_fun mf1 mf2 mf2' :
      functional_at (meta_fact.rel mf1) ->
      meta_fact.wf wf_rel mf1 mf2 ->
      meta_fact.wf wf_rel mf1 mf2' ->
      mf2 = mf2'.
    Proof.
      cbv [meta_fact.wf]. intros. fwd. apply meta_fact.eq_ext; [|congruence].
      eapply wf_fact_pattern_fun; eassumption.
    Qed.

    Lemma wf_meta_fact_inj mf1 mf1' mf2 :
      inj_at (meta_fact.rel mf1) (meta_fact.rel mf1') ->
      meta_fact.wf wf_rel mf1 mf2 ->
      meta_fact.wf wf_rel mf1' mf2 ->
      mf1 = mf1'.
    Proof.
      cbv [meta_fact.wf]. intros. fwd. apply meta_fact.eq_ext; [|congruence].
      eapply wf_fact_pattern_inj; eassumption.
    Qed.

    Lemma wf_fact_fun f1 f2 f2' :
      functional_at (fact.rel f1) ->
      fact.wf wf_rel f1 f2 ->
      fact.wf wf_rel f1 f2' ->
      f2 = f2'.
    Proof.
      destruct f1, f2, f2'; simpl; intros; try contradiction;
        f_equal; eauto using wf_normal_fact_fun, wf_meta_fact_fun.
    Qed.

    Lemma wf_fact_inj f1 f1' f2 :
      inj_at (fact.rel f1) (fact.rel f1') ->
      fact.wf wf_rel f1 f2 ->
      fact.wf wf_rel f1' f2 ->
      f1 = f1'.
    Proof.
      destruct f1, f1', f2; simpl; intros; try contradiction;
        f_equal; eauto using wf_normal_fact_inj, wf_meta_fact_inj.
    Qed.

    Lemma wf_clauses_rels cs1 cs2 :
      Forall2 (clause.wf wf_rel) cs1 cs2 ->
      Forall2 wf_rel (map clause.rel cs1) (map clause.rel cs2).
    Proof.
      intros. rewrite <- Forall2_map_l, <- Forall2_map_r.
      eapply Forall2_impl; [eassumption|]. cbv [clause.wf]. intros. fwd. assumption.
    Qed.

    Lemma wf_clause_patterns_rels cs1 cs2 :
      Forall2 (clause_pattern.wf wf_rel) cs1 cs2 ->
      Forall2 wf_rel (map clause_pattern.rel cs1) (map clause_pattern.rel cs2).
    Proof.
      intros. rewrite <- Forall2_map_l, <- Forall2_map_r.
      eapply Forall2_impl; [eassumption|]. cbv [clause_pattern.wf]. intros. fwd. assumption.
    Qed.

    Lemma wf_rule_hyp_rels r1 r2 :
      rule.wf wf_rel r1 r2 ->
      Forall2 wf_rel (rule.hyp_rels r1) (rule.hyp_rels r2).
    Proof. destruct 1; simpl; eauto using wf_clauses_rels. Qed.

    Lemma wf_rule_concl_rels r1 r2 :
      rule.wf wf_rel r1 r2 ->
      Forall2 wf_rel (rule.concl_rels r1) (rule.concl_rels r2).
    Proof. destruct 1; simpl; eauto using wf_clauses_rels. Qed.

    Lemma wf_meta_rule_hyp_rels mr1 mr2 :
      meta_rule.wf wf_rel mr1 mr2 ->
      Forall2 wf_rel (meta_rule.hyp_rels mr1) (meta_rule.hyp_rels mr2).
    Proof. cbv [meta_rule.wf]. intros. fwd. eauto using wf_clause_patterns_rels. Qed.

    Lemma wf_meta_rule_concl_rels mr1 mr2 :
      meta_rule.wf wf_rel mr1 mr2 ->
      Forall2 wf_rel (meta_rule.concl_rels mr1) (meta_rule.concl_rels mr2).
    Proof. cbv [meta_rule.wf]. intros. fwd. eauto using wf_clause_patterns_rels. Qed.

    Lemma wf_program_hyp_rels p1 p2 :
      program.wf wf_rel p1 p2 ->
      Forall2 wf_rel (program.hyp_rels p1) (program.hyp_rels p2).
    Proof.
      cbv [program.wf program.hyp_rels]. intros. fwd. apply Forall2_app.
      - apply Forall2_flat_map. eapply Forall2_impl; [eassumption|].
        eauto using wf_rule_hyp_rels.
      - apply Forall2_flat_map. eapply Forall2_impl; [eassumption|].
        eauto using wf_meta_rule_hyp_rels.
    Qed.

    Lemma wf_program_concl_rels p1 p2 :
      program.wf wf_rel p1 p2 ->
      Forall2 wf_rel (program.concl_rels p1) (program.concl_rels p2).
    Proof.
      cbv [program.wf program.concl_rels]. intros. fwd. apply Forall2_app.
      - apply Forall2_flat_map. eapply Forall2_impl; [eassumption|].
        eauto using wf_rule_concl_rels.
      - apply Forall2_flat_map. eapply Forall2_impl; [eassumption|].
        eauto using wf_meta_rule_concl_rels.
    Qed.

    Lemma clause_interp_wf ctx c1 c2 h1 :
      clause.wf wf_rel c1 c2 ->
      clause.interp ctx c1 h1 ->
      exists h2, normal_fact.wf wf_rel h1 h2 /\ clause.interp ctx c2 h2.
    Proof.
      cbv [clause.wf clause.interp normal_fact.wf]. intros. fwd.
      exists {| normal_fact.rel := c2.(clause.rel); normal_fact.args := h1.(normal_fact.args) |}.
      simpl. ssplit; congruence.
    Qed.

    Lemma clause_interp_wf_inv ctx c1 c2 h2 :
      clause.wf wf_rel c1 c2 ->
      clause.interp ctx c2 h2 ->
      exists h1, normal_fact.wf wf_rel h1 h2 /\ clause.interp ctx c1 h1.
    Proof.
      cbv [clause.wf clause.interp normal_fact.wf]. intros. fwd.
      exists {| normal_fact.rel := c1.(clause.rel); normal_fact.args := h2.(normal_fact.args) |}.
      simpl. ssplit; congruence.
    Qed.

    Lemma Forall2_clause_interp_wf ctx cs1 cs2 hs1 :
      Forall2 (clause.wf wf_rel) cs1 cs2 ->
      Forall2 (clause.interp ctx) cs1 hs1 ->
      exists hs2, Forall2 (normal_fact.wf wf_rel) hs1 hs2 /\ Forall2 (clause.interp ctx) cs2 hs2.
    Proof.
      intros Hwf H.
      eapply Forall2_Forall2_exists with (T := normal_fact.wf wf_rel) (U := clause.interp ctx) in Hwf;
        [exact Hwf | exact H |].
      intros. eapply clause_interp_wf; eassumption.
    Qed.

    Lemma Forall2_clause_interp_wf_inv ctx cs1 cs2 hs2 :
      Forall2 (clause.wf wf_rel) cs1 cs2 ->
      Forall2 (clause.interp ctx) cs2 hs2 ->
      exists hs1, Forall2 (normal_fact.wf wf_rel) hs1 hs2 /\ Forall2 (clause.interp ctx) cs1 hs1.
    Proof.
      intros Hwf H. rewrite <- Forall2_flip_iff in Hwf.
      eapply Forall2_Forall2_exists
        with (T := fun h2 h1 => normal_fact.wf wf_rel h1 h2) (U := clause.interp ctx) in Hwf;
        [| exact H | intros; eapply clause_interp_wf_inv; eassumption].
      fwd. rewrite <- Forall2_flip_iff in Hwfp0. eauto.
    Qed.

    Lemma rule_interp_wf r1 r2 nf1 hyps1 :
      rule.wf wf_rel r1 r2 ->
      rule.interp r1 nf1 hyps1 ->
      exists nf2 hyps2,
        normal_fact.wf wf_rel nf1 nf2 /\ Forall2 (fact.wf wf_rel) hyps1 hyps2 /\ rule.interp r2 nf2 hyps2.
    Proof.
      intros Hwf Hint. destruct Hwf; invert Hint.
      - apply Exists_exists in H3. fwd.
        eapply Forall2_In_l in H3p0; [|eassumption]. fwd.
        eapply clause_interp_wf in H3p1; [|eassumption]. fwd.
        eapply Forall2_clause_interp_wf in H6; [|eassumption]. fwd.
        eexists _, (map fact.normal hs2). ssplit.
        + eassumption.
        + rewrite <- Forall2_map_l, <- Forall2_map_r. eapply Forall2_impl; [eassumption|]. auto.
        + econstructor; [apply Exists_exists; eauto | eassumption].
      - exists {| normal_fact.rel := concl2;
                 normal_fact.args := interp_agg a vals :: args |},
          (fact.meta
             (meta_fact.mk
                {| fact_pattern.rel := hyp2;
                  fact_pattern.args := value_pattern.any :: value_pattern.any
                                         :: map value_pattern.exactly args |}
                (map (fun '(i, x) => i :: x :: args) vals))
             :: map (fun '(i, x_i) =>
                       fact.normal {| normal_fact.rel := hyp2;
                                     normal_fact.args := i :: x_i :: args |}) vals).
        ssplit.
        + cbv [normal_fact.wf]. auto.
        + constructor.
          * cbv [fact.wf meta_fact.wf fact_pattern.wf meta_fact.mk]. auto.
          * apply Forall2_map_map, Forall_forall. intros [i x] _.
            cbv [fact.wf normal_fact.wf]. auto.
        + constructor. assumption.
    Qed.

    Lemma rule_interp_wf_inv r1 r2 nf2 hyps2 :
      rule.wf wf_rel r1 r2 ->
      rule.interp r2 nf2 hyps2 ->
      exists nf1 hyps1,
        normal_fact.wf wf_rel nf1 nf2 /\ Forall2 (fact.wf wf_rel) hyps1 hyps2 /\ rule.interp r1 nf1 hyps1.
    Proof.
      intros Hwf Hint. destruct Hwf; invert Hint.
      - apply Exists_exists in H3. fwd.
        eapply Forall2_In_r in H3p0; [|eassumption]. fwd.
        eapply clause_interp_wf_inv in H3p1; [|eassumption]. fwd.
        eapply Forall2_clause_interp_wf_inv in H6; [|eassumption]. fwd.
        eexists _, (map fact.normal hs1). ssplit.
        + eassumption.
        + rewrite <- Forall2_map_l, <- Forall2_map_r. eapply Forall2_impl; [eassumption|]. auto.
        + econstructor; [apply Exists_exists; eauto | eassumption].
      - exists {| normal_fact.rel := concl1;
                 normal_fact.args := interp_agg a vals :: args |},
          (fact.meta
             (meta_fact.mk
                {| fact_pattern.rel := hyp1;
                  fact_pattern.args := value_pattern.any :: value_pattern.any
                                         :: map value_pattern.exactly args |}
                (map (fun '(i, x) => i :: x :: args) vals))
             :: map (fun '(i, x_i) =>
                       fact.normal {| normal_fact.rel := hyp1;
                                     normal_fact.args := i :: x_i :: args |}) vals).
        ssplit.
        + cbv [normal_fact.wf]. auto.
        + constructor.
          * cbv [fact.wf meta_fact.wf fact_pattern.wf meta_fact.mk]. auto.
          * apply Forall2_map_map, Forall_forall. intros [i x] _.
            cbv [fact.wf normal_fact.wf]. auto.
        + constructor. assumption.
    Qed.

    Lemma clause_pattern_interp_wf ctx c1 c2 fp1 :
      clause_pattern.wf wf_rel c1 c2 ->
      clause_pattern.interp ctx c1 fp1 ->
      exists fp2, fact_pattern.wf wf_rel fp1 fp2 /\ clause_pattern.interp ctx c2 fp2.
    Proof.
      cbv [clause_pattern.wf clause_pattern.interp fact_pattern.wf]. intros. fwd.
      exists {| fact_pattern.rel := c2.(clause_pattern.rel);
               fact_pattern.args := fp1.(fact_pattern.args) |}.
      simpl. ssplit; congruence.
    Qed.

    Lemma clause_pattern_interp_wf_inv ctx c1 c2 fp2 :
      clause_pattern.wf wf_rel c1 c2 ->
      clause_pattern.interp ctx c2 fp2 ->
      exists fp1, fact_pattern.wf wf_rel fp1 fp2 /\ clause_pattern.interp ctx c1 fp1.
    Proof.
      cbv [clause_pattern.wf clause_pattern.interp fact_pattern.wf]. intros. fwd.
      exists {| fact_pattern.rel := c1.(clause_pattern.rel);
               fact_pattern.args := fp2.(fact_pattern.args) |}.
      simpl. ssplit; congruence.
    Qed.

    Lemma Forall2_clause_pattern_interp_wf ctx cs1 cs2 fps1 :
      Forall2 (clause_pattern.wf wf_rel) cs1 cs2 ->
      Forall2 (clause_pattern.interp ctx) cs1 fps1 ->
      exists fps2,
        Forall2 (fact_pattern.wf wf_rel) fps1 fps2 /\ Forall2 (clause_pattern.interp ctx) cs2 fps2.
    Proof.
      intros Hwf H.
      eapply Forall2_Forall2_exists
        with (T := fact_pattern.wf wf_rel) (U := clause_pattern.interp ctx) in Hwf;
        [exact Hwf | exact H |].
      intros. eapply clause_pattern_interp_wf; eassumption.
    Qed.

    Lemma Forall2_clause_pattern_interp_wf_inv ctx cs1 cs2 fps2 :
      Forall2 (clause_pattern.wf wf_rel) cs1 cs2 ->
      Forall2 (clause_pattern.interp ctx) cs2 fps2 ->
      exists fps1,
        Forall2 (fact_pattern.wf wf_rel) fps1 fps2 /\ Forall2 (clause_pattern.interp ctx) cs1 fps1.
    Proof.
      intros Hwf H. rewrite <- Forall2_flip_iff in Hwf.
      eapply Forall2_Forall2_exists
        with (T := fun fp2 fp1 => fact_pattern.wf wf_rel fp1 fp2) (U := clause_pattern.interp ctx) in Hwf;
        [| exact H | intros; eapply clause_pattern_interp_wf_inv; eassumption].
      fwd. rewrite <- Forall2_flip_iff in Hwfp0. eauto.
    Qed.

    Lemma pattern_interp_wf mr1 mr2 pat1 pats1 :
      meta_rule.wf wf_rel mr1 mr2 ->
      meta_rule.pattern_interp mr1 pat1 pats1 ->
      exists pat2 pats2,
        fact_pattern.wf wf_rel pat1 pat2 /\ Forall2 (fact_pattern.wf wf_rel) pats1 pats2 /\
          meta_rule.pattern_interp mr2 pat2 pats2.
    Proof.
      cbv [meta_rule.wf meta_rule.pattern_interp]. intros Hwf H. fwd.
      eapply Forall2_In_l in Hp0p0; [|eassumption]. fwd.
      eapply clause_pattern_interp_wf in Hp0p1; [|eassumption]. fwd.
      eapply Forall2_clause_pattern_interp_wf in Hp1; [|eassumption]. fwd.
      eexists _, _. ssplit; [eassumption | eassumption |].
      exists ctx. split; [apply Exists_exists; eauto | assumption].
    Qed.

    Lemma pattern_interp_wf_inv mr1 mr2 pat2 pats2 :
      meta_rule.wf wf_rel mr1 mr2 ->
      meta_rule.pattern_interp mr2 pat2 pats2 ->
      exists pat1 pats1,
        fact_pattern.wf wf_rel pat1 pat2 /\ Forall2 (fact_pattern.wf wf_rel) pats1 pats2 /\
          meta_rule.pattern_interp mr1 pat1 pats1.
    Proof.
      cbv [meta_rule.wf meta_rule.pattern_interp]. intros Hwf H. fwd.
      eapply Forall2_In_r in Hp0p0; [|eassumption]. fwd.
      eapply clause_pattern_interp_wf_inv in Hp0p1; [|eassumption]. fwd.
      eapply Forall2_clause_pattern_interp_wf_inv in Hp1; [|eassumption]. fwd.
      eexists _, _. ssplit; [eassumption | eassumption |].
      exists ctx. split; [apply Exists_exists; eauto | assumption].
    Qed.

    Lemma wf_meta_fact_of_pattern pat1 mf2 :
      fact_pattern.wf wf_rel pat1 mf2.(meta_fact.pattern) ->
      exists mf1, pat1 = mf1.(meta_fact.pattern) /\ meta_fact.wf wf_rel mf1 mf2.
    Proof.
      intros H. exists (meta_fact.map_rel (fun _ => pat1.(fact_pattern.rel)) mf2).
      cbv [fact_pattern.wf meta_fact.wf meta_fact.map_rel fact_pattern.map_rel] in *.
      destruct pat1. simpl in *. fwd. auto.
    Qed.

    Lemma wf_meta_facts_of_patterns pats1 mhyps2 :
      Forall2 (fact_pattern.wf wf_rel) pats1 (map meta_fact.pattern mhyps2) ->
      exists mhyps1, pats1 = map meta_fact.pattern mhyps1 /\ Forall2 (meta_fact.wf wf_rel) mhyps1 mhyps2.
    Proof.
      intros H. rewrite <- Forall2_flip_iff, <- Forall2_map_l in H.
      eapply Forall2_exists_r_map with (R' := fun mf2 mf1 => meta_fact.wf wf_rel mf1 mf2) in H;
        [|eauto using wf_meta_fact_of_pattern]. fwd.
      rewrite <- Forall2_flip_iff in Hp1. eauto.
    Qed.

    Lemma Forall2_wf_fact_meta mhyps1 hyps2 :
      Forall2 (fact.wf wf_rel) (map fact.meta mhyps1) hyps2 ->
      exists mhyps2, hyps2 = map fact.meta mhyps2 /\ Forall2 (meta_fact.wf wf_rel) mhyps1 mhyps2.
    Proof.
      intros H. rewrite <- Forall2_map_l in H. eapply Forall2_exists_r_map; [eassumption|].
      intros mf1 [nf2|mf2]; simpl; [contradiction|]. eauto.
    Qed.

    Lemma covered_by_wf h1 h2 fp1 fp2 :
      functional_at (fact.rel h1) ->
      fact.wf wf_rel h1 h2 ->
      fact_pattern.wf wf_rel fp1 fp2 ->
      fact.covered_by h1 fp1 ->
      fact.covered_by h2 fp2.
    Proof.
      destruct h1 as [nf1|mf1], h2 as [nf2|mf2]; simpl; intros Hfun Hh Hfp Hcov;
        try contradiction.
      - cbv [normal_fact.wf fact_pattern.wf fact_pattern.matches functional_at] in *. fwd.
        split; [apply Hfun | ]; congruence.
      - subst. eapply wf_fact_pattern_fun; [exact Hfun | exact Hfp |]. apply Hh.
    Qed.

    Lemma covered_by_pats_wf h1 h2 pats1 pats2 :
      functional_at (fact.rel h1) ->
      fact.wf wf_rel h1 h2 ->
      Forall2 (fact_pattern.wf wf_rel) pats1 pats2 ->
      fact.covered_by_pats pats1 h1 ->
      fact.covered_by_pats pats2 h2.
    Proof.
      cbv [fact.covered_by_pats]. intros Hfun Hh Hpats Hcov.
      apply Exists_exists in Hcov. fwd. eapply Forall2_In_l in Hcovp0; [|eassumption]. fwd.
      apply Exists_exists. eauto using covered_by_wf.
    Qed.

    Lemma implied_by_mf_wf h1 h2 mf1 mf2 :
      functional_at (fact.rel h1) ->
      fact.wf wf_rel h1 h2 ->
      meta_fact.wf wf_rel mf1 mf2 ->
      fact.implied_by_mf h1 mf1 ->
      fact.implied_by_mf h2 mf2.
    Proof.
      destruct h1 as [nf1|m1], h2 as [nf2|m2]; simpl; intros Hfun Hh Hmf H; try contradiction.
      - cbv [normal_fact.wf meta_fact.wf fact_pattern.wf meta_fact.matches fact_pattern.matches
               functional_at meta_fact.rel] in *. fwd.
        ssplit; [apply Hfun | |]; congruence.
      - subst. eapply wf_meta_fact_fun; eassumption.
    Qed.

    Lemma implied_by_mfs_wf h1 h2 mfs1 mfs2 :
      functional_at (fact.rel h1) ->
      fact.wf wf_rel h1 h2 ->
      Forall2 (meta_fact.wf wf_rel) mfs1 mfs2 ->
      fact.implied_by_mfs mfs1 h1 ->
      fact.implied_by_mfs mfs2 h2.
    Proof.
      cbv [fact.implied_by_mfs]. intros Hfun Hh Hmfs H.
      apply Exists_exists in H. fwd. eapply Forall2_In_l in Hp0; [|eassumption]. fwd.
      apply Exists_exists. eauto using implied_by_mf_wf.
    Qed.

    (* A hypothesis of p1 covered by a pattern of mf1 is implied by mf1 once the
       image of mf1 agrees with whatever implied the image of the hypothesis. *)
    Lemma implied_by_mf_wf_bw h1 h2 mf1 mf2 mf2' :
      functional_at (fact.rel h1) ->
      fact.wf wf_rel h1 h2 ->
      meta_fact.wf wf_rel mf1 mf2' ->
      meta_fact.agree mf2 mf2' ->
      fact.implied_by_mf h2 mf2 ->
      fact.covered_by h1 mf1.(meta_fact.pattern) ->
      fact.implied_by_mf h1 mf1.
    Proof.
      destruct h1 as [nf1|m1], h2 as [nf2|m2]; simpl; intros Hfun Hh Hmf Hagree H Hcov;
        try contradiction.
      - cbv [normal_fact.wf meta_fact.wf fact_pattern.wf meta_fact.matches fact_pattern.matches
               functional_at meta_fact.agree meta_fact.rel] in *. fwd.
        split; [auto|]. rewrite Hmfp1, Hhp1.
        rewrite <- (Hagree nf2); [assumption | auto | split; [apply Hfun|]; congruence].
      - subst. apply meta_fact.eq_ext; [congruence|].
        rewrite (proj2 Hh), (proj2 Hmf). f_equal. apply meta_fact.eq_of_agree; [|assumption].
        eapply wf_fact_pattern_fun; [exact Hfun | apply Hh |]. rewrite <- Hcov. apply Hmf.
    Qed.

    Lemma implied_by_mfs_wf_bw h1 h2 mfs1 mfs2 :
      functional_at (fact.rel h1) ->
      fact.wf wf_rel h1 h2 ->
      Forall2 (meta_fact.wf wf_rel) mfs1 mfs2 ->
      meta_facts_agree mfs2 ->
      fact.implied_by_mfs mfs2 h2 ->
      fact.covered_by_pats (map meta_fact.pattern mfs1) h1 ->
      fact.implied_by_mfs mfs1 h1.
    Proof.
      cbv [fact.implied_by_mfs fact.covered_by_pats]. intros Hfun Hh Hmfs Hagree H Hcov.
      rewrite Exists_map in Hcov. apply Exists_exists in H, Hcov. fwd.
      eapply Forall2_In_l in Hcovp0; [|eassumption]. fwd.
      apply Exists_exists. exists x. split; [eauto|].
      eapply implied_by_mf_wf_bw;
        [eassumption | eassumption | eassumption | | eassumption | eassumption].
      apply Hagree; eauto.
    Qed.

    Lemma implied_by_mf_wf_bw_inj h1 h2 mf1 mf2 :
      inj_at (fact.rel h1) (meta_fact.rel mf1) ->
      fact.wf wf_rel h1 h2 ->
      meta_fact.wf wf_rel mf1 mf2 ->
      fact.implied_by_mf h2 mf2 ->
      fact.implied_by_mf h1 mf1.
    Proof.
      destruct h1 as [nf1|m1], h2 as [nf2|m2]; simpl; intros Hinj Hh Hmf H; try contradiction.
      - cbv [normal_fact.wf meta_fact.wf fact_pattern.wf meta_fact.matches fact_pattern.matches
               inj_at meta_fact.rel] in *. fwd.
        ssplit; [symmetry; eapply Hinj; [eassumption | congruence] | congruence | congruence].
      - subst. eapply wf_meta_fact_inj; eassumption.
    Qed.

    Lemma implied_by_mfs_wf_bw_inj h1 h2 mfs1 mfs2 :
      Forall (fun mf => inj_at (fact.rel h1) (meta_fact.rel mf)) mfs1 ->
      fact.wf wf_rel h1 h2 ->
      Forall2 (meta_fact.wf wf_rel) mfs1 mfs2 ->
      fact.implied_by_mfs mfs2 h2 ->
      fact.implied_by_mfs mfs1 h1.
    Proof.
      cbv [fact.implied_by_mfs]. intros Hinj Hh Hmfs H. rewrite Forall_forall in Hinj.
      apply Exists_exists in H. fwd. eapply Forall2_In_r in Hp0; [|eassumption]. fwd.
      apply Exists_exists. exists x0. split; [eauto|].
      eapply implied_by_mf_wf_bw_inj; eauto.
    Qed.

    Section Program.
      Context (p1 : program (relt := rel1)) (p2 : program (relt := rel2)) (Hwf : program.wf wf_rel p1 p2)
        (Hfun : Forall functional_at (program.all_rels p1)).

      Lemma functional_at_concl x :
        In x (program.concl_rels p1) ->
        functional_at x.
      Proof. rewrite Forall_forall in Hfun. auto. Qed.

      Lemma functional_at_hyp x :
        In x (program.hyp_rels p1) ->
        functional_at x.
      Proof. rewrite Forall_forall in Hfun. auto. Qed.
      Hint Resolve functional_at_concl functional_at_hyp : core.

      Lemma functional_at_hyps r hyps nf h :
        In r p1.(program.rules) ->
        rule.interp r nf hyps ->
        In h hyps ->
        functional_at (fact.rel h).
      Proof.
        intros Hr Hint Hh. pose proof (rule.interp_hyp_relname_in _ _ _ Hint) as Hrels.
        rewrite Forall_forall in Hrels. eauto.
      Qed.

      Lemma functional_at_pats mr pat pats fp :
        In mr p1.(program.meta_rules) ->
        meta_rule.pattern_interp mr pat pats ->
        In fp pats ->
        functional_at fp.(fact_pattern.rel).
      Proof.
        intros Hmr Hpat Hfp.
        pose proof (meta_rule.pattern_interp_hyp_relname_in _ _ _ Hpat) as Hrels.
        rewrite Forall_forall in Hrels. eauto.
      Qed.

      Lemma wf_fact_exists h1 :
        In (fact.rel h1) (program.hyp_rels p1) ->
        exists h2, fact.wf wf_rel h1 h2.
      Proof.
        intros H. eapply Forall2_In_l in H; [|apply wf_program_hyp_rels; exact Hwf]. fwd.
        exists (fact.map_rel (fun _ => y) h1). apply wf_fact_map_rel_r. assumption.
      Qed.

      Lemma wf_fact_exists_inv h2 :
        In (fact.rel h2) (program.hyp_rels p2) ->
        exists h1, fact.wf wf_rel h1 h2.
      Proof.
        intros H. eapply Forall2_In_r in H; [|apply wf_program_hyp_rels; exact Hwf]. fwd.
        exists (fact.map_rel (fun _ => x) h2). apply wf_fact_map_rel_l. assumption.
      Qed.

      Lemma one_step_derives_wf mhyps1 mhyps2 nf1 nf2 :
        Forall2 (meta_fact.wf wf_rel) mhyps1 mhyps2 ->
        normal_fact.wf wf_rel nf1 nf2 ->
        rule.one_step_derives p1.(program.rules) mhyps1 nf1 ->
        rule.one_step_derives p2.(program.rules) mhyps2 nf2.
      Proof.
        cbv [rule.one_step_derives]. intros Hmhyps Hnf H. fwd.
        eapply Forall2_In_l in Hp0p0; [|apply Hwf]. fwd.
        eapply rule_interp_wf in Hp0p1 as Hint2; [|eassumption]. fwd.
        replace nf2 with nf0.
        2: { eapply wf_normal_fact_fun; [|eassumption..].
             eauto using rule.interp_concl_relname_in. }
        exists hyps2. split; [apply Exists_exists; eauto|].
        rewrite Forall_forall in Hp1 |- *. intros h2 Hh2.
        eapply Forall2_In_r in Hh2; [|eassumption]. fwd.
        eapply implied_by_mfs_wf with (h1 := x0); eauto using functional_at_hyps.
      Qed.

      Section General.
        Context (Hinj : Forall inj_on_elt (program.concl_rels p1))
          (Hvalid : program.meta_rules_valid p1).

        Lemma inj_at_concl x x' :
          In x (program.concl_rels p1) ->
          inj_at x x'.
        Proof. rewrite Forall_forall in Hinj. auto. Qed.
        Hint Resolve inj_at_concl : core.

        Lemma one_step_derives_wf_bw mr1 pat1 mhyps1 mhyps2 nf1 nf2 :
          In mr1 p1.(program.meta_rules) ->
          meta_rule.pattern_interp mr1 pat1 (map meta_fact.pattern mhyps1) ->
          fact_pattern.matches pat1 nf1 ->
          Forall2 (meta_fact.wf wf_rel) mhyps1 mhyps2 ->
          meta_facts_agree mhyps2 ->
          normal_fact.wf wf_rel nf1 nf2 ->
          rule.one_step_derives p2.(program.rules) mhyps2 nf2 ->
          rule.one_step_derives p1.(program.rules) mhyps1 nf1.
        Proof.
          cbv [rule.one_step_derives]. intros Hmr Hpat Hmatch Hmhyps Hagree Hnf H. fwd.
          eapply Forall2_In_r in Hp0p0; [|apply Hwf]. fwd.
          eapply rule_interp_wf_inv in Hp0p1 as Hint1; [|eassumption]. fwd.
          replace nf1 with nf0 in *.
          2: { eapply wf_normal_fact_inj; [|eassumption..].
               eauto using rule.interp_concl_relname_in. }
          exists hyps1. split; [apply Exists_exists; eauto|].
          pose proof (Hvalid _ _ Hmr ltac:(eauto) _ _ _ _ Hpat Hint1p2 Hmatch) as Hcov.
          rewrite Forall_forall in Hp1, Hcov |- *. intros h1 Hh1.
          eapply Forall2_In_l in Hh1 as Hh2; [|eassumption]. fwd.
          eapply implied_by_mfs_wf_bw with (h2 := y); eauto using functional_at_hyps.
        Qed.

        Lemma meta_rule_interp_wf mr1 mr2 mf1 mf2 mhyps1 mhyps2 :
          In mr1 p1.(program.meta_rules) ->
          meta_rule.wf wf_rel mr1 mr2 ->
          meta_fact.wf wf_rel mf1 mf2 ->
          Forall2 (meta_fact.wf wf_rel) mhyps1 mhyps2 ->
          meta_facts_agree mhyps2 ->
          meta_rule.interp p1.(program.rules) mr1 mf1 mhyps1 ->
          meta_rule.interp p2.(program.rules) mr2 mf2 mhyps2.
        Proof.
          intros Hmr Hwfmr Hmf Hmhyps Hagree [Hpat Hset].
          eapply pattern_interp_wf in Hpat as Hpat2; [|eassumption]. fwd.
          replace pat2 with mf2.(meta_fact.pattern) in *.
          2: { eapply wf_fact_pattern_fun; [| apply Hmf | eassumption].
               eauto using meta_rule.pattern_interp_concl_relname_in. }
          replace pats2 with (map meta_fact.pattern mhyps2) in *.
          2: { eapply Forall2_unique_r; [| eassumption |].
               - rewrite <- Forall2_map_l, <- Forall2_map_r.
                 eapply Forall2_impl; [eassumption|]. intros. apply H.
               - eauto using wf_fact_pattern_fun, functional_at_pats. }
          split; [assumption|].
          intros nf2 Hmatch2.
          pose proof (Hset {| normal_fact.rel := meta_fact.rel mf1;
                             normal_fact.args := nf2.(normal_fact.args) |}) as Hset1.
          cbv [meta_fact.wf fact_pattern.wf fact_pattern.matches meta_fact.rel] in *. fwd.
          simpl in Hset1. rewrite <- Hmfp1, Hset1 by (split; congruence).
          split.
          - eapply one_step_derives_wf; [eassumption|]. cbv [normal_fact.wf]. simpl.
            split; congruence.
          - eapply one_step_derives_wf_bw; [eassumption | eassumption | | eassumption | eassumption |].
            + cbv [fact_pattern.matches]. simpl. split; congruence.
            + cbv [normal_fact.wf]. simpl. split; congruence.
        Qed.

        Lemma meta_rule_interp_wf_bw mr1 mr2 mf1 mf2 mhyps2 :
          In mr1 p1.(program.meta_rules) ->
          meta_rule.wf wf_rel mr1 mr2 ->
          meta_fact.wf wf_rel mf1 mf2 ->
          meta_facts_agree mhyps2 ->
          meta_rule.interp p2.(program.rules) mr2 mf2 mhyps2 ->
          exists mhyps1,
            Forall2 (meta_fact.wf wf_rel) mhyps1 mhyps2 /\
              meta_rule.interp p1.(program.rules) mr1 mf1 mhyps1.
        Proof.
          intros Hmr Hwfmr Hmf Hagree [Hpat Hset].
          eapply pattern_interp_wf_inv in Hpat as Hpat1; [|eassumption]. fwd.
          replace pat1 with mf1.(meta_fact.pattern) in *.
          2: { symmetry. eapply wf_fact_pattern_inj; [| eassumption | apply Hmf].
               eauto using meta_rule.pattern_interp_concl_relname_in. }
          apply wf_meta_facts_of_patterns in Hpat1p1. fwd.
          exists mhyps1. split; [assumption|]. split; [assumption|].
          intros nf1 Hmatch1.
          pose proof (Hset {| normal_fact.rel := meta_fact.rel mf2;
                             normal_fact.args := nf1.(normal_fact.args) |}) as Hset2.
          cbv [meta_fact.wf fact_pattern.wf fact_pattern.matches meta_fact.rel] in *. fwd.
          simpl in Hset2. rewrite Hmfp1, Hset2 by (split; congruence).
          split.
          - eapply one_step_derives_wf_bw; [eassumption | eassumption | | eassumption | eassumption |].
            + cbv [fact_pattern.matches]. simpl. split; congruence.
            + cbv [normal_fact.wf]. simpl. split; congruence.
          - eapply one_step_derives_wf; [eassumption|]. cbv [normal_fact.wf]. simpl.
            split; congruence.
        Qed.

        Lemma interp_step_wf f1 f2 hyps1 hyps2 :
          fact.wf wf_rel f1 f2 ->
          Forall2 (fact.wf wf_rel) hyps1 hyps2 ->
          facts_agree hyps2 ->
          program.interp_step p1 f1 hyps1 ->
          program.interp_step p2 f2 hyps2.
        Proof.
          intros Hf Hhyps Hagree H. invert H.
          - destruct f2 as [nf2|]; [|contradiction].
            apply Exists_exists in H0. fwd.
            eapply Forall2_In_l in H0p0; [|apply Hwf]. fwd.
            eapply rule_interp_wf in H0p1 as Hint2; [|eassumption]. fwd.
            replace nf2 with nf0.
            2: { eapply wf_normal_fact_fun; [|eassumption..].
                 eauto using rule.interp_concl_relname_in. }
            replace hyps2 with hyps0.
            2: { eapply Forall2_unique_r; [eassumption | eassumption |].
                 eauto using wf_fact_fun, functional_at_hyps. }
            constructor. apply Exists_exists. eauto.
          - destruct f2 as [|mf2]; [contradiction|].
            apply Forall2_wf_fact_meta in Hhyps. fwd.
            eapply Forall2_In_l in H0p0; [|apply Hwf]. fwd.
            constructor. apply Exists_exists. exists y. split; [eauto|].
            eapply meta_rule_interp_wf; eauto using facts_agree_meta.
        Qed.

        Lemma interp_step_wf_bw f1 f2 hyps2 :
          fact.wf wf_rel f1 f2 ->
          facts_agree hyps2 ->
          program.interp_step p2 f2 hyps2 ->
          exists hyps1, Forall2 (fact.wf wf_rel) hyps1 hyps2 /\ program.interp_step p1 f1 hyps1.
        Proof.
          intros Hf Hagree H. invert H.
          - destruct f1 as [nf1|]; [|contradiction].
            apply Exists_exists in H0. fwd.
            eapply Forall2_In_r in H0p0; [|apply Hwf]. fwd.
            eapply rule_interp_wf_inv in H0p1 as Hint1; [|eassumption]. fwd.
            replace nf1 with nf0.
            2: { eapply wf_normal_fact_inj; [|eassumption..].
                 eauto using rule.interp_concl_relname_in. }
            exists hyps1. split; [assumption|]. constructor. apply Exists_exists. eauto.
          - destruct f1 as [|mf1]; [contradiction|].
            apply Exists_exists in H0. fwd.
            eapply Forall2_In_r in H0p0; [|apply Hwf]. fwd.
            eapply meta_rule_interp_wf_bw in H0p1; eauto using facts_agree_meta. fwd.
            exists (map fact.meta mhyps1). split.
            + rewrite <- Forall2_map_l, <- Forall2_map_r. eapply Forall2_impl; [eassumption|].
              auto.
            + constructor. apply Exists_exists. eauto.
        Qed.

        Context (Q1 Q2 : fact -> Prop)
          (Hgood : program.good_input_set p1 Q1)
          (HQ : forall f1 f2, fact.wf wf_rel f1 f2 -> Q1 f1 <-> Q2 f2).

        Lemma interp_wf_transport f1 f1' f2 :
          fact.wf wf_rel f1 f2 ->
          fact.wf wf_rel f1' f2 ->
          program.interp p1 Q1 f1 ->
          program.interp p1 Q1 f1'.
        Proof.
          intros H1 H1' Hi. destruct (program.interp_rel_of _ _ _ Hi) as [HQ1|Hin].
          - apply pftree.leaf. apply (HQ _ _ H1'), (HQ _ _ H1). assumption.
          - rewrite <- (wf_fact_inj f1 f1' f2); auto.
        Qed.

        Lemma facts_agree_of_interp hyps2 :
          (forall h2, In h2 hyps2 -> exists h1, fact.wf wf_rel h1 h2 /\ program.interp p1 Q1 h1) ->
          facts_agree hyps2.
        Proof.
          intros H mf2 mf2' Hin Hin'.
          destruct (H _ Hin) as ([|mf1] & Hwf1 & Hi1); [contradiction|].
          destruct (H _ Hin') as ([|mf1'] & Hwf1' & Hi1'); [contradiction|].
          intros nf Hm Hm'.
          assert (Hi'' : program.interp p1 Q1
                           (fact.meta (meta_fact.map_rel (fun _ => meta_fact.rel mf1) mf1'))).
          { eapply interp_wf_transport with (f1 := fact.meta mf1'); [eassumption| |eassumption].
            cbv [fact.wf meta_fact.wf fact_pattern.wf fact_pattern.matches meta_fact.map_rel
                   fact_pattern.map_rel meta_fact.rel] in *. simpl. fwd. ssplit; congruence. }
          pose proof (program.meta_facts_consistent p1 Q1 _ _ (proj1 Hgood)
                        ltac:(intros; eapply fact.set_doesnt_lie_agree; [apply Hgood | eassumption..])
                        Hvalid Hi1 Hi'') as Hagree.
          specialize (Hagree {| normal_fact.rel := meta_fact.rel mf1;
                               normal_fact.args := nf.(normal_fact.args) |}).
          cbv [fact.wf meta_fact.wf fact_pattern.wf fact_pattern.matches meta_fact.map_rel
                 fact_pattern.map_rel meta_fact.rel] in *. simpl in *. fwd.
          rewrite <- Hwf1p1, <- Hwf1'p1. apply Hagree; split; congruence.
        Qed.

        Lemma interp_wf f1 :
          program.interp p1 Q1 f1 ->
          forall f2, fact.wf wf_rel f1 f2 -> program.interp p2 Q2 f2.
        Proof.
          induction 1; intros f2 Hf2.
          - apply pftree.leaf. apply (HQ _ _ Hf2). assumption.
          - edestruct (Forall_exists_r_Forall2 (fact.wf wf_rel) l) as [hyps2 Hhyps2].
            { eapply Forall_impl; [eapply program.interp_step_hyp_relname_in; eassumption|].
              simpl. eauto using wf_fact_exists. }
            rewrite Forall_forall in H0, H1.
            eapply pftree.step.
            + eapply interp_step_wf; [eassumption | eassumption | | eassumption].
              apply facts_agree_of_interp. intros h2 Hh2.
              eapply Forall2_In_r in Hh2; [|eassumption]. fwd. eauto.
            + apply Forall_forall. intros h2 Hh2.
              eapply Forall2_In_r in Hh2; [|eassumption]. fwd. eauto.
        Qed.

        Lemma interp_wf_bw f2 :
          program.interp p2 Q2 f2 ->
          forall f1, fact.wf wf_rel f1 f2 -> program.interp p1 Q1 f1.
        Proof.
          induction 1; intros f1 Hf1.
          - apply pftree.leaf. apply (HQ _ _ Hf1). assumption.
          - rewrite Forall_forall in H1.
            pose proof (program.interp_step_hyp_relname_in _ _ _ H) as Hrels.
            rewrite Forall_forall in Hrels.
            edestruct interp_step_wf_bw as (hyps1 & Hhyps1 & Hstep1); [eassumption | | eassumption |].
            { apply facts_agree_of_interp. intros h2 Hh2.
              edestruct wf_fact_exists_inv as [h1 Hh1]; [eauto|]. eauto. }
            eapply pftree.step; [eassumption|].
            apply Forall_forall. intros h1 Hh1.
            eapply Forall2_In_l in Hh1; [|eassumption]. fwd. eauto.
        Qed.
      End General.

      (*now an easier theorem: if wf_rel happens to be injective, then the renaming is
        automatically correct*)
      Section Inj.
        Context (l : list rel1) (Hl : incl (program.all_rels p1) l) (Hinj : inj_on l).

        Lemma in_l x :
          In x (program.all_rels p1) ->
          In x l.
        Proof. auto. Qed.
        Hint Resolve in_l : core.

        Lemma inj_at_concl_l x x' :
          In x (program.concl_rels p1) ->
          In x' l ->
          inj_at x x'.
        Proof. auto. Qed.

        Lemma inj_at_hyp_l x x' :
          In x (program.hyp_rels p1) ->
          In x' l ->
          inj_at x x'.
        Proof. auto. Qed.
        Hint Resolve inj_at_concl_l inj_at_hyp_l : core.

        Lemma one_step_derives_wf_bw_inj mhyps1 mhyps2 nf1 nf2 :
          In nf1.(normal_fact.rel) l ->
          Forall (fun mf => In (meta_fact.rel mf) l) mhyps1 ->
          Forall2 (meta_fact.wf wf_rel) mhyps1 mhyps2 ->
          normal_fact.wf wf_rel nf1 nf2 ->
          rule.one_step_derives p2.(program.rules) mhyps2 nf2 ->
          rule.one_step_derives p1.(program.rules) mhyps1 nf1.
        Proof.
          cbv [rule.one_step_derives]. intros Hnf1 Hmhyps1 Hmhyps Hnf H. fwd.
          eapply Forall2_In_r in Hp0p0; [|apply Hwf]. fwd.
          eapply rule_interp_wf_inv in Hp0p1 as Hint1; [|eassumption]. fwd.
          replace nf1 with nf0 in *.
          2: { eapply wf_normal_fact_inj; [|eassumption..].
               eauto 6 using rule.interp_concl_relname_in. }
          exists hyps1. split; [apply Exists_exists; eauto|].
          pose proof (rule.interp_hyp_relname_in _ _ _ Hint1p2) as Hrels.
          rewrite Forall_forall in Hp1, Hrels, Hmhyps1 |- *. intros h1 Hh1.
          eapply Forall2_In_l in Hh1 as Hh2; [|eassumption]. fwd.
          eapply implied_by_mfs_wf_bw_inj; [|eassumption..|eauto].
          apply Forall_forall. eauto 6.
        Qed.

        Lemma meta_rule_interp_wf_inj mr1 mr2 mf1 mf2 mhyps1 mhyps2 :
          In mr1 p1.(program.meta_rules) ->
          meta_rule.wf wf_rel mr1 mr2 ->
          meta_fact.wf wf_rel mf1 mf2 ->
          Forall2 (meta_fact.wf wf_rel) mhyps1 mhyps2 ->
          meta_rule.interp p1.(program.rules) mr1 mf1 mhyps1 ->
          meta_rule.interp p2.(program.rules) mr2 mf2 mhyps2.
        Proof.
          intros Hmr Hwfmr Hmf Hmhyps [Hpat Hset].
          pose proof (meta_rule.pattern_interp_hyp_relname_in _ _ _ Hpat) as Hrels.
          rewrite Lists.List.Forall_map in Hrels.
          eapply pattern_interp_wf in Hpat as Hpat2; [|eassumption]. fwd.
          replace pat2 with mf2.(meta_fact.pattern) in *.
          2: { eapply wf_fact_pattern_fun; [| apply Hmf | eassumption].
               eauto using meta_rule.pattern_interp_concl_relname_in. }
          replace pats2 with (map meta_fact.pattern mhyps2) in *.
          2: { eapply Forall2_unique_r; [| eassumption |].
               - rewrite <- Forall2_map_l, <- Forall2_map_r.
                 eapply Forall2_impl; [eassumption|]. intros. apply H.
               - eauto using wf_fact_pattern_fun, functional_at_pats. }
          split; [assumption|].
          intros nf2 Hmatch2.
          pose proof (Hset {| normal_fact.rel := meta_fact.rel mf1;
                             normal_fact.args := nf2.(normal_fact.args) |}) as Hset1.
          pose proof (meta_rule.pattern_interp_concl_relname_in _ _ _ Hpat) as Hconcl.
          cbv [meta_fact.wf fact_pattern.wf fact_pattern.matches meta_fact.rel] in *. fwd.
          simpl in Hset1. rewrite <- Hmfp1, Hset1 by (split; congruence).
          split.
          - eapply one_step_derives_wf; [eassumption|]. cbv [normal_fact.wf]. simpl.
            split; congruence.
          - eapply one_step_derives_wf_bw_inj; [| |eassumption|].
            + simpl. eauto 6.
            + eapply Forall_impl; [eassumption|]. eauto 6.
            + cbv [normal_fact.wf]. simpl. split; congruence.
        Qed.

        Lemma meta_rule_interp_wf_bw_inj mr1 mr2 mf1 mf2 mhyps2 :
          In mr1 p1.(program.meta_rules) ->
          In (meta_fact.rel mf1) l ->
          meta_rule.wf wf_rel mr1 mr2 ->
          meta_fact.wf wf_rel mf1 mf2 ->
          meta_rule.interp p2.(program.rules) mr2 mf2 mhyps2 ->
          exists mhyps1,
            Forall2 (meta_fact.wf wf_rel) mhyps1 mhyps2 /\
              meta_rule.interp p1.(program.rules) mr1 mf1 mhyps1.
        Proof.
          intros Hmr Hmf1 Hwfmr Hmf [Hpat Hset].
          eapply pattern_interp_wf_inv in Hpat as Hpat1; [|eassumption]. fwd.
          replace pat1 with mf1.(meta_fact.pattern) in *.
          2: { symmetry. eapply wf_fact_pattern_inj; [| eassumption | apply Hmf].
               eauto 6 using meta_rule.pattern_interp_concl_relname_in. }
          pose proof (meta_rule.pattern_interp_hyp_relname_in _ _ _ Hpat1p2) as Hrels.
          apply wf_meta_facts_of_patterns in Hpat1p1. fwd.
          rewrite Lists.List.Forall_map in Hrels.
          exists mhyps1. split; [assumption|]. split; [assumption|].
          intros nf1 Hmatch1.
          pose proof (Hset {| normal_fact.rel := meta_fact.rel mf2;
                             normal_fact.args := nf1.(normal_fact.args) |}) as Hset2.
          cbv [meta_fact.wf fact_pattern.wf fact_pattern.matches meta_fact.rel] in *. fwd.
          simpl in Hset2. rewrite Hmfp1, Hset2 by (split; congruence).
          split.
          - eapply one_step_derives_wf_bw_inj; [| |eassumption|].
            + simpl. congruence.
            + eapply Forall_impl; [eassumption|]. eauto 6.
            + cbv [normal_fact.wf]. simpl. split; congruence.
          - eapply one_step_derives_wf; [eassumption|]. cbv [normal_fact.wf]. simpl.
            split; congruence.
        Qed.

        Lemma interp_step_wf_inj f1 f2 hyps1 hyps2 :
          fact.wf wf_rel f1 f2 ->
          Forall2 (fact.wf wf_rel) hyps1 hyps2 ->
          program.interp_step p1 f1 hyps1 ->
          program.interp_step p2 f2 hyps2.
        Proof.
          intros Hf Hhyps H. invert H.
          - destruct f2 as [nf2|]; [|contradiction].
            apply Exists_exists in H0. fwd.
            eapply Forall2_In_l in H0p0; [|apply Hwf]. fwd.
            eapply rule_interp_wf in H0p1 as Hint2; [|eassumption]. fwd.
            replace nf2 with nf0.
            2: { eapply wf_normal_fact_fun; [|eassumption..].
                 eauto using rule.interp_concl_relname_in. }
            replace hyps2 with hyps0.
            2: { eapply Forall2_unique_r; [eassumption | eassumption |].
                 eauto using wf_fact_fun, functional_at_hyps. }
            constructor. apply Exists_exists. eauto.
          - destruct f2 as [|mf2]; [contradiction|].
            apply Forall2_wf_fact_meta in Hhyps. fwd.
            eapply Forall2_In_l in H0p0; [|apply Hwf]. fwd.
            constructor. apply Exists_exists. exists y. split; [eauto|].
            eapply meta_rule_interp_wf_inj; eauto.
        Qed.

        Lemma interp_step_wf_bw_inj f1 f2 hyps2 :
          In (fact.rel f1) l ->
          fact.wf wf_rel f1 f2 ->
          program.interp_step p2 f2 hyps2 ->
          exists hyps1, Forall2 (fact.wf wf_rel) hyps1 hyps2 /\ program.interp_step p1 f1 hyps1.
        Proof.
          intros Hf1 Hf H. invert H.
          - destruct f1 as [nf1|]; [|contradiction].
            apply Exists_exists in H0. fwd.
            eapply Forall2_In_r in H0p0; [|apply Hwf]. fwd.
            eapply rule_interp_wf_inv in H0p1 as Hint1; [|eassumption]. fwd.
            replace nf1 with nf0.
            2: { eapply wf_normal_fact_inj; [|eassumption..].
                 eauto 6 using rule.interp_concl_relname_in. }
            exists hyps1. split; [assumption|]. constructor. apply Exists_exists. eauto.
          - destruct f1 as [|mf1]; [contradiction|].
            apply Exists_exists in H0. fwd.
            eapply Forall2_In_r in H0p0; [|apply Hwf]. fwd.
            eapply meta_rule_interp_wf_bw_inj in H0p1; eauto. fwd.
            exists (map fact.meta mhyps1). split.
            + rewrite <- Forall2_map_l, <- Forall2_map_r. eapply Forall2_impl; [eassumption|].
              auto.
            + constructor. apply Exists_exists. eauto.
        Qed.

        Context (Q1 Q2 : fact -> Prop)
          (HQ : forall f1 f2, fact.wf wf_rel f1 f2 -> Q1 f1 <-> Q2 f2).

        Lemma interp_wf_inj f1 :
          program.interp p1 Q1 f1 ->
          forall f2, fact.wf wf_rel f1 f2 -> program.interp p2 Q2 f2.
        Proof.
          induction 1; intros f2 Hf2.
          - apply pftree.leaf. apply (HQ _ _ Hf2). assumption.
          - edestruct (Forall_exists_r_Forall2 (fact.wf wf_rel) l0) as [hyps2 Hhyps2].
            { eapply Forall_impl; [eapply program.interp_step_hyp_relname_in; eassumption|].
              simpl. eauto using wf_fact_exists. }
            rewrite Forall_forall in H1.
            eapply pftree.step; [eapply interp_step_wf_inj; eassumption|].
            apply Forall_forall. intros h2 Hh2.
            eapply Forall2_In_r in Hh2; [|eassumption]. fwd. eauto.
        Qed.

        Lemma interp_wf_bw_inj f2 :
          program.interp p2 Q2 f2 ->
          forall f1, fact.wf wf_rel f1 f2 -> In (fact.rel f1) l -> program.interp p1 Q1 f1.
        Proof.
          induction 1; intros f1 Hf1 Hl1.
          - apply pftree.leaf. apply (HQ _ _ Hf1). assumption.
          - rewrite Forall_forall in H1.
            edestruct interp_step_wf_bw_inj as (hyps1 & Hhyps1 & Hstep1); [eassumption..|].
            pose proof (program.interp_step_hyp_relname_in _ _ _ Hstep1) as Hrels.
            rewrite Forall_forall in Hrels.
            eapply pftree.step; [eassumption|].
            apply Forall_forall. intros h1 Hh1.
            eapply Forall2_In_l in Hh1 as Hh2; [|eassumption]. fwd. eauto 6.
        Qed.
      End Inj.
    End Program.

    Theorem interp_wf_iff p1 p2 Q1 Q2 f1 f2 :
      program.wf wf_rel p1 p2 ->
      Forall functional_at (program.all_rels p1) ->
      Forall inj_on_elt (program.concl_rels p1) ->
      program.meta_rules_valid p1 ->
      program.good_input_set p1 Q1 ->
      (forall g1 g2, fact.wf wf_rel g1 g2 -> Q1 g1 <-> Q2 g2) ->
      fact.wf wf_rel f1 f2 ->
      program.interp p1 Q1 f1 <-> program.interp p2 Q2 f2.
    Proof.
      intros. split; intros H'.
      - eapply interp_wf; eassumption.
      - eapply interp_wf_bw; eassumption.
    Qed.

    Theorem interp_wf_iff_inj p1 p2 Q1 Q2 f1 f2 :
      program.wf wf_rel p1 p2 ->
      Forall functional_at (program.all_rels p1) ->
      inj_on (fact.rel f1 :: program.all_rels p1) ->
      (forall g1 g2, fact.wf wf_rel g1 g2 -> Q1 g1 <-> Q2 g2) ->
      fact.wf wf_rel f1 f2 ->
      program.interp p1 Q1 f1 <-> program.interp p2 Q2 f2.
    Proof.
      intros. split; intros H'.
      - eapply interp_wf_inj with (l := fact.rel f1 :: program.all_rels p1); eauto using incl_tl, incl_refl.
      - eapply interp_wf_bw_inj with (l := fact.rel f1 :: program.all_rels p1); eauto using incl_tl, incl_refl.
        simpl. auto.
    Qed.

    Lemma meta_rules_valid_wf p1 p2 :
      program.wf wf_rel p1 p2 ->
      Forall functional_at (program.hyp_rels p1) ->
      inj_on (program.concl_rels p1) ->
      program.meta_rules_valid p1 ->
      program.meta_rules_valid p2.
    Proof.
      cbv [program.meta_rules_valid meta_rule.valid_for].
      intros Hwf Hfun Hinj Hvalid mr2 nr2 Hmr2 Hnr2 pat2 pats2 nf2 hyps2 Hpat2 Hint2 Hmatch2.
      eapply Forall2_In_r in Hmr2; [|apply Hwf]. eapply Forall2_In_r in Hnr2; [|apply Hwf]. fwd.
      eapply pattern_interp_wf_inv in Hpat2 as Hpat1; [|eassumption]. fwd.
      eapply rule_interp_wf_inv in Hint2 as Hint1; [|eassumption]. fwd.
      pose proof (rule.interp_hyp_relname_in _ _ _ Hint1p2) as Hrels.
      rewrite Forall_forall in Hfun.
      specialize (Hvalid _ _ ltac:(eauto) ltac:(eauto) _ _ _ _ Hpat1p2 Hint1p2).
      specialize' Hvalid.
      { cbv [fact_pattern.wf normal_fact.wf fact_pattern.matches] in *. fwd.
        rewrite Hmatch2p0 in Hpat1p0p0.
        split; [|congruence]. eapply Hinj; [| |eassumption..].
        - eauto using meta_rule.pattern_interp_concl_relname_in.
        - eauto using rule.interp_concl_relname_in. }
      rewrite Forall_forall in Hvalid, Hrels |- *. intros h2 Hh2.
      eapply Forall2_In_r in Hh2; [|eassumption]. fwd.
      eapply covered_by_pats_wf; [| eassumption | eassumption |]; eauto 6.
    Qed.
  End Wf.

  Section Map.
    Context {rel1 rel2} (f : rel1 -> rel2).

    Definition map_rel (x : rel1) (y : rel2) := f x = y.

    Definition fact_equiv f1 f2 := fact.map_rel f f1 = fact.map_rel f f2.

    Lemma wf_fact_map g1 g2 :
      fact.wf map_rel g1 g2 <-> fact.map_rel f g1 = g2.
    Proof.
      split; intros H.
      - destruct g1 as [nf1|mf1], g2 as [[r2 a2]|[[r2 a2] s2 p2]];
          cbv [fact.wf normal_fact.wf meta_fact.wf fact_pattern.wf map_rel] in H; fwd;
          try contradiction;
          cbv [fact.map_rel normal_fact.map_rel meta_fact.map_rel fact_pattern.map_rel]; simpl in *.
        + congruence.
        + f_equal. apply meta_fact.eq_ext; simpl; congruence.
      - subst. apply wf_fact_map_rel_r. reflexivity.
    Qed.

    Lemma map_fact_inj a b :
      (f (fact.rel a) = f (fact.rel b) -> fact.rel a = fact.rel b) ->
      fact.map_rel f a = fact.map_rel f b ->
      a = b.
    Proof.
      intros Hinj H. eapply (wf_fact_inj map_rel).
      - cbv [inj_at map_rel]. intros. apply Hinj. congruence.
      - apply wf_fact_map. exact H.
      - apply wf_fact_map. reflexivity.
    Qed.

    Lemma wf_clauses_map cs :
      Forall2 (clause.wf map_rel) cs (map (clause.map_rel f) cs).
    Proof.
      rewrite <- Forall2_map_r. apply Forall2_same, Forall_forall. cbv [clause.wf map_rel]. auto.
    Qed.

    Lemma wf_clause_patterns_map cs :
      Forall2 (clause_pattern.wf map_rel) cs (map (clause_pattern.map_rel f) cs).
    Proof.
      rewrite <- Forall2_map_r. apply Forall2_same, Forall_forall.
      cbv [clause_pattern.wf map_rel]. auto.
    Qed.

    Lemma wf_rule_map r :
      rule.wf map_rel r (rule.map_rel f r).
    Proof. destruct r; constructor; cbv [map_rel]; auto using wf_clauses_map. Qed.

    Lemma wf_meta_rule_map mr :
      meta_rule.wf map_rel mr (meta_rule.map_rel f mr).
    Proof. cbv [meta_rule.wf meta_rule.map_rel]. simpl. split; apply wf_clause_patterns_map. Qed.

    Lemma wf_program_map p :
      program.wf map_rel p (program.map_rel f p).
    Proof.
      cbv [program.wf program.map_rel]. simpl.
      split; rewrite <- Forall2_map_r; apply Forall2_same, Forall_forall;
        auto using wf_rule_map, wf_meta_rule_map.
    Qed.

    Lemma functional_at_map x :
      functional_at map_rel x.
    Proof. cbv [functional_at map_rel]. congruence. Qed.

    Lemma inj_on_map l :
      injective_on f l ->
      inj_on map_rel l.
    Proof. cbv [injective_on inj_on inj_at map_rel]. intros. subst. auto. Qed.

    Lemma concl_rels_map_rule_rels r :
      rule.concl_rels (rule.map_rel f r) = map f (rule.concl_rels r).
    Proof. destruct r; simpl; [rewrite !map_map|]; reflexivity. Qed.

    Lemma hyp_rels_map_rule_rels r :
      rule.hyp_rels (rule.map_rel f r) = map f (rule.hyp_rels r).
    Proof. destruct r; simpl; [rewrite !map_map|]; reflexivity. Qed.

    Lemma concl_rels_map_meta_rule_rels mr :
      meta_rule.concl_rels (meta_rule.map_rel f mr) = map f (meta_rule.concl_rels mr).
    Proof. cbv [meta_rule.concl_rels meta_rule.map_rel]. simpl. rewrite !map_map. reflexivity. Qed.

    Lemma hyp_rels_map_meta_rule_rels mr :
      meta_rule.hyp_rels (meta_rule.map_rel f mr) = map f (meta_rule.hyp_rels mr).
    Proof. cbv [meta_rule.hyp_rels meta_rule.map_rel]. simpl. rewrite !map_map. reflexivity. Qed.

    Lemma concl_rels_map_program p :
      program.concl_rels (program.map_rel f p) = map f (program.concl_rels p).
    Proof.
      cbv [program.concl_rels program.map_rel]. simpl.
      rewrite map_app, !map_flat_map, !flat_map_map. f_equal.
      - apply flat_map_ext. apply concl_rels_map_rule_rels.
      - apply flat_map_ext. apply concl_rels_map_meta_rule_rels.
    Qed.

    Lemma hyp_rels_map_program p :
      program.hyp_rels (program.map_rel f p) = map f (program.hyp_rels p).
    Proof.
      cbv [program.hyp_rels program.map_rel]. simpl.
      rewrite map_app, !map_flat_map, !flat_map_map. f_equal.
      - apply flat_map_ext. apply hyp_rels_map_rule_rels.
      - apply flat_map_ext. apply hyp_rels_map_meta_rule_rels.
    Qed.

    Lemma all_rels_map_program p :
      program.all_rels (program.map_rel f p) = map f (program.all_rels p).
    Proof.
      cbv [program.all_rels]. rewrite concl_rels_map_program, hyp_rels_map_program.
      rewrite map_app. reflexivity.
    Qed.

    Lemma map_input_set_iff Q g1 g2 :
      (forall f1 f2, fact_equiv f1 f2 -> Q f1 <-> Q f2) ->
      fact.wf map_rel g1 g2 ->
      Q g1 <-> (exists g, g2 = fact.map_rel f g /\ Q g).
    Proof.
      intros HQ Hg. apply wf_fact_map in Hg. subst. split; [eauto|].
      intros (g & Hg & HQg). apply (HQ g); [symmetry; exact Hg | exact HQg].
    Qed.

    Lemma interp_map_iff p Q fct :
      program.meta_rules_valid p ->
      program.good_input_set p Q ->
      (forall f1 f2, fact_equiv f1 f2 -> Q f1 <-> Q f2) ->
      Forall (inj_on_elt map_rel) (program.concl_rels p) ->
      program.interp p Q fct <->
        program.interp (program.map_rel f p)
          (fun f' => exists g, f' = fact.map_rel f g /\ Q g) (fact.map_rel f fct).
    Proof.
      intros. apply (interp_wf_iff map_rel); auto using wf_program_map, map_input_set_iff.
      - apply Forall_forall. auto using functional_at_map.
      - apply wf_fact_map. reflexivity.
    Qed.

    Lemma interp_map_iff_inj p Q fct :
      injective_on f (fact.rel fct :: program.all_rels p) ->
      (forall f1 f2, fact_equiv f1 f2 -> Q f1 <-> Q f2) ->
      program.interp p Q fct <->
        program.interp (program.map_rel f p)
          (fun f' => exists g, f' = fact.map_rel f g /\ Q g) (fact.map_rel f fct).
    Proof.
      intros. apply (interp_wf_iff_inj map_rel);
        auto using wf_program_map, inj_on_map, map_input_set_iff.
      - apply Forall_forall. auto using functional_at_map.
      - apply wf_fact_map. reflexivity.
    Qed.
  End Map.

  Section Combinators.
    Context {rel1 rel2 rel3 : Type}.

    Lemma wf_clause_flip (R : rel1 -> rel2 -> Prop) c1 c2 :
      clause.wf R c1 c2 ->
      clause.wf (fun y x => R x y) c2 c1.
    Proof. cbv [clause.wf]. intuition. Qed.

    Lemma wf_rule_flip (R : rel1 -> rel2 -> Prop) r1 r2 :
      rule.wf R r1 r2 ->
      rule.wf (fun y x => R x y) r2 r1.
    Proof.
      destruct 1; constructor; try assumption;
        rewrite <- Forall2_flip_iff; eapply Forall2_impl; eauto using wf_clause_flip.
    Qed.

    Lemma wf_clause_pattern_flip (R : rel1 -> rel2 -> Prop) c1 c2 :
      clause_pattern.wf R c1 c2 ->
      clause_pattern.wf (fun y x => R x y) c2 c1.
    Proof. cbv [clause_pattern.wf]. intuition. Qed.

    Lemma wf_meta_rule_flip (R : rel1 -> rel2 -> Prop) mr1 mr2 :
      meta_rule.wf R mr1 mr2 ->
      meta_rule.wf (fun y x => R x y) mr2 mr1.
    Proof.
      cbv [meta_rule.wf]. intros. fwd.
      split; rewrite <- Forall2_flip_iff; eapply Forall2_impl; eauto using wf_clause_pattern_flip.
    Qed.

    Lemma wf_program_flip (R : rel1 -> rel2 -> Prop) p1 p2 :
      program.wf R p1 p2 ->
      program.wf (fun y x => R x y) p2 p1.
    Proof.
      cbv [program.wf]. intros. fwd.
      split; rewrite <- Forall2_flip_iff; eapply Forall2_impl;
        eauto using wf_rule_flip, wf_meta_rule_flip.
    Qed.

    Lemma wf_clause_comp (R : rel1 -> rel2 -> Prop) (S : rel2 -> rel3 -> Prop) c1 c2 c3 :
      clause.wf R c1 c2 ->
      clause.wf S c2 c3 ->
      clause.wf (fun x z => exists y, R x y /\ S y z) c1 c3.
    Proof. cbv [clause.wf]. intros. fwd. split; [eauto | congruence]. Qed.

    Lemma wf_clauses_comp (R : rel1 -> rel2 -> Prop) (S : rel2 -> rel3 -> Prop) cs1 cs2 cs3 :
      Forall2 (clause.wf R) cs1 cs2 ->
      Forall2 (clause.wf S) cs2 cs3 ->
      Forall2 (clause.wf (fun x z => exists y, R x y /\ S y z)) cs1 cs3.
    Proof.
      intros. eapply Forall2_impl; [eapply Forall2_comp; eassumption|].
      intros ? ? Hab. cbv beta in Hab. fwd. eauto using wf_clause_comp.
    Qed.

    Lemma wf_rule_comp (R : rel1 -> rel2 -> Prop) (S : rel2 -> rel3 -> Prop) r1 r2 r3 :
      rule.wf R r1 r2 ->
      rule.wf S r2 r3 ->
      rule.wf (fun x z => exists y, R x y /\ S y z) r1 r3.
    Proof. destruct 1; invert 1; constructor; eauto using wf_clauses_comp. Qed.

    Lemma wf_clause_pattern_comp (R : rel1 -> rel2 -> Prop) (S : rel2 -> rel3 -> Prop) c1 c2 c3 :
      clause_pattern.wf R c1 c2 ->
      clause_pattern.wf S c2 c3 ->
      clause_pattern.wf (fun x z => exists y, R x y /\ S y z) c1 c3.
    Proof. cbv [clause_pattern.wf]. intros. fwd. split; [eauto | congruence]. Qed.

    Lemma wf_meta_rule_comp (R : rel1 -> rel2 -> Prop) (S : rel2 -> rel3 -> Prop) mr1 mr2 mr3 :
      meta_rule.wf R mr1 mr2 ->
      meta_rule.wf S mr2 mr3 ->
      meta_rule.wf (fun x z => exists y, R x y /\ S y z) mr1 mr3.
    Proof.
      cbv [meta_rule.wf]. intros. fwd.
      split; (eapply Forall2_impl; [eapply Forall2_comp; eassumption|]);
        intros ? ? Hab; cbv beta in Hab; fwd; eauto using wf_clause_pattern_comp.
    Qed.

    Lemma wf_program_comp (R : rel1 -> rel2 -> Prop) (S : rel2 -> rel3 -> Prop) p1 p2 p3 :
      program.wf R p1 p2 ->
      program.wf S p2 p3 ->
      program.wf (fun x z => exists y, R x y /\ S y z) p1 p3.
    Proof.
      cbv [program.wf]. intros. fwd.
      split; (eapply Forall2_impl; [eapply Forall2_comp; eassumption|]);
        intros ? ? Hab; cbv beta in Hab; fwd; eauto using wf_rule_comp, wf_meta_rule_comp.
    Qed.
  End Combinators.
End RelMap.
