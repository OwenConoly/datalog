From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List Datatypes.Option Eqb.
From Datalog Require Import Eqb.

From Datalog Require Import Datalog Map Tactics List.

Import ListNotations.

Section __.
  Context `{params : datalog_params}.
  Context {var_eqb : Eqb exprvar} {var_eqb_ok : Eqb_ok var_eqb}.

  (*A short answer to "why is completeness hard":
    R(x * x, x) :- Q(x).
    R(-1, _) :-.
    In principle, the expression language could include a function f(x, y) := if [the xth Turing machine terminates in y steps] then 1 else 0.  Then completeness is even harder:
    R(f(x, y), x) :- Q(x, y).
    R(0, 42) :-.
    is valid iff 42nd Turing machine never halts.
   *)

  Context {fn_eqb : Eqb fn} {fn_eqb_ok : Eqb_ok fn_eqb}.
  Context {rel_eqb : Eqb rel} {rel_eqb_ok : Eqb_ok rel_eqb}.
  Context (fn_inj : fn -> bool).

  #[global] Instance expr_eqb : Eqb expr :=
    fix expr_eqb e1 e2 :=
      match e1, e2 with
      | Datalog.expr.var v1, Datalog.expr.var v2 => var_eqb v1 v2
      | Datalog.expr.app f1 args1, Datalog.expr.app f2 args2 =>
          fn_eqb f1 f2 && list_eqb (aeqb := expr_eqb) args1 args2
      | _, _ => false
      end.

  #[global] Instance expr_eqb_ok : Eqb_ok expr_eqb.
  Proof.
    intros e1. induction e1; intros [v0|f0 args0]; cbv [eqb] in *; simpl; try congruence.
    - destr (var_eqb v v0); congruence.
    - pose proof (list_eqb_ok_strong args H args0) as Hl.
      Tactics.destruct_one_match; fwd; try congruence.
      destruct E as [|E]; try congruence. rewrite E in *. congruence.
  Qed.

  (*Note: this can be weakened; we only need injectivity on length-n lists (for each n)*)
  Context (fn_inj_spec :
            forall f,
              fn_inj f = true ->
              partial_injective (interp_fun f)).

  (*var * var may as well be separate namespaces, e.g. mvar * nvar*)
  Fixpoint expr_compat (e1 e2 : expr) : option (list (exprvar * exprvar)) :=
    match e1, e2 with
    | Datalog.expr.var v1, Datalog.expr.var v2 => Some [(v1, v2)]
    | Datalog.expr.app f1 args1, Datalog.expr.app f2 args2 =>
        if fn_eqb f1 f2 &&
             fn_inj f1 &&
             Nat.eqb (List.length args1) (List.length args2) then
          option_map (@concat _) (option_all (map2 expr_compat args1 args2))
        else
          None
    | _, _ => None
    end.

  Lemma expr_compat_sound e1 e2 l ctx1 ctx2 val :
    expr_compat e1 e2 = Some l ->
    expr.interp ctx1 e1 val ->
    expr.interp ctx2 e2 val ->
    Forall (fun '(v1, v2) =>
              exists val', map.get ctx1 v1 = Some val' /\ map.get ctx2 v2 = Some val') l.
  Proof.
    revert e2 l ctx1 ctx2 val.
    induction e1; intros e2 l ctx1 ctx2 val Hcomp H1 H2.
    - destruct e2; simpl in Hcomp; try discriminate.
      repeat invert_stuff.
      eauto.
    - destruct e2; simpl in Hcomp; try discriminate.
      repeat invert_stuff.
      apply eq_Forall2_eq in Hcompp0. apply Forall2_map_r in Hcompp0.
      eapply fn_inj_spec in Ep0p1. cbv [partial_injective] in Ep0p1.
      match goal with
      | H1: interp_fun _ _ = Some _, H2: interp_fun _ _ = Some _ |- _ =>
          specialize (Ep0p1 _ _ _ H1 H2)
      end.
      subst.
      apply Forall_concat.
      eapply Forall_impl.
      1: { eapply Forall2_forget_l. eassumption. }
      simpl. intros vs Hvs. fwd.
      rewrite map2_eq_map_combine in Hvsp0. apply in_map_iff in Hvsp0.
      fwd.
      match goal with
      | H1: Forall2 (expr.interp ctx1) _ _, H2: Forall2 (expr.interp ctx2) _ _ |- _ =>
          eapply Forall2_same_r in H2; [|exact H1];
          rename H2 into Hargs
      end.
      apply Forall2_combine in Hargs.
      rewrite Forall_forall in Hargs.
      specialize (Hargs _ ltac:(eassumption)). simpl in Hargs. fwd.
      rewrite Forall_forall in H. eauto using in_combine_l.
  Qed.

  Definition clause_compat (cp : clause_pattern) (nc : clause) : option (list (exprvar * exprvar)) :=
    option_map (@concat _)
      (option_all (map2 (fun ep e =>
                           match ep with
                           | expr_pattern.exactly me => expr_compat me e
                           | expr_pattern.any => Some []
                           end)
                     cp.(clause_pattern.args)
                     nc.(clause.args))).

  Lemma clause_compat_sound cp nc l ctx1 ctx2 fp nf :
    clause_compat cp nc = Some l ->
    clause_pattern.interp ctx1 cp fp ->
    clause.interp ctx2 nc nf ->
    Forall2 value_pattern.matches fp.(fact_pattern.args) nf.(normal_fact.args) ->
    Forall (fun '(v1, v2) => exists val', map.get ctx1 v1 = Some val' /\ map.get ctx2 v2 = Some val') l.
  Proof.
    intros Hcomp Hcp Hnc Hmatch.
    cbv [clause_compat] in Hcomp. cbv [clause_pattern.interp] in Hcp.
    cbv [clause.interp] in Hnc. fwd.
    apply option_map_Some in Hcomp. fwd. apply option_all_Forall2 in Hcompp0.
    apply Forall_concat.
    eapply Forall_impl.
    1: { eapply Forall2_forget_l. eassumption. }
    clear Hcompp0. simpl. intros vs Hvs. fwd.
    apply Forall2_flip in Hmatch.
    eapply Forall2_same_r in Hcpp1; [|exact Hmatch]. clear Hmatch.
    apply Forall2_flip in Hcpp1. eapply Forall2_same_r in Hcpp1; [|exact Hncp1].
    rewrite map2_eq_map_combine in Hvsp0.
    apply Forall2_flip in Hcpp1.
    apply Forall2_combine in Hcpp1. rewrite Forall_forall in Hcpp1.
    apply in_map_iff in Hvsp0. destruct Hvsp0 as [[ep e] Hvsp0]. fwd.
    apply Hcpp1 in Hvsp0p1. fwd.
    destruct ep; fwd.
    - invert Hvsp0p1p2p2. simpl in Hvsp0p1p2p1. subst.
      eapply expr_compat_sound; eauto.
    - constructor.
  Qed.

  Fixpoint expr_matches (equalities : list (exprvar * exprvar)) (e1 e2 : expr) :=
    match e1, e2 with
    | Datalog.expr.var v1, Datalog.expr.var v2 =>
        inb (v1, v2) equalities
    | Datalog.expr.app f1 args1, Datalog.expr.app f2 args2 =>
        fn_eqb f1 f2 &&
          Nat.eqb (List.length args1) (List.length args2) &&
          forallb (eqb true) (map2 (expr_matches equalities) args1 args2)
    | _, _ => false
    end.

  Lemma expr_matches_sound equalities e1 e2 ctx1 ctx2 val :
    expr_matches equalities e1 e2 = true ->
    Forall (fun '(x, y) => map.get ctx1 x = map.get ctx2 y) equalities ->
    expr.interp ctx1 e1 val ->
    expr.interp ctx2 e2 val.
  Proof.
    revert e2 ctx1 ctx2 val.
    induction e1; intros e2 ctx1 ctx2 val Hmatch Heq H1.
    - destruct e2; simpl in Hmatch; try discriminate.
      repeat invert_stuff.
      rewrite Forall_forall in Heq. apply Heq in Hmatch.
      rewrite Hmatch in *. auto.
    - destruct e2; simpl in Hmatch; try discriminate.
      repeat invert_stuff.
      rewrite map2_eq_map_combine in Hmatchp1.
      rewrite Lists.List.Forall_map in Hmatchp1.
      apply Forall_combine_Forall2 in Hmatchp1.
      2: { assumption. }
      econstructor; [|eassumption].
      eapply Forall2_impl.
      1: { eapply Forall2_same_r; apply Forall2_flip; eassumption. }
      simpl.
      intros e e' He. fwd.
      rewrite Forall_forall in H. eapply H; eauto.
  Qed.

  Definition clause_matches (equalities : list (exprvar * exprvar)) (cp : clause_pattern) (nc : clause) :=
    rel_eqb cp.(clause_pattern.rel) nc.(clause.rel) &&
      (length cp.(clause_pattern.args) =? length nc.(clause.args))%nat &&
      forallb
        (eqb true)
        (map2 (fun ep e =>
                 match ep with
                 | expr_pattern.exactly me => expr_matches equalities me e
                 | expr_pattern.any => true
                 end)
           cp.(clause_pattern.args)
           nc.(clause.args)).

  Lemma clause_matches_sound equalities cp nc ctx1 ctx2 fp nf :
    clause_matches equalities cp nc = true ->
    Forall (fun '(x, y) => map.get ctx1 x = map.get ctx2 y) equalities ->
    clause_pattern.interp ctx1 cp fp ->
    clause.interp ctx2 nc nf ->
    fact_pattern.matches fp nf.
  Proof.
    intros Hmatch Heq Hcp Hnc.
    cbv [clause_matches] in Hmatch. cbv [clause_pattern.interp] in Hcp.
    cbv [clause.interp] in Hnc. cbv [fact_pattern.matches]. fwd.
    split; [congruence|].
    rewrite map2_eq_map_combine in Hmatchp1.
    rewrite Lists.List.Forall_map in Hmatchp1.
    apply Forall_combine_Forall2 in Hmatchp1; [|assumption].
    apply Forall2_flip in Hcpp1.
    apply Forall2_flip in Hmatchp1.
    eapply Forall2_same_r in Hcpp1; [|exact Hmatchp1].
    apply Forall2_flip in Hncp1, Hcpp1.
    eapply Forall2_same_r in Hcpp1; [|exact Hncp1].
    apply Forall2_flip in Hcpp1.
    eapply Forall2_impl; [eassumption|].
    simpl. intros vp val H. fwd. symmetry in Hp2p1.
    destruct z0; fwd.
    - invert Hp2p2. simpl. eapply expr.interp_det; [|eassumption].
      eapply expr_matches_sound; eauto.
    - invert Hp2p2. constructor.
  Qed.

  Definition check_meta_rule_against_impl (mconcls mhyps : list clause_pattern)
    (nconcls nhyps : list clause) : bool :=
    forallb (fun mconcl =>
               let nconcl_matches :=
                 filter (fun nconcl => rel_eqb mconcl.(clause_pattern.rel) nconcl.(clause.rel))
                   nconcls in
               forallb (fun nconcl =>
                          match clause_compat mconcl nconcl with
                          | Some equalities =>
                              forallb (fun nhyp =>
                                         existsb (fun mhyp => clause_matches equalities mhyp nhyp)
                                           mhyps)
                                nhyps
                          | None => false (*we already know they have the same relation, so they'd better be compatible*)
                          end)
                 nconcl_matches)
      mconcls.

  Lemma check_meta_rule_against_impl_sound mr nconcls nhyps pat pats nf hyps :
    check_meta_rule_against_impl mr.(meta_rule.concls) mr.(meta_rule.hyps) nconcls nhyps = true ->
    meta_rule.pattern_interp mr pat pats ->
    rule.interp (rule.impl nconcls nhyps) nf hyps ->
    fact_pattern.matches pat nf ->
    Forall (fact.covered_by_pats pats) hyps.
  Proof.
    intros Hcheck Hpat Hn Hmatch.
    cbv [meta_rule.pattern_interp] in Hpat. fwd.
    invert Hn. fwd.
    pose proof Hmatch as Hrel. cbv [fact_pattern.matches] in Hrel. fwd.
    rewrite Forall_forall in Hcheck. specialize (Hcheck _ Hpatp0p0).
    rewrite forallb_forall in Hcheck.
    specialize (Hcheck x0).
    especialize Hcheck.
    { apply filter_In. split; [assumption|].
      destr (rel_eqb (clause_pattern.rel x) (clause.rel x0)); [reflexivity|].
      cbv [clause_pattern.interp clause.interp] in Hpatp0p1, H1p1. fwd. congruence. }
    destruct (clause_compat x x0) as [equalities|] eqn:E; [|discriminate].
    rewrite forallb_forall in Hcheck.
    assert (Heqs: Forall (fun '(v1, v2) => map.get ctx v1 = map.get ctx0 v2) equalities).
    { eapply Forall_impl.
      1: { eapply clause_compat_sound; try eassumption. }
      simpl. intros [? ?] ?. fwd. congruence. }
    rewrite Lists.List.Forall_map.
    eapply Forall_impl.
    1: { eapply Forall2_forget_l. exact H4. }
    simpl. intros h1 Hh1. fwd.
    specialize (Hcheck _ Hh1p0). apply existsb_exists in Hcheck.
    destruct Hcheck as [mhyp [Hmhyp Hcm]].
    apply Forall2_forget_r in Hpatp1. rewrite Forall_forall in Hpatp1.
    destruct (Hpatp1 _ Hmhyp) as [pat' [Hpat' Hip']].
    cbv [fact.covered_by_pats]. apply Exists_exists.
    exists pat'. split; [assumption|]. simpl.
    eapply clause_matches_sound; eassumption.
  Qed.

  Definition check_meta_rule_against_agg (mconcls mhyps : list clause_pattern)
    (concl_rel hyp_rel : rel) : bool :=
    forallb (fun mconcl =>
               negb (rel_eqb mconcl.(clause_pattern.rel) concl_rel) ||
                 match mconcl.(clause_pattern.args) with
                 | _ :: stuff =>
                     existsb
                       (fun mhyp =>
                          rel_eqb mhyp.(clause_pattern.rel) hyp_rel &&
                            match mhyp.(clause_pattern.args) with
                            | expr_pattern.any :: expr_pattern.any :: stuff' =>
                                match option_all (map expr_pattern.expr_of stuff),
                                  option_all (map expr_pattern.expr_of stuff') with
                                | Some es, Some es' => eqb es es'
                                | _, _ => false
                                end
                            | _ => false
                            end)
                       mhyps
                 | [] => false
                 end)
      mconcls.

  Lemma option_all_expr_of_pattern ps es :
    option_all (map expr_pattern.expr_of ps) = Some es ->
    ps = map expr_pattern.exactly es.
  Proof.
    revert es. induction ps as [|p ps]; simpl; intros es H.
    - invert H. reflexivity.
    - destruct p; simpl in H; [|discriminate].
      destruct (option_all _) eqn:E; invert H. simpl. f_equal. auto.
  Qed.

  Lemma exactly_interp_forall2 ctx es vps :
    Forall2 (expr_pattern.interp ctx) (map expr_pattern.exactly es) vps ->
    exists vs, vps = map value_pattern.exactly vs /\ Forall2 (expr.interp ctx) es vs.
  Proof.
    intros H. rewrite <- Forall2_map_l in H. induction H; fwd.
    - now exists [].
    - invert H. exists (v :: vs). simpl. eauto using Forall2_cons.
  Qed.

  Lemma matches_map_exactly_eq (vs args : list value) :
    Forall2 value_pattern.matches (map value_pattern.exactly vs) args ->
    vs = args.
  Proof.
    intros H. rewrite <- Forall2_map_l in H. induction H; simpl in *; congruence.
  Qed.

  Lemma check_meta_rule_against_agg_sound mr concl_rel agg hyp_rel pat pats nf hyps :
    check_meta_rule_against_agg mr.(meta_rule.concls) mr.(meta_rule.hyps) concl_rel hyp_rel = true ->
    meta_rule.pattern_interp mr pat pats ->
    rule.interp (rule.agg concl_rel agg hyp_rel) nf hyps ->
    fact_pattern.matches pat nf ->
    Forall (fact.covered_by_pats pats) hyps.
  Proof.
    intros Hcheck Hpat Hn Hmatch.
    cbv [meta_rule.pattern_interp] in Hpat. fwd.
    invert Hn.
    pose proof Hmatch as Hrel. cbv [fact_pattern.matches] in Hrel. fwd. simpl in *.
    rewrite Forall_forall in Hcheck. specialize (Hcheck _ Hpatp0p0).
    cbv [clause_pattern.interp] in Hpatp0p1. fwd.
    destr (rel_eqb (clause_pattern.rel x) concl_rel); simpl in Hcheck; [|congruence].
    invert_list_stuff.
    destruct Hcheck as [Hcheck|Hcheck]; [congruence|].
    destruct (clause_pattern.args x) as [|ep0 stuff]; [discriminate|].
    apply existsb_exists in Hcheck. destruct Hcheck as [mhyp [Hmhyp Hc]].
    apply andb_prop in Hc. destruct Hc as [Hcrel Hc].
    destr (rel_eqb (clause_pattern.rel mhyp) hyp_rel); [|discriminate].
    destruct (clause_pattern.args mhyp) as [|ep1 rest] eqn:Em; [discriminate|].
    destruct ep1; [discriminate|].
    destruct rest as [|ep2 stuff']; [discriminate|].
    destruct ep2; [discriminate|].
    destruct (option_all (map expr_pattern.expr_of stuff)) as [es|] eqn:Es; [|discriminate].
    destruct (option_all (map expr_pattern.expr_of stuff')) as [es'|] eqn:Es'; [|discriminate].
    assert (es' = es) as ->.
    { pose proof (eqb_spec es es') as He. rewrite Hc in He. congruence. }
    apply option_all_expr_of_pattern in Es, Es'. subst stuff stuff'.
    invert Hpatp0p1p1.
    rewrite <- H in H5. invert H5.
    apply exactly_interp_forall2 in H7. fwd.
    apply matches_map_exactly_eq in H3. subst vs.
    apply Forall2_forget_r in Hpatp1. rewrite Forall_forall in Hpatp1.
    destruct (Hpatp1 _ Hmhyp) as [pat' [Hpat' Hip']].
    cbv [clause_pattern.interp] in Hip'. rewrite Em in Hip'.
    destruct Hip' as [Hrel' Hargs'].
    invert Hargs'. invert H5. invert H7. invert H5.
    apply exactly_interp_forall2 in H9. fwd.
    assert (vs = args) as ->.
    { eapply Forall2_unique_r; eauto using expr.interp_det. }
    constructor.
    { cbv [fact.covered_by_pats]. apply Exists_exists. exists pat'. split; [assumption|].
      simpl. destruct pat'. simpl in *. f_equal; congruence. }
    apply Forall_forall. intros f' Hf'. apply in_map_iff in Hf'.
    destruct Hf' as [[i x_i] [<- _]].
    cbv [fact.covered_by_pats]. apply Exists_exists. exists pat'. split; [assumption|].
    simpl. cbv [fact_pattern.matches]. simpl. split; [congruence|].
    rewrite <- H3. constructor; [exact I|]. constructor; [exact I|].
    apply value_pattern.matches_map_exactly.
  Qed.

  Definition check_meta_rule_against_rule (mr : meta_rule) (nr : rule) : bool :=
    match nr with
    | rule.impl nconcls nhyps =>
        check_meta_rule_against_impl mr.(meta_rule.concls) mr.(meta_rule.hyps) nconcls nhyps
    | rule.agg concl_rel _ hyp_rel =>
        check_meta_rule_against_agg mr.(meta_rule.concls) mr.(meta_rule.hyps) concl_rel hyp_rel
    end.

  Lemma check_meta_rule_against_rule_sound mr nr :
    check_meta_rule_against_rule mr nr = true ->
    meta_rule.valid_for mr nr.
  Proof.
    cbv [meta_rule.valid_for]. intros H pat pats nf hyps Hpat Hn Hmatch.
    destruct nr; simpl in H.
    - eapply check_meta_rule_against_impl_sound; eassumption.
    - eapply check_meta_rule_against_agg_sound; eassumption.
  Qed.

  Definition check_meta_rules_valid (p : program) : bool :=
    forallb (fun '(mr, nr) => check_meta_rule_against_rule mr nr)
      (list_prod p.(program.meta_rules) p.(program.rules)).

  Lemma check_meta_rules_valid_sound p :
    check_meta_rules_valid p = true ->
    program.meta_rules_valid p.
  Proof.
    cbv [check_meta_rules_valid program.meta_rules_valid]. intros H mr nr Hmr Hnr.
    apply check_meta_rule_against_rule_sound.
    rewrite forallb_forall in H. apply (H (_, _)).
    apply in_prod_iff. auto.
  Qed.

End __.
