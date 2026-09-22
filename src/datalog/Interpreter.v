From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import Permutation.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List Datatypes.Option Eqb.
From Datalog Require Import Eqb Default Decidable Monadish Pftree.

From Datalog Require Import Datalog Map Tactics Fp List.
From GraphSearch Require Import Dag.

Import ListNotations.
Local Open Scope option_monad_scope.

Section __.
  Context `{params : datalog_params}.
  Context {rel_eqb : Eqb rel} {rel_eqb_ok : Eqb_ok rel_eqb}.
  Context {var_eqb : Eqb exprvar} {var_eqb_ok : Eqb_ok var_eqb}.

  (* Print list_prod. (*why is this not defined in terms of flat_map?*) *)
  Definition edges_of_rule (r : rule) :=
    list_prod (rule.concl_rels r) (rule.hyp_rels r).

  Definition edges_of_meta_rule (mr : meta_rule) :=
    list_prod (meta_rule.concl_rels mr) (meta_rule.hyp_rels mr).

  Definition rel_graph (p : program) :=
    flat_map edges_of_rule p.(program.rules) ++
      flat_map edges_of_meta_rule p.(program.meta_rules).

  (* Lemma diff_rels_Forall_r p1 p2 : *)
  (*   Forall (fun r2 => *)
  (*             forall r1 c1 c2, *)
  (*               In r1 p1 -> *)
  (*               In c1 r1.(rule_concls) -> *)
  (*               In c2 r2.(rule_concls) -> *)
  (*               c1.(fact_R) <> c2.(fact_R)) p2 -> *)
  (*   diff_rels p1 p2. *)
  (* Proof. *)
  (*   intros H. rewrite Forall_forall in H. cbv [diff_rels]. eauto. *)
  (* Qed. *)

  Lemma edges_of_rule_spec r nf hyps :
    rule.interp r nf hyps ->
    Forall (fun hyp => In (nf.(normal_fact.rel), fact.rel hyp) (edges_of_rule r)) hyps.
  Proof.
    intros H. pose proof H as H'.
    apply rule.interp_concl_relname_in in H. apply rule.interp_hyp_relname_in in H'.
    eapply Forall_impl; [eassumption|]. simpl. intros.
    cbv [edges_of_rule]. apply in_prod_iff. auto.
  Qed.

  Lemma edges_of_meta_rule_spec prog mr mf mhyps :
    meta_rule.interp prog mr mf mhyps ->
    Forall (fun mhyp => In (meta_fact.rel mf, meta_fact.rel mhyp) (edges_of_meta_rule mr))
      mhyps.
  Proof.
    intros H. pose proof H as H'.
    apply meta_rule.interp_concl_relname_in in H.
    apply meta_rule.interp_hyp_relname_in in H'.
    eapply Forall_impl; [eassumption|]. simpl. intros.
    cbv [edges_of_meta_rule]. apply in_prod_iff. auto.
  Qed.

  Lemma rel_graph_spec p f hyps :
    program.interp_step p f hyps ->
    Forall (fun hyp => In (fact.rel f, fact.rel hyp) (rel_graph p)) hyps.
  Proof.
    cbv [rel_graph]. invert 1; fwd.
    - apply edges_of_rule_spec in H0p1.
      eapply Forall_impl; [eassumption|]. simpl. intros.
      apply in_or_app. left. apply in_flat_map. eauto.
    - apply edges_of_meta_rule_spec in H0p1. apply List.Forall_map.
      eapply Forall_impl; [eassumption|]. simpl. intros.
      apply in_or_app. right. apply in_flat_map. eauto.
  Qed.

  Fixpoint subst_in_expr (ctx : context) e : option value :=
    match e with
    | expr.var v => map.get ctx v
    | expr.app f args => option_coalesce (option_map (interp_fun f) (option_all (map (subst_in_expr ctx) args)))
    end.

  Lemma subst_in_expr_sound ctx e v :
    subst_in_expr ctx e = Some v ->
    expr.interp ctx e v.
  Proof.
    revert v. induction e; simpl; intros; eauto.
    apply option_coalesce_Some, option_map_Some in H0. fwd.
    apply option_all_Forall2 in H0p0. econstructor; eauto.
    rewrite <- Forall2_map_l in H0p0. eapply Forall2_impl_strong; [eassumption|].
    simpl. intros. rewrite Forall_forall in H. eauto.
  Qed.

  Lemma subst_in_expr_complete ctx e v :
    expr.interp ctx e v ->
    subst_in_expr ctx e = Some v.
  Proof.
    revert v. induction e; invert 1; simpl; eauto.
    erewrite Forall2_option_all.
    2: { rewrite <- Forall2_map_l. eapply Forall2_impl_strong; [eassumption|].
         rewrite Forall_forall in H. eauto. }
    simpl. rewrite H5. reflexivity.
  Qed.

  Definition subst_in_clause ctx (c : clause) : option normal_fact :=
    option_map (fun args => {| normal_fact.rel := c.(clause.rel);
                              normal_fact.args := args |})
      (option_all (map (subst_in_expr ctx) c.(clause.args))).

  Lemma subst_in_clause_sound ctx c nf :
    subst_in_clause ctx c = Some nf ->
    clause.interp ctx c nf.
  Proof.
    cbv [subst_in_clause]. intros H. apply option_map_Some in H.
    fwd. apply option_all_Forall2 in Hp0. cbv [clause.interp].
    rewrite <- Forall2_map_l in Hp0. simpl.
    eauto using Forall2_impl, subst_in_expr_sound.
  Qed.

  Lemma subst_in_clause_complete ctx c nf :
    clause.interp ctx c nf ->
    subst_in_clause ctx c = Some nf.
  Proof.
    intros. repeat invert_stuff. cbv [subst_in_clause].
    erewrite Forall2_option_all.
    2: { rewrite <- Forall2_map_l.
         eauto using Forall2_impl, subst_in_expr_complete. }
    simpl. simp. reflexivity.
  Qed.

  Definition subst_in_expr_pattern ctx (ep : expr_pattern) : option value_pattern :=
    match ep with
    | expr_pattern.exactly e => option_map value_pattern.exactly (subst_in_expr ctx e)
    | expr_pattern.any => Some value_pattern.any
    end.

  Lemma subst_in_expr_pattern_sound ctx ep vp :
    subst_in_expr_pattern ctx ep = Some vp ->
    expr_pattern.interp ctx ep vp.
  Proof.
    destruct ep; simpl; intros H; fwd.
    - apply option_map_Some in H. fwd. eauto using subst_in_expr_sound, expr_pattern.interp.
    - constructor.
  Qed.

  Lemma subst_in_expr_pattern_complete ctx ep vp :
    expr_pattern.interp ctx ep vp ->
    subst_in_expr_pattern ctx ep = Some vp.
  Proof.
    invert 1; simpl; [|reflexivity].
    erewrite subst_in_expr_complete by eassumption. reflexivity.
  Qed.

  Definition subst_in_clause_pattern ctx (cp : clause_pattern) : option fact_pattern :=
    option_map (fun args => {| fact_pattern.rel := cp.(clause_pattern.rel);
                              fact_pattern.args := args |})
      (option_all (map (subst_in_expr_pattern ctx) cp.(clause_pattern.args))).

  Lemma subst_in_clause_pattern_sound ctx cp fp :
    subst_in_clause_pattern ctx cp = Some fp ->
    clause_pattern.interp ctx cp fp.
  Proof.
    cbv [subst_in_clause_pattern]. intros H. apply option_map_Some in H.
    fwd. apply option_all_Forall2 in Hp0. cbv [clause_pattern.interp].
    rewrite <- Forall2_map_l in Hp0. simpl.
    eauto using Forall2_impl, subst_in_expr_pattern_sound.
  Qed.

  Lemma subst_in_clause_pattern_complete ctx cp fp :
    clause_pattern.interp ctx cp fp ->
    subst_in_clause_pattern ctx cp = Some fp.
  Proof.
    cbv [clause_pattern.interp]. intros. fwd. cbv [subst_in_clause_pattern].
    erewrite Forall2_option_all.
    2: { rewrite <- Forall2_map_l.
         eauto using Forall2_impl, subst_in_expr_pattern_complete. }
    simpl. simp. reflexivity.
  Qed.

  Definition context_of_args (args : list expr) (args' : list value) :=
    concat (zip (fun arg arg' =>
                   match arg with
                   | expr.var v => [(v, arg')]
                   | _ => []
                   end) args args').

  Definition context_of_clause (c : clause) (f : normal_fact) :=
    context_of_args c.(clause.args) f.(normal_fact.args).

  Definition context_of_hyps (hyps : list clause) (hyps' : list normal_fact) :=
    concat (zip context_of_clause hyps hyps').

  Lemma bare_in_context_args ctx x args args' :
    In (expr.var x) args ->
    Forall2 (expr.interp ctx) args args' ->
    exists v, In (x, v) (context_of_args args args').
  Proof.
    intros H1 H2. cbv [context_of_args]. apply Forall2_forget_r_strong in H2.
    rewrite Forall_forall in H2. specialize (H2 _ H1). fwd.
    exists y. cbv [zip]. rewrite in_concat. eexists. rewrite in_map_iff. split.
    { eexists. split; [|eassumption]. reflexivity. }
    simpl. auto.
  Qed.

  Lemma bare_in_context_clause ctx x c f :
    In (expr.var x) c.(clause.args) ->
    clause.interp ctx c f ->
    exists v, In (x, v) (context_of_clause c f).
  Proof.
    intros H1 H2. cbv [clause.interp] in H2. fwd. eapply bare_in_context_args; eassumption.
  Qed.

  Lemma bare_in_context_hyps ctx x hyps hyps' :
    In (expr.var x) (flat_map clause.args hyps) ->
    Forall2 (clause.interp ctx) hyps hyps' ->
    exists v, In (x, v) (context_of_hyps hyps hyps').
  Proof.
    intros H1 H2. apply in_flat_map in H1. fwd. cbv [context_of_hyps].
    apply Forall2_forget_r_strong in H2. rewrite Forall_forall in H2.
    specialize (H2 _ H1p0). fwd. eapply bare_in_context_clause in H2p1; eauto. fwd.
    eexists. rewrite in_concat. cbv [zip]. eexists. rewrite in_map_iff. split.
    { eexists. split; [|eassumption]. reflexivity. }
    eassumption.
  Qed.

  Lemma interp_args_context_right ctx args args' :
    Forall2 (expr.interp ctx) args args' ->
    Forall (fun '(x, v) => map.get ctx x = Some v) (context_of_args args args').
  Proof.
    intros H. apply Forall2_combine in H. rewrite Forall_forall in *.
    intros [x v] Hx. apply in_concat in Hx. fwd.
    cbv [zip] in Hxp0. apply in_map_iff in Hxp0. fwd. apply H in Hxp0p1.
    do 2 (destruct_one_match_hyp; simpl in Hxp1; try contradiction).
    destruct Hxp1; try contradiction. invert H0. invert Hxp0p1. assumption.
  Qed.

  Lemma interp_clause_context_right ctx c f :
    clause.interp ctx c f ->
    Forall (fun '(x, v) => map.get ctx x = Some v) (context_of_clause c f).
  Proof.
    intros. cbv [clause.interp] in H. fwd. apply interp_args_context_right. assumption.
  Qed.

  Lemma interp_hyps_context_right ctx hyps hyps' :
    Forall2 (clause.interp ctx) hyps hyps' ->
    Forall (fun '(x, v) => map.get ctx x = Some v) (context_of_hyps hyps hyps').
  Proof.
    intros H. apply Forall2_combine in H. rewrite Forall_forall in *.
    intros x Hx. cbv [context_of_hyps] in *. rewrite in_concat in Hx.
    fwd. cbv [zip] in Hxp0. rewrite in_map_iff in Hxp0. fwd. destruct x1 as [c f].
    apply H in Hxp0p1. apply interp_clause_context_right in Hxp0p1.
    rewrite Forall_forall in Hxp0p1. apply Hxp0p1 in Hxp1. assumption.
  Qed.

  Lemma interp_hyps_context_right_weak ctx hyps hyps' :
    Forall2 (clause.interp ctx) hyps hyps' ->
    map.extends ctx (map.of_list (context_of_hyps hyps hyps')).
  Proof.
    intros H. apply interp_hyps_context_right in H. cbv [map.extends].
    intros. apply of_list_Some_in in H0. rewrite Forall_forall in H.
    apply H in H0. assumption.
  Qed.

  Lemma context_of_hyps_agree ctx hyps hyps' v :
    Forall2 (clause.interp ctx) hyps hyps' ->
    In (expr.var v) (flat_map clause.args hyps) ->
    agree_on ctx (map.of_list (context_of_hyps hyps hyps')) v.
  Proof.
    intros H1 H2.
    pose proof bare_in_context_hyps as H'.
    specialize (H' _ _ _ _ ltac:(eassumption) ltac:(eassumption)). fwd.
    apply in_fst in H'. apply in_of_list_Some_strong in H'. fwd.
    eapply interp_hyps_context_right_weak in H1; eauto.
    specialize (H1 _ _ H'p0). cbv [agree_on]. rewrite H1, H'p0. reflexivity.
  Qed.

  Lemma expr_pattern_interp_option ctx ep vp :
    expr_pattern.interp ctx ep vp ->
    option_relation (expr.interp ctx) (expr_pattern.expr_of ep) (value_pattern.value_of vp).
  Proof. invert 1; simpl; auto. Qed.

  Lemma pattern_args_interp_keep_Some ctx ps vps :
    Forall2 (expr_pattern.interp ctx) ps vps ->
    Forall2 (expr.interp ctx)
      (keep_Some (map expr_pattern.expr_of ps)) (keep_Some (map value_pattern.value_of vps)).
  Proof.
    intros H. apply Forall2_option_relation_keep_Some.
    rewrite <- Forall2_map_l, <- Forall2_map_r.
    eauto using Forall2_impl, expr_pattern_interp_option.
  Qed.

  Definition context_of_clause_pattern (cp : clause_pattern) (fp : fact_pattern) :=
    context_of_args
      (keep_Some (map expr_pattern.expr_of cp.(clause_pattern.args)))
      (keep_Some (map value_pattern.value_of fp.(fact_pattern.args))).

  Definition context_of_pattern_hyps (hyps : list clause_pattern) (pats : list fact_pattern) :=
    concat (zip context_of_clause_pattern hyps pats).

  Lemma interp_pattern_hyps_context_right ctx hyps pats :
    Forall2 (clause_pattern.interp ctx) hyps pats ->
    Forall (fun '(x, v) => map.get ctx x = Some v) (context_of_pattern_hyps hyps pats).
  Proof.
    intros H. apply Forall2_combine in H. rewrite Forall_forall in *.
    intros x Hx. cbv [context_of_pattern_hyps] in *. rewrite in_concat in Hx. fwd.
    cbv [zip] in Hxp0. rewrite in_map_iff in Hxp0. fwd. destruct x1 as [cp f].
    apply H in Hxp0p1. cbv [clause_pattern.interp] in Hxp0p1. fwd.
    cbv [context_of_clause_pattern] in Hxp1. revert x Hxp1.
    apply Forall_forall.
    auto using interp_args_context_right, pattern_args_interp_keep_Some.
  Qed.

  Lemma interp_pattern_hyps_context_right_weak ctx hyps pats :
    Forall2 (clause_pattern.interp ctx) hyps pats ->
    map.extends ctx (map.of_list (context_of_pattern_hyps hyps pats)).
  Proof.
    intros H. apply interp_pattern_hyps_context_right in H. cbv [map.extends].
    intros. apply of_list_Some_in in H0. rewrite Forall_forall in H.
    apply H in H0. assumption.
  Qed.

  Lemma bare_in_context_clause_pattern ctx x cp fp :
    In (expr.var x) (keep_Some (map expr_pattern.expr_of cp.(clause_pattern.args))) ->
    clause_pattern.interp ctx cp fp ->
    exists v, In (x, v) (context_of_clause_pattern cp fp).
  Proof.
    intros H1 H2.
    cbv [clause_pattern.interp] in H2. fwd.
    cbv [context_of_clause_pattern].
    eauto using bare_in_context_args, pattern_args_interp_keep_Some.
  Qed.

  Lemma bare_in_context_pattern_hyps ctx x hyps pats :
    In (expr.var x)
      (flat_map (fun cp => keep_Some (map expr_pattern.expr_of cp.(clause_pattern.args))) hyps) ->
    Forall2 (clause_pattern.interp ctx) hyps pats ->
    exists v, In (x, v) (context_of_pattern_hyps hyps pats).
  Proof.
    intros H1 H2. apply in_flat_map in H1. fwd. cbv [context_of_pattern_hyps].
    apply Forall2_forget_r_strong in H2. rewrite Forall_forall in H2.
    specialize (H2 _ H1p0). fwd.
    eapply bare_in_context_clause_pattern in H2p1; eauto. fwd.
    eexists. rewrite in_concat. cbv [zip]. eexists. rewrite in_map_iff. eauto.
  Qed.

  Lemma context_of_pattern_hyps_agree ctx hyps pats v :
    Forall2 (clause_pattern.interp ctx) hyps pats ->
    In (expr.var v)
      (flat_map (fun cp => keep_Some (map expr_pattern.expr_of cp.(clause_pattern.args))) hyps) ->
    agree_on ctx (map.of_list (context_of_pattern_hyps hyps pats)) v.
  Proof.
    intros H1 H2.
    pose proof bare_in_context_pattern_hyps as H'.
    specialize (H' _ _ _ _ ltac:(eassumption) ltac:(eassumption)). fwd.
    apply in_fst in H'. apply in_of_list_Some_strong in H'. fwd.
    eapply interp_pattern_hyps_context_right_weak in H1; eauto.
    specialize (H1 _ _ H'p0). cbv [agree_on]. rewrite H1, H'p0. reflexivity.
  Qed.

  Definition eval_agg_rule concl_rel agg hyp_rel facts (mf : meta_fact) : option normal_fact :=
    assert eqb (meta_fact.rel mf) hyp_rel;;
    assert inclb (meta_fact.normal_facts mf) (flat_map fact.normal_facts facts);;
    '(value_pattern.any :: value_pattern.any :: rest) <- mf.(meta_fact.pattern).(fact_pattern.args);;
    '(Some args) <- option_all (map value_pattern.value_of rest);;
    let vals := map (fun f => '(i :: x_i :: _) <- f;; Some (i, x_i)) (map.keys mf.(meta_fact.set)) in
    '(Some vals) <- option_all vals;;
    Some {| normal_fact.rel := concl_rel;
      normal_fact.args := interp_agg agg vals :: args |}.

  Definition check_hyps ctx rule_hyps hyps :=
    eqb (option_all (map (subst_in_clause ctx) rule_hyps)) (Some hyps).

  Definition ctx_of_rule rule_hyps hyps :=
    let ctx := map.of_list (context_of_hyps rule_hyps hyps) in
    assert check_hyps ctx rule_hyps hyps;;
    Some ctx.

  Definition check_meta_hyps ctx rule_hyps pats :=
    eqb (option_all (map (subst_in_clause_pattern ctx) rule_hyps)) (Some pats).

  Definition ctx_of_meta_rule rule_hyps pats :=
    let ctx := map.of_list (context_of_pattern_hyps rule_hyps pats) in
    assert check_meta_hyps ctx rule_hyps pats;;
    Some ctx.

  Definition step_rule facts (r : rule) : list normal_fact :=
    match r with
    | rule.impl rule_concls rule_hyps =>
        flat_map (fun hyps =>
                    '(Some ctx) <- ctx_of_rule rule_hyps hyps;;
                    keep_Some (map (subst_in_clause ctx) rule_concls))
          (choose_any_n (length rule_hyps) (flat_map fact.normal_facts facts))
    | rule.agg concl_rel agg hyp_rel =>
        keep_Some (map (eval_agg_rule concl_rel agg hyp_rel facts) (flat_map fact.meta_facts facts))
    end.

  Definition step_rules facts := flat_map (step_rule facts).

  Definition implied_facts mfs :=
    map fact.meta mfs ++ map fact.normal (flat_map meta_fact.normal_facts mfs).

  Definition eval_one_step_derives rules mfs := step_rules (implied_facts mfs) rules.

  Definition step_meta_rule rules mfs (mr : meta_rule) : list meta_fact :=
    flat_map (fun mhyps =>
                '(Some ctx) <- ctx_of_meta_rule mr.(meta_rule.hyps) (map meta_fact.pattern mhyps);;
                let pats := keep_Some (map (subst_in_clause_pattern ctx) mr.(meta_rule.concls)) in
                map (fun pat => meta_fact.mk pat (map normal_fact.args (filter (fact_pattern.matchesb pat) (eval_one_step_derives rules mhyps)))) pats)
      (choose_any_n (length mr.(meta_rule.hyps)) mfs).

  Definition step_meta_rules (p : program) (facts : list fact) : list meta_fact :=
    flat_map (step_meta_rule p.(program.rules) (flat_map fact.meta_facts facts)) p.(program.meta_rules).

  Definition step_program (p : program) (facts : list fact) : list fact :=
    map fact.normal (step_rules facts p.(program.rules)) ++
      map fact.meta (step_meta_rules p facts).

  Definition eval n (p : program) start :=
    Nat.iter n (fun fs => step_program p fs ++ fs) start.

  (*a bit conservative*)
  Definition count_rels p := S (length (rel_graph p)).

  Definition eval_dag p start := eval (count_rels p) p start.

  (*if r is a goodish rule, and this condition holds, then we get the functionalish
    behavrios as encapsulated in lemma agree_fucntional*)
  (* Definition goodish_fun (r : rule) := *)
  (*   exists concl, *)
  (*     r.(rule_concls) = [concl] /\ *)
  (*       (forall v,  ~ (exists ae : agg_expr, rule_agg r = Some (v, ae)) /\ In v (vars_of_fact concl) -> *)
  (*            In (expr.var v) (fact_ins concl) \/ *)
  (*              In (expr.var v) (flat_map fact_args r.(rule_hyps))) /\ *)
  (*       match r.(rule_agg) with *)
  (*       | Some (_, aexpr) => *)
  (*           (forall v, appears_in_agg_expr v aexpr -> *)
  (*                 In (expr.var v) (fact_ins concl) \/ *)
  (*                   In (expr.var v) (flat_map fact_args r.(rule_hyps))) *)
  (*       | None => True *)
  (*       end. *)

  (*i don't remember what this is for.*)
  (* Definition eval_rule_q r concl_ins hyps' agg_hyps's := *)
  (*   let ctx := map.putmany (map.of_list (context_of_args (flat_map fact_ins r.(rule_concls)) concl_ins)) (map.of_list (context_of_hyps r.(rule_hyps) hyps')) in *)
  (*   let ctx' := *)
  (*     match r.(rule_agg) with *)
  (*     | None => Some ctx *)
  (*     | Some (res, aexpr) => *)
  (*         match eval_aexpr aexpr ctx agg_hyps's with *)
  (*         | None => None *)
  (*         | Some res' => Some (map.put ctx res res') *)
  (*         end *)
  (*     end in *)
  (*   match ctx' with *)
  (*   | None => [] *)
  (*   | Some ctx' => *)
  (*       ListMisc.extract_Some (map (subst_in_fact ctx') r.(rule_concls)) *)
  (*   end. *)

  (* Lemma eval_rule_q_complete ctx0 R args r hyps' agg_hyps's : *)
  (*   goodish_rule r -> *)
  (*   goodish_fun r -> *)
  (*   rule_impl' ctx0 r (R, args) hyps' agg_hyps's -> *)
  (*   eval_rule_q r (skipn (outs R) args) hyps' agg_hyps's = [(R, args)]. *)
  (* Proof. *)
  (*   intros Hgood Hfun Himpl. cbv [eval_rule_q]. cbv [goodish_rule] in Hgood. *)
  (*   cbv [goodish_fun] in Hfun. fwd. *)
  (*   invert Himpl. rewrite Hgoodp0 in *. invert_list_stuff. simpl. rewrite app_nil_r. *)
  (*   invert H. *)
  (*   - rewrite <- H5 in *. fwd. erewrite subst_in_fact_complete. 1: reflexivity. *)
  (*     eapply interp_fact_agree_on; [eassumption|]. *)
  (*     apply Forall_forall. intros v H. cbv [agree_on]. invert H4. *)
  (*     rewrite map.get_putmany_dec. destruct_one_match. *)
  (*     + apply of_list_Some_in in E. apply interp_hyps_context_right in H1. *)
  (*       rewrite Forall_forall in H1. apply H1 in E. assumption. *)
  (*     + apply get_of_list_None_bw in E. specialize (Hfunp1 v). specialize' Hfunp1. *)
  (*       { split; auto. intro. fwd. congruence. } *)
  (*       destruct Hfunp1 as [Hfunp1|Hfunp1]. *)
  (*       -- eapply Forall2_skipn in H6. pose proof H6 as H6'. *)
  (*          apply interp_args_context_right in H6. rewrite Forall_forall in H6. *)
  (*          cbv [fact_ins] in Hgoodp1. eapply bare_in_context_args in H6'. *)
  (*          2: { eassumption. } *)
  (*          fwd. apply in_fst in H6'. apply in_of_list_Some_strong in H6'. *)
  (*          fwd. apply H6 in H6'p1. cbv [fact_ins]. rewrite H6'p0, H6'p1. reflexivity. *)
  (*       -- eapply bare_in_context_hyps in Hfunp1; [|eassumption]. fwd. *)
  (*          apply in_fst in Hfunp1. exfalso. auto. *)
  (*   - rewrite <- H0 in *. fwd. erewrite eval_aexpr_complete; try assumption. *)
  (*     2: { eapply interp_agg_expr_agree_on; [eassumption|]. intros v Hv. *)
  (*          specialize (Hfunp2 _ Hv). *)
  (*          cbv [agree_on]. rewrite map.get_putmany_dec. destruct_one_match. *)
  (*          + apply of_list_Some_in in E. apply interp_hyps_context_right in H1. *)
  (*            rewrite Forall_forall in H1. apply H1 in E. assumption. *)
  (*          + apply get_of_list_None_bw in E. Print appears_in_agg_expr. *)
  (*            destruct Hfunp2 as [H'|H']. *)
  (*            -- invert H4. eapply Forall2_skipn in H5. pose proof H5 as H5'. *)
  (*               apply interp_args_context_right in H5. rewrite Forall_forall in H5. *)
  (*               cbv [fact_ins] in Hgoodp1. eapply bare_in_context_args in H5'. *)
  (*               2: { eassumption. } *)
  (*               fwd. apply in_fst in H5'. apply in_of_list_Some_strong in H5'. *)
  (*               fwd. apply H5 in H5'p1. cbv [fact_ins]. rewrite H5'p0. *)
  (*               rewrite map.get_put_diff in H5'p1; auto. intros ?. subst. *)
  (*               Search res. apply Hgoodp1. do 2 eexists. split; [|reflexivity]. *)
  (*               apply in_flat_map. eexists. split; [eassumption|]. simpl. auto. *)
  (*            -- eapply bare_in_context_hyps in H'; [|eassumption]. fwd. *)
  (*               apply in_fst in H'. exfalso. auto. } *)
  (*     erewrite subst_in_fact_complete. 1: reflexivity. *)
  (*     eapply interp_fact_agree_on; [eassumption|]. *)
  (*     apply Forall_forall. intros v Hv. cbv [agree_on]. invert H4. *)
  (*     do 2 rewrite map.get_put_dec. destruct_one_match; try reflexivity. *)
  (*     rewrite map.get_putmany_dec. destruct_one_match. *)
  (*     + apply of_list_Some_in in E0. apply interp_hyps_context_right in H1. *)
  (*       rewrite Forall_forall in H1. apply H1 in E0. assumption. *)
  (*     + apply get_of_list_None_bw in E0. specialize (Hfunp1 v). specialize' Hfunp1. *)
  (*       { split; auto. intro. fwd. congruence. } *)
  (*       destruct Hfunp1 as [H'|H']. *)
  (*       -- eapply Forall2_skipn in H5. pose proof H5 as H5'. *)
  (*          apply interp_args_context_right in H5. rewrite Forall_forall in H5. *)
  (*          cbv [fact_ins] in Hgoodp1. eapply bare_in_context_args in H5'. *)
  (*          2: { eassumption. } *)
  (*          fwd. apply in_fst in H5'. apply in_of_list_Some_strong in H5'. *)
  (*          fwd. apply H5 in H5'p1. cbv [fact_ins]. rewrite H5'p0. *)
  (*          rewrite map.get_put_diff in H5'p1; auto. *)
  (*       -- eapply bare_in_context_hyps in H'; [|eassumption]. fwd. *)
  (*          apply in_fst in H'. exfalso. auto. *)
  (* Qed. *)

  Lemma in_implied_facts mfs f :
    In f (implied_facts mfs) <-> fact.implied_by_mfs mfs f.
  Proof.
    cbv [implied_facts fact.implied_by_mfs]. rewrite in_app_iff, !in_map_iff, Exists_exists.
    destruct f as [nf|m]; simpl.
    - setoid_rewrite in_flat_map. setoid_rewrite meta_fact.in_normal_facts. split.
      + intros [(? & [=] & _) | (? & [= <-] & ? & ? & ?)]. eauto.
      + intros (? & ? & ?). right. eauto.
    - split.
      + intros [(? & [= <-] & ?) | (? & [=] & _)]. eauto.
      + intros (? & ? & <-). left. eauto.
  Qed.

  Lemma subst_in_clauses_Some ctx cs nfs :
    option_all (map (subst_in_clause ctx) cs) = Some nfs <-> Forall2 (clause.interp ctx) cs nfs.
  Proof.
    split; intros H.
    - apply option_all_Forall2 in H. rewrite <- Forall2_map_l in H.
      eauto using Forall2_impl, subst_in_clause_sound.
    - apply Forall2_option_all. rewrite <- Forall2_map_l.
      eauto using Forall2_impl, subst_in_clause_complete.
  Qed.

  Lemma subst_in_clause_patterns_Some ctx cps pats :
    option_all (map (subst_in_clause_pattern ctx) cps) = Some pats <->
      Forall2 (clause_pattern.interp ctx) cps pats.
  Proof.
    split; intros H.
    - apply option_all_Forall2 in H. rewrite <- Forall2_map_l in H.
      eauto using Forall2_impl, subst_in_clause_pattern_sound.
    - apply Forall2_option_all. rewrite <- Forall2_map_l.
      eauto using Forall2_impl, subst_in_clause_pattern_complete.
  Qed.

  #[global] Instance check_hyps_spec ctx rule_hyps hyps :
    Reflects (Forall2 (clause.interp ctx) rule_hyps hyps) (check_hyps ctx rule_hyps hyps).
  Proof. cbv [check_hyps]. eapply Reflects_iff; [|apply subst_in_clauses_Some]. exact _. Qed.

  #[global] Instance check_meta_hyps_spec ctx rule_hyps pats :
    Reflects (Forall2 (clause_pattern.interp ctx) rule_hyps pats) (check_meta_hyps ctx rule_hyps pats).
  Proof. cbv [check_meta_hyps]. eapply Reflects_iff; [|apply subst_in_clause_patterns_Some]. exact _. Qed.

  Lemma ctx_of_rule_Some rule_hyps hyps ctx :
    ctx_of_rule rule_hyps hyps = Some ctx <->
      ctx = map.of_list (context_of_hyps rule_hyps hyps) /\ Forall2 (clause.interp ctx) rule_hyps hyps.
  Proof.
    cbv [ctx_of_rule default option_default].
    destruct (check_hyps_spec (map.of_list (context_of_hyps rule_hyps hyps)) rule_hyps hyps).
    - split; [intros [= <-] | intros [-> _]]; auto.
    - split; [discriminate | intros [-> ?]]; contradiction.
  Qed.

  Lemma ctx_of_meta_rule_Some rule_hyps pats ctx :
    ctx_of_meta_rule rule_hyps pats = Some ctx <->
      ctx = map.of_list (context_of_pattern_hyps rule_hyps pats) /\
        Forall2 (clause_pattern.interp ctx) rule_hyps pats.
  Proof.
    cbv [ctx_of_meta_rule default option_default].
    destruct (check_meta_hyps_spec (map.of_list (context_of_pattern_hyps rule_hyps pats)) rule_hyps pats).
    - split; [intros [= <-] | intros [-> _]]; auto.
    - split; [discriminate | intros [-> ?]]; contradiction.
  Qed.

  Lemma in_args_filter_matches pat results nf :
    fact_pattern.matches pat nf ->
    In nf.(normal_fact.args) (map normal_fact.args (filter (fact_pattern.matchesb pat) results)) <->
      In nf results.
  Proof.
    intros Hm. rewrite in_map_iff. setoid_rewrite filter_In. split.
    - intros (nf' & Hargs & Hin & Hm'). rewrite Reflects_true_iff in Hm' by typeclasses eauto.
      replace nf with nf'; [assumption|].
      destruct nf, nf'. cbv [fact_pattern.matches] in *. simpl in *. fwd. f_equal. congruence.
    - intros Hin. exists nf. split; [reflexivity|]. split; [assumption|].
      rewrite Reflects_true_iff by typeclasses eauto. exact Hm.
  Qed.

  Lemma eval_agg_rule_sound concl_rel agg hyp_rel facts mf nf :
    eval_agg_rule concl_rel agg hyp_rel facts mf = Some nf ->
    incl (map fact.normal (meta_fact.normal_facts mf)) facts /\
      rule.interp (rule.agg concl_rel agg hyp_rel) nf
        (fact.meta mf :: map fact.normal (meta_fact.normal_facts mf)).
  Proof.
    destruct mf as [[R pat_args] st pf]. cbv [eval_agg_rule meta_fact.rel default option_default].
    simpl. intros H.
    destr (eqb R hyp_rel); [|discriminate]. subst.
    destruct (inclb _ _) eqn:Hincl; [|discriminate]. apply inclb_incl in Hincl.
    destruct pat_args as [|[|] [|[|] rest]]; try discriminate.
    destruct (option_all (map value_pattern.value_of rest)) as [args|] eqn:Hargs; [|discriminate].
    destruct (option_all (map _ (map.keys st))) as [vals|] eqn:Hvals; [|discriminate].
    invert H.
    apply option_all_Forall2 in Hargs, Hvals. rewrite <- Forall2_map_l in Hargs. rewrite <- Forall2_map_l in Hvals.
    assert (Hrest : rest = map value_pattern.exactly args).
    { rewrite <- (map_id rest). apply Forall2_map_eq.
      eapply Forall2_impl; [exact Hargs|]. intros [v|] v'; simpl; congruence. }
    subst rest.
    assert (Hkeys : map.keys st = map (fun '(i, x) => i :: x :: args) vals).
    { rewrite <- (map_id (map.keys st)). apply Forall2_map_eq.
      eapply Forall2_impl_strong; [exact Hvals|]. intros k (i, x) Hk Hin _.
      pose proof (meta_fact.contains_matches {| meta_fact.pattern := _; meta_fact._pf := pf |} k Hin) as Hm.
      simpl in Hm. invert_list_stuff. simpl. do 2 f_equal.
      eauto using value_pattern.matches_map_exactly_inv. }
    split.
    - intros f Hf. apply in_map_iff in Hf. fwd. apply fact.in_flat_map_normal_facts. auto.
    - replace (map fact.normal (meta_fact.normal_facts _))
        with (map (fun '(i, x) => fact.normal {| normal_fact.rel := hyp_rel;
                                                normal_fact.args := i :: x :: args |}) vals).
      2: { cbv [meta_fact.normal_facts meta_fact.rel]. simpl. rewrite Hkeys, !map_map.
           apply map_ext. intros (i, x). reflexivity. }
      rewrite <- meta_fact.mk_keys at 1. simpl. rewrite Hkeys.
      apply rule.interp_agg. apply (NoDup_map_inv (fun '(i, x) => i :: x :: args)).
      rewrite <- Hkeys. apply map.keys_NoDup.
  Qed.

  Lemma step_rule_sound facts r nf :
    In nf (step_rule facts r) ->
    exists hyps, incl hyps facts /\ rule.interp r nf hyps.
  Proof.
    destruct r as [concls rule_hyps | concl_rel agg hyp_rel]; simpl; intros H.
    - apply in_flat_map in H. destruct H as (hyps & Hhyps & H). apply in_choose_any_n in Hhyps.
      destruct (ctx_of_rule rule_hyps hyps) as [ctx|] eqn:E; [|simpl in H; contradiction].
      apply ctx_of_rule_Some in E. apply in_keep_Some, in_map_iff in H. fwd.
      exists (map fact.normal hyps). split.
      + intros f Hf. apply in_map_iff in Hf. fwd. apply fact.in_flat_map_normal_facts. auto.
      + eapply rule.interp_impl; [|eassumption]. apply Exists_exists. eauto using subst_in_clause_sound.
    - apply in_keep_Some, in_map_iff in H. destruct H as (mf & Hmf & Hin).
      apply fact.in_flat_map_meta_facts in Hin. apply eval_agg_rule_sound in Hmf. fwd.
      eexists. split; [|eassumption]. apply incl_cons; assumption.
  Qed.

  Lemma step_rules_sound facts rules nf :
    In nf (step_rules facts rules) ->
    exists hyps, incl hyps facts /\ Exists (fun r => rule.interp r nf hyps) rules.
  Proof.
    cbv [step_rules]. rewrite in_flat_map. intros (r & Hr & H). apply step_rule_sound in H. fwd.
    eexists. split; [eassumption|]. apply Exists_exists. eauto.
  Qed.

  Lemma subst_in_expr_ctxs_agree ctx ctx' e :
    Forall (agree_on ctx ctx') (expr.vars e) ->
    subst_in_expr ctx e = subst_in_expr ctx' e.
  Proof.
    intros H.
    destruct (subst_in_expr ctx e) eqn:E; destruct (subst_in_expr ctx' e) eqn:E'; auto.
    - apply subst_in_expr_sound in E, E'. f_equal. eauto using expr.interp_det'.
    - apply subst_in_expr_sound in E. eapply expr.interp_agree_on in E; eauto.
      apply subst_in_expr_complete in E. congruence.
    - apply subst_in_expr_sound in E'. eapply expr.interp_agree_on in E'.
      2: { eapply Forall_impl; [eassumption|]. intros. symmetry. eassumption. }
      apply subst_in_expr_complete in E'. congruence.
  Qed.

  Lemma subst_in_clauses_ctxs_agree ctx ctx' cs :
    Forall (agree_on ctx ctx') (flat_map clause.vars cs) ->
    map (subst_in_clause ctx) cs = map (subst_in_clause ctx') cs.
  Proof.
    intros H. apply Forall_flat_map in H. apply map_ext_Forall. eapply Forall_impl; [exact H|].
    intros c Hc. cbv [clause.vars] in Hc. apply Forall_flat_map in Hc.
    cbv [subst_in_clause]. do 2 f_equal. apply map_ext_Forall.
    eauto using Forall_impl, subst_in_expr_ctxs_agree.
  Qed.

  Lemma subst_in_expr_pattern_ctxs_agree ctx ctx' ep :
    Forall (agree_on ctx ctx') (expr_pattern.vars ep) ->
    subst_in_expr_pattern ctx ep = subst_in_expr_pattern ctx' ep.
  Proof.
    destruct ep; simpl; intros H; [|reflexivity].
    erewrite subst_in_expr_ctxs_agree by eassumption. reflexivity.
  Qed.

  Lemma subst_in_clause_patterns_ctxs_agree ctx ctx' cps :
    Forall (agree_on ctx ctx') (flat_map clause_pattern.vars cps) ->
    map (subst_in_clause_pattern ctx) cps = map (subst_in_clause_pattern ctx') cps.
  Proof.
    intros H. apply Forall_flat_map in H. apply map_ext_Forall. eapply Forall_impl; [exact H|].
    intros c Hc. cbv [clause_pattern.vars] in Hc. apply Forall_flat_map in Hc.
    cbv [subst_in_clause_pattern]. do 2 f_equal. apply map_ext_Forall.
    eauto using Forall_impl, subst_in_expr_pattern_ctxs_agree.
  Qed.

  Lemma is_bottomup_ctx_agree ctx concls rule_hyps hyps :
    rule.is_bottomup (rule.impl concls rule_hyps) ->
    Forall2 (clause.interp ctx) rule_hyps hyps ->
    Forall (agree_on ctx (map.of_list (context_of_hyps rule_hyps hyps)))
      (rule.all_vars (rule.impl concls rule_hyps)).
  Proof.
    intros Hgood Hmatch. apply Forall_forall. intros v Hv. apply Hgood in Hv.
    eauto using context_of_hyps_agree.
  Qed.

  Lemma meta_is_bottomup_ctx_agree ctx mr pats :
    meta_rule.is_bottomup mr ->
    Forall2 (clause_pattern.interp ctx) mr.(meta_rule.hyps) pats ->
    Forall (agree_on ctx (map.of_list (context_of_pattern_hyps mr.(meta_rule.hyps) pats)))
      (meta_rule.all_vars mr).
  Proof.
    intros Hgood Hmatch. apply Forall_forall. intros v Hv. apply Hgood in Hv.
    eapply context_of_pattern_hyps_agree; [eassumption|].
    cbv [meta_rule.hyp_args] in Hv. rewrite in_flat_map in *. fwd.
    eexists. split; [eassumption|]. apply in_keep_Some.
    apply in_map_iff. eexists. split; [|eassumption]. reflexivity.
  Qed.

  (*aggregators are meant to be commutative monoids, but the signature does not say so*)
  Context (interp_agg_perm : forall agg vals vals',
              Permutation vals vals' -> interp_agg agg vals = interp_agg agg vals').

  Lemma eval_agg_rule_complete concl_rel agg hyp_rel facts args vals :
    NoDup vals ->
    incl (map (fun '(i, x) => fact.normal {| normal_fact.rel := hyp_rel;
                                            normal_fact.args := i :: x :: args |}) vals) facts ->
    exists vals',
      Permutation vals vals' /\
        eval_agg_rule concl_rel agg hyp_rel facts
          (meta_fact.mk
             {| fact_pattern.rel := hyp_rel;
                fact_pattern.args := value_pattern.any :: value_pattern.any :: map value_pattern.exactly args |}
             (map (fun '(i, x) => i :: x :: args) vals))
        = Some {| normal_fact.rel := concl_rel; normal_fact.args := interp_agg agg vals' :: args |}.
  Proof.
    intros Hnd Hincl.
    pose proof (meta_fact.mk_keys_perm
      {| fact_pattern.rel := hyp_rel;
         fact_pattern.args := value_pattern.any :: value_pattern.any :: map value_pattern.exactly args |}
      (map (fun '(i, x) => i :: x :: args) vals)) as Hkeys.
    specialize' Hkeys.
    { apply Finite.Injective_map_NoDup; [|assumption]. intros (?, ?) (?, ?). congruence. }
    specialize' Hkeys.
    { apply Forall_forall. intros k Hk. apply in_map_iff in Hk. destruct Hk as ((i, x) & <- & _).
      repeat constructor. apply value_pattern.matches_map_exactly. }
    eapply Permutation_map with (f := fun f => '(i :: x_i :: _) <- f;; Some (i, x_i)) in Hkeys.
    rewrite map_map in Hkeys. erewrite map_ext with (g := Some) in Hkeys by (intros (?, ?); reflexivity).
    apply Permutation_map_inv in Hkeys. destruct Hkeys as (vals' & Hvals' & Hperm).
    exists vals'. split; [assumption|].
    cbv [eval_agg_rule meta_fact.rel]. rewrite Hvals', option_all_map_Some.
    erewrite (proj2 (inclb_incl _ _)).
    2: { intros nf Hnf. rewrite meta_fact.in_normal_facts, meta_fact.matches_mk in Hnf.
         destruct Hnf as [Hm Hin]. apply in_map_iff in Hin. destruct Hin as ((i, x) & Hix & Hin).
         apply fact.in_flat_map_normal_facts, Hincl, in_map_iff. exists (i, x). split; [|assumption].
         destruct nf. cbv [fact_pattern.matches] in Hm. simpl in *. fwd. f_equal. congruence. }
    simpl. destr (eqb hyp_rel hyp_rel); [|congruence].
    rewrite map_map. simpl. rewrite option_all_map_Some. reflexivity.
  Qed.

  Lemma step_rule_complete facts r nf hyps :
    rule.is_bottomup r ->
    incl hyps facts ->
    rule.interp r nf hyps ->
    In nf (step_rule facts r).
  Proof.
    intros Hgood Hincl H. invert H.
    - simpl. apply in_flat_map. exists hyps0. split.
      { apply in_choose_any_n. split; [symmetry; eauto using Forall2_length|].
        intros h Hh. apply fact.in_flat_map_normal_facts, Hincl, in_map, Hh. }
      pose proof (is_bottomup_ctx_agree _ _ _ _ Hgood H1) as Hagree.
      cbv [rule.all_vars rule.concl_vars rule.hyp_vars] in Hagree. apply Forall_app in Hagree.
      destruct Hagree as [Hagree_c Hagree_h].
      rewrite (proj2 (ctx_of_rule_Some _ _ (map.of_list (context_of_hyps rule_hyps hyps0)))).
      2: { split; [reflexivity|]. apply subst_in_clauses_Some.
           erewrite <- subst_in_clauses_ctxs_agree by eassumption. apply subst_in_clauses_Some, H1. }
      simpl. apply in_keep_Some. erewrite <- subst_in_clauses_ctxs_agree by eassumption.
      apply in_map_iff. apply Exists_exists in H0. fwd. eauto using subst_in_clause_complete.
    - simpl. apply in_keep_Some, in_map_iff. apply incl_cons_inv in Hincl. destruct Hincl as [Hmf Hincl].
      edestruct eval_agg_rule_complete as (vals' & Hperm & Heval); [eassumption | eassumption |].
      eexists. split.
      + rewrite Heval, (interp_agg_perm _ _ _ Hperm). reflexivity.
      + apply fact.in_flat_map_meta_facts, Hmf.
  Qed.

  Lemma step_rules_complete facts rules nf hyps :
    Forall rule.is_bottomup rules ->
    incl hyps facts ->
    Exists (fun r => rule.interp r nf hyps) rules ->
    In nf (step_rules facts rules).
  Proof.
    intros Hgood Hincl Hex. cbv [step_rules]. apply in_flat_map.
    rewrite Forall_forall in Hgood. apply Exists_exists in Hex. fwd. eauto using step_rule_complete.
  Qed.

  Lemma eval_one_step_derives_spec rules mfs nf :
    Forall rule.is_bottomup rules ->
    In nf (eval_one_step_derives rules mfs) <-> rule.one_step_derives rules mfs nf.
  Proof.
    intros Hgood. cbv [eval_one_step_derives rule.one_step_derives]. split.
    - intros H. apply step_rules_sound in H. fwd. eexists. split; [apply Exists_exists; eauto|].
      apply Forall_forall. intros f Hf. apply in_implied_facts. auto.
    - intros (hyps & Hex & Himp). eapply step_rules_complete; [assumption | | eassumption].
      intros f Hf. apply in_implied_facts. rewrite Forall_forall in Himp. auto.
  Qed.

  Lemma step_meta_rule_sound rules mfs mr mf :
    Forall rule.is_bottomup rules ->
    In mf (step_meta_rule rules mfs mr) ->
    exists mhyps, incl mhyps mfs /\ meta_rule.interp rules mr mf mhyps.
  Proof.
    intros Hgood H. cbv [step_meta_rule] in H. apply in_flat_map in H.
    destruct H as (mhyps & Hmhyps & H). apply in_choose_any_n in Hmhyps.
    destruct (ctx_of_meta_rule _ _) as [ctx|] eqn:E; [|simpl in H; contradiction].
    apply ctx_of_meta_rule_Some in E. apply in_map_iff in H. destruct H as (pat & <- & Hpat).
    apply in_keep_Some, in_map_iff in Hpat. fwd.
    exists mhyps. split; [tauto|]. split.
    - eexists. split; [|eassumption]. apply Exists_exists. eauto using subst_in_clause_pattern_sound.
    - intros nf Hm. simpl in Hm |- *. rewrite meta_fact.contains_to_canonical_set.
      rewrite in_args_filter_matches, eval_one_step_derives_spec by assumption.
      cbv [fact_pattern.matches] in Hm. tauto.
  Qed.

  Lemma step_meta_rule_complete rules mfs mr mf mhyps :
    Forall rule.is_bottomup rules ->
    meta_rule.is_bottomup mr ->
    incl mhyps mfs ->
    meta_rule.interp rules mr mf mhyps ->
    In mf (step_meta_rule rules mfs mr).
  Proof.
    intros Hgood Hmgood Hincl [(ctx & Hex & Hmatch) Hset].
    cbv [step_meta_rule]. apply in_flat_map. exists mhyps. split.
    { apply in_choose_any_n. split; [|assumption]. apply Forall2_length in Hmatch.
      rewrite length_map in Hmatch. congruence. }
    pose proof (meta_is_bottomup_ctx_agree _ _ _ Hmgood Hmatch) as Hagree.
    cbv [meta_rule.all_vars meta_rule.concl_vars meta_rule.hyp_vars] in Hagree.
    apply Forall_app in Hagree. destruct Hagree as [Hagree_c Hagree_h].
    rewrite (proj2 (ctx_of_meta_rule_Some _ _
               (map.of_list (context_of_pattern_hyps mr.(meta_rule.hyps) (map meta_fact.pattern mhyps))))).
    2: { split; [reflexivity|]. apply subst_in_clause_patterns_Some.
         erewrite <- subst_in_clause_patterns_ctxs_agree by eassumption.
         apply subst_in_clause_patterns_Some, Hmatch. }
    simpl. apply in_map_iff. exists mf.(meta_fact.pattern). split.
    - apply meta_fact.eq_of_agree; [reflexivity|]. intros nf Hm _. simpl in Hm |- *.
      rewrite meta_fact.contains_to_canonical_set.
      rewrite in_args_filter_matches, eval_one_step_derives_spec, (Hset nf Hm) by assumption.
      cbv [fact_pattern.matches] in Hm. tauto.
    - apply in_keep_Some. erewrite <- subst_in_clause_patterns_ctxs_agree by eassumption.
      apply in_map_iff. apply Exists_exists in Hex. fwd. eauto using subst_in_clause_pattern_complete.
  Qed.

  Lemma step_program_sound p facts f :
    Forall rule.is_bottomup p.(program.rules) ->
    In f (step_program p facts) ->
    exists hyps, incl hyps facts /\ program.interp_step p f hyps.
  Proof.
    intros Hgood H. cbv [step_program step_meta_rules] in H. apply in_app_iff in H.
    destruct H as [H|H]; apply in_map_iff in H; destruct H as (x & <- & H).
    - apply step_rules_sound in H. fwd. eauto using program.rule_step.
    - apply in_flat_map in H. destruct H as (mr & Hmr & H).
      apply step_meta_rule_sound in H; [|assumption]. fwd.
      eexists. split; [|constructor; apply Exists_exists; eauto].
      intros g Hg. apply in_map_iff in Hg. fwd. apply fact.in_flat_map_meta_facts. auto.
  Qed.

  Lemma step_program_complete p facts f hyps :
    Forall rule.is_bottomup p.(program.rules) ->
    Forall meta_rule.is_bottomup p.(program.meta_rules) ->
    incl hyps facts ->
    program.interp_step p f hyps ->
    In f (step_program p facts).
  Proof.
    intros Hgood Hmgood Hincl H. cbv [step_program step_meta_rules]. apply in_app_iff. invert H.
    - left. apply in_map. eauto using step_rules_complete.
    - right. apply in_map, in_flat_map. apply Exists_exists in H0. fwd.
      rewrite Forall_forall in Hmgood. eexists. split; [eassumption|].
      eapply step_meta_rule_complete; eauto.
      intros mf Hmf. apply fact.in_flat_map_meta_facts, Hincl, in_map, Hmf.
  Qed.

  Lemma eval_start_incl n p start :
    incl start (eval n p start).
  Proof. induction n; simpl; auto with incl. Qed.

  Lemma eval_sound p Q n start f :
    Forall rule.is_bottomup p.(program.rules) ->
    (forall x, In x start -> Q x) ->
    In f (eval n p start) ->
    program.interp p Q f.
  Proof.
    intros Hgood HQ. revert f. induction n; intros f Hf; simpl in Hf.
    - apply pftree.leaf. auto.
    - apply in_app_iff in Hf. destruct Hf as [Hf|Hf]; [|auto].
      apply step_program_sound in Hf; [|assumption]. fwd.
      eapply program.interp_step_strong; [eassumption|]. apply Forall_forall. auto.
  Qed.

  Lemma eval_complete p Q n start f :
    Forall rule.is_bottomup p.(program.rules) ->
    Forall meta_rule.is_bottomup p.(program.meta_rules) ->
    (forall x, Q x <-> In x start) ->
    program.interp p Q f ->
    In f (eval n p start) \/
      (exists l, path (rel_graph p) (fact.rel f) l /\ n <= length l).
  Proof.
    intros Hp Hmp HQ. revert f. induction n.
    - intros f Hf. invert Hf.
      + left. apply HQ. assumption.
      + right. exists nil. simpl. split; [constructor|lia].
    - intros f Hf. invert Hf.
      + left. apply eval_start_incl. apply HQ. assumption.
      + eapply Forall_impl in H0; [|exact IHn].
        apply Forall_or in H0. destruct H0 as [H0|H0].
        * left. simpl. rewrite in_app_iff. left.
          eapply step_program_complete; try assumption;
            [rewrite Forall_forall in H0; exact H0 | eassumption].
        * right. rewrite Exists_exists in H0. fwd. eexists (_ :: _). split.
          { constructor; [|eassumption]. apply rel_graph_spec in H.
            rewrite Forall_forall in H. apply H. assumption. }
          simpl. lia.
  Qed.

  Lemma eval_dag_complete p Q start f :
    Forall rule.is_bottomup p.(program.rules) ->
    Forall meta_rule.is_bottomup p.(program.meta_rules) ->
    (forall x, Q x <-> In x start) ->
    dag (rel_graph p) ->
    program.interp p Q f ->
    In f (eval_dag p start).
  Proof.
    intros Hp Hmp HQ Hdag Hf.
    eapply eval_complete in Hf; eauto. destruct Hf as [Hf|Hf]; eauto.
    fwd. eapply dag_paths_short in Hfp0; eauto. cbv [count_rels] in *. lia.
  Qed.

  Lemma eval_dag_iff p Q start f :
    Forall rule.is_bottomup p.(program.rules) ->
    Forall meta_rule.is_bottomup p.(program.meta_rules) ->
    (forall x, Q x <-> In x start) ->
    dag (rel_graph p) ->
    In f (eval_dag p start) <-> program.interp p Q f.
  Proof.
    intros Hp Hmp HQ Hdag. split; [|eauto using eval_dag_complete].
    apply eval_sound; [assumption|]. intros x. apply HQ.
  Qed.
End __.

Module program.
  Section __.
    Context `{params : datalog_params}.
    Context {rel_eqb : Eqb rel} {rel_eqb_ok : Eqb_ok rel_eqb}.

    Definition finite rules p Q :=
      forall pat hyps,
        Exists (fun mr => meta_rule.pattern_interp mr pat (map meta_fact.pattern hyps)) p.(program.meta_rules) ->
        Forall (program.interp p Q) (map fact.meta hyps) ->
        program.interp p Q (fact.meta (meta_fact.mk pat (map normal_fact.args (filter (fact_pattern.matchesb pat) (eval_one_step_derives rules hyps))))).
  End __.
End program.
