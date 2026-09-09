From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Bool.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List Datatypes.Option Eqb.
From Datalog Require Import Eqb.

From Datalog Require Import Datalog Map Tactics Fp List.
From GraphSearch Require Import Dag.

Import ListNotations.

Section __.
  Context `{params : datalog_params}.
  Context {var_eqb : Eqb exprvar} {var_eqb_ok : Eqb_ok var_eqb}.

  Implicit Type ctx : context.

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

  Fixpoint subst_in_expr ctx e : option value :=
    match e with
    | expr.var v => map.get ctx v
    | expr.app f args => option_coalesce (option_map (interp_fun f) (option_all (map (subst_in_expr ctx) args)))
    end.

  Hint Constructors expr.interp : core.
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

  Definition context_of_clause (c : clause) (f : fact) :=
    match f with
    | fact.normal nf => context_of_args c.(clause.args) nf.(normal_fact.args)
    | fact.meta _ => []
    end.

  Definition context_of_hyps (hyps : list clause) (hyps' : list fact) :=
    concat (zip context_of_clause hyps hyps').

  (*the pool an interpreter works over is a list fact, so here are the
    clause-fact versions of the interp relations*)
  Definition clause_fact_interp ctx (c : clause) (f : fact) :=
    match f with
    | fact.normal nf => clause.interp ctx c nf
    | fact.meta _ => False
    end.

  Definition clause_pattern_fact_interp ctx (cp : clause_pattern) (f : fact) :=
    match f with
    | fact.meta mf => clause_pattern.interp ctx cp mf.(meta_fact.pattern)
    | fact.normal _ => False
    end.

  Lemma clause_fact_interp_normal ctx hyps hyps' :
    Forall2 (clause.interp ctx) hyps hyps' ->
    Forall2 (clause_fact_interp ctx) hyps (map fact.normal hyps').
  Proof.
    intros. rewrite <- Forall2_map_r. eapply Forall2_impl; [eassumption|]. auto.
  Qed.

  Lemma clause_pattern_fact_interp_meta ctx hyps mhyps :
    Forall2 (clause_pattern.interp ctx) hyps (map meta_fact.pattern mhyps) ->
    Forall2 (clause_pattern_fact_interp ctx) hyps (map fact.meta mhyps).
  Proof.
    intros H. rewrite <- Forall2_map_r in H. rewrite <- Forall2_map_r.
    eapply Forall2_impl; [eassumption|]. simpl. auto.
  Qed.

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
    clause_fact_interp ctx c f ->
    exists v, In (x, v) (context_of_clause c f).
  Proof.
    intros H1 H2. destruct f; simpl in *; [|contradiction].
    cbv [clause.interp] in H2. fwd. eapply bare_in_context_args; eassumption.
  Qed.

  Lemma bare_in_context_hyps ctx x hyps hyps' :
    In (expr.var x) (flat_map clause.args hyps) ->
    Forall2 (clause_fact_interp ctx) hyps hyps' ->
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
    clause_fact_interp ctx c f ->
    Forall (fun '(x, v) => map.get ctx x = Some v) (context_of_clause c f).
  Proof.
    intros. destruct f; simpl in *; [|contradiction].
    cbv [clause.interp] in H. fwd. apply interp_args_context_right. assumption.
  Qed.

  Lemma interp_hyps_context_right ctx hyps hyps' :
    Forall2 (clause_fact_interp ctx) hyps hyps' ->
    Forall (fun '(x, v) => map.get ctx x = Some v) (context_of_hyps hyps hyps').
  Proof.
    intros H. apply Forall2_combine in H. rewrite Forall_forall in *.
    intros x Hx. cbv [context_of_hyps] in *. rewrite in_concat in Hx.
    fwd. cbv [zip] in Hxp0. rewrite in_map_iff in Hxp0. fwd. destruct x1 as [c f].
    apply H in Hxp0p1. apply interp_clause_context_right in Hxp0p1.
    rewrite Forall_forall in Hxp0p1. apply Hxp0p1 in Hxp1. assumption.
  Qed.

  Lemma interp_hyps_context_right_weak ctx hyps hyps' :
    Forall2 (clause_fact_interp ctx) hyps hyps' ->
    map.extends ctx (map.of_list (context_of_hyps hyps hyps')).
  Proof.
    intros H. apply interp_hyps_context_right in H. cbv [map.extends].
    intros. apply of_list_Some_in in H0. rewrite Forall_forall in H.
    apply H in H0. assumption.
  Qed.

  Lemma context_of_hyps_agree ctx hyps hyps' v :
    Forall2 (clause_fact_interp ctx) hyps hyps' ->
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

  Definition expr_of_pattern (p : expr_pattern) : option expr :=
    match p with
    | expr_pattern.exactly e => Some e
    | expr_pattern.any => None
    end.

  Definition value_of_pattern (p : value_pattern) : option value :=
    match p with
    | value_pattern.exactly v => Some v
    | value_pattern.any => None
    end.

  Lemma expr_pattern_interp_option ctx ep vp :
    expr_pattern.interp ctx ep vp ->
    option_relation (expr.interp ctx) (expr_of_pattern ep) (value_of_pattern vp).
  Proof. invert 1; simpl; auto. Qed.

  Lemma pattern_args_interp_keep_Some ctx ps vps :
    Forall2 (expr_pattern.interp ctx) ps vps ->
    Forall2 (expr.interp ctx)
      (keep_Some (map expr_of_pattern ps)) (keep_Some (map value_of_pattern vps)).
  Proof.
    intros H. apply Forall2_option_relation_keep_Some.
    rewrite <- Forall2_map_l, <- Forall2_map_r.
    eauto using Forall2_impl, expr_pattern_interp_option.
  Qed.

  Definition context_of_clause_pattern (cp : clause_pattern) (f : fact) :=
    match f with
    | fact.meta mf =>
        context_of_args
          (keep_Some (map expr_of_pattern cp.(clause_pattern.args)))
          (keep_Some (map value_of_pattern
                        mf.(meta_fact.pattern).(fact_pattern.args)))
    | fact.normal _ => []
    end.

  Definition context_of_pattern_hyps (hyps : list clause_pattern) (hyps' : list fact) :=
    concat (zip context_of_clause_pattern hyps hyps').

  Lemma interp_clause_pattern_context_right ctx cp f :
    clause_pattern_fact_interp ctx cp f ->
    Forall (fun '(x, v) => map.get ctx x = Some v) (context_of_clause_pattern cp f).
  Proof.
    intros H. destruct f; simpl in *; [contradiction|].
    cbv [clause_pattern.interp] in H. fwd.
    auto using interp_args_context_right, pattern_args_interp_keep_Some.
  Qed.

  Lemma interp_pattern_hyps_context_right ctx hyps hyps' :
    Forall2 (clause_pattern_fact_interp ctx) hyps hyps' ->
    Forall (fun '(x, v) => map.get ctx x = Some v) (context_of_pattern_hyps hyps hyps').
  Proof.
    intros H. apply Forall2_combine in H. rewrite Forall_forall in *.
    intros x Hx. cbv [context_of_pattern_hyps] in *. rewrite in_concat in Hx. fwd.
    cbv [zip] in Hxp0. rewrite in_map_iff in Hxp0. fwd. destruct x1 as [cp f].
    apply H in Hxp0p1. apply interp_clause_pattern_context_right in Hxp0p1.
    rewrite Forall_forall in Hxp0p1. apply Hxp0p1 in Hxp1. assumption.
  Qed.

  Lemma interp_pattern_hyps_context_right_weak ctx hyps hyps' :
    Forall2 (clause_pattern_fact_interp ctx) hyps hyps' ->
    map.extends ctx (map.of_list (context_of_pattern_hyps hyps hyps')).
  Proof.
    intros H. apply interp_pattern_hyps_context_right in H. cbv [map.extends].
    intros. apply of_list_Some_in in H0. rewrite Forall_forall in H.
    apply H in H0. assumption.
  Qed.

  Lemma bare_in_context_clause_pattern ctx x cp f :
    In (expr.var x) (keep_Some (map expr_of_pattern cp.(clause_pattern.args))) ->
    clause_pattern_fact_interp ctx cp f ->
    exists v, In (x, v) (context_of_clause_pattern cp f).
  Proof.
    intros H1 H2. destruct f; simpl in *; [contradiction|].
    cbv [clause_pattern.interp] in H2. fwd.
    eauto using bare_in_context_args, pattern_args_interp_keep_Some.
  Qed.

  Lemma bare_in_context_pattern_hyps ctx x hyps hyps' :
    In (expr.var x)
      (flat_map (fun cp => keep_Some (map expr_of_pattern cp.(clause_pattern.args))) hyps) ->
    Forall2 (clause_pattern_fact_interp ctx) hyps hyps' ->
    exists v, In (x, v) (context_of_pattern_hyps hyps hyps').
  Proof.
    intros H1 H2. apply in_flat_map in H1. fwd. cbv [context_of_pattern_hyps].
    apply Forall2_forget_r_strong in H2. rewrite Forall_forall in H2.
    specialize (H2 _ H1p0). fwd.
    eapply bare_in_context_clause_pattern in H2p1; eauto. fwd.
    eexists. rewrite in_concat. cbv [zip]. eexists. rewrite in_map_iff. eauto.
  Qed.

  Lemma context_of_pattern_hyps_agree ctx hyps hyps' v :
    Forall2 (clause_pattern_fact_interp ctx) hyps hyps' ->
    In (expr.var v)
      (flat_map (fun cp => keep_Some (map expr_of_pattern cp.(clause_pattern.args))) hyps) ->
    agree_on ctx (map.of_list (context_of_pattern_hyps hyps hyps')) v.
  Proof.
    intros H1 H2.
    pose proof bare_in_context_pattern_hyps as H'.
    specialize (H' _ _ _ _ ltac:(eassumption) ltac:(eassumption)). fwd.
    apply in_fst in H'. apply in_of_list_Some_strong in H'. fwd.
    eapply interp_pattern_hyps_context_right_weak in H1; eauto.
    specialize (H1 _ _ H'p0). cbv [agree_on]. rewrite H1, H'p0. reflexivity.
  Qed.

  Definition metas_of : list fact -> list meta_fact :=
    flat_map (fun f => match f with
                       | fact.meta mf => [mf]
                       | fact.normal _ => []
                       end).

  Lemma metas_of_map_meta l :
    metas_of (map fact.meta l) = l.
  Proof. induction l; simpl; congruence. Qed.

  (*the set an interpreted meta rule attaches to its conclusions*)
  Definition step_set (rules : list rule) (hyps' : list fact) (R : rel) : list value -> Prop :=
    fun args => rule.one_step_derives rules (metas_of hyps')
                  {| normal_fact.rel := R; normal_fact.args := args |}.

  Definition eval_rule ctx (hyps' : list fact) (r : rule) : list fact :=
    match r with
    | rule.impl rule_concls _ =>
        map fact.normal (keep_Some (map (subst_in_clause ctx) rule_concls))
    | rule.agg concl_rel agg hyp_rel =>
        match hyps' with
        | fact.meta mf :: rest =>
            match mf.(meta_fact.pattern).(fact_pattern.args) with
            | _ :: _ :: vargs =>
                let args := option_all (map value_of_pattern vargs) in
                let vals := option_all
                              (map (fun f =>
                                      match f with
                                      | fact.normal nf =>
                                          match nf.(normal_fact.args) with
                                          | i :: x_i :: _ => Some (i, x_i)
                                          | _ => None
                                          end
                                      | fact.meta _ => None
                                      end) rest) in
                match args, vals with
                | Some args, Some vals =>
                    [fact.normal {| normal_fact.rel := concl_rel;
                                   normal_fact.args := interp_agg agg vals :: args |}]
                | _, _ => []
                end
            | _ => []
            end
        | _ => []
        end
    end.

  Definition eval_meta_rule (rules : list rule) ctx (hyps' : list fact) (mr : meta_rule) : list fact :=
    map (fun pat => fact.meta {| meta_fact.pattern := pat;
                                meta_fact.set := step_set rules hyps' pat.(fact_pattern.rel) |})
      (keep_Some (map (subst_in_clause_pattern ctx) mr.(meta_rule.concls))).

  Definition matches_ctx (r : rule) (hyps' : list fact) ctx : Prop :=
    match r with
    | rule.impl _ rule_hyps => Forall2 (clause_fact_interp ctx) rule_hyps hyps'
    | rule.agg _ _ _ => True
    end.
  Hint Unfold matches_ctx : core.

  Definition meta_matches_ctx (mr : meta_rule) (hyps' : list fact) ctx : Prop :=
    Forall2 (clause_pattern_fact_interp ctx) mr.(meta_rule.hyps) hyps'.
  Hint Unfold meta_matches_ctx : core.

  Lemma option_all_map_value_of_exactly args :
    option_all (map value_of_pattern (map value_pattern.exactly args)) = Some args.
  Proof. induction args; simpl; [reflexivity|]. rewrite IHargs. reflexivity. Qed.

  Lemma eval_rule_complete r nf hyps :
    rule.interp r nf hyps ->
    exists ctx,
      In (fact.normal nf) (eval_rule ctx hyps r) /\
        matches_ctx r hyps ctx.
  Proof.
    invert 1.
    - exists ctx. cbv [eval_rule].
      apply Exists_exists in H0. fwd.
      split; auto using clause_fact_interp_normal.
      apply in_map. apply in_keep_Some. apply in_map_iff.
      eauto using subst_in_clause_complete.
    - exists map.empty. cbv [eval_rule]. simpl. split; [|exact I].
      rewrite option_all_map_value_of_exactly.
      rewrite map_map. erewrite map_ext.
      2: { intros (?, ?). reflexivity. }
      rewrite option_all_map_Some. simpl. auto.
  Qed.

  Lemma eval_meta_rule_complete rules mr mf mhyps :
    meta_rule.interp rules mr mf mhyps ->
    exists ctx f',
      In f' (eval_meta_rule rules ctx (map fact.meta mhyps) mr) /\
        fact.equiv (fact.meta mf) f' /\
        meta_matches_ctx mr (map fact.meta mhyps) ctx.
  Proof.
    cbv [meta_rule.interp meta_rule.pattern_interp]. intros H. fwd.
    exists ctx. eexists. ssplit.
    - cbv [eval_meta_rule]. apply in_map. apply in_keep_Some. apply in_map_iff.
      eauto using subst_in_clause_pattern_complete.
    - cbv [fact.equiv]. etransitivity; [eassumption|].
      cbv [meta_fact.equiv step_set]. simpl. rewrite metas_of_map_meta.
      auto.
    - auto using clause_pattern_fact_interp_meta.
  Qed.

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

  Definition ctx_of_rule (r : rule) (hyps' : list fact) : context :=
    match r with
    | rule.impl _ rule_hyps => map.of_list (context_of_hyps rule_hyps hyps')
    | rule.agg _ _ _ => map.empty
    end.

  Definition ctx_of_meta_rule (mr : meta_rule) (hyps' : list fact) : context :=
    map.of_list (context_of_pattern_hyps mr.(meta_rule.hyps) hyps').

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

  Lemma subst_in_clause_ctxs_agree ctx ctx' c :
    Forall (agree_on ctx ctx') (clause.vars c) ->
    subst_in_clause ctx c = subst_in_clause ctx' c.
  Proof.
    intros H. cbv [subst_in_clause]. f_equal. f_equal. apply map_ext_in.
    intros. cbv [clause.vars] in H. apply Forall_flat_map in H.
    rewrite Forall_forall in H. specialize (H _ ltac:(eassumption)).
    apply subst_in_expr_ctxs_agree. assumption.
  Qed.

  Lemma subst_in_expr_pattern_ctxs_agree ctx ctx' ep :
    Forall (agree_on ctx ctx') (expr_pattern.vars ep) ->
    subst_in_expr_pattern ctx ep = subst_in_expr_pattern ctx' ep.
  Proof.
    destruct ep; simpl; intros H; [|reflexivity].
    erewrite subst_in_expr_ctxs_agree by eassumption. reflexivity.
  Qed.

  Lemma subst_in_clause_pattern_ctxs_agree ctx ctx' cp :
    Forall (agree_on ctx ctx') (clause_pattern.vars cp) ->
    subst_in_clause_pattern ctx cp = subst_in_clause_pattern ctx' cp.
  Proof.
    intros H. cbv [subst_in_clause_pattern]. f_equal. f_equal. apply map_ext_in.
    intros. cbv [clause_pattern.vars] in H. apply Forall_flat_map in H.
    rewrite Forall_forall in H. specialize (H _ ltac:(eassumption)).
    apply subst_in_expr_pattern_ctxs_agree. assumption.
  Qed.

  Lemma eval_rule_ctxs_agree ctx ctx' hyps' r :
    (forall v, In v (rule.all_vars r) -> agree_on ctx ctx' v) ->
    eval_rule ctx hyps' r = eval_rule ctx' hyps' r.
  Proof.
    destruct r; simpl; intros H; [|reflexivity].
    f_equal. f_equal. apply map_ext_in. intros c Hc.
    apply subst_in_clause_ctxs_agree.
    apply Forall_forall. intros v Hv. apply H.
    cbv [rule.all_vars rule.concl_vars]. apply in_app_iff. left.
    apply in_flat_map. eauto.
  Qed.

  Lemma eval_meta_rule_ctxs_agree rules ctx ctx' hyps' mr :
    (forall v, In v (meta_rule.all_vars mr) -> agree_on ctx ctx' v) ->
    eval_meta_rule rules ctx hyps' mr = eval_meta_rule rules ctx' hyps' mr.
  Proof.
    intros H. cbv [eval_meta_rule]. f_equal. f_equal. apply map_ext_in.
    intros cp Hcp. apply subst_in_clause_pattern_ctxs_agree.
    apply Forall_forall. intros v Hv. apply H.
    cbv [meta_rule.all_vars meta_rule.concl_vars]. apply in_app_iff. left.
    apply in_flat_map. eauto.
  Qed.

  Lemma is_bottomup_ctx_agree ctx r hyps' v :
    rule.is_bottomup r ->
    matches_ctx r hyps' ctx ->
    In v (rule.all_vars r) ->
    agree_on ctx (ctx_of_rule r hyps') v.
  Proof.
    intros Hgood Hmatch Hv.
    cbv [rule.is_bottomup] in Hgood. apply Hgood in Hv.
    destruct r; simpl in *.
    - eauto using context_of_hyps_agree.
    - contradiction.
  Qed.

  Lemma meta_is_bottomup_ctx_agree ctx mr hyps' v :
    meta_rule.is_bottomup mr ->
    meta_matches_ctx mr hyps' ctx ->
    In v (meta_rule.all_vars mr) ->
    agree_on ctx (ctx_of_meta_rule mr hyps') v.
  Proof.
    intros Hgood Hmatch Hv.
    cbv [meta_rule.is_bottomup] in Hgood. apply Hgood in Hv.
    eapply context_of_pattern_hyps_agree; [eassumption|].
    cbv [meta_rule.hyp_args] in Hv. rewrite in_flat_map in *. fwd.
    eexists. split; [eassumption|]. apply in_keep_Some.
    apply in_map_iff. eexists. split; [|eassumption]. reflexivity.
  Qed.

  Definition possible_hyps (r : rule) (facts : list fact) : list (list fact) :=
    match r with
    | rule.impl _ rule_hyps => choose_any_n (length rule_hyps) facts
    | rule.agg _ _ _ => flat_map (fun n => choose_any_n n facts) (seq 1 (S (length facts)))
    end.

  Definition possible_meta_hyps (mr : meta_rule) (facts : list fact) : list (list fact) :=
    choose_any_n (length mr.(meta_rule.hyps)) facts.

  Lemma rule_interp_possible_hyps r nf hyps facts :
    incl hyps facts ->
    rule.interp r nf hyps ->
    In hyps (possible_hyps r facts).
  Proof.
    intros Hincl. invert 1.
    - cbv [possible_hyps]. apply choose_n_spec; [|exact Hincl].
      rewrite length_map. eauto using Forall2_length, Forall2_flip.
    - cbv [possible_hyps]. apply in_flat_map.
      eexists (Datatypes.S (length vals)). split.
      + apply in_seq. apply incl_cons_inv in Hincl. fwd.
        apply NoDup_incl_length in Hinclp1.
        -- rewrite length_map in Hinclp1. lia.
        -- apply Finite.Injective_map_NoDup. 2: cbv [is_list_set] in *; fwd; auto.
           cbv [Finite.Injective]. intros (?, ?) (?, ?). congruence.
      + apply choose_n_spec.
        -- simpl. rewrite length_map. reflexivity.
        -- assumption.
  Qed.

  Lemma meta_rule_interp_possible_hyps rules mr mf mhyps facts :
    incl (map fact.meta mhyps) facts ->
    meta_rule.interp rules mr mf mhyps ->
    In (map fact.meta mhyps) (possible_meta_hyps mr facts).
  Proof.
    cbv [meta_rule.interp meta_rule.pattern_interp possible_meta_hyps].
    intros Hincl H. fwd. apply choose_n_spec; [|assumption].
    rewrite length_map. apply Forall2_length in Hp0p1.
    rewrite length_map in Hp0p1. congruence.
  Qed.

  Definition step_rule (r : rule) (facts : list fact) : list fact :=
    flat_map
      (fun hyps' => eval_rule (ctx_of_rule r hyps') hyps' r)
      (possible_hyps r facts).

  Definition step_meta_rule (rules : list rule) (mr : meta_rule) (facts : list fact) : list fact :=
    flat_map
      (fun hyps' => eval_meta_rule rules (ctx_of_meta_rule mr hyps') hyps' mr)
      (possible_meta_hyps mr facts).

  Definition step_program (p : program) (facts : list fact) : list fact :=
    flat_map (fun r => step_rule r facts) p.(program.rules) ++
      flat_map (fun mr => step_meta_rule p.(program.rules) mr facts)
        p.(program.meta_rules).

  Lemma step_rule_complete r nf hyps facts :
    rule.is_bottomup r ->
    incl hyps facts ->
    rule.interp r nf hyps ->
    In (fact.normal nf) (step_rule r facts).
  Proof.
    intros Hgood Hincl Himpl.
    cbv [step_rule]. apply in_flat_map. eexists. split.
    - eapply rule_interp_possible_hyps; eassumption.
    - destruct (eval_rule_complete _ _ _ Himpl) as [ctx [Hctx Hmatch]].
      erewrite eval_rule_ctxs_agree; [exact Hctx|].
      intros v Hv. symmetry. eapply is_bottomup_ctx_agree; eassumption.
  Qed.

  Lemma step_meta_rule_complete rules mr mf mhyps facts :
    meta_rule.is_bottomup mr ->
    incl (map fact.meta mhyps) facts ->
    meta_rule.interp rules mr mf mhyps ->
    exists f',
      In f' (step_meta_rule rules mr facts) /\ fact.equiv (fact.meta mf) f'.
  Proof.
    intros Hgood Hincl Himpl.
    destruct (eval_meta_rule_complete _ _ _ _ Himpl) as [ctx [f' [Hctx [Heq Hmatch]]]].
    exists f'. split; [|exact Heq].
    cbv [step_meta_rule]. apply in_flat_map. eexists. split.
    - eapply meta_rule_interp_possible_hyps; eassumption.
    - erewrite eval_meta_rule_ctxs_agree; [exact Hctx|].
      intros v Hv. symmetry. eapply meta_is_bottomup_ctx_agree; eassumption.
  Qed.

  Lemma step_program_complete p f hyps facts :
    Forall rule.is_bottomup p.(program.rules) ->
    Forall meta_rule.is_bottomup p.(program.meta_rules) ->
    incl hyps facts ->
    program.interp_step p f hyps ->
    exists f', In f' (step_program p facts) /\ fact.equiv f f'.
  Proof.
    intros Hgood Hmgood Hincl H. rewrite Forall_forall in Hgood, Hmgood.
    cbv [step_program]. invert H; fwd.
    - exists (fact.normal f0). split; [|reflexivity].
      apply in_or_app. left. apply in_flat_map.
      eauto using step_rule_complete.
    - edestruct step_meta_rule_complete as [f' [Hin Heq]]; eauto.
      exists f'. split; [|assumption].
      apply in_or_app. right. apply in_flat_map. eauto.
  Qed.

  Definition eval n (p : program) start :=
    Nat.iter n (fun fs => step_program p fs ++ fs) start.

  (*a bit conservative*)
  Definition count_rels p := S (length (rel_graph p)).

  Definition eval_dag p start := eval (count_rels p) p start.

  Lemma possible_hyps_mono r fs1 fs2 :
    incl fs1 fs2 ->
    length fs1 <= length fs2 ->
    incl (possible_hyps r fs1) (possible_hyps r fs2).
  Proof. intros Hincl Hlen. destruct r; simpl; auto with incl. Qed.
  Hint Resolve possible_hyps_mono : incl.

  Lemma possible_meta_hyps_mono mr fs1 fs2 :
    incl fs1 fs2 ->
    incl (possible_meta_hyps mr fs1) (possible_meta_hyps mr fs2).
  Proof. intros Hincl. cbv [possible_meta_hyps]. auto with incl. Qed.
  Hint Resolve possible_meta_hyps_mono : incl.

  Lemma step_rule_mono r fs1 fs2 :
    incl fs1 fs2 ->
    length fs1 <= length fs2 ->
    incl (step_rule r fs1) (step_rule r fs2).
  Proof. intros. cbv [step_rule]. auto with incl. Qed.
  Hint Resolve step_rule_mono : incl.

  Lemma step_meta_rule_mono rules mr fs1 fs2 :
    incl fs1 fs2 ->
    incl (step_meta_rule rules mr fs1) (step_meta_rule rules mr fs2).
  Proof. intros. cbv [step_meta_rule]. auto with incl. Qed.
  Hint Resolve step_meta_rule_mono : incl.

  Lemma step_program_mono p fs1 fs2 :
    incl fs1 fs2 ->
    length fs1 <= length fs2 ->
    incl (step_program p fs1) (step_program p fs2).
  Proof. intros. cbv [step_program]. auto with incl. Qed.
  Hint Resolve step_program_mono : incl.

  Lemma eval_mono n m p start :
    n <= m ->
    incl (eval n p start) (eval m p start).
  Proof. induction 1; simpl; auto with incl. Qed.

  Lemma eval_start_incl n p start :
    incl start (eval n p start).
  Proof. apply eval_mono with (n := 0). lia. Qed.

  Lemma eval_complete p Q n start :
    Forall rule.is_bottomup p.(program.rules) ->
    Forall meta_rule.is_bottomup p.(program.meta_rules) ->
    (forall x, Q x <-> In x start) ->
    forall f,
      program.interp p Q f ->
      (exists f', In f' (eval n p start) /\ fact.equiv f f') \/
        (exists l, path (rel_graph p) (fact.rel f) l /\ n <= length l).
  Proof.
    intros Hp Hmp HQ. induction n.
    - intros f Hf. invert Hf.
      + left. exists f. split; [apply HQ; assumption | reflexivity].
      + right. exists nil. simpl. split; [constructor|lia].
    - intros f Hf. invert Hf.
      + left. exists f. split; [|reflexivity].
        apply eval_start_incl. apply HQ. assumption.
      + eapply Forall_impl in H0.
        2: { intros x Hx. apply IHn in Hx. exact Hx. }
        apply Forall_or in H0. destruct H0 as [H0|H0].
        * left. apply Forall_exists_r_Forall2 in H0. fwd.
          eapply program.interp_step_ext_hyps in H.
          2: { eapply Forall2_impl; [eassumption|]. simpl. intros. fwd. eassumption. }
          eapply step_program_complete in H; try assumption.
          { fwd. eexists. simpl. rewrite in_app_iff. eauto. }
          apply Forall2_forget_l in H0. intros y Hy. rewrite Forall_forall in H0.
          apply H0 in Hy. fwd. assumption.
        * right. rewrite Exists_exists in H0. fwd. eexists (_ :: _). split.
          { constructor; [|eassumption]. apply rel_graph_spec in H.
            rewrite Forall_forall in H. apply H. assumption. }
          simpl. lia.
  Qed.

  Lemma eval_dag_complete p Q start :
    Forall rule.is_bottomup p.(program.rules) ->
    Forall meta_rule.is_bottomup p.(program.meta_rules) ->
    (forall x, Q x <-> In x start) ->
    dag (rel_graph p) ->
    forall f,
      program.interp p Q f ->
      exists f', In f' (eval_dag p start) /\ fact.equiv f f'.
  Proof.
    intros Hp Hmp HQ Hdag f Hf.
    eapply eval_complete in Hf; eauto. destruct Hf as [Hf|Hf]; eauto.
    fwd. eapply dag_paths_short in Hfp0; eauto. cbv [count_rels] in *. lia.
  Qed.

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
    - pose proof (eqb_spec v v0) as Hv. cbv [eqb] in Hv.
      destruct (var_eqb v v0); subst; congruence.
    - pose proof (eqb_spec f f0) as Hf. cbv [eqb] in Hf.
      destruct (fn_eqb f f0); simpl; [subst|congruence].
      pose proof (list_eqb_ok_strong args H args0) as Hl. cbv [eqb] in Hl.
      destruct (list_eqb args args0); [subst|]; congruence.
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
                                match option_all (map expr_of_pattern stuff),
                                  option_all (map expr_of_pattern stuff') with
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
    option_all (map expr_of_pattern ps) = Some es ->
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
    destruct (option_all (map expr_of_pattern stuff)) as [es|] eqn:Es; [|discriminate].
    destruct (option_all (map expr_of_pattern stuff')) as [es'|] eqn:Es'; [|discriminate].
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
