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

  Definition eval_rule ctx (hyps' : list fact) (r : rule) : list fact :=
    match r with
    | rule.impl rule_concls _ =>
        map fact.normal (keep_Some (map (subst_in_clause ctx) rule_concls))
    | rule.agg concl_rel agg hyp_rel =>
        match hyps' with
        | fact.meta mf :: rest =>
            match mf.(meta_fact.pattern).(fact_pattern.args) with
            | _ :: _ :: vargs =>
                let args := option_all (map value_pattern.value_of vargs) in
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

  Definition eval_meta_rule set ctx (mr : meta_rule) : list meta_fact :=
    map (fun pat => meta_fact.mk pat set)
      (keep_Some (map (subst_in_clause_pattern ctx) mr.(meta_rule.concls))).

  Definition matches_ctx (r : rule) (hyps' : list fact) ctx : Prop :=
    match r with
    | rule.impl _ rule_hyps => exists nfs,
        hyps' = map fact.normal nfs /\
        Forall2 (clause.interp ctx) rule_hyps nfs
    | rule.agg _ _ _ => True
    end.
  Hint Unfold matches_ctx : core.

  Definition meta_matches_ctx (mr : meta_rule) (hyps' : list meta_fact) ctx : Prop :=
    Forall2 (clause_pattern.interp ctx) mr.(meta_rule.hyps) (map meta_fact.pattern hyps').
  Hint Unfold meta_matches_ctx : core.

  Lemma eval_rule_complete r nf hyps :
    rule.interp r nf hyps ->
    exists ctx,
      In (fact.normal nf) (eval_rule ctx hyps r) /\
        matches_ctx r hyps ctx.
  Proof.
    invert 1.
    - exists ctx. cbv [eval_rule].
      apply Exists_exists in H0. fwd. split.
      + apply in_map. apply in_keep_Some. apply in_map_iff.
        eauto using subst_in_clause_complete.
      + cbv [matches_ctx]. eauto.
    - exists map.empty. cbv [eval_rule]. simpl. split; [|exact I].
      rewrite map_map. simpl. rewrite option_all_map_Some.
      rewrite map_map. erewrite map_ext.
      2: { intros (?, ?). reflexivity. }
      rewrite option_all_map_Some. simpl. auto.
  Qed.

  Lemma eval_meta_rule_complete rules mr mf mhyps :
    meta_rule.interp rules mr mf mhyps ->
    exists ctx vals,
      In mf (eval_meta_rule vals ctx mr) /\
        Forall (fun args => rule.one_step_derives rules mhyps {| normal_fact.rel := meta_fact.rel mf; normal_fact.args := args |}) vals /\
        meta_matches_ctx mr mhyps ctx.
  Proof.
    intros [Hpat Hset]. cbv [meta_rule.pattern_interp] in Hpat. fwd.
    exists ctx, (map.keys mf.(meta_fact.set)). ssplit.
    - cbv [eval_meta_rule]. apply in_map_iff. eexists.
      split; [apply meta_fact.mk_keys|]. apply in_keep_Some. apply in_map_iff.
      eauto using subst_in_clause_pattern_complete.
    - apply Forall_forall. intros args Hargs. apply Hset; [|exact Hargs].
      split; [reflexivity | apply meta_fact.contains_matches, Hargs].
    - exact Hpatp1.
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
    | rule.impl _ rule_hyps => map.of_list (context_of_hyps rule_hyps (flat_map fact.normal_facts hyps'))
    | rule.agg _ _ _ => map.empty
    end.

  Definition ctx_of_meta_rule (mr : meta_rule) (hyps' : list meta_fact) : context :=
    map.of_list (context_of_pattern_hyps mr.(meta_rule.hyps)
                   (map meta_fact.pattern hyps')).

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

  Lemma eval_meta_rule_same_set set set' ctx mr :
    same_set set set' ->
    eval_meta_rule set ctx mr = eval_meta_rule set' ctx mr.
  Proof.
    intros H. cbv [eval_meta_rule]. apply map_ext. intros pat.
    apply meta_fact.mk_same_set, H.
  Qed.

  Lemma eval_meta_rule_ctxs_agree rules ctx ctx' mr :
    (forall v, In v (meta_rule.all_vars mr) -> agree_on ctx ctx' v) ->
    eval_meta_rule rules ctx mr = eval_meta_rule rules ctx' mr.
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
    - fwd. rewrite flat_map_map. simpl. rewrite <- map_is_flat_map. rewrite map_id.
      eauto using context_of_hyps_agree.
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

  Definition possible_meta_hyps (mr : meta_rule) (facts : list fact) : list (list meta_fact) :=
    choose_any_n (length mr.(meta_rule.hyps)) (flat_map fact.meta_facts facts).

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
    In mhyps (possible_meta_hyps mr facts).
  Proof.
    cbv [meta_rule.interp meta_rule.pattern_interp possible_meta_hyps].
    intros Hincl H. fwd. apply choose_n_spec.
    - apply Forall2_length in Hp0p1.
      rewrite length_map in Hp0p1. congruence.
    - cbv [incl] in *. setoid_rewrite in_map_iff in Hincl. intros f Hf.
      rewrite in_flat_map. setoid_rewrite fact.in_meta_facts. eauto 6.
  Qed.

  Definition step_rule (r : rule) (facts : list fact) : list fact :=
    flat_map
      (fun hyps' => eval_rule (ctx_of_rule r hyps') hyps' r)
      (possible_hyps r facts).

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

  Definition step_rules rules facts :=
    flat_map (fun r => step_rule r facts) rules.

  Definition eval_one_step_derives rules mfs :=
    step_rules rules
      (map fact.meta mfs ++ map fact.normal (flat_map meta_fact.normal_facts mfs)).

  Lemma eval_one_step_derives_complete rules mfs nf :
    Forall rule.is_bottomup rules ->
    rule.one_step_derives rules mfs nf ->
    In (fact.normal nf) (eval_one_step_derives rules mfs).
  Proof.
    intros Hgood (hyps & Hex & Himp). rewrite Forall_forall in Hgood, Himp.
    rewrite Exists_exists in Hex. destruct Hex as (r & Hr & Hinterp).
    cbv [eval_one_step_derives step_rules]. apply in_flat_map.
    exists r. split; [exact Hr|].
    eapply step_rule_complete; [auto | | eassumption].
    intros f Hf. apply Himp in Hf.
    cbv [fact.implied_by_mfs] in Hf. rewrite Exists_exists in Hf.
    destruct Hf as (mf & Hmf & Himpl). apply in_app_iff.
    destruct f as [nf0 | m].
    - right. apply in_map, in_flat_map. exists mf.
      split; [exact Hmf | apply meta_fact.in_normal_facts, Himpl].
    - left. cbv [fact.implied_by_mf] in Himpl. subst m. apply in_map, Hmf.
  Qed.

  Definition possible_concl_sets fs :=
    subsets (map normal_fact.args (flat_map fact.normal_facts fs)).

  Definition step_meta_rule (rules : list rule) (mr : meta_rule) (facts : list fact) : list meta_fact :=
    flat_map
      (fun hyps' =>
         flat_map
           (fun set => eval_meta_rule set (ctx_of_meta_rule mr hyps') mr)
           (possible_concl_sets (eval_one_step_derives rules hyps')))
      (possible_meta_hyps mr facts).

  Lemma step_meta_rule_complete rules mr mf mhyps facts :
    Forall rule.is_bottomup rules ->
    meta_rule.is_bottomup mr ->
    incl (map fact.meta mhyps) facts ->
    meta_rule.interp rules mr mf mhyps ->
    In mf (step_meta_rule rules mr facts).
  Proof.
    intros Hrules Hgood Hincl Himpl.
    destruct (eval_meta_rule_complete _ _ _ _ Himpl) as (ctx & vals & Hin & Hvals & Hmatch).
    rewrite Forall_forall in Hvals.
    cbv [step_meta_rule]. apply in_flat_map. exists mhyps. split.
    { eapply meta_rule_interp_possible_hyps; eassumption. }
    cbv [possible_concl_sets]. eapply in_flat_map_subsets with (s := vals).
    { intros. apply eval_meta_rule_same_set. assumption. }
    { intros args Hargs. apply Hvals in Hargs.
      apply eval_one_step_derives_complete in Hargs; [|assumption].
      apply in_map_iff. eexists. split.
      2: { apply in_flat_map. eexists.
           split; [eassumption | apply fact.in_normal_facts; reflexivity]. }
      reflexivity. }
    erewrite eval_meta_rule_ctxs_agree with (ctx' := ctx); [exact Hin|].
    intros v Hv. symmetry. eapply meta_is_bottomup_ctx_agree; eassumption.
  Qed.

  Definition step_meta_rules (p : program) (facts : list fact) : list meta_fact :=
    flat_map (fun mr => step_meta_rule p.(program.rules) mr facts) p.(program.meta_rules).

  Definition step_program (p : program) (facts : list fact) : list fact :=
    step_rules p.(program.rules) facts ++
      map fact.meta (step_meta_rules p facts).

  Lemma step_program_complete p f hyps facts :
    Forall rule.is_bottomup p.(program.rules) ->
    Forall meta_rule.is_bottomup p.(program.meta_rules) ->
    incl hyps facts ->
    program.interp_step p f hyps ->
    In f (step_program p facts).
  Proof.
    intros Hgood Hmgood Hincl H. pose proof Hgood as Hgood'.
    rewrite Forall_forall in Hgood, Hmgood.
    cbv [step_program]. invert H; fwd.
    - apply in_or_app. left. cbv [step_rules]. apply in_flat_map.
      eauto using step_rule_complete.
    - apply in_or_app. right. apply in_map. cbv [step_meta_rules]. apply in_flat_map.
      eexists. split; [eassumption|].
      eapply step_meta_rule_complete; eauto.
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

  Lemma step_rules_mono rules fs1 fs2 :
    incl fs1 fs2 ->
    length fs1 <= length fs2 ->
    incl (step_rules rules fs1) (step_rules rules fs2).
  Proof. intros. cbv [step_rules]. auto with incl. Qed.
  Hint Resolve step_rules_mono : incl.

  Lemma step_meta_rules_mono p fs1 fs2 :
    incl fs1 fs2 ->
    incl (step_meta_rules p fs1) (step_meta_rules p fs2).
  Proof. intros. cbv [step_meta_rules]. auto with incl. Qed.
  Hint Resolve step_meta_rules_mono : incl.

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
      In f (eval n p start) \/
        (exists l, path (rel_graph p) (fact.rel f) l /\ n <= length l).
  Proof.
    intros Hp Hmp HQ. induction n.
    - intros f Hf. invert Hf.
      + left. apply HQ. assumption.
      + right. exists nil. simpl. split; [constructor|lia].
    - intros f Hf. invert Hf.
      + left. apply eval_start_incl. apply HQ. assumption.
      + eapply Forall_impl in H0.
        2: { intros x Hx. apply IHn in Hx. exact Hx. }
        apply Forall_or in H0. destruct H0 as [H0|H0].
        * left. simpl. rewrite in_app_iff. left.
          eapply step_program_complete; try assumption;
            [rewrite Forall_forall in H0; exact H0 | eassumption].
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
      In f (eval_dag p start).
  Proof.
    intros Hp Hmp HQ Hdag f Hf.
    eapply eval_complete in Hf; eauto. destruct Hf as [Hf|Hf]; eauto.
    fwd. eapply dag_paths_short in Hfp0; eauto. cbv [count_rels] in *. lia.
  Qed.
End __.
