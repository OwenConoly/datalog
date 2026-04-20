From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Permutation.


From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics.

From Datalog Require Import Datalog Map Tactics Fp List Dag.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List.

Import ListNotations.

Section __.
  Context {rel var fn aggregator T : Type}.
  Context `{sig : signature fn aggregator T} `{query_sig : query_signature rel}.
  Context {context : map.map var T} {context_ok : map.ok context}.
  Context {var_eqb : var -> var -> bool} {var_eqb_spec :  forall x0 y0 : var, BoolSpec (x0 = y0) (x0 <> y0) (var_eqb x0 y0)}.

  Local Notation expr := (expr var fn).
  Local Notation rule := (rule rel var fn aggregator).
  Local Notation clause := (clause rel var fn).
  Local Notation meta_clause := (meta_clause rel var fn).
  Local Notation fact:= (fact rel T).

  Implicit Type r : rule.
  Implicit Type ctx : context.

  (* Print list_prod. (*why is this not defined in terms of flat_map?*) *)
  Definition edges_of_rule r :=
    list_prod (concl_rels r) (hyp_rels r).

  Definition rel_graph := flat_map edges_of_rule.

  Lemma rel_graph_app p1 p2 :
    rel_graph (p1 ++ p2) = rel_graph p1 ++ rel_graph p2.
  Proof. cbv [rel_graph]. apply flat_map_app. Qed.

  Definition diff_rels (p1 p2 : list rule) :=
    disjoint_lists (flat_map concl_rels p1) (flat_map concl_rels p2).

  Lemma diff_rels_app_r p p1 p2 :
    diff_rels p p1 ->
    diff_rels p p2 ->
    diff_rels p (p1 ++ p2).
  Proof.
    intros. cbv [diff_rels]. rewrite flat_map_app.
    apply disjoint_lists_app_r; auto.
  Qed.

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

  Lemma edges_of_rule_spec env r f hyps :
    rule_impl env r f hyps ->
    Forall (fun hyp => In (rel_of f, rel_of hyp) (edges_of_rule r)) hyps.
  Proof.
    intros H. pose proof H as H'.
    apply rule_impl_concl_relname_in in H. apply rule_impl_hyp_relname_in in H'.
    eapply Forall_impl; [|eassumption]. simpl. intros.
    cbv [edges_of_rule]. Search list_prod. apply in_prod_iff. auto.
  Qed.

  Lemma rel_graph_spec env p f hyps :
    Exists (fun r => rule_impl env r f hyps) p ->
    Forall (fun hyp => In (rel_of f, rel_of hyp) (rel_graph p)) hyps.
  Proof.
    intros H. apply Exists_exists in H. fwd. apply edges_of_rule_spec in Hp1.
    eapply Forall_impl; [|eassumption]. simpl. intros. cbv [rel_graph].
    apply in_flat_map. eauto.
  Qed.

  Fixpoint subst_in_expr ctx e : option T :=
    match e with
    | var_expr v => map.get ctx v
    | fun_expr f args => option_coalesce (option_map (interp_fun f) (option_all (map (subst_in_expr ctx) args)))
    end.

  Hint Constructors interp_expr : core.
  Lemma subst_in_expr_sound ctx e v :
    subst_in_expr ctx e = Some v ->
    interp_expr ctx e v.
  Proof.
    revert v. induction e; simpl; intros; eauto.
    apply option_coalesce_Some, option_map_Some in H0. fwd.
    apply option_all_Forall2 in H0p0. econstructor; eauto.
    rewrite <- Forall2_map_l in H0p0. eapply Forall2_impl_strong; [|eassumption].
    simpl. intros. rewrite Forall_forall in H. eauto.
  Qed.

  Lemma subst_in_expr_complete ctx e v :
    interp_expr ctx e v ->
    subst_in_expr ctx e = Some v.
  Proof.
    revert v. induction e; invert 1; simpl; eauto.
    erewrite Forall2_option_all.
    2: { rewrite <- Forall2_map_l. eapply Forall2_impl_strong; [|eassumption].
         rewrite Forall_forall in H. eauto. }
    simpl. rewrite H5. reflexivity.
  Qed.

  Definition subst_in_clause ctx (c : clause) :=
    option_map (normal_fact c.(clause_rel))
      (option_all (map (subst_in_expr ctx) c.(clause_args))).

  Lemma subst_in_clause_sound ctx f f' :
    subst_in_clause ctx f = Some f' ->
    interp_clause ctx f f'.
  Proof.
    cbv [subst_in_clause]. intros H. apply option_map_Some in H.
    fwd. apply option_all_Forall2 in Hp0. cbv [interp_clause].
    rewrite <- Forall2_map_l in Hp0. eexists. split; [|reflexivity].
    eapply Forall2_impl; [|eassumption].
    simpl. auto using subst_in_expr_sound.
  Qed.

  Lemma subst_in_clause_complete ctx c f :
    interp_clause ctx c f ->
    subst_in_clause ctx c = Some f.
  Proof.
    intros. repeat invert_stuff. cbv [subst_in_clause].
    erewrite Forall2_option_all; [reflexivity|].
    rewrite <- Forall2_map_l. eapply Forall2_impl; [|eassumption].
    auto using subst_in_expr_complete.
  Qed.

  Lemma subst_in_expr_mono ctx ctx' e v :
    map.extends ctx' ctx ->
    subst_in_expr ctx e = Some v ->
    subst_in_expr ctx' e = Some v.
  Proof.
    intros H. revert v. induction e; simpl; intros; eauto. rewrite Forall_forall in H0.
    apply option_coalesce_Some, option_map_Some in H1. fwd.
    apply option_all_Forall2 in H1p0. erewrite Forall2_option_all.
    2: { rewrite <- Forall2_map_l in *. eapply Forall2_impl_strong; [|eassumption].
         simpl. eauto. }
    simpl. rewrite H1p1. reflexivity.
  Qed.

  Lemma subst_expr_with_vars ctx ctx' e :
    Forall (fun v => map.get ctx v <> None) (vars_of_expr e) ->
    map.extends ctx' ctx ->
    subst_in_expr ctx e = subst_in_expr ctx' e.
  Proof.
    induction e; simpl; intros; invert_list_stuff.
    - destruct (map.get _ _) eqn:E; try congruence. symmetry. auto.
    - rewrite Forall_flat_map in H0. f_equal. f_equal. f_equal. apply map_ext_in.
      rewrite Forall_forall in *. eauto.
  Qed.

  Definition context_of_args (args : list expr) (args' : list T) :=
    concat (zip (fun arg arg' =>
                   match arg with
                   | var_expr v => [(v, arg')]
                   | _ => []
                   end) args args').

  Definition context_of_clause (c : clause) (f : fact) :=
    match f with
    | normal_fact _ args =>
        context_of_args c.(clause_args) args
    | meta_fact _ _ _ => []
    end.

  Definition context_of_hyps (hyps : list clause) (hyps' : list fact) :=
    concat (zip context_of_clause hyps hyps').

  Lemma bare_in_context_args ctx x args args' :
    In (var_expr x) args ->
    Forall2 (interp_expr ctx) args args' ->
    exists v, In (x, v) (context_of_args args args').
  Proof.
    intros H1 H2. cbv [context_of_args]. apply Forall2_forget_r_strong in H2.
    rewrite Forall_forall in H2. specialize (H2 _ H1). fwd.
    exists y. cbv [zip]. rewrite in_concat. eexists. rewrite in_map_iff. split.
    { eexists. split; [|eassumption]. reflexivity. }
    simpl. auto.
  Qed.

  Lemma bare_in_context_fact ctx x c f :
    In (var_expr x) c.(clause_args) ->
    interp_clause ctx c f ->
    exists v, In (x, v) (context_of_clause c f).
  Proof.
    intros H1 H2. cbv [context_of_clause]. invert_stuff.
    eapply bare_in_context_args; eassumption.
  Qed.

  Lemma bare_in_context_hyps ctx x hyps hyps' :
    In (var_expr x) (flat_map clause_args hyps) ->
    Forall2 (interp_clause ctx) hyps hyps' ->
    exists v, In (x, v) (context_of_hyps hyps hyps').
  Proof.
    intros H1 H2. apply in_flat_map in H1. fwd. cbv [context_of_hyps].
    apply Forall2_forget_r_strong in H2. rewrite Forall_forall in H2.
    specialize (H2 _ H1p0). fwd. eapply bare_in_context_fact in H2p1; eauto. fwd.
    eexists. rewrite in_concat. cbv [zip]. eexists. rewrite in_map_iff. split.
    { eexists. split; [|eassumption]. reflexivity. }
    eassumption.
  Qed.

  Lemma interp_args_context_right ctx args args' :
    Forall2 (interp_expr ctx) args args' ->
    Forall (fun '(x, v) => map.get ctx x = Some v) (context_of_args args args').
  Proof.
    intros H. apply Forall2_combine in H. rewrite Forall_forall in *.
    intros [x v] Hx. cbv [context_of_clause] in Hx. apply in_concat in Hx. fwd.
    cbv [zip] in Hxp0. apply in_map_iff in Hxp0. fwd. apply H in Hxp0p1.
    do 2 (destruct_one_match_hyp; simpl in Hxp1; try contradiction).
    destruct Hxp1; try contradiction. invert H0. invert Hxp0p1. assumption.
  Qed.

  Lemma context_of_args_agree_on ctx args args' v :
    Forall2 (interp_expr ctx) args args' ->
    In (var_expr v) args ->
    agree_on ctx (map.of_list (context_of_args args args')) v.
  Proof.
    intros H Hv. pose proof H as H'.
    Search context_of_args. eapply bare_in_context_args in H'; eauto. fwd.
    apply in_fst in H'. apply in_of_list_Some_strong in H'. fwd.
    apply interp_args_context_right in H. rewrite Forall_forall in H.
    specialize (H _ H'p1). simpl in H. cbv [agree_on]. eauto using eq_trans.
  Qed.

  Lemma interp_clause_context_right ctx f f' :
    interp_clause ctx f f' ->
    Forall (fun '(x, v) => map.get ctx x = Some v) (context_of_clause f f').
  Proof.
    intros. invert_stuff. apply interp_args_context_right. assumption.
  Qed.

  Lemma interp_hyps_context_right ctx hyps hyps' :
    Forall2 (interp_clause ctx) hyps hyps' ->
    Forall (fun '(x, v) => map.get ctx x = Some v) (context_of_hyps hyps hyps').
  Proof.
    intros H. apply Forall2_combine in H. rewrite Forall_forall in *.
    intros x Hx. cbv [context_of_hyps] in *. rewrite in_concat in Hx.
    fwd. cbv [zip] in Hxp0. rewrite in_map_iff in Hxp0. fwd. destruct x1 as [v v'].
    apply H in Hxp0p1. apply interp_clause_context_right in Hxp0p1.
    rewrite Forall_forall in Hxp0p1. apply Hxp0p1 in Hxp1. assumption.
  Qed.

  Lemma interp_hyps_context_right_weak ctx hyps hyps' :
    Forall2 (interp_clause ctx) hyps hyps' ->
    map.extends ctx (map.of_list (context_of_hyps hyps hyps')).
  Proof.
    intros H. apply interp_hyps_context_right in H. cbv [map.extends].
    intros. apply of_list_Some_in in H0. rewrite Forall_forall in H.
    apply H in H0. assumption.
  Qed.

  Lemma context_of_hyps_agree ctx hyps hyps' v :
    Forall2 (interp_clause ctx) hyps hyps' ->
    In (var_expr v) (flat_map clause_args hyps) ->
    agree_on ctx (map.of_list (context_of_hyps hyps hyps')) v.
  Proof.
    intros H1 H2.
    pose proof bare_in_context_hyps as H'.
    specialize (H' _ _ _ _ ltac:(eassumption) ltac:(eassumption)). fwd.
    apply in_fst in H'. apply in_of_list_Some_strong in H'. fwd.
    eapply interp_hyps_context_right_weak in H1; eauto.
    specialize (H1 _ _ H'p0). cbv [agree_on]. rewrite H1, H'p0. reflexivity.
  Qed.

  Lemma in_vars_interp_expr_not_None ctx e e' v :
    interp_expr ctx e e' ->
    In v (vars_of_expr e) ->
    map.get ctx v <> None.
  Proof.
    intros H1 H2. revert e' H1. induction e.
    - intros e' H. invert H. simpl in H2. destruct H2; congruence.
    - intros e' H'. invert H'. apply Forall2_forget_r in H3.
      eapply Forall_and in H3; [|exact H]. clear H. simpl in H2.
      apply in_flat_map in H2. fwd. rewrite Forall_forall in H3.
      specialize (H3 _ H2p0). fwd. eapply H3p0; eauto.
  Qed.

  Definition all_rule_ctxs hyps hyps' :=
    map.of_list (context_of_hyps hyps hyps').

  Print good_rule.
  Lemma all_rule_ctxs_correct' r ctx hyps' :
    good_rule r ->
    Forall2 (interp_fact ctx) r.(rule_hyps) hyps' ->
    exists ctx',
      In ctx' (all_rule_ctxs r.(rule_hyps) r.(rule_set_hyps) hyps') /\
        map.extends ctx ctx' /\
        Forall2 (interp_fact ctx') r.(rule_hyps) hyps' /\
        Forall (x_in_S ctx') r.(rule_set_hyps).
  Proof.
    intros Hgood Hh Hsh. cbv [good_rule] in Hgood. fwd.
    apply all_rule_ctxs_correct''; auto. intros.
    Fail solve[auto]. apply Hgoodp0. auto. (*???*)
  Qed.

  Lemma all_rule_ctxs_correct r ctx hyps' :
    good_rule r ->
    Forall2 (interp_fact ctx) r.(rule_hyps) hyps' ->
    Forall (x_in_S ctx) r.(rule_set_hyps) ->
    exists ctx',
      In ctx' (all_rule_ctxs r.(rule_hyps) r.(rule_set_hyps) hyps') /\
        (forall v, appears_in_rule v r -> agree_on ctx' ctx v).
  Proof.
    intros Hgood Hh Hsh. pose proof all_rule_ctxs_correct' as H'.
    specialize (H' _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
    fwd. eexists. split; [eassumption|]. intros v Hv.
    cbv [good_rule] in Hgood. fwd. apply Hgoodp0 in Hv. destruct Hv as [Hv|Hv].
    - apply in_flat_map in Hv. fwd. eapply Forall2_and in H'p2; [|exact Hh].
      apply Forall2_forget_r in H'p2. rewrite Forall_forall in H'p2.
      specialize  (H'p2 _ Hvp0). fwd. eauto using interp_fact_same_agree.
    - rewrite Forall_forall in H'p3. apply in_map_iff in Hv. fwd.
      destruct x as [x s]. simpl in Hvp0. subst.
      specialize (H'p3 _ Hvp1). simpl in H'p3. fwd. cbv [agree_on].
      invert H'p3p0. rewrite H0. apply H'p1 in H0. rewrite H0. reflexivity.
  Qed.

  Definition eval_rule ctx r agg_hyps's :=
    let ctx' :=
      match r.(rule_agg) with
      | None => Some ctx
      | Some (res, aexpr) =>
          match eval_aexpr aexpr ctx agg_hyps's with
          | None => None
          | Some res' => Some (map.put ctx res res')
          end
      end in
    match ctx' with
    | None => []
    | Some ctx' =>
        ListMisc.extract_Some (map (subst_in_fact ctx') r.(rule_concls))
    end.

  Lemma eval_rule_complete f ctx r hyps' agg_hyps's :
    good_rule r ->
    rule_impl' ctx r f hyps' agg_hyps's ->
    In f (eval_rule ctx r agg_hyps's).
  Proof.
    intros Hgood Himpl. invert Himpl.
    cbv [eval_rule]. cbv [good_rule] in Hgood.
    rewrite Exists_exists in H0. fwd. invert H.
    - rewrite <- ListMisc.in_extract_Some. rewrite in_map_iff. eexists. split; eauto.
      apply subst_in_fact_complete. assumption.
    - rewrite <- H0 in *. erewrite eval_aexpr_complete; try assumption; cycle 1.
      { eassumption. }
      rewrite <- ListMisc.in_extract_Some. rewrite in_map_iff. eexists. split; eauto.
      apply subst_in_fact_complete. assumption.
  Qed.

  (*if r is a goodish rule, and this condition holds, then we get the functionalish
    behavrios as encapsulated in lemma agree_fucntional*)
  Definition goodish_fun (r : rule) :=
    exists concl,
      r.(rule_concls) = [concl] /\
        (forall v,  ~ (exists ae : agg_expr, rule_agg r = Some (v, ae)) /\ In v (vars_of_fact concl) ->
             In (var_expr v) (fact_ins concl) \/
               In (var_expr v) (flat_map fact_args r.(rule_hyps))) /\
        match r.(rule_agg) with
        | Some (_, aexpr) =>
            (forall v, appears_in_agg_expr v aexpr ->
                  In (var_expr v) (fact_ins concl) \/
                    In (var_expr v) (flat_map fact_args r.(rule_hyps)))
        | None => True
        end.

  (*conjunction of this and goodish_rule imply goodish_fun*)
  Definition no_set_hyps (r : rule) :=
    r.(rule_set_hyps) = nil.

  Lemma no_set_hyps_enough r :
    goodish_rule r ->
    no_set_hyps r ->
    goodish_fun r.
  Proof.
    cbv [goodish_rule no_set_hyps goodish_fun]. intros H H0. fwd.
    eexists. intuition eauto.
    - specialize (Hp2 v). specialize' Hp2.
      { cbv [appears_in_rule]. rewrite Hp0. simpl. rewrite app_nil_r. left. auto. }
      destruct Hp2 as [Hp2 | [Hp2|Hp2]]; auto. rewrite H0 in Hp2. simpl in Hp2.
      contradiction.
    - destruct (rule_agg r) as [(?&?)|] eqn:E; auto. fwd. intros.
      specialize (Hp2 v0). specialize' Hp2.
      { cbv [appears_in_rule]. rewrite Hp0. simpl. rewrite app_nil_r. eauto 10. }
      destruct Hp2 as [Hp2 | [Hp2|Hp2]]; auto. rewrite H0 in Hp2. simpl in Hp2.
      contradiction.
  Qed.

  Definition eval_rule_q r concl_ins hyps' agg_hyps's :=
    let ctx := map.putmany (map.of_list (context_of_args (flat_map fact_ins r.(rule_concls)) concl_ins)) (map.of_list (context_of_hyps r.(rule_hyps) hyps')) in
    let ctx' :=
      match r.(rule_agg) with
      | None => Some ctx
      | Some (res, aexpr) =>
          match eval_aexpr aexpr ctx agg_hyps's with
          | None => None
          | Some res' => Some (map.put ctx res res')
          end
      end in
    match ctx' with
    | None => []
    | Some ctx' =>
        ListMisc.extract_Some (map (subst_in_fact ctx') r.(rule_concls))
    end.

  Lemma eval_rule_q_complete ctx0 R args r hyps' agg_hyps's :
    goodish_rule r ->
    goodish_fun r ->
    rule_impl' ctx0 r (R, args) hyps' agg_hyps's ->
    eval_rule_q r (skipn (outs R) args) hyps' agg_hyps's = [(R, args)].
  Proof.
    intros Hgood Hfun Himpl. cbv [eval_rule_q]. cbv [goodish_rule] in Hgood.
    cbv [goodish_fun] in Hfun. fwd.
    invert Himpl. rewrite Hgoodp0 in *. invert_list_stuff. simpl. rewrite app_nil_r.
    invert H.
    - rewrite <- H5 in *. fwd. erewrite subst_in_fact_complete. 1: reflexivity.
      eapply interp_fact_agree_on; [eassumption|].
      apply Forall_forall. intros v H. cbv [agree_on]. invert H4.
      rewrite map.get_putmany_dec. destruct_one_match.
      + apply of_list_Some_in in E. apply interp_hyps_context_right in H1.
        rewrite Forall_forall in H1. apply H1 in E. assumption.
      + apply get_of_list_None_bw in E. specialize (Hfunp1 v). specialize' Hfunp1.
        { split; auto. intro. fwd. congruence. }
        destruct Hfunp1 as [Hfunp1|Hfunp1].
        -- eapply Forall2_skipn in H6. pose proof H6 as H6'.
           apply interp_args_context_right in H6. rewrite Forall_forall in H6.
           cbv [fact_ins] in Hgoodp1. eapply bare_in_context_args in H6'.
           2: { eassumption. }
           fwd. apply in_fst in H6'. apply in_of_list_Some_strong in H6'.
           fwd. apply H6 in H6'p1. cbv [fact_ins]. rewrite H6'p0, H6'p1. reflexivity.
        -- eapply bare_in_context_hyps in Hfunp1; [|eassumption]. fwd.
           apply in_fst in Hfunp1. exfalso. auto.
    - rewrite <- H0 in *. fwd. erewrite eval_aexpr_complete; try assumption.
      2: { eapply interp_agg_expr_agree_on; [eassumption|]. intros v Hv.
           specialize (Hfunp2 _ Hv).
           cbv [agree_on]. rewrite map.get_putmany_dec. destruct_one_match.
           + apply of_list_Some_in in E. apply interp_hyps_context_right in H1.
             rewrite Forall_forall in H1. apply H1 in E. assumption.
           + apply get_of_list_None_bw in E. Print appears_in_agg_expr.
             destruct Hfunp2 as [H'|H'].
             -- invert H4. eapply Forall2_skipn in H5. pose proof H5 as H5'.
                apply interp_args_context_right in H5. rewrite Forall_forall in H5.
                cbv [fact_ins] in Hgoodp1. eapply bare_in_context_args in H5'.
                2: { eassumption. }
                fwd. apply in_fst in H5'. apply in_of_list_Some_strong in H5'.
                fwd. apply H5 in H5'p1. cbv [fact_ins]. rewrite H5'p0.
                rewrite map.get_put_diff in H5'p1; auto. intros ?. subst.
                Search res. apply Hgoodp1. do 2 eexists. split; [|reflexivity].
                apply in_flat_map. eexists. split; [eassumption|]. simpl. auto.
             -- eapply bare_in_context_hyps in H'; [|eassumption]. fwd.
                apply in_fst in H'. exfalso. auto. }
      erewrite subst_in_fact_complete. 1: reflexivity.
      eapply interp_fact_agree_on; [eassumption|].
      apply Forall_forall. intros v Hv. cbv [agree_on]. invert H4.
      do 2 rewrite map.get_put_dec. destruct_one_match; try reflexivity.
      rewrite map.get_putmany_dec. destruct_one_match.
      + apply of_list_Some_in in E0. apply interp_hyps_context_right in H1.
        rewrite Forall_forall in H1. apply H1 in E0. assumption.
      + apply get_of_list_None_bw in E0. specialize (Hfunp1 v). specialize' Hfunp1.
        { split; auto. intro. fwd. congruence. }
        destruct Hfunp1 as [H'|H'].
        -- eapply Forall2_skipn in H5. pose proof H5 as H5'.
           apply interp_args_context_right in H5. rewrite Forall_forall in H5.
           cbv [fact_ins] in Hgoodp1. eapply bare_in_context_args in H5'.
           2: { eassumption. }
           fwd. apply in_fst in H5'. apply in_of_list_Some_strong in H5'.
           fwd. apply H5 in H5'p1. cbv [fact_ins]. rewrite H5'p0.
           rewrite map.get_put_diff in H5'p1; auto.
        -- eapply bare_in_context_hyps in H'; [|eassumption]. fwd.
           apply in_fst in H'. exfalso. auto.
  Qed.

  Definition num_agg_hyps r :=
    match r.(rule_agg) with
    | None => O
    | Some (_, aexpr) => length aexpr.(agg_hyps)
    end.

  Lemma num_agg_hyps_spec' ctx res aexpr agg_hyps's :
    interp_agg_expr ctx aexpr res agg_hyps's ->
    Forall (fun agg_hyps' => length agg_hyps' = length aexpr.(agg_hyps)) agg_hyps's.
  Proof.
    invert 1. simpl. apply Forall3_ignore12 in H2. eapply Forall_impl; [|eassumption].
    clear. simpl. intros. fwd. apply Forall2_length in Hp1. auto.
  Qed.

  Lemma num_agg_hyps_spec ctx r f hyps' agg_hyps's :
    rule_impl' ctx r f hyps' agg_hyps's ->
    Forall (fun agg_hyps' => length agg_hyps' = num_agg_hyps r) agg_hyps's.
  Proof.
    intros H. invert H. cbv [num_agg_hyps]. invert H0; auto.
    eapply num_agg_hyps_spec'. eassumption.
  Qed.

  Definition step (r : rule) (facts : list (rel * list T)) : list (rel * list T) :=
    let hyps'_choices := choose_any_n (length r.(rule_hyps)) facts in
    flat_map
      (fun hyps' =>
         let agg_hyps'_choices := choose_any_n (num_agg_hyps r) facts in
         let ctx_choices := all_rule_ctxs r.(rule_hyps) r.(rule_set_hyps) hyps' in
         flat_map
           (fun ctx =>
              let agg_hyps's_choices := choose_any_n (agg_hyps'_len r ctx) agg_hyps'_choices in
              flat_map (eval_rule ctx r) agg_hyps's_choices)
           ctx_choices)
      hyps'_choices.

  Lemma rule_impl'_hyps'_len ctx r f hyps' agg_hyps' :
    rule_impl' ctx r f hyps' agg_hyps' ->
    length hyps' = length r.(rule_hyps).
  Proof.
    intros H. invert H. apply Forall2_length in H2. auto.
  Qed.

  Lemma agg_hyps_determined ctx r f hyps' :
    good_rule r ->
    forall agg_hyps's,
      rule_impl' ctx r f hyps' agg_hyps's ->
      length agg_hyps's = agg_hyps'_len r ctx.
  Proof.
    intros Hgood agg_hyps' H. invert H. cbv [agg_hyps'_len].
    invert H0; [reflexivity|]. invert H6. simpl. erewrite subst_in_expr_complete.
    2: { eassumption. }
    simpl. rewrite H4. apply Forall3_length in H5. fwd. lia.
  Qed.

  Lemma subst_in_expr_ctxs_agree ctx ctx' e :
    Forall (agree_on ctx ctx') (vars_of_expr e) ->
    subst_in_expr ctx e = subst_in_expr ctx' e.
  Proof.
    intros H.
    destruct (subst_in_expr ctx e) eqn:E; destruct (subst_in_expr ctx' e) eqn:E'; auto.
    - apply subst_in_expr_sound in E, E'. f_equal. eauto using interp_expr_det'.
    - apply subst_in_expr_sound in E. eapply interp_expr_agree_on in E; eauto.
      apply subst_in_expr_complete in E. congruence.
    - apply subst_in_expr_sound in E'. eapply interp_expr_agree_on in E'.
      2: { eapply Forall_impl; [|eassumption]. intros. symmetry. eassumption. }
      apply subst_in_expr_complete in E'. congruence.
  Qed.

  Lemma subst_in_fact_ctxs_agree ctx ctx' f :
    Forall (agree_on ctx ctx') (vars_of_fact f) ->
    subst_in_fact ctx f = subst_in_fact ctx' f.
  Proof.
    intros H. cbv [subst_in_fact]. f_equal. f_equal. apply map_ext_in.
    intros. cbv [vars_of_fact] in H. apply Forall_flat_map in H.
    rewrite Forall_forall in H. specialize (H _ ltac:(eassumption)).
    apply subst_in_expr_ctxs_agree. assumption.
  Qed.

  Hint Unfold appears_in_agg_expr : core.
  Lemma eval_aexpr_ctxs_agree ctx0 res0 ctx ctx' aexpr agg_hyps's :
    good_agg_expr aexpr ->
    interp_agg_expr ctx0 aexpr res0 agg_hyps's ->
    (forall v, appears_in_agg_expr v aexpr -> agree_on ctx ctx' v) ->
    eval_aexpr aexpr ctx agg_hyps's = eval_aexpr aexpr ctx' agg_hyps's.
  Proof.
    intros Hgood H Hagree. cbv [eval_aexpr]. erewrite subst_in_expr_ctxs_agree.
    2: { apply Forall_forall. auto. }
    destruct (option_coalesce _); [|reflexivity].
    erewrite zip_ext_in.
    2: { intros x y Hin. apply subst_in_expr_ctxs_agree.
         instantiate (1 := (map.putmany ctx'
                              (map.put (map.of_list (context_of_hyps (agg_hyps aexpr) y)) (agg_i aexpr) x))).
         apply Forall_forall.
         intros v Hv. cbv [agree_on]. do 2 rewrite map.get_putmany_dec.
         destruct_one_match; [reflexivity|]. apply in_combine_r in Hin.
         invert H. simpl in *. apply Forall3_ignore12 in H2.
         rewrite Forall_forall in H2. specialize (H2 _ ltac:(eassumption)).
         fwd. apply Hagree. cbv [appears_in_agg_expr].
         right. simpl. split; auto. rewrite map.get_put_dec in E.
         destr (var_eqb i v); [congruence|]. intros [H'|H']; auto.
         eapply bare_in_context_hyps in H2p1.
         2: { move Hgood at bottom. cbv [good_agg_expr] in Hgood. simpl in Hgood.
              rewrite Forall_forall in Hgood. apply Hgood. eassumption. }
         fwd. apply in_fst in H2p1. apply in_of_list_Some in H2p1. fwd.
         congruence. }
    reflexivity.
  Qed.

  Lemma eval_rule_ctxs_agree ctx0 ctx ctx' r f hyps' agg_hyps's :
    good_rule r ->
    rule_impl' ctx0 r f hyps' agg_hyps's ->
    (forall v : var, appears_in_rule v r -> agree_on ctx ctx' v) ->
    eval_rule ctx r agg_hyps's = eval_rule ctx' r agg_hyps's.
  Proof.
    intros Hgood H Hagree. cbv [eval_rule]. invert H.
    cbv [good_rule] in Hgood. fwd. invert H0.
    - f_equal. apply map_ext_in. intros.
      apply subst_in_fact_ctxs_agree.
      apply Forall_forall. intros v Hv. apply Hagree. cbv [appears_in_rule].
      left. split.
      + intros ?. fwd. congruence.
      + apply in_flat_map. eauto.
    - rewrite <- H in *. erewrite eval_aexpr_ctxs_agree; eauto; cycle 1.
      { intros. apply Hagree. cbv [appears_in_rule]. rewrite <- H. eauto 7. }
      destruct (eval_aexpr _ _ _); [|reflexivity].
      f_equal. apply map_ext_in. intros. apply subst_in_fact_ctxs_agree.
      apply Forall_forall. intros. cbv [agree_on]. do 2 rewrite map.get_put_dec.
      destruct_one_match; [reflexivity|]. apply Hagree. cbv [appears_in_rule].
      left. split.
      + intros ?. fwd. congruence.
      + apply in_flat_map. eauto.
  Qed.

  Lemma agg_hyps's_len_ctxs_agree ctx ctx' r :
    good_rule r ->
    (forall v : var, appears_in_rule v r -> agree_on ctx ctx' v) ->
    agg_hyps'_len r ctx = agg_hyps'_len r ctx'.
  Proof.
    intros Hgood Hagree. cbv [agg_hyps'_len].
    destruct r.(rule_agg) as [(?&?)|] eqn:E; [|reflexivity].
    erewrite subst_in_expr_ctxs_agree; cycle 1.
    { apply Forall_forall. intros. apply Hagree. eauto 10. }
    reflexivity.
  Qed.

  Lemma step_complete r hyps' facts f :
    good_rule r ->
    incl hyps' facts ->
    rule_impl r f hyps' ->
    In f (step r facts).
  Proof.
    intros H1 H2 H3. cbv [step]. apply in_flat_map.
    cbv [rule_impl] in H3. fwd.
    apply incl_app_inv in H2. fwd.
    apply incl_concat_l in H2p1.
    exists hyps'0. split.
    { apply choose_n_spec.
      - eapply rule_impl'_hyps'_len. eassumption.
      - assumption. }
    pose proof eval_rule_complete as H''.
    specialize (H'' _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    apply in_flat_map.
    pose proof all_rule_ctxs_correct as H'.
    invert H3p1.
    specialize (H' _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
    fwd. eexists. split; [eassumption|].
    apply in_flat_map. eexists.
    erewrite eval_rule_ctxs_agree by (eassumption || econstructor; eauto).
    erewrite agg_hyps's_len_ctxs_agree by eassumption.
    split; [|assumption].
    apply choose_n_spec.
    - eapply agg_hyps_determined; eauto. econstructor; eauto.
    - cbv [incl]. apply Forall_forall. eapply Forall_impl.
      2: { apply Forall_and; [eassumption|]. eapply num_agg_hyps_spec.
           econstructor; eassumption. }
      simpl. intros. fwd. apply choose_n_spec; assumption.
  Qed.

  Definition step_everybody p fs := flat_map (fun r => step r fs) p.

  Lemma step_everybody_complete p hyps' facts f :
    Forall good_rule p ->
    incl hyps' facts ->
    Exists (fun r => rule_impl r f hyps') p ->
    In f (step_everybody p facts).
  Proof.
    intros H1 H2 H3. rewrite Forall_forall in H1. apply Exists_exists in H3.
    fwd. specialize (H1 _ H3p0). cbv [step_everybody]. apply in_flat_map.
    eexists. split; eauto. eapply step_complete; eauto.
  Qed.

  Definition eval n p := Nat.iter n (fun fs => step_everybody p fs ++ fs) nil.

  (*a bit conservative*)
  Definition count_rels p := S (length (rel_graph p)).

  Definition eval_dag p := eval (count_rels p) p.

  Lemma choose_any_n_mono {A : Type} n (xs ys : list A) :
    incl xs ys ->
    incl (choose_any_n n xs) (choose_any_n n ys).
  Proof.
    induction n; simpl; auto with incl.
  Qed.

  Hint Resolve choose_any_n_mono : core.

  Lemma step_mono r fs1 fs2 :
    incl fs1 fs2 ->
    incl (step r fs1) (step r fs2).
  Proof. cbv [step]. auto 6 with incl. Qed.

  Hint Resolve step_mono : core.

  Lemma eval_mono n m p1 p2 :
    incl p1 p2 ->
    n <= m ->
    incl (eval n p1) (eval m p2).
  Proof.
    intros H. revert m. induction n; simpl; auto with incl. intros m Hm.
    destruct m as [|m]; [lia|]. specialize (IHn m ltac:(lia)).
    simpl. cbv [step_everybody]. auto with incl.
  Qed.

  Lemma incl_mono_fun {X : Type} (f g : list X -> list X) x n :
    (forall l1 l2, incl l1 l2 -> incl (f l1) (g l2)) ->
    incl (Nat.iter n f x) (Nat.iter n g x).
  Proof. intros. induction n; simpl; auto with incl. Qed.

  Lemma eval_complete p n :
    Forall good_rule p ->
    forall f,
      prog_impl_fact p f ->
      In f (eval n p) \/
        (exists l, path (rel_graph p) (fst f) l /\ n <= length l).
  Proof.
    intros Hp. induction n.
    - intros. simpl. right. exists nil. simpl. split; [constructor|lia].
    - intros f Hf. simpl. invert Hf. eapply Forall_impl in H0.
      2: { intros x Hx. apply IHn in Hx. exact Hx. }
      apply Forall_or in H0. destruct H0 as [H0|H0].
      + left. apply in_app_iff. left. eapply step_everybody_complete; eauto.
        rewrite Forall_forall in H0. auto.
      + right. rewrite Exists_exists in H0. fwd. exists ((fst x) :: l0). simpl. split; [|lia].
        constructor; auto. apply rel_graph_spec in H.
        rewrite Forall_forall in H. apply H. assumption.
  Qed.

  Lemma eval_dag_complete p :
    Forall good_rule p ->
    dag (rel_graph p) ->
    forall f,
      prog_impl_fact p f ->
      In f (eval_dag p).
  Proof.
    intros. eapply eval_complete in H; eauto. destruct H; [eassumption|].
    fwd. eapply dag_paths_short in H0; eauto. cbv [count_rels] in *. lia.
  Qed.
End __.
