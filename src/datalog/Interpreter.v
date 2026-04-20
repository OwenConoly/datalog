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

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List Datatypes.Option.

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

  Definition subst_in_meta_clause ctx (c : meta_clause) (S : list T -> Prop) :=
    option_map (fun args => meta_fact c.(meta_clause_rel) args S)
      (option_all (map (fun o => match o with
                                 | None => Some None
                                 | Some e => option_map Some (subst_in_expr ctx e)
                                 end) c.(meta_clause_args))).

  Lemma subst_in_meta_clause_sound ctx c S f :
    subst_in_meta_clause ctx c S = Some f ->
    interp_meta_clause ctx c f.
  Proof.
    cbv [subst_in_meta_clause interp_meta_clause]. intros H.
    apply option_map_Some in H. fwd.
    apply option_all_Forall2 in Hp0.
    do 2 eexists. split; [|reflexivity].
    rewrite <- Forall2_map_l in Hp0.
    eapply Forall2_impl; [|eassumption].
    simpl. intros o o' H. destruct o; simpl in H; fwd; try constructor.
    apply option_map_Some in H. fwd.
    simpl. apply subst_in_expr_sound. auto.
  Qed.

  Definition set_of (f : fact) :=
    match f with
    | meta_fact _ _ S0 => S0
    | normal_fact _ _ => fun _ => True
    end.

  Lemma subst_in_meta_clause_complete ctx c R args S0 :
    interp_meta_clause ctx c (meta_fact R args S0) ->
    forall S1,
      subst_in_meta_clause ctx c S1 = Some (meta_fact R args S1).
  Proof.
    intros Hinterp. repeat invert_stuff.
    cbv [subst_in_meta_clause].
    erewrite Forall2_option_all.
    2: { rewrite <- Forall2_map_l. eapply Forall2_impl; [|eassumption].
         intros a b Hab. destruct a, b; simpl in Hab; try congruence; try contradiction.          erewrite subst_in_expr_complete by eassumption. reflexivity. }
    simpl. eauto.
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

  Lemma bare_in_context_clause ctx x c f :
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
    specialize (H2 _ H1p0). fwd. eapply bare_in_context_clause in H2p1; eauto. fwd.
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

  Definition eval_rule env ctx (hyps' : list fact) (r : rule) : list fact :=
    match r with
    | normal_rule rule_concls _ =>
        keep_Some (map (subst_in_clause ctx) rule_concls)
    | meta_rule rule_concls _ =>
        keep_Some (map (fun c => subst_in_meta_clause ctx c (env hyps' c.(meta_clause_rel))) rule_concls)
    | agg_rule concl_rel agg hyp_rel =>
        match hyps' with
        | meta_fact _ (_ :: _ :: args) _ :: rest =>
            let args := option_all args in
            let vals := option_all (map
                                      (fun f => match f with
                                             | normal_fact _ (i :: x_i :: _) => Some (i, x_i)
                                             | _ => None
                                             end) rest) in
            match args, vals with
            | Some args, Some vals =>
                [normal_fact concl_rel (interp_agg agg vals :: args)]
            | _, _ => []
            end
        | _ => []
        end
    end.

  Lemma non_meta_rule_impl_complete env r R args hyps :
    non_meta_rule_impl r R args hyps ->
    exists ctx, In (normal_fact R args) (eval_rule env ctx hyps r).
  Proof.
    invert 1.
    - exists ctx. cbv [eval_rule].
      apply Exists_exists in H0. destruct H0 as [c [Hcin Hc]].
      cbv [keep_Some]. apply in_flat_map.
      eexists. split.
      + apply in_map_iff. eexists. split; [reflexivity | exact Hcin].
      + apply subst_in_clause_complete in Hc. rewrite Hc.
        simpl. left. reflexivity.
    - exists map.empty. cbv [eval_rule].
      rewrite option_all_map_Some.
      rewrite map_map. erewrite map_ext.
      2:{ intros (?, ?). reflexivity. }
      rewrite option_all_map_Some. simpl. auto.
  Qed.

  Lemma eval_rule_complete env r f hyps' :
    rule_impl env r f hyps' ->
    exists ctx f', In f' (eval_rule env ctx hyps' r) /\ extensionally_equal f f'.
  Proof.
    invert 1.
    - eapply non_meta_rule_impl_complete in H0.
      fwd. eauto.
    - apply Exists_exists in H0. fwd. eexists _, _.
      split.
      + cbv [eval_rule].
        apply in_keep_Some. apply in_map_iff.
        eauto using subst_in_meta_clause_complete.
      + repeat invert_stuff. auto.
  Qed.

  (*if r is a goodish rule, and this condition holds, then we get the functionalish
    behavrios as encapsulated in lemma agree_fucntional*)
  (* Definition goodish_fun (r : rule) := *)
  (*   exists concl, *)
  (*     r.(rule_concls) = [concl] /\ *)
  (*       (forall v,  ~ (exists ae : agg_expr, rule_agg r = Some (v, ae)) /\ In v (vars_of_fact concl) -> *)
  (*            In (var_expr v) (fact_ins concl) \/ *)
  (*              In (var_expr v) (flat_map fact_args r.(rule_hyps))) /\ *)
  (*       match r.(rule_agg) with *)
  (*       | Some (_, aexpr) => *)
  (*           (forall v, appears_in_agg_expr v aexpr -> *)
  (*                 In (var_expr v) (fact_ins concl) \/ *)
  (*                   In (var_expr v) (flat_map fact_args r.(rule_hyps))) *)
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

  Definition context_of_meta_clause (c : meta_clause) (f : fact) :=
    match f with
    | meta_fact _ mf_args _ =>
        context_of_args (keep_Some c.(meta_clause_args)) (keep_Some mf_args)
    | normal_fact _ _ => []
    end.

  Definition context_of_meta_hyps (hyps : list meta_clause) (hyps' : list fact) :=
    concat (zip context_of_meta_clause hyps hyps').

  Definition ctx_of_rule (r : rule) (hyps' : list fact) : context :=
    match r with
    | normal_rule _ rule_hyps =>
        map.of_list (context_of_hyps rule_hyps hyps')
    | meta_rule _ rule_hyps =>
        map.of_list (context_of_meta_hyps rule_hyps hyps')
    | agg_rule _ _ _ =>
        map.empty
    end.

  Definition possible_hyps (r : rule) (facts : list fact) : list (list fact) :=
    match r with
    | normal_rule _ rule_hyps =>
        choose_any_n (length rule_hyps) facts
    | meta_rule _ rule_hyps =>
        choose_any_n (length rule_hyps) facts
    | agg_rule _ _ _ =>
        flat_map (fun n => choose_any_n n facts) (seq 1 (S (length facts)))
    end.

  Lemma non_meta_rule_impl_possible_hyps r R args hyps facts :
    incl hyps facts ->
    non_meta_rule_impl r R args hyps ->
    In hyps (possible_hyps r facts).
  Proof.
    intros Hincl. invert 1.
    - cbv [possible_hyps]. apply choose_n_spec; [|exact Hincl].
      eapply Forall2_length. apply Forall2_flip. eassumption.
    - cbv [possible_hyps]. apply in_flat_map.
      eexists (Datatypes.S (length vals)). split.
      + apply in_seq. apply incl_cons_inv in Hincl. fwd.
        apply NoDup_incl_length in Hinclp1.
        -- rewrite length_map in Hinclp1. lia.
        -- apply FinFun.Injective_map_NoDup. 2: cbv [is_list_set] in *; fwd; auto.
           cbv [FinFun.Injective]. intros (?, ?) (?, ?). congruence.
      + apply choose_n_spec.
        -- simpl. rewrite length_map. reflexivity.
        -- assumption.
  Qed.

  Lemma rule_impl_possible_hyps env r f hyps facts :
    incl hyps facts ->
    rule_impl env r f hyps ->
    In hyps (possible_hyps r facts).
  Proof.
    intros Hincl. invert 1.
    - eapply non_meta_rule_impl_possible_hyps; eassumption.
    - cbv [possible_hyps]. apply choose_n_spec; [|exact Hincl].
      eauto using Forall2_length, Forall2_flip.
  Qed.

  Definition step env (r : rule) (facts : list fact) : list fact :=
    flat_map
      (fun hyps' => eval_rule env (ctx_of_rule r hyps') hyps' r)
      (possible_hyps r facts).

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

  Lemma subst_in_clause_ctxs_agree ctx ctx' f :
    Forall (agree_on ctx ctx') (vars_of_clause f) ->
    subst_in_clause ctx f = subst_in_clause ctx' f.
  Proof.
    intros H. cbv [subst_in_clause]. f_equal. f_equal. apply map_ext_in.
    intros. cbv [vars_of_clause] in H. apply Forall_flat_map in H.
    rewrite Forall_forall in H. specialize (H _ ltac:(eassumption)).
    apply subst_in_expr_ctxs_agree. assumption.
  Qed.

  Lemma subst_in_meta_clause_ctxs_agree ctx ctx' c S :
    Forall (agree_on ctx ctx') (vars_of_meta_clause c) ->
    subst_in_meta_clause ctx c S = subst_in_meta_clause ctx' c S.
  Proof.
    cbv [subst_in_meta_clause vars_of_meta_clause]. intros H. f_equal. f_equal.
    apply map_ext_in. intros o Ho. destruct o as [e|]; [|reflexivity].
    simpl. f_equal. apply subst_in_expr_ctxs_agree.
    rewrite Forall_flat_map, Forall_forall in H. apply H.
    apply in_keep_Some. assumption.
  Qed.

  Lemma eval_rule_ctxs_agree env ctx ctx' hyps' r :
    (forall v, In v (all_vars r) -> agree_on ctx ctx' v) ->
    eval_rule env ctx hyps' r = eval_rule env ctx' hyps' r.
  Proof.
    destruct r; simpl; intros H.
    - f_equal. apply map_ext_in. intros c Hc.
      apply subst_in_clause_ctxs_agree.
      apply Forall_forall. intros v Hv. apply H.
      cbv [all_vars concl_vars]. apply in_app_iff. left.
      apply in_flat_map. eauto.
    - f_equal. apply map_ext_in. intros c Hc.
      apply subst_in_meta_clause_ctxs_agree.
      apply Forall_forall. intros v Hv. apply H.
      cbv [all_vars concl_vars]. apply in_app_iff. left.
      apply in_flat_map. eauto.
    - reflexivity.
  Qed.

  Lemma Forall2_option_relation_keep_Some {A B} (R : A -> B -> Prop) l1 l2 :
    Forall2 (option_relation R) l1 l2 ->
    Forall2 R (keep_Some l1) (keep_Some l2).
  Proof.
    induction 1; simpl; auto.
    cbv [option_relation] in H.
    destruct x, y; simpl; contradiction || congruence || auto.
  Qed.

  Lemma interp_meta_args_context_right ctx c f :
    interp_meta_clause ctx c f ->
    Forall (fun '(x, v) => map.get ctx x = Some v) (context_of_meta_clause c f).
  Proof.
    intros. cbv [interp_meta_clause] in H. fwd.
    simpl.
    apply interp_args_context_right.
    apply Forall2_option_relation_keep_Some. assumption.
  Qed.

  Lemma interp_meta_hyps_context_right ctx hyps hyps' :
    Forall2 (interp_meta_clause ctx) hyps hyps' ->
    Forall (fun '(x, v) => map.get ctx x = Some v) (context_of_meta_hyps hyps hyps').
  Proof.
    intros H. apply Forall2_combine in H. rewrite Forall_forall in *.
    intros x Hx. cbv [context_of_meta_hyps] in *.
    rewrite in_concat in Hx. fwd.
    cbv [zip] in Hxp0. rewrite in_map_iff in Hxp0. fwd. destruct x1 as [v v'].
    apply H in Hxp0p1. apply interp_meta_args_context_right in Hxp0p1.
    rewrite Forall_forall in Hxp0p1. apply Hxp0p1 in Hxp1. assumption.
  Qed.

  Lemma interp_meta_hyps_context_right_weak ctx hyps hyps' :
    Forall2 (interp_meta_clause ctx) hyps hyps' ->
    map.extends ctx (map.of_list (context_of_meta_hyps hyps hyps')).
  Proof.
    intros H. apply interp_meta_hyps_context_right in H. cbv [map.extends].
    intros. apply of_list_Some_in in H0. rewrite Forall_forall in H.
    apply H in H0. assumption.
  Qed.

  Lemma bare_in_context_hyps' ctx x hyps hyps' :
    In (var_expr x) (flat_map clause_args hyps) ->
    Forall2 (interp_clause ctx) hyps hyps' ->
    exists v, In (x, v) (context_of_hyps hyps hyps').
  Proof.
    intros H1 H2. apply in_flat_map in H1. fwd. cbv [context_of_hyps].
    apply Forall2_forget_r_strong in H2. rewrite Forall_forall in H2.
    specialize (H2 _ H1p0). fwd. eapply bare_in_context_clause in H2p1; eauto. fwd.
    eexists. rewrite in_concat. cbv [zip]. eexists. rewrite in_map_iff. split.
    { eexists. split; [|eassumption]. reflexivity. }
    eassumption.
  Qed.

  Lemma bare_in_context_meta_clause ctx x c f :
    In (var_expr x) (keep_Some c.(meta_clause_args)) ->
    interp_meta_clause ctx c f ->
    exists v, In (x, v) (context_of_meta_clause c f).
  Proof.
    intros H1 H2. cbv [context_of_meta_clause]. repeat invert_stuff.
    eapply bare_in_context_args; [eassumption|].
    apply Forall2_option_relation_keep_Some. eassumption.
  Qed.

  Lemma bare_in_context_meta_hyps ctx x hyps hyps' :
    In (var_expr x) (flat_map (fun c => keep_Some c.(meta_clause_args)) hyps) ->
    Forall2 (interp_meta_clause ctx) hyps hyps' ->
    exists v, In (x, v) (context_of_meta_hyps hyps hyps').
  Proof.
    intros H1 H2. apply in_flat_map in H1. fwd. cbv [context_of_meta_hyps].
    apply Forall2_forget_r_strong in H2. rewrite Forall_forall in H2.
    specialize (H2 _ H1p0). fwd. eapply bare_in_context_meta_clause in H2p1; eauto. fwd.
    eexists. rewrite in_concat. cbv [zip]. eexists. rewrite in_map_iff. eauto.
  Qed.

  Lemma context_of_meta_hyps_agree ctx hyps hyps' v :
    Forall2 (interp_meta_clause ctx) hyps hyps' ->
    In (var_expr v) (flat_map (fun c => keep_Some c.(meta_clause_args)) hyps) ->
    agree_on ctx (map.of_list (context_of_meta_hyps hyps hyps')) v.
  Proof.
    intros H1 H2.
    pose proof bare_in_context_meta_hyps as H'.
    specialize (H' _ _ _ _ ltac:(eassumption) ltac:(eassumption)). fwd.
    apply in_fst in H'. apply in_of_list_Some_strong in H'. fwd.
    eapply interp_meta_hyps_context_right_weak in H1; eauto.
    specialize (H1 _ _ H'p0).
    cbv [agree_on]. rewrite H1, H'p0. reflexivity.
  Qed.

  Print good_rule.
  Lemma non_meta_rule_impl_step_complete env r R args hyps facts :
    good_rule r ->
    incl hyps facts ->
    non_meta_rule_impl r R args hyps ->
    In (normal_fact R args) (step env r facts).
  Proof.
    intros Hgood Hincl Himpl.
    cbv [step]. apply in_flat_map. eexists. split.
    - eapply non_meta_rule_impl_possible_hyps; eassumption.
    - pose proof (non_meta_rule_impl_complete env _ _ _ _ Himpl) as [ctx Hctx].
      erewrite <- eval_rule_ctxs_agree; [exact Hctx |].
      intros v Hv.
      (* Prove context agreement for the specific rule type *)
      destruct r; inversion Himpl; subst.
      + eapply context_of_hyps_agree. match goal with Hf2 : Forall2 _ _ _ |- _ =>
          eapply context_of_hyps_agree; [exact Hf2 | exact Hv]
        end.
      + (* Case: agg_rule (no variables to bind, so trivial agreement) *)
        cbv [agree_on]. reflexivity.
  Qed.

  Lemma non_meta_rule_impl_step_complete env r R args hyps facts :
    good_rule r ->
    incl hyps facts ->
    non_meta_rule_impl r R args hyps ->
    In (normal_fact R args) (step env r facts).
  Proof.
    intros Hgood Hincl Himpl.
    cbv [step]. apply in_flat_map. eexists hyps. split.

    (* 1. Prove that `hyps` is successfully generated by `possible_hyps` *)
    - destruct r; inversion Himpl; subst.
      + (* Case: normal_rule *)
        cbv [possible_hyps]. apply choose_n_spec; [|exact Hincl].
        match goal with Hf2 : Forall2 _ _ _ |- _ =>
          clear -Hf2; induction Hf2; simpl; congruence
        end.

      + (* Case: agg_rule *)
        cbv [possible_hyps]. apply in_flat_map. eexists (length hyps).
        split.
        * apply in_seq. split; [lia|].
          apply NoDup_incl_length; [|exact Hincl].
          match goal with Hset : is_list_set _ _ |- _ => destruct Hset as [_ Hnodup] end.
          constructor.
          -- intro Hmap. apply in_map_iff in Hmap. fwd. discriminate.
          -- apply FinFun.Injective_map_NoDup; [|exact Hnodup].
             intros [i1 x1] [i2 x2] Heq_inj. inversion Heq_inj. reflexivity.
        * apply choose_n_spec; [reflexivity | exact Hincl].

    (* 2. Prove that `eval_rule` returns the fact using our generated `ctx` *)
    - pose proof (non_meta_rule_impl_complete env _ _ _ _ Himpl) as [ctx Hctx].
      erewrite <- eval_rule_ctxs_agree; [exact Hctx |].
      intros v Hv. cbv [good_rule] in Hgood. apply Hgood in Hv.

      (* Prove context agreement for the specific rule type *)
      destruct r; inversion Himpl; subst.
      + (* Case: normal_rule *)
        match goal with Hf2 : Forall2 _ _ _ |- _ =>
          eapply context_of_hyps_agree; [exact Hf2 | exact Hv]
        end.
      + (* Case: agg_rule (no variables to bind, so trivial agreement) *)
        cbv [agree_on]. reflexivity.
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
