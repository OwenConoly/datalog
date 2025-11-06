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
  Local Notation fact := (fact rel var fn).
  Local Notation agg_expr := (agg_expr rel var fn aggregator).

  Implicit Type r : rule.
  Implicit Type ctx : context.
  Implicit Type aexpr : agg_expr.

  Definition edges_of_rule r :=
    flat_map (fun c => map (fun h => (c.(fact_R), h.(fact_R))) (rule_agg_hyps r ++ r.(rule_hyps))) r.(rule_concls).

  Definition rel_graph := flat_map edges_of_rule.
  
  Definition diff_rels (p1 p2 : list rule) :=
    forall r1 r2 c1 c2,
      In r1 p1 ->
      In r2 p2 ->
      In c1 r1.(rule_concls) ->
      In c2 r2.(rule_concls) ->
      c1.(fact_R) <> c2.(fact_R).

  Lemma diff_rels_app_r p p1 p2 :
    diff_rels p p1 ->
    diff_rels p p2 ->
    diff_rels p (p1 ++ p2).
  Proof.
    cbv [diff_rels]. intros H H0 r1 r2 c1 c2 H1 H2 H3 H4. apply in_app_iff in H2.
    destruct H2; eauto.
  Qed.

  Lemma diff_rels_Forall_r p1 p2 :
    Forall (fun r2 =>
              forall r1 c1 c2,
                In r1 p1 ->
                In c1 r1.(rule_concls) ->
                In c2 r2.(rule_concls) ->
                c1.(fact_R) <> c2.(fact_R)) p2 ->
    diff_rels p1 p2.
  Proof.
    intros H. rewrite Forall_forall in H. cbv [diff_rels]. eauto.
  Qed.

  Lemma edges_of_rule_spec r f hyps :
    rule_impl r f hyps ->
    Forall (fun hyp => In (fst f, fst hyp) (edges_of_rule r)) hyps.
  Proof.
    cbv [rule_impl]. intros H. fwd. invert Hp1. apply Forall_app. split.
    - cbv [edges_of_rule]. apply Forall_forall. intros. apply in_flat_map.
      apply Exists_exists in H0. fwd. eexists. split; [eassumption|].
      apply in_map_iff. invert H0p1. simpl. apply Forall2_forget_l in H1.
      rewrite Forall_forall in H1. specialize (H1 _ ltac:(eassumption)).
      fwd. invert H1p1. simpl. eexists. split; [reflexivity|].
      apply in_app_iff. auto.
    - clear -H H0. apply Forall_concat. rewrite Exists_exists in H0.
      fwd. cbv [edges_of_rule rule_agg_hyps]. invert H; [constructor|].
      invert H3. simpl in *. apply Forall3_ignore12 in H2.
      eapply Forall_impl; [|eassumption]. clear H2. simpl. intros l Hl.
      fwd. apply Forall2_forget_l in Hlp1. eapply Forall_impl; [|eassumption].
      simpl. intros l0 Hl0. fwd. apply in_flat_map. eexists. split; [eassumption|].
      apply in_map_iff.  invert Hl0p1. simpl. invert H0p1. simpl.
      eexists. split; [reflexivity|]. apply in_app_iff. auto.
  Qed.

  Lemma rel_graph_spec p f hyps :
    Exists (fun r => rule_impl r f hyps) p ->
    Forall (fun hyp => In (fst f, fst hyp) (rel_graph p)) hyps.
  Proof.
    intros H. apply Exists_exists in H. fwd. apply edges_of_rule_spec in Hp1.
    eapply Forall_impl; [|eassumption]. simpl. intros. cbv [rel_graph].
    apply in_flat_map. eauto.
  Qed.    

  Fixpoint choose_any_n {X : Type} n (fs : list X) :=
    match n with
    | S n' => flat_map (fun f => map (cons f) (choose_any_n n' fs)) fs
    | O => [[]]
    end.
  
  Lemma choose_n_spec {X : Type} n (hyps fs : list X) :
    length hyps = n ->
    incl hyps fs ->
    In hyps (choose_any_n n fs).
  Proof.
    revert hyps fs. induction n; intros hyps fs Hlen Hincl.
    - destruct hyps; [|discriminate Hlen]. simpl. auto.
    - destruct hyps; [discriminate Hlen|]. simpl in Hlen.
      apply incl_cons_inv in Hincl. fwd.
      specialize (IHn hyps _ ltac:(lia) ltac:(eassumption)).
      simpl. apply in_flat_map. eexists. split; [eassumption|].
      apply in_map. assumption.
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

  Definition subst_in_fact ctx (f : fact) :=
    option_map (fun args' => (f.(fact_R), args'))
      (option_all (map (subst_in_expr ctx) f.(fact_args))).

  Lemma subst_in_fact_sound ctx f f' :
    subst_in_fact ctx f = Some f' ->
    interp_fact ctx f f'.
  Proof.
    cbv [subst_in_fact]. intros H. apply option_map_Some in H.
    fwd. apply option_all_Forall2 in Hp0. constructor.
    rewrite <- Forall2_map_l in Hp0. eapply Forall2_impl; [|eassumption].
    simpl. auto using subst_in_expr_sound.
  Qed.

  Lemma subst_in_fact_complete ctx f f' :
    interp_fact ctx f f' ->
    subst_in_fact ctx f = Some f'.
  Proof.
    intros H. invert H. cbv [subst_in_fact].
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

  Definition context_of_fact (f : fact) (f' : rel * list T) :=
    context_of_args f.(fact_args) (snd f').
  
  Definition context_of_hyps (hyps : list fact) (hyps' : list (rel * list T)) :=
    concat (zip context_of_fact hyps hyps').

  Definition agg_hyps'_len r ctx :=
    match r.(rule_agg) with
    | None => O
    | Some (_, aexpr) =>
        match option_coalesce (option_map get_set (subst_in_expr ctx aexpr.(agg_s))) with
        | Some s => length s
        | None => O
        end
    end.

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
  
  Lemma bare_in_context_fact ctx x f f' :
    In (var_expr x) f.(fact_args) ->
    interp_fact ctx f f' ->
    exists v, In (x, v) (context_of_fact f f').
  Proof.
    intros H1 H2. cbv [context_of_fact]. invert H2.
    eapply bare_in_context_args; eassumption.
  Qed.

  Lemma bare_in_context_hyps ctx x hyps hyps' :
    In (var_expr x) (flat_map fact_args hyps) ->
    Forall2 (interp_fact ctx) hyps hyps' ->
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
    intros [x v] Hx. cbv [context_of_fact] in Hx. apply in_concat in Hx. fwd.
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
  
  Lemma interp_fact_context_right ctx f f' :
    interp_fact ctx f f' ->
    Forall (fun '(x, v) => map.get ctx x = Some v) (context_of_fact f f').
  Proof.
    intros H. invert H. apply interp_args_context_right. assumption.
  Qed.

  Lemma interp_hyps_context_right ctx hyps hyps' :
    Forall2 (interp_fact ctx) hyps hyps' ->
    Forall (fun '(x, v) => map.get ctx x = Some v) (context_of_hyps hyps hyps').
  Proof.
    intros H. apply Forall2_combine in H. rewrite Forall_forall in *.
    intros x Hx. cbv [context_of_hyps] in *. rewrite in_concat in Hx.
    fwd. cbv [zip] in Hxp0. rewrite in_map_iff in Hxp0. fwd. destruct x1 as [v v'].
    apply H in Hxp0p1. apply interp_fact_context_right in Hxp0p1.
    rewrite Forall_forall in Hxp0p1. apply Hxp0p1 in Hxp1. assumption.
  Qed.

  Lemma interp_hyps_context_right_weak ctx hyps hyps' :
    Forall2 (interp_fact ctx) hyps hyps' ->
    map.extends ctx (map.of_list (context_of_hyps hyps hyps')).
  Proof.
    intros H. apply interp_hyps_context_right in H. cbv [map.extends].
    intros. apply of_list_Some_in in H0. rewrite Forall_forall in H.
    apply H in H0. assumption.
  Qed.
  
  Lemma context_of_hyps_agree ctx hyps hyps' v :
    Forall2 (interp_fact ctx) hyps hyps' ->
    In (var_expr v) (flat_map fact_args hyps) ->
    agree_on ctx (map.of_list (context_of_hyps hyps hyps')) v.
  Proof.
    intros H1 H2.
    pose proof bare_in_context_hyps as H'.
    specialize (H' _ _ _ _ ltac:(eassumption) ltac:(eassumption)). fwd.
    apply in_fst in H'. apply in_of_list_Some_strong in H'. fwd.
    eapply interp_hyps_context_right_weak in H1; eauto.
    specialize (H1 _ _ H'p0). cbv [agree_on]. rewrite H1, H'p0. reflexivity.
  Qed.

  Definition eval_aexpr aexpr ctx agg_hyps's :=
    match option_coalesce (option_map get_set (subst_in_expr ctx aexpr.(agg_s))) with
    | None => None
    | Some s' =>
        
        let body's := zip (fun i' agg_hyps' =>
                             let bodyctx := map.of_list (context_of_hyps aexpr.(agg_hyps) agg_hyps') in
                             let bodyctx := map.putmany ctx (map.put bodyctx aexpr.(agg_i) i') in
                             subst_in_expr bodyctx aexpr.(agg_body)) s' agg_hyps's in
        match option_all body's with
        | None => None
        | Some body's =>
            Some (fold_right (interp_agg aexpr.(agg_agg)) (agg_id aexpr.(agg_agg)) body's)
        end
    end.

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

  Lemma eval_aexpr_complete ctx aexpr res agg_hyps's :
    good_agg_expr aexpr ->
    interp_agg_expr ctx aexpr res agg_hyps's ->
    eval_aexpr aexpr ctx agg_hyps's = Some res.
  Proof.
    intros Hgood H. invert H. cbv [eval_aexpr]. simpl.
    apply subst_in_expr_complete in H0. rewrite H0. simpl. rewrite H1.
    erewrite Forall2_option_all. 1: reflexivity.
    cbv [zip]. rewrite <- Forall2_map_l. eapply Forall3_combine12.
    apply Forall3_swap23. eapply Forall3_impl; [|eassumption]. simpl.
    clear H2. intros x y z Hxyz. fwd.
    apply subst_in_expr_complete. 
    eapply interp_expr_agree_on; eauto. cbv [good_agg_expr] in Hgood.
    simpl in Hgood. rewrite Forall_forall in Hgood. rewrite Forall_forall.
    intros v Hv. cbv [agree_on]. rewrite map.get_putmany_dec.
    do 2 rewrite map.get_put_dec. destr (var_eqb i v); [reflexivity|].
    destruct (map.get ctx' v) eqn:E'. 
    - Search context_of_hyps. pose proof Hxyzp1 as Hxyzp1'.
      apply interp_hyps_context_right in Hxyzp1.
      pose proof E' as E''.
      erewrite map.get_of_list_zip in E' by eassumption.
      apply map.zipped_lookup_Some_in in E'.
      apply Hgood in E'. Search context_of_hyps var_expr.
      eapply bare_in_context_hyps in Hxyzp1'; eauto. fwd.
      apply in_fst in Hxyzp1'. apply in_of_list_Some_strong in Hxyzp1'.
      fwd. 
      rewrite Forall_forall in Hxyzp1. specialize (Hxyzp1 _ Hxyzp1'p1).
      simpl in Hxyzp1. rewrite <- E''. rewrite <- Hxyzp1.
      rewrite map.get_put_diff by auto. reflexivity.
    - eapply in_vars_interp_expr_not_None in Hxyzp2; eauto.
      rewrite map.get_put_diff in Hxyzp2 by auto. exfalso. auto.
  Qed.

  (*repeatedly iterate over set hyps.
    if we find x \in S, where S is bound to something,
    then seize on it.  for each x' in get_set S,
    bind x to x', and repeat.
   *)
  Definition is_Some {T : Type} (x : option T) :=
    match x with
    | Some _ => true
    | None => false
    end.
  Definition is_None {T : Type} (x : option T) :=
    match x with
    | Some _ => false
    | None => true
    end.
  Print find.
  Search (option _ -> option _ -> option _).
  Definition option_or {T : Type} (x y : option T) : option T :=
    match x, y with
    | Some x, _ => Some x
    | None, Some y => Some y
    | None, None => None
    end.
  Fixpoint find_Some {T U : Type} (f : T -> option U) (l : list T) :=
    match l with
    | a :: l => option_or (f a) (find_Some f l)
    | [] => None
    end.

  Lemma option_or_Some {U : Type} (x y : option U) z :
    option_or x y = Some z ->
    x = Some z \/ x = None /\ y = Some z.
  Proof.
    destruct x, y; simpl; intros; fwd; auto; congruence.
  Qed.

  Lemma option_or_None {U : Type} (x y : option U) :
    option_or x y = None ->
    x = None /\ y = None.
  Proof.
    destruct x, y; simpl; auto; congruence.
  Qed.
  
  Lemma find_Some_sound {V U : Type} (f : V -> option U) l y :
    find_Some f l = Some y ->
    Exists (fun x => f x = Some y) l.
  Proof.
    induction l; simpl.
    - congruence.
    - intros H. apply option_or_Some in H. destruct H; fwd; auto.
  Qed.

  Lemma find_Some_complete {V U : Type} (f : V -> option U) l :
    find_Some f l = None ->
    Forall (fun x => f x = None) l.
  Proof.
    induction l; simpl; auto.
    intros H. apply option_or_None in H. fwd. auto.
  Qed.

  Notation "x <- a ; f" := (match a with Some x => f | _ => None end)
                             (right associativity, at level 70).
  
  Definition get_one_binding ctx (set_hyps : list (expr * expr)) :=
    find_Some
      (fun '(x, s) =>
         x <- match x with
             | var_expr x => Some x
             | _ => None end;
       match map.get ctx x, subst_in_expr ctx s with
       | None, Some s' => Some (x, s')
       | _, _ => None
       end)
      set_hyps.

  Definition option_default {T : Type} (x : option T) (d : T) :=
    match x with
    | Some x => x
    | None => d
    end.
  
  Definition expand_ctx_from_set_hyps set_hyps ctx :=
    match get_one_binding ctx set_hyps with
    | Some (x, s') => map (map.put ctx x) (option_default (get_set s') [])
    | None => [ctx]
    end.

  Definition step_set_hyps_ctxs set_hyps ctxs :=
    flat_map (expand_ctx_from_set_hyps set_hyps) ctxs.

  Lemma get_one_binding_sound ctx ctx' set_hyps x s' :
    map.extends ctx' ctx ->
    Forall (x_in_S ctx') set_hyps ->
    get_one_binding ctx set_hyps = Some (x, s') ->
    map.get ctx x = None /\
      In (var_expr x) (map fst set_hyps) /\
      exists x',
        map.get ctx' x = Some x' /\
          In x' (option_default (get_set s') []).
  Proof.
    intros Hext Hsat H. cbv [get_one_binding] in H.
    apply find_Some_sound in H. apply Exists_exists in H. fwd.
    rewrite Forall_forall in Hsat. split; [assumption|]. split.
    { apply in_map_iff. eexists (_, _). simpl. eauto. }
    apply Hsat in Hp0. simpl in Hp0. fwd.
    invert Hp0p0. eexists. split; [eassumption|].
    apply subst_in_expr_sound in E1. eapply interp_expr_subst_more in E1; eauto.
    eapply interp_expr_det in E1. 2: exact Hp0p1. subst. rewrite Hp0p2. assumption.
  Qed.

  Lemma get_one_binding_extends ctx set_hyps x s' :
    get_one_binding ctx set_hyps = Some (x, s') ->
    map.get ctx x = None.
  Proof.
    intros H. cbv [get_one_binding] in H. apply find_Some_sound in H.
    apply Exists_exists in H. fwd. auto.
  Qed.

  (*I basically have no idea what this is or why i proved it*)
  (*I am sleepy*)
  Lemma idk P (set_hyps : list (expr * expr)) :
    (forall x y,
        In (var_expr x, y) set_hyps ->
        (forall v, In v (vars_of_expr y) -> P v) ->
        P x) ->
    (forall v, in_set_hyps v set_hyps ->
          P v \/ In (var_expr v) (map fst set_hyps)) ->
    well_founded (depends_on_in_set_hyps set_hyps) ->
    forall v, in_set_hyps v set_hyps ->
         P v.
  Proof.
    intros H1 H2 H3. intros v. specialize (H3 v). induction H3 as [v H3 H4].
    intros H5. apply H2 in H5. destruct H5 as [H5|H5]; auto. clear H3.
    apply in_map_iff in H5. fwd. destruct x as [x s]. simpl in H5p0. subst.
    eapply H1; eauto. intros. apply H4.
    - cbv [depends_on_in_set_hyps]. eauto.
    - cbv [in_set_hyps]. right. rewrite in_flat_map. eexists. rewrite in_map_iff. eauto.
  Qed.
  
  Lemma get_one_binding_complete ctx ctx' set_hyps :
    map.extends ctx' ctx ->
    Forall (x_in_S ctx') set_hyps ->
    get_one_binding ctx set_hyps = None ->
    (forall v, in_set_hyps v set_hyps ->
          map.get ctx v <> None \/ In (var_expr v) (map fst set_hyps)) ->
    well_founded (depends_on_in_set_hyps set_hyps) ->
    Forall (x_in_S ctx) set_hyps.
  Proof.
    intros Hext Hsat H Hwf1 Hwf2. cbv [get_one_binding] in H.
    apply find_Some_complete in H.
    assert (H': forall v, in_set_hyps v set_hyps -> map.get ctx v <> None).
    { apply idk; auto. intros x y H0 H1. intros H'. rewrite Forall_forall in H.
      specialize (H _ ltac:(eassumption)). simpl in H. rewrite H' in H.
      destruct_one_match_hyp; [congruence|]. rewrite Forall_forall in Hsat.
      specialize (Hsat _ ltac:(eassumption)). simpl in Hsat. fwd.
      eapply interp_expr_agree_on in Hsatp1.
      { apply subst_in_expr_complete in Hsatp1. rewrite E in Hsatp1. congruence. }
      apply Forall_forall. intros x0 ?. specialize (H1 _ ltac:(eassumption)).
      destruct (map.get ctx x0) eqn:Ex0; [|congruence].
      cbv [agree_on]. rewrite Ex0. apply Hext in Ex0. rewrite Ex0. reflexivity. }
    clear -Hext Hsat H'. rewrite Forall_forall in *. intros [x y] Hxy.
    specialize (Hsat _ Hxy). simpl in Hsat. fwd. cbv [x_in_S]. do 3 eexists.
    ssplit; eauto.
    - eapply interp_expr_agree_on; eauto. apply Forall_forall. intros v Hv.
      cbv [agree_on]. specialize (H' v). specialize' H'.
      { cbv [in_set_hyps]. left. rewrite in_flat_map. eexists. rewrite in_map_iff. eauto. }
      destruct (map.get ctx v) eqn:Ev; [|congruence]. apply Hext. apply Ev.
    - eapply interp_expr_agree_on; eauto. apply Forall_forall. intros v Hv.
      cbv [agree_on]. specialize (H' v). specialize' H'.
      { cbv [in_set_hyps]. right. rewrite in_flat_map. eexists. rewrite in_map_iff. eauto. }
      destruct (map.get ctx v) eqn:Ev; [|congruence]. apply Hext. apply Ev.
  Qed.

  Lemma step_progress' ctx'' ctx set_hyps :
    map.extends ctx'' ctx ->
    Forall (x_in_S ctx'') set_hyps ->
    (forall v, in_set_hyps v set_hyps ->
          map.get ctx v <> None \/ In (var_expr v) (map fst set_hyps)) ->
    well_founded (depends_on_in_set_hyps set_hyps) ->
    Exists (fun ctx' =>
              map.extends ctx'' ctx' /\
                (ctx' = ctx /\
                   Forall (x_in_S ctx) set_hyps \/
                   exists x,
                     map.get ctx' x <> None /\
                       map.get ctx x = None /\
                       In (var_expr x) (map fst set_hyps)))
      (expand_ctx_from_set_hyps set_hyps ctx).
  Proof.
    intros Hext Hsat Hwf1 Hwf2. cbv [expand_ctx_from_set_hyps].
    destruct (get_one_binding ctx set_hyps) as [(x&s')|] eqn:E.
    - eapply get_one_binding_sound in E; eauto. fwd. apply Exists_map.
      apply Exists_exists. eexists. split; [eassumption|]. split.
      { map_solver context_ok. }
      right. exists x. rewrite map.get_put_same. intuition (try congruence).
    - eapply get_one_binding_complete in E; eauto.
  Qed.

  Lemma step_progress ctx'' ctx ctxs set_hyps :
    map.extends ctx'' ctx ->
    In ctx ctxs ->
    Forall (x_in_S ctx'') set_hyps ->
    Forall (fun ctx =>
              (forall v, in_set_hyps v set_hyps ->
                    map.get ctx v <> None \/ In (var_expr v) (map fst set_hyps))) ctxs ->
    well_founded (depends_on_in_set_hyps set_hyps) ->
    Exists (fun ctx' =>
              map.extends ctx'' ctx' /\
                (ctx' = ctx /\
                Forall (x_in_S ctx) set_hyps \/
                exists x,
                    map.get ctx' x <> None /\
                    map.get ctx x = None /\
                    In (var_expr x) (map fst set_hyps)))
      (step_set_hyps_ctxs set_hyps ctxs).
  Proof.
    intros Hext Hin Hsat Hwf1 Hwf2. cbv [step_set_hyps_ctxs]. apply Exists_flat_map.
    apply Exists_exists. eexists. split; [eassumption|]. apply step_progress'; auto.
    rewrite Forall_forall in Hwf1. auto.
  Qed.

  Lemma expand_ctx_from_set_hyps_extends set_hyps ctx :
    Forall (fun ctx' => map.extends ctx' ctx) (expand_ctx_from_set_hyps set_hyps ctx).
  Proof.
    cbv [expand_ctx_from_set_hyps]. destruct (get_one_binding _ _) as [(x&s')|] eqn:E.
    - apply get_one_binding_extends in E. apply Forall_map. apply Forall_forall.
      intros x' _. map_solver context_ok.
    - eauto using map.extends_refl.
  Qed.

  Lemma step_extends set_hyps ctxs :
    Forall (fun ctx' => exists ctx, In ctx ctxs /\ map.extends ctx' ctx) (step_set_hyps_ctxs set_hyps ctxs).
  Proof.
    cbv [step_set_hyps_ctxs]. apply Forall_flat_map. apply Forall_forall.
    intros ctx Hctx. eapply Forall_impl. 2: apply expand_ctx_from_set_hyps_extends.
    simpl. eauto.
  Qed.

  Lemma steps_extends set_hyps ctxs n :
    Forall (fun ctx' => exists ctx, In ctx ctxs /\ map.extends ctx' ctx) (Nat.iter n (step_set_hyps_ctxs set_hyps) ctxs).
  Proof.
    apply Nat.iter_invariant.
    - intros x H. eapply Forall_impl. 2: apply step_extends. simpl. intros. fwd.
      rewrite Forall_forall in H. specialize (H _ ltac:(eassumption)). fwd.
      eauto using extends_trans.
    - apply Forall_forall. eauto using map.extends_refl.
  Qed.

  Check Exists_impl.
  Lemma Exists_impl_strong {A : Type} (P Q : A -> Prop) l :
    Exists P l ->
    (forall a, In a l -> P a -> Q a) ->
    Exists Q l.
  Proof. do 2 rewrite Exists_exists. intros. fwd. eauto. Qed.    

  Lemma steps_progress ctx'' n ctx set_hyps :
    map.extends ctx'' ctx ->
    Forall (x_in_S ctx'') set_hyps ->
    (forall v, in_set_hyps v set_hyps ->
                    map.get ctx v <> None \/ In (var_expr v) (map fst set_hyps)) ->
    well_founded (depends_on_in_set_hyps set_hyps) ->
    Exists (fun ctx' =>
              map.extends ctx'' ctx' /\ 
              (Forall (x_in_S ctx') set_hyps \/
                exists l,
                  length l = n /\ NoDup l /\
                    Forall (fun x => map.get ctx' x <> None /\
                                    map.get ctx x = None /\
                                    In (var_expr x) (map fst set_hyps)) l))
      (Nat.iter n (step_set_hyps_ctxs set_hyps) [ctx]).
  Proof.
    intros H H1 H2 H3. induction n.
    - simpl. apply Exists_exists. eexists. split; [simpl; eauto|].
      split; [assumption|]. right. exists nil. simpl. intuition constructor.
    - simpl. apply Exists_exists in IHn. fwd. cbv [step_set_hyps_ctxs].
      apply Exists_flat_map. eapply Exists_exists. eexists. split; [eassumption|].
      eapply Forall_forall in IHnp0. 2: apply steps_extends. simpl in IHnp0. fwd.
      eapply Exists_impl_strong.
      { apply step_progress'; auto. 2: eassumption. 1: assumption.
        intros v Hv. apply H2 in Hv. destruct Hv as [Hv|Hv]; auto. left. intros H'.
        apply Hv. destruct IHnp0p0; contradiction || subst.
        eauto using extends_None. }
      simpl. intros ctx' Hin Hctx'. fwd. split; [assumption|].
      eapply Forall_forall in Hin. 2: apply expand_ctx_from_set_hyps_extends.
      simpl in Hin. destruct IHnp2 as [IHnp2|IHnp2].
      { left. eapply Forall_impl; [|eassumption]. eauto using x_in_S_subst_more. }
      destruct Hctx'p1 as [Hctx'p1|Hctx'p1].
      { fwd. left. eapply Forall_impl; [|eassumption]. eauto using x_in_S_subst_more. }
      fwd. right. exists (x0 :: l). split; [reflexivity|]. split.
      + constructor; auto. intros H'. rewrite Forall_forall in IHnp2p2.
        apply IHnp2p2 in H'. fwd. auto.
      + constructor.
        -- intuition auto. subst. eauto using extends_None.
        -- eapply Forall_impl; [|eassumption]. simpl. intros. fwd. intuition auto.
           subst. eauto using extends_None.
  Qed.

  (*get all the possible contexts *)
  Definition all_set_hyps_ctxs ctx set_hyps :=
    Nat.iter (S (length set_hyps)) (step_set_hyps_ctxs set_hyps) [ctx].
  (* S is artifcat of dumb proof, not actually required. *)

  Lemma all_set_hyps_ctxs_extend ctx set_hyps :
    Forall (fun ctx' => map.extends ctx' ctx) (all_set_hyps_ctxs ctx set_hyps).
  Proof.
    cbv [all_set_hyps_ctxs]. eapply Forall_impl. 2: apply steps_extends.
    simpl. intros. fwd. destruct Hp0; contradiction || subst. assumption.
  Qed.
  
  Lemma all_set_hyps_ctxs_correct ctx'' ctx set_hyps :
    map.extends ctx'' ctx ->
    Forall (x_in_S ctx'') set_hyps ->
    (forall v, in_set_hyps v set_hyps ->
          map.get ctx v <> None \/ In (var_expr v) (map fst set_hyps)) ->
    well_founded (depends_on_in_set_hyps set_hyps) ->
    Exists (fun ctx' => map.extends ctx'' ctx' /\ Forall (x_in_S ctx') set_hyps)
      (all_set_hyps_ctxs ctx set_hyps).
  Proof.
    intros. eapply Exists_impl; cycle 1.
    { cbv [all_set_hyps_ctxs]. apply steps_progress; eauto. }
    clear. simpl. intros ctx' Hctx'. fwd. destruct Hctx'p1; auto. fwd.
    exfalso. assert (H: incl (map var_expr l) (map fst set_hyps)).
    { rewrite Forall_forall in Hp2. intros x Hx. apply in_map_iff in Hx.
      fwd. apply Hp2 in Hxp1. fwd. assumption. }
    eapply NoDup_incl_length in H.
    2: { apply FinFun.Injective_map_NoDup; auto. cbv [FinFun.Injective]. congruence. }
    do 2 rewrite length_map in *. lia.
  Qed.

  Definition all_rule_ctxs hyps set_hyps hyps' :=
    let ctx := map.of_list (context_of_hyps hyps hyps') in
    all_set_hyps_ctxs ctx set_hyps.

  (*this is a bit wordy because it should be applicable to stuff in agg_expr too,
    once/if i add set hyps there*)
  Lemma all_rule_ctxs_correct'' ctx hyps set_hyps hyps' :
    (forall v : var,
        in_set_hyps v set_hyps ->
        In (var_expr v) (flat_map fact_args hyps) \/
          In (var_expr v) (map fst set_hyps)) ->
    (forall v : var,
        In v (flat_map vars_of_fact hyps) ->
        In (var_expr v) (flat_map fact_args hyps) \/
          In (var_expr v) (map fst set_hyps)) ->
    well_founded (depends_on_in_set_hyps set_hyps) ->
    Forall2 (interp_fact ctx) hyps hyps' ->
    Forall (x_in_S ctx) set_hyps ->
    exists ctx',
      In ctx' (all_rule_ctxs hyps set_hyps hyps') /\
        map.extends ctx ctx' /\
        Forall2 (interp_fact ctx') hyps hyps' /\
        Forall (x_in_S ctx') set_hyps.
  Proof.
    intros Hwf1 Hgood Hwf2 Hh Hsh. cbv [all_rule_ctxs]. pose proof Hh as Hh'.
    apply interp_hyps_context_right in Hh'.
    eapply all_set_hyps_ctxs_correct in Hsh; cycle 1.
    { apply interp_hyps_context_right_weak. eassumption. }
    { intros v Hv. specialize (Hwf1 v Hv). destruct Hwf1 as [Hwf1|Hwf1]; auto.
      left. Search context_of_hyps. eapply bare_in_context_hyps in Hwf1; eauto.
      fwd. Search map.of_list. Search In fst. apply in_fst in Hwf1.
      apply in_of_list_Some in Hwf1. fwd. congruence. }
    { apply Hwf2. }
    rewrite Exists_exists in Hsh. fwd. exists x. intuition auto.
    - eapply Forall2_impl_strong; [|eassumption]. intros f (R&es') Hfes Hf Hes.
      eapply interp_fact_agree_on; [eassumption|].
      apply Forall_forall. intros v Hv. specialize (Hgood v).
      rewrite in_flat_map in Hgood. specialize (Hgood ltac:(eauto)).
      destruct Hgood as [Hgood|Hgood].
      + eapply bare_in_context_hyps in Hgood; eauto.
        fwd. apply in_fst in Hgood. apply in_of_list_Some_strong in Hgood. fwd.
        rewrite Forall_forall in Hh'. apply Hh' in Hgoodp1. cbv [agree_on].
        eapply Forall_forall in Hshp0. 2: apply all_set_hyps_ctxs_extend.
        simpl in Hshp0. apply Hshp0 in Hgoodp0. eauto using eq_trans.
      + apply in_map_iff in Hgood. fwd. rewrite Forall_forall in Hshp2.
        apply Hshp2 in Hgoodp1. destruct x0 as [x0 s0]. simpl in Hgoodp0. subst.
        simpl in Hgoodp1. fwd. invert Hgoodp1p0. cbv [agree_on]. rewrite H0.
        apply Hshp1 in H0. rewrite H0. reflexivity.
  Qed.    

  Hint Unfold appears_in_rule : core.
  Lemma all_rule_ctxs_correct' r ctx hyps' :
    good_rule r ->
    Forall2 (interp_fact ctx) r.(rule_hyps) hyps' ->
    Forall (x_in_S ctx) r.(rule_set_hyps) ->
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

  (* Lemma eval_rule_q_complete R args r hyps' agg_hyps's : *)
  (*   goodish_rule r -> *)
  (*   rule_impl' r (R, args) hyps' agg_hyps's -> *)
  (*   eval_rule_q r (skipn (outs R) args) hyps' agg_hyps's = [(R, args)]. *)
  (* Proof. *)
  (*   intros Hgood Himpl. cbv [eval_rule_q]. cbv [goodish_rule] in Hgood. fwd. *)
  (*   invert Himpl. rewrite Hgoodp0 in *. invert_list_stuff. simpl. rewrite app_nil_r. *)
  (*   invert H. *)
  (*   - rewrite <- H5 in *. fwd. erewrite subst_in_fact_complete. 1: reflexivity. *)
  (*     eapply interp_fact_agree_on; [eassumption|]. *)
  (*     apply Forall_forall. intros v H. cbv [agree_on]. invert H4. *)
  (*     rewrite map.get_putmany_dec. destruct_one_match. *)
  (*     + apply of_list_Some_in in E. apply interp_hyps_context_right in H1. *)
  (*       rewrite Forall_forall in H1. apply H1 in E. assumption. *)
  (*     + apply get_of_list_None_bw in E. specialize (Hgoodp2 v). specialize' Hgoodp2. *)
  (*       { cbv [appears_in_rule]. left. rewrite <- H5. *)
  (*         split; [intros ?; fwd; congruence|]. rewrite Hgoodp0. simpl. rewrite app_nil_r. *)
  (*         assumption. } *)
  (*       destruct Hgoodp2 as [H'|H']. *)
  (*       -- eapply bare_in_context_hyps in H'; [|eassumption]. fwd. *)
  (*          apply in_fst in H'. exfalso. auto. *)
  (*       -- eapply Forall2_skipn in H6. pose proof H6 as H6'. *)
  (*          apply interp_args_context_right in H6. rewrite Forall_forall in H6. *)
  (*          cbv [fact_ins] in Hgoodp1. eapply bare_in_context_args in H6'. *)
  (*          2: { eassumption. } *)
  (*          fwd. apply in_fst in H6'. apply in_of_list_Some_strong in H6'. *)
  (*          fwd. apply H6 in H6'p1. cbv [fact_ins]. rewrite H6'p0, H6'p1. reflexivity. *)
  (*   - rewrite <- H0 in *. fwd. erewrite eval_aexpr_complete; try assumption. *)
  (*     2: { eapply interp_agg_expr_agree_on; [eassumption|]. intros v Hv. *)
  (*          specialize (Hgoodp2 v). specialize' Hgoodp2. *)
  (*          { cbv [appears_in_rule]. right. right. eauto. } *)
  (*          cbv [agree_on]. rewrite map.get_putmany_dec. destruct_one_match. *)
  (*          + apply of_list_Some_in in E. apply interp_hyps_context_right in H1. *)
  (*            rewrite Forall_forall in H1. apply H1 in E. assumption. *)
  (*          + apply get_of_list_None_bw in E. *)
  (*            destruct Hgoodp2 as [H'|H']. *)
  (*            -- eapply bare_in_context_hyps in H'; [|eassumption]. fwd. *)
  (*               apply in_fst in H'. exfalso. auto. *)
  (*            -- invert H4. eapply Forall2_skipn in H5. pose proof H5 as H5'. *)
  (*               apply interp_args_context_right in H5. rewrite Forall_forall in H5. *)
  (*               cbv [fact_ins] in Hgoodp1. eapply bare_in_context_args in H5'. *)
  (*               2: { eassumption. } *)
  (*               fwd. apply in_fst in H5'. apply in_of_list_Some_strong in H5'. *)
  (*               fwd. apply H5 in H5'p1. cbv [fact_ins]. rewrite H5'p0. *)
  (*               rewrite map.get_put_diff in H5'p1; auto. intros ?. subst. *)
  (*               Search res. apply Hgoodp1. do 2 eexists. split; [|reflexivity]. *)
  (*               apply in_flat_map. eexists. split; [eassumption|]. simpl. auto. } *)
  (*     erewrite subst_in_fact_complete. 1: reflexivity. *)
  (*     eapply interp_fact_agree_on; [eassumption|]. *)
  (*     apply Forall_forall. intros v H. cbv [agree_on]. invert H4. *)
  (*     do 2 rewrite map.get_put_dec. destruct_one_match; try reflexivity. *)
  (*     rewrite map.get_putmany_dec. destruct_one_match. *)
  (*     + apply of_list_Some_in in E0. apply interp_hyps_context_right in H1. *)
  (*       rewrite Forall_forall in H1. apply H1 in E0. assumption. *)
  (*     + apply get_of_list_None_bw in E0. specialize (Hgoodp2 v). specialize' Hgoodp2. *)
  (*       { cbv [appears_in_rule]. left. rewrite <- H0. *)
  (*         split; [intros ?; fwd; congruence|]. rewrite Hgoodp0. simpl. rewrite app_nil_r. *)
  (*         assumption. } *)
  (*       destruct Hgoodp2 as [H'|H']. *)
  (*       -- eapply bare_in_context_hyps in H'; [|eassumption]. fwd. *)
  (*          apply in_fst in H'. exfalso. auto. *)
  (*       -- eapply Forall2_skipn in H7. pose proof H7 as H7'. *)
  (*          apply interp_args_context_right in H7. rewrite Forall_forall in H7. *)
  (*          cbv [fact_ins] in Hgoodp1. eapply bare_in_context_args in H7'. *)
  (*          2: { eassumption. } *)
  (*          fwd. apply in_fst in H7'. apply in_of_list_Some_strong in H7'. *)
  (*          fwd. apply H7 in H7'p1. cbv [fact_ins]. rewrite H7'p0. *)
  (*          rewrite map.get_put_diff in H7'p1; auto. *)
  (* Qed. *)

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
