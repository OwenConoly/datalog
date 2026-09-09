From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Permutation.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List Datatypes.Option Eqb.

From Datalog Require Import Map Tactics Fp List Eqb Datalog.
From GraphSearch Require Import Dag.

Import ListNotations.

Class type_signature {rel fn aggregator : Type} : Type :=
  {
    type : Type;
    fun_type : fn -> list type * type;
    rel_type : rel -> list type;
    agg_type : aggregator -> type * type;
  }.
Arguments type_signature : clear implicits.

Section __.
  Context `{params : datalog_params}.
  Context {var_eqb : Eqb exprvar} {var_eqb_ok : Eqb_ok var_eqb}.
  Context `{tsig : type_signature rel fn aggregator}.
  Context {type_context : map.map exprvar type}
          {type_context_ok : map.ok type_context}.

  Unset Elimination Schemes.
  Inductive well_typed_expr (tctx : type_context) : expr -> type -> Prop :=
  | wt_var_expr x t :
    map.get tctx x = Some t ->
    well_typed_expr tctx (expr.var x) t
  | wt_fun_expr f args arg_ts t :
    fun_type f = (arg_ts, t) ->
    Forall2 (well_typed_expr tctx) args arg_ts ->
    well_typed_expr tctx (expr.app f args) t.
  Set Elimination Schemes.

  Definition well_typed_clause (tctx : type_context) (c : clause) : Prop :=
    Forall2 (well_typed_expr tctx) c.(clause.args) (rel_type c.(clause.rel)).

  Definition well_typed_expr_pattern (tctx : type_context) (ep : expr_pattern) (t : type) : Prop :=
    match ep with
    | expr_pattern.any => True
    | expr_pattern.exactly e => well_typed_expr tctx e t
    end.

  Definition well_typed_clause_pattern (tctx : type_context) (c : clause_pattern) : Prop :=
    Forall2 (well_typed_expr_pattern tctx)
      c.(clause_pattern.args) (rel_type c.(clause_pattern.rel)).

  Definition well_typed_rule (r : rule) : Prop :=
    exists tctx : type_context,
      match r with
      | rule.impl concls hyps =>
          Forall (well_typed_clause tctx) concls /\
          Forall (well_typed_clause tctx) hyps
      | rule.agg concl_rel agg hyp_rel =>
          exists i_type in_type out_type shared,
            agg_type agg = (in_type, out_type) /\
            rel_type concl_rel = out_type :: shared /\
            rel_type hyp_rel = i_type :: in_type :: shared
      end.

  Definition well_typed_meta_rule (r : meta_rule) : Prop :=
    exists tctx : type_context,
      Forall (well_typed_clause_pattern tctx) r.(meta_rule.concls) /\
        Forall (well_typed_clause_pattern tctx) r.(meta_rule.hyps).

  Context {type_eqb : Eqb type} {type_eqb_ok : Eqb_ok type_eqb}.

  Fixpoint check_expr_type e t : option type_context :=
    match e with
    | expr.var x => Some (map.put map.empty x t)
    | expr.app f args =>
        let '(arg_ts, ret_t) := fun_type f in
        if (type_eqb ret_t t && Nat.eqb (length arg_ts) (length args))%bool
        then compatible_union_of_list_option (map2 check_expr_type args arg_ts)
        else None
    end.

  Definition check_clause_type (c : clause) : option type_context :=
    let arg_ts := rel_type c.(clause.rel) in
    if Nat.eqb (length c.(clause.args)) (length arg_ts)
    then compatible_union_of_list_option
           (map2 check_expr_type c.(clause.args) arg_ts)
    else None.

  Definition check_expr_pattern_type (ep : expr_pattern) (t : type) : option type_context :=
    match ep with
    | expr_pattern.any => Some map.empty
    | expr_pattern.exactly e => check_expr_type e t
    end.

  Definition check_clause_pattern_type (c : clause_pattern) : option type_context :=
    let arg_ts := rel_type c.(clause_pattern.rel) in
    if Nat.eqb (length c.(clause_pattern.args)) (length arg_ts)
    then compatible_union_of_list_option
           (map2 check_expr_pattern_type c.(clause_pattern.args) arg_ts)
    else None.

  Definition check_rule_type (r : rule) : option type_context :=
    match r with
    | rule.impl concls hyps =>
        compatible_union_of_list_option (map check_clause_type (concls ++ hyps))
    | rule.agg concl_rel agg hyp_rel =>
        let '(in_type, out_type) := agg_type agg in
        match rel_type concl_rel, rel_type hyp_rel with
        | out_t :: c_shared, _ :: in_t :: h_shared =>
            if (type_eqb out_type out_t &&
                type_eqb in_type in_t &&
                list_eqb c_shared h_shared)%bool
            then Some map.empty
            else None
        | _, _ => None
        end
    end.

  Definition check_meta_rule_type (r : meta_rule) : option type_context :=
    compatible_union_of_list_option
      (map check_clause_pattern_type (r.(meta_rule.concls) ++ r.(meta_rule.hyps))).

  Lemma well_typed_expr_extends e :
    forall tctx tctx' t,
      well_typed_expr tctx e t ->
      map.extends tctx' tctx ->
      well_typed_expr tctx' e t.
  Proof.
    induction e; intros tctx tctx' t' Hwt Hext.
    - inversion Hwt; subst. constructor. apply Hext. assumption.
    - inversion Hwt; subst. econstructor; [eassumption|].
      eapply Forall2_impl_strong; [eassumption|].
      intros a t_a Hwa Hin _. rewrite Forall_forall in H. eauto.
  Qed.

  Lemma well_typed_clause_extends tctx tctx' c :
    well_typed_clause tctx c ->
    map.extends tctx' tctx ->
    well_typed_clause tctx' c.
  Proof.
    cbv [well_typed_clause]. intros H Hext.
    eapply Forall2_impl_strong; [eassumption|].
    intros; eauto using well_typed_expr_extends.
  Qed.

  Lemma well_typed_clause_pattern_extends tctx tctx' c :
    well_typed_clause_pattern tctx c ->
    map.extends tctx' tctx ->
    well_typed_clause_pattern tctx' c.
  Proof.
    cbv [well_typed_clause_pattern]. intros H Hext.
    eapply Forall2_impl_strong; [eassumption|].
    intros [e|] t Hep _ _; cbv [well_typed_expr_pattern] in *;
      eauto using well_typed_expr_extends.
  Qed.

  Lemma check_expr_type_sound e :
    forall t tctx,
      check_expr_type e t = Some tctx ->
      well_typed_expr tctx e t.
  Proof.
    induction e; intros t' tctx Hck; simpl in Hck.
    - fwd. constructor. apply map.get_put_same.
    - destruct (fun_type f) as [arg_ts ret_t] eqn:Eft.
      destruct ((type_eqb ret_t t' && Nat.eqb (length arg_ts) (length args))%bool) eqn:Echk;
        [|discriminate].
      apply Bool.andb_true_iff in Echk. destruct Echk as [Eret Elen].
      destr (type_eqb ret_t t'); [|discriminate].
      apply Nat.eqb_eq in Elen.
      cbv [compatible_union_of_list_option] in Hck.
      destruct (option_all (map2 check_expr_type args arg_ts)) as [ctxs|] eqn:Eall;
        [|discriminate].
      simpl in Hck. fwd.
      apply option_all_map2_Forall3 in Eall; [|congruence].
      econstructor; [eassumption|].
      apply Forall3_ignore3_strong in Eall.
      eapply Forall2_impl_strong; [eassumption|].
      intros a t_a [c [Hin Hck_a]] Hin_a _.
      rewrite Forall_forall in H.
      eapply well_typed_expr_extends; eauto.
      eapply compatible_union_of_list_extends; eassumption.
  Qed.

  Lemma check_clause_type_sound c tctx :
    check_clause_type c = Some tctx ->
    well_typed_clause tctx c.
  Proof.
    cbv [check_clause_type well_typed_clause].
    intros Hck. fwd.
    cbv [compatible_union_of_list_option] in Hck.
    destruct (option_all _) as [ctxs|] eqn:Eall; [|discriminate].
    simpl in Hck. fwd.
    apply option_all_map2_Forall3 in Eall; [|assumption].
    apply Forall3_ignore3_strong in Eall.
    eapply Forall2_impl_strong; [eassumption|].
    intros a t_a [c0 [Hin Hck_a]] _ _.
    eapply well_typed_expr_extends; eauto using check_expr_type_sound.
    eapply compatible_union_of_list_extends; eassumption.
  Qed.

  Lemma check_clause_pattern_type_sound c tctx :
    check_clause_pattern_type c = Some tctx ->
    well_typed_clause_pattern tctx c.
  Proof.
    cbv [check_clause_pattern_type well_typed_clause_pattern].
    intros Hck.
    fwd.
    cbv [compatible_union_of_list_option] in Hck.
    destruct (option_all _) as [ctxs|] eqn:Eall; [|discriminate].
    simpl in Hck. fwd.
    apply option_all_map2_Forall3 in Eall; [|assumption].
    apply Forall3_ignore3_strong in Eall.
    eapply Forall2_impl_strong; [eassumption|].
    intros [e|] t_a [c0 [Hin Hck_a]] _ _;
      cbv [check_expr_pattern_type well_typed_expr_pattern] in *.
    - eapply well_typed_expr_extends; eauto using check_expr_type_sound.
      eapply compatible_union_of_list_extends; eassumption.
    - exact I.
  Qed.

  Lemma check_rule_type_sound r tctx :
    check_rule_type r = Some tctx ->
    well_typed_rule r.
  Proof.
    cbv [check_rule_type well_typed_rule]. destruct r as [concls hyps|cr ag hr].
    - intros Hck. exists tctx.
      cbv [compatible_union_of_list_option] in Hck.
      destruct (option_all (map check_clause_type (concls ++ hyps))) as [ctxs|] eqn:Eall;
        [|discriminate].
      simpl in Hck.
      destruct (compatible_union_of_list ctxs) as [u|] eqn:Eun;
        [|discriminate].
      simpl in Hck. inversion Hck; subst u; clear Hck.
      pose proof (compatible_union_of_list_extends _ _ Eun) as Hext.
      apply option_all_map_Some' in Eall.
      apply Forall_app.
      enough (Hall : Forall (well_typed_clause tctx) (concls ++ hyps)) by tauto.
      apply Forall_forall. intros c0 Hin.
      assert (In (check_clause_type c0) (map Some ctxs)) as Hin'
          by (rewrite <- Eall; apply in_map; assumption).
      apply in_map_iff in Hin'. destruct Hin' as [m [Heq Hin_m]].
      eapply well_typed_clause_extends; [eauto using check_clause_type_sound|].
      auto.
    - destruct (agg_type ag) as [in_t out_t] eqn:Eagt.
      destruct (rel_type cr) as [|out_t' c_sh] eqn:Ecr; [discriminate|].
      destruct (rel_type hr) as [|i_t [|in_t' h_sh]] eqn:Ehr; try discriminate.
      destruct ((type_eqb out_t out_t' &&
                 type_eqb in_t in_t' &&
                 list_eqb c_sh h_sh)%bool) eqn:Echk; [|discriminate].
      intros _.
      apply Bool.andb_true_iff in Echk. destruct Echk as [Echk Esh].
      apply Bool.andb_true_iff in Echk. destruct Echk as [Eout Ein].
      destr (type_eqb out_t out_t'); [|discriminate].
      destr (type_eqb in_t in_t'); [|discriminate].
      destr (list_eqb c_sh h_sh); [|discriminate].
      exists map.empty, i_t, in_t', out_t', h_sh. auto.
  Qed.

  Lemma check_meta_rule_type_sound r tctx :
    check_meta_rule_type r = Some tctx ->
    well_typed_meta_rule r.
  Proof.
    cbv [check_meta_rule_type well_typed_meta_rule].
    remember (meta_rule.concls r) as concls. remember (meta_rule.hyps r) as hyps.
    intros Hck. exists tctx.
    cbv [compatible_union_of_list_option] in Hck.
    destruct (option_all (map check_clause_pattern_type (concls ++ hyps))) as [ctxs|] eqn:Eall;
      [|discriminate].
    simpl in Hck.
    destruct (compatible_union_of_list ctxs) as [u|] eqn:Eun;
      [|discriminate].
    simpl in Hck. inversion Hck; subst u; clear Hck.
    pose proof (compatible_union_of_list_extends _ _ Eun) as Hext.
    apply option_all_map_Some' in Eall.
    apply Forall_app.
    enough (Hall : Forall (well_typed_clause_pattern tctx) (concls ++ hyps)) by tauto.
    apply Forall_forall. intros c0 Hin.
    assert (In (check_clause_pattern_type c0) (map Some ctxs)) as Hin'
      by (rewrite <- Eall; apply in_map; assumption).
    apply in_map_iff in Hin'. destruct Hin' as [m [Heq Hin_m]].
    eapply well_typed_clause_pattern_extends;
      [eauto using check_clause_pattern_type_sound|]. auto.
  Qed.

End __.
