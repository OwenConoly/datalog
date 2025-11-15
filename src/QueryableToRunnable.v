From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Permutation.

From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics.

From Stdlib Require Import Wellfounded.Inclusion.
From Stdlib Require Import Wellfounded Wellfounded.Wellfounded Wellfounded.Transitive_Closure.
From Stdlib Require Import Wellfounded.Inverse_Image.
From Stdlib Require Import Relations.Relation_Definitions.

From Datalog Require Import Datalog Map Tactics Fp List Interpreter Dag.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List.

Import ListNotations.

Section relmap.
  Context {rel1 rel2 var fn aggregator T : Type}.
  Context `{sig : signature fn aggregator T}.
  Context (g : rel1 -> rel2).
  Context {context : map.map var T} {context_ok : map.ok context}.
  Context {var_eqb : var -> var -> bool} {var_eqb_spec :  forall x0 y0 : var, BoolSpec (x0 = y0) (x0 <> y0) (var_eqb x0 y0)}.

  Definition fact_relmap (f : fact rel1 var fn) :=
    {| fact_R := g f.(fact_R); fact_args := f.(fact_args) |}.

  Definition fact'_relmap (f' : rel1 * list T) :=
    let (R, args) := f' in (g R, args).

  Definition agg_expr_relmap (ae : agg_expr rel1 var fn aggregator) :=
    {| agg_agg := ae.(agg_agg); agg_i := ae.(agg_i); agg_vs := ae.(agg_vs);
                                     agg_s := ae.(agg_s);
                                     agg_body := ae.(agg_body);
                                     agg_hyps := map fact_relmap ae.(agg_hyps) |}.

  Lemma vars_of_fact_relmap f :
    vars_of_fact (fact_relmap f) = vars_of_fact f.
  Proof. reflexivity. Qed.

  Lemma good_agg_expr_relmap ae :
    good_agg_expr ae ->
    good_agg_expr (agg_expr_relmap ae).
  Proof.
    cbv [good_agg_expr]. intros H. eapply Forall_impl; [|eassumption]. simpl.
    intros. rewrite flat_map_map. simpl. apply H0.
  Qed.

  Lemma appears_in_agg_expr_with_bool v ae :
    appears_in_agg_expr v (agg_expr_relmap ae) ->
    appears_in_agg_expr v ae.
  Proof.
    destruct ae. cbv [agg_expr_relmap appears_in_agg_expr]. simpl.
    rewrite flat_map_map. erewrite flat_map_ext.
    2: { intros x. rewrite vars_of_fact_relmap. reflexivity. }
    auto.
  Qed.

  Lemma interp_fact_relmap ctx f f' :
    interp_fact ctx f f' ->
    interp_fact ctx (fact_relmap f) (fact'_relmap f').
  Proof. intros H. invert H. constructor. simpl. assumption. Qed.

  Hint Resolve interp_fact_relmap : core.
  Hint Constructors Forall3 : core.
  
  Lemma interp_agg_expr_relmap ctx (aexpr : agg_expr rel1 var fn aggregator) res' agg_hyps' :
    interp_agg_expr ctx aexpr res' agg_hyps' ->
    interp_agg_expr ctx (agg_expr_relmap aexpr) res' (map (map fact'_relmap) agg_hyps').
  Proof.
    intros H. invert H. cbv [agg_expr_relmap]. simpl.
    econstructor; eauto.
    erewrite <- Forall3_map3. eapply Forall3_impl; [|eassumption].
    simpl. intros. fwd. do 2 eexists. intuition eauto.
    rewrite <- Forall2_map_l. erewrite <- Forall2_map_r.
    eapply Forall2_impl; [|eassumption]. intros. apply interp_fact_relmap.
    eassumption.
  Qed.

  Lemma interp_facts_relmap hyps hyps' ctx :
    Forall2 (interp_fact ctx) hyps hyps' ->
    map fact_R hyps = map fst hyps' /\
      Forall2 (interp_fact ctx) (map fact_relmap hyps) (map fact'_relmap hyps').
  Proof. induction 1; simpl; fwd; intuition eauto. invert H. simpl. f_equal; auto. Qed.  
End relmap.

Section Transform.
  Context {rel var fn aggregator T : Type}.
  Context `{sig : signature fn aggregator T} `{query_sig : query_signature rel}.
  Context {context : map.map var T} {context_ok : map.ok context}.
  Context {rel_eqb : rel -> rel -> bool} {rel_eqb_spec :  forall x0 y0, BoolSpec (x0 = y0) (x0 <> y0) (rel_eqb x0 y0)}.
  Context {var_eqb : var -> var -> bool} {var_eqb_spec :  forall x0 y0, BoolSpec (x0 = y0) (x0 <> y0) (var_eqb x0 y0)}. 

  Local Notation rule' := (rule (rel*bool) var fn aggregator).
  Local Notation rule := (rule rel var fn aggregator).
  Local Notation fact' := (@fact (rel*bool) var fn).
  Local Notation fact := (@fact rel var fn).
  Local Notation agg_expr' := (agg_expr (rel * bool) var fn aggregator).
  Local Notation agg_expr := (agg_expr rel var fn aggregator).
  
  Notation plus_false := (fun x => (x, false)).
  Notation plus_true := (fun x => (x, true)).

  Definition agree (p : list rule) (r1 r2 : rule) :=
    forall R args1 args2 hyps1 hyps2,
      rule_impl r1 (R, args1) hyps1 ->
      rule_impl r2 (R, args2) hyps2 ->
      Forall (prog_impl_fact p) hyps1 ->
      Forall (prog_impl_fact p) hyps2 ->
      skipn (outs R) args1 = skipn (outs R) args2 ->
      args1 = args2.

  Lemma agree_weaken p1 p2 r1 r2 :
    agree p1 r1 r2 ->
    incl p2 p1 ->
    agree p2 r1 r2.
  Proof. cbv [agree]. eauto 6 using Forall_impl, prog_impl_fact_subset. Qed.    

  Definition pairs_satisfy {X : Type} (P : X -> X -> Prop) (l : list X) :=
    forall x1 x2, In x1 l -> In x2 l -> x1 = x2 \/ P x1 x2.

  Lemma pairs_satisfy_weaken {X : Type} P1 P2 (l1 l2 : list X) :
    pairs_satisfy P1 l1 ->
    (forall x y, P1 x y -> P2 x y) ->
    incl l2 l1 ->
    pairs_satisfy P2 l2.
  Proof.
    cbv [pairs_satisfy]. intros H1 H2 H3 x y Hx Hy.
    specialize (H1 x y ltac:(eauto) ltac:(eauto)). destruct H1; auto.
  Qed.

  Definition functional (p : list rule) :=
    forall args1 args2 R,
      prog_impl_fact p (R, args1) ->
      prog_impl_fact p (R, args2) ->
      skipn (outs R) args1 = skipn (outs R) args2 ->
      args1 = args2.
  
  Hint Resolve pairs_satisfy_weaken agree_weaken : core.

  Lemma hyp_ins_det' ctx (r : rule) R (args : list T) hyps ahyps :
    goodish_rule r ->
    rule_impl' ctx r (R, args) hyps ahyps ->
    exists concl,
      r.(rule_concls) = [concl] /\
        let ctx := map.of_list (context_of_args (skipn (outs R) concl.(fact_args)) (skipn (outs R) args)) in
        Forall2 (fun f '(R, hyp_args) =>
                   f.(fact_R) = R /\ Forall2 (interp_expr ctx) (skipn (outs R) f.(fact_args)) (skipn (outs R) hyp_args))
          r.(rule_hyps) hyps.
  Proof.
    intros Hgood H. invert H. cbv [goodish_rule] in Hgood. fwd. eexists.
    split; [eassumption|]. simpl.
    rewrite Hgoodp0 in *. invert_list_stuff.
    eapply Forall2_impl_strong; [|eassumption].
    intros f (Ry&argsy) Hfy Hf Hy. invert Hfy. split; [reflexivity|].
    eapply Forall2_impl_strong. 2: apply Forall2_skipn; eassumption.
    intros x y Hx Hy0 Hxy. eapply interp_expr_agree_on; [eassumption|].
    rewrite Forall_forall. intros v Hv. assert (In (var_expr v) (fact_ins concl)).
    { apply Hgoodp3. apply in_flat_map. eexists. split; eauto.
      apply in_flat_map. eauto. }
    invert H4. eapply Forall2_skipn in H7. pose proof H7 as H7'.
    eapply bare_in_context_args in H7.
    2: { apply Hgoodp3. apply in_flat_map. eexists. split; [|eassumption].
         apply in_flat_map. eauto. }
    apply interp_args_context_right in H7'.
    fwd. cbv [agree_on]. apply in_fst in H7. apply in_of_list_Some_strong in H7.
    fwd. rewrite H7p0. rewrite Forall_forall in H7'. apply H7' in H7p1.
    move H0 at bottom. invert H0; [assumption|]. rewrite <- H1 in *.
    rewrite map.get_put_diff in H7p1; auto. intros ?. subst.
    Search res. apply Hgoodp1. do 2 eexists. split; [|reflexivity].
    apply in_flat_map. eexists. split; [eassumption|]. simpl. auto.
  Qed.

  Lemma hyp_ins_det (r : rule) ctx1 ctx2 R args1 args2 hyps1 hyps2 ahyps1 ahyps2 :
    goodish_rule r ->
    rule_impl' ctx1 r (R, args1) hyps1 ahyps1 ->
    rule_impl' ctx2 r (R, args2) hyps2 ahyps2 ->
    skipn (outs R) args1 = skipn (outs R) args2 ->
    Forall2 (fun '(R1, hyp1) '(R2, hyp2) =>
               R1 = R2 /\ skipn (outs R1) hyp1 = skipn (outs R2) hyp2)
      hyps1 hyps2.
  Proof.
    intros Hgood H1 H2 Hsame. eapply hyp_ins_det' in H1, H2; try assumption.
    fwd. rewrite H1p0 in *. invert H2p0. simpl in *.
    apply Forall2_flip in H1p1. eapply Forall2_Forall2_Forall3 in H2p1; [|exact H1p1].
    apply Forall3_ignore2 in H2p1. eapply Forall2_impl; [|eassumption].
    simpl. intros [Ra argsa] [Rb argsb] H. fwd. split; [reflexivity|].
    apply Forall2_flip in Hp1p1. eapply Forall2_Forall2_Forall3 in Hp3; [|exact Hp1p1].
    apply Forall3_ignore2 in Hp3. apply Forall2_eq_eq.
    eapply Forall2_impl; [|eassumption]. simpl. intros a b Hab. fwd.
    rewrite Hsame in *. eapply interp_expr_det; eassumption.
  Qed.

    (*if we get a message saying concls of r need to be computed, then send out messages
    saying premises of r need to be computed*)
  (*note: this is nonsensical if length r.(rule_concls) > 1*)
  Definition request_hyps (r : rule) : rule' :=
    {| rule_agg := None;
      rule_hyps := map (fact_relmap plus_false) (map with_only_ins r.(rule_concls));
      rule_concls := map (fact_relmap plus_false) (map with_only_ins r.(rule_hyps));
      rule_set_hyps := []
    |}.

  Definition noop_rule : rule' :=
    {| rule_agg := None;
      rule_hyps := [];
      rule_concls := [];
      rule_set_hyps := [] |}.

  Definition request_agg_hyps (r : rule) : rule' :=
    match r.(rule_agg) with
    | Some (res, aexpr) =>
        {| rule_agg := None;
          rule_hyps := map (fact_relmap plus_false) (map with_only_ins r.(rule_concls));
          rule_concls := map (fact_relmap plus_false) (map with_only_ins aexpr.(agg_hyps));
          rule_set_hyps := [(var_expr aexpr.(agg_i), aexpr.(agg_s))] |}
    | None => noop_rule
    end.

  (*add a hypothesis saying that the conclusion is something we need to compute*)
  (*note: this is fairly nonsensical (not semantically equivalent) if length r.(rule_concls) > 1*)
  Definition add_hyp (r : rule) : rule' :=
    {| rule_agg := option_map (fun '(x, y) => (x, agg_expr_relmap plus_true y)) r.(rule_agg);
      rule_hyps := map (fact_relmap plus_false) (map with_only_ins r.(rule_concls)) ++
                     map (fact_relmap plus_true) r.(rule_hyps);
      rule_concls := map (fact_relmap plus_true) r.(rule_concls);
      rule_set_hyps := r.(rule_set_hyps) |}.

  (*semanticallly equivalent if each rule has concl length at most 1*)
  Definition make_good (p : list rule) : list rule' :=
    map add_hyp p ++ map request_hyps p ++ map request_agg_hyps p.

  Print goodish_rule.
  Definition good_index (r : rule) :=
    match r.(rule_agg) with
    | None => True
    | Some (_, aexpr) =>
        ~In aexpr.(agg_i) (flat_map vars_of_expr (flat_map fact_ins r.(rule_concls))) /\
          ~In aexpr.(agg_i) (flat_map vars_of_expr (flat_map fact_ins r.(rule_hyps)))
    end.

  Lemma ahyp_ins_det'1 ctx0 (r : rule) R (args : list T) hyps ahypss :
    goodish_rule r ->
    rule_impl' ctx0 r (R, args) hyps ahypss ->
    exists concl,
      r.(rule_concls) = [concl] /\
        match r.(rule_agg) with
        | None => ahypss = []
        | Some (_, aexpr) =>
            let ctx := map.of_list (context_of_args (skipn (outs R) concl.(fact_args)) (skipn (outs R) args)) in
            exists s',
              interp_expr ctx aexpr.(agg_s) s' /\
                Forall2 (fun i' ahyps =>
                          let ctx' := map.put ctx aexpr.(agg_i) i' in
                          Forall2 (fun f '(R, hyp_args) =>
                                     f.(fact_R) = R /\ Forall2 (interp_expr ctx') (skipn (outs R) f.(fact_args)) (skipn (outs R) hyp_args))
                            aexpr.(agg_hyps) ahyps) (option_default (get_set s') []) ahypss
        end.
  Proof.
    intros Hgood H. invert H. cbv [goodish_rule] in Hgood. fwd.
    rewrite Hgoodp0 in *. invert_list_stuff. eexists.
    split; [reflexivity|]. simpl. invert H0. 1: reflexivity.
    rewrite <- H in *. fwd. invert H6. simpl in *.
    eexists. split.
    { eapply interp_expr_agree_on; [eassumption|].
      apply Forall_forall. intros v Hv. apply Hgoodp5p1 in Hv.
      invert H4. eapply Forall2_skipn in H8.
      apply context_of_args_agree_on; auto.
      eapply Forall2_impl_strong; [|eassumption].
      intros e e' He Hin _. eapply interp_expr_agree_on; [eassumption|].
      apply Forall_forall. intros v' Hv'. cbv [agree_on]. apply map.get_put_diff.
      intros H'. subst. apply Hgoodp1. eexists. eexists. intuition eauto.
      apply in_flat_map. eauto. }
    apply Forall3_ignore2 in H5. rewrite H1. simpl.
    eapply Forall2_impl; [|eassumption].
    simpl. intros i' ahyps' Hh. fwd.
    eapply Forall2_impl_strong; [|eassumption].
    intros f (R'&args'). invert 1. intros Hin1 Hin2. split; [reflexivity|].
    eapply Forall2_impl_strong. 2: apply Forall2_skipn; eassumption.
    intros e e' He Hine Hine'. eapply interp_expr_agree_on; [eassumption|].
    apply Forall_forall. intros v Hv. cbv [agree_on].
    rewrite <- map.put_putmany_commute. do 2 rewrite map.get_put_dec.
    destr (var_eqb i v); [reflexivity|].
    move H4 at bottom. invert H4.
    move Hgoodp5p2 at bottom. specialize (Hgoodp5p2 v). specialize' Hgoodp5p2.
    { apply in_flat_map. eexists. intuition eauto. apply in_flat_map. eauto. }
    destruct Hgoodp5p2 as [Hgoodp5p2|Hgoodp5p2]; [congruence|]. fwd.
    eapply Forall2_skipn in H8. eapply context_of_args_agree_on in H8.
    2: { eassumption. }
    cbv [agree_on] in H8. rewrite map.get_put_diff in H8; cycle 1.
    { intros H'. subst. apply Hgoodp1. eexists. eexists. intuition eauto.
      apply in_flat_map. exists (var_expr res). simpl. eauto. }
    rewrite <- H8. rewrite map.get_putmany_dec. destruct_one_match; auto.
    exfalso. erewrite map.get_of_list_zip in E0 by eassumption.
    apply map.zipped_lookup_Some_in in E0. auto.
  Qed.

  Lemma ahyp_ins_det ctx1 ctx2 (r : rule) R args1 args2 hyps ahypss1 ahypss2 :
    goodish_rule r ->
    rule_impl' ctx1 r (R, args1) hyps ahypss1 ->
    rule_impl' ctx2 r (R, args2) hyps ahypss2 ->
    skipn (outs R) args1 = skipn (outs R) args2 ->
    Forall2 (Forall2 (fun '(R1, hyp1) '(R2, hyp2) =>
                        R1 = R2 /\ skipn (outs R1) hyp1 = skipn (outs R2) hyp2))
      ahypss1 ahypss2.
  Proof.
    intros Hgood H1 H2 Hsame.
    apply ahyp_ins_det'1 in H1, H2; try assumption.
    fwd. rewrite H1p0 in *. invert_list_stuff.
    destruct r.(rule_agg) as [(?&?)|]; simpl in *.
    2: subst; constructor. invert_list_stuff. rewrite Hsame in *.
    fwd. eapply interp_expr_det in H1p1p0; [|exact H2p1p0]. subst.
    apply Forall2_flip in H1p1p1.
    eapply Forall2_Forall2_Forall3 in H2p1p1; [|exact H1p1p1].
    clear H1p1p1. apply Forall3_ignore2 in H2p1p1.
    eapply Forall2_impl; [|eassumption]. simpl. intros l1 l2 H. fwd.
    apply Forall2_flip in Hp1. eapply Forall2_Forall2_Forall3 in Hp2; [|exact Hp1].
    clear Hp1. clear H2p1p1. apply Forall3_ignore2 in Hp2.
    eapply Forall2_impl; [|eassumption]. simpl. intros [? ?] [? ?] H'. fwd.
    split; [reflexivity|].
    apply Forall2_flip in H'p1p1.
    eapply Forall2_Forall2_Forall3 in H'p3; [|exact H'p1p1].
    clear H'p1p1. clear Hp2. apply Forall3_ignore2 in H'p3. apply Forall2_eq_eq.
    eapply Forall2_impl; [|eassumption].
    simpl. intros. fwd. eapply interp_expr_det; eassumption.
  Qed.

  Lemma agree_functional p :
    dag (rel_graph p) ->
    Forall goodish_fun p ->
    Forall goodish_rule p ->
    pairs_satisfy (agree p) p ->
    functional p.
  Proof.
    intros H1 Hfun H2 H3. cbv [functional]. intros args1 args2 R. revert args1 args2.
    specialize (H1 R). induction H1. clear H.
    intros args1 args2 Hargs1 Hargs2 Hins.
    invert Hargs1. invert Hargs2.
    pose proof H as Hrel1. pose proof H4 as Hrel2.
    apply rel_graph_spec in Hrel1, Hrel2. 
    cbv [pairs_satisfy] in H3. rewrite Exists_exists in *. fwd.
    match goal with
    | H1: _ , H2: _ |- _ => specialize (H3 _ _ H1 H2)
    end.
    destruct H3; [|solve[eauto]]. subst. cbv [rule_impl] in *. fwd.
    pose proof hyp_ins_det as H'. epose proof (H' _ _ _ _ args1 args2) as H'.
    rewrite Forall_forall in *.
    specialize (H' _ _ _ _ ltac:(eauto) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
    assert (hyps'0 = hyps').
    { apply Forall2_eq_eq. eapply Forall2_impl_strong; [|eassumption].
      simpl. intros [R1' args1'] [R2' args2'] H12 H1' H2'. fwd. f_equal.
      eapply H0; eauto.
      - move Hrel1 at bottom. eapply (Hrel1 (_, _)). apply in_app_iff. eauto.
      - eapply H1. apply in_app_iff. eauto.
      - eapply H5. apply in_app_iff. eauto. }
    subst. clear H'.
    pose proof ahyp_ins_det as H'. epose proof (H' _ _ _ _ args1 args2) as H'.
    specialize (H' _ _ _ ltac:(eauto) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
    assert (agg_hyps's0 = agg_hyps's).
    { apply Forall2_eq_eq. eapply Forall2_impl_strong; [|eassumption].
      simpl. intros xs ys Hxsys Hxs Hys. apply Forall2_eq_eq.
      eapply Forall2_impl_strong; [|eassumption]. simpl.
      intros [R1' args1'] [R2' args2'] H12 H1' H2'. fwd. f_equal.
      eapply H0; eauto.
      - move Hrel1 at bottom. eapply (Hrel1 (_, _)). apply in_app_iff. rewrite in_concat. eauto.
      - eapply H1. apply in_app_iff. rewrite in_concat. eauto.
      - eapply H5. apply in_app_iff. rewrite in_concat. eauto. }
    subst. clear H'. Print goodish_rule.
    apply eval_rule_q_complete in Hp1p1, H4p1p1; auto.
    rewrite Hins in *. rewrite Hp1p1 in H4p1p1. invert_list_stuff.
    reflexivity.
  Qed.      

  Ltac t :=
    repeat match goal with
      | _ => assumption || contradiction
      | H: context[In _ (flat_map _ _)] |- _ => rewrite in_flat_map in H
      | H: context[In _ (map _ _)] |- _ => rewrite in_map_iff in H
      | H: context[In _ (_ ++ _)] |- _ => rewrite in_app_iff in H
      | |- In _ (map _ _) => apply in_map_iff
      | |- In _ (flat_map _ _) => apply in_flat_map
      | |- In _ (_ ++ _) => apply in_app_iff
      | |- exists _, _ /\ _ => eexists; split; [solve[eauto] |]
      | |- _ /\ _ => split; [solve[eauto] |]
      | _ => progress (intros; cbv [rel_graph edges_of_rule add_hyp request_agg_hyps rule_agg_hyps] in *; fwd; subst; simpl in * )
      | _ => progress invert_list_stuff
      | _ => destruct_one_match_hyp
      | _ => solve[eauto]
      | H: _ = [_] |- _ => rewrite H in *
      | |- _ \/ False => left
      | H: _ \/ _ |- _ => destruct H
      end.

  Lemma request_hyps_dag' b1 b2 R1 R2 r :
    In ((R1, b1), (R2, b2)) (edges_of_rule (request_hyps r)) ->
    b1 = false /\ b2 = false /\ In (R2, R1) (edges_of_rule r).
  Proof. t. Qed.

  Lemma request_agg_hyps_dag' b1 b2 R1 R2 r :
    In ((R1, b1), (R2, b2)) (edges_of_rule (request_agg_hyps r)) ->
    b1 = false /\ b2 = false /\ In (R2, R1) (edges_of_rule r).
  Proof. t. Qed.

  Lemma add_hyp_dag' b1 b2 R1 R2 r concl :
    r.(rule_concls) = [concl] ->
    In ((R1, b1), (R2, b2)) (edges_of_rule (add_hyp r)) ->
    b1 = true /\ if b2 then In (R1, R2) (edges_of_rule r) else R2 = R1.
  Proof. t. Qed.

  Lemma map_add_hyp_dag' b1 b2 R1 R2 p :
    Forall (fun r => exists concl, r.(rule_concls) = [concl]) p ->
    In ((R1, b1), (R2, b2)) (rel_graph (map add_hyp p)) ->
    b1 = true /\ if b2 then In (R1, R2) (rel_graph p) else R2 = R1.
  Proof.
    intros H1 H2. apply in_flat_map in H2. fwd. apply in_map_iff in H2p0. fwd.
    rewrite Forall_forall in H1. specialize (H1 _ H2p0p1). fwd.
    eapply add_hyp_dag' in H2p1; eauto. fwd. destruct b2; auto. intuition auto.
    apply in_flat_map. eauto.
  Qed.

  Lemma map_request_hyps_incl p :
    inclusion _
      (edge_rel (rel_graph (map request_hyps p ++ map request_agg_hyps p)))
      (fun x y => snd x = false /\ snd y = false /\ edge_rel (rel_graph p) (fst y) (fst x)).
  Proof.
    intros [R1 b1] [R2 b2] H. cbv [edge_rel] in *. rewrite rel_graph_app in H.
    apply in_app_iff in H. destruct H.
    - cbv [rel_graph] in H. rewrite flat_map_map in H. rewrite in_flat_map in H.
      fwd. apply request_hyps_dag' in Hp1. fwd. simpl. intuition auto.
      cbv [rel_graph]. apply in_flat_map. eauto.
    - cbv [rel_graph] in H. rewrite flat_map_map in H. rewrite in_flat_map in H.
      fwd. apply request_agg_hyps_dag' in Hp1. fwd. simpl. intuition auto.
      cbv [rel_graph]. apply in_flat_map. eauto.
  Qed.

  Lemma map_request_hyps_dag p :
    dag (rel_graph p) ->
    dag (rel_graph (map request_hyps p ++ map request_agg_hyps p)).
  Proof.
    intros H. eapply wf_incl. 1: apply map_request_hyps_incl.
    eapply wf_incl. 2: apply wf_inverse_image; apply dag_dag_alt; eassumption.
    intros x y Hxy. fwd. eassumption.
  Qed.
  
  Lemma map_add_hyp_dag p :
    Forall (fun r : rule => exists concl : fact, rule_concls r = [concl]) p ->
    dag (rel_graph p) ->
    dag (rel_graph (map add_hyp p)).
  Proof.
    intros H0 H.
    intros (R, b). specialize (H R). induction H. constructor. intros (Ry, By) Hy.
    apply map_add_hyp_dag' in Hy; auto. fwd. destruct By.
    { apply H1. assumption. }
    subst. constructor. clear -H0. intros (Ry, By) Hy. apply map_add_hyp_dag' in Hy; auto.
    fwd. congruence.
  Qed.

  Lemma request_hyps_hyps_false p :
    Forall (fun '(R, b) => b = false) (map snd (rel_graph (map request_hyps p))).
  Proof.
    apply Forall_map. apply Forall_flat_map. apply Forall_map. apply Forall_forall.
    intros r _. apply Forall_flat_map. apply Forall_forall. intros f' _.
    apply Forall_map. apply Forall_app. split.
    - destruct r. simpl. constructor.
    - destruct r. simpl. apply Forall_map. apply Forall_map. apply Forall_forall.
      intros f _. simpl. reflexivity.
  Qed.

  Lemma add_hyps_concls_true p :
    Forall (fun '(R, b) => b = true) (map fst (rel_graph (map add_hyp p))).
  Proof.
    apply Forall_map. apply Forall_flat_map. apply Forall_map. apply Forall_forall.
    intros r _. apply Forall_flat_map. apply Forall_forall. intros f' Hf'.
    apply Forall_map. simpl. apply Forall_forall. intros _ _. destruct r. simpl in *.
    apply in_map_iff in Hf'. fwd. reflexivity.
  Qed.

  Lemma make_good_dag p :
    Forall goodish_rule p ->
    dag (rel_graph p) ->
    dag (rel_graph (make_good p)).
  Proof.
    intros H1 H2. cbv [make_good]. do 2 rewrite rel_graph_app.
    apply dag_app; cycle 1.
    { apply map_add_hyp_dag; auto. eapply Forall_impl; [|eassumption].
      cbv [goodish_rule]. intros. fwd. eauto. }
    { rewrite <- rel_graph_app. apply map_request_hyps_dag. assumption. }
    cbv [no_cycles]. eapply Forall_impl; [|apply add_hyps_concls_true].
    intros (?, ?) H. subst. cbv [not_in_snd]. intros H.
    rewrite <- rel_graph_app in H. apply in_map_iff in H. fwd. destruct x.
    apply map_request_hyps_incl in Hp1. simpl in *. fwd. subst. simpl in *. congruence.
  Qed.
  
  Lemma incl_fact_ins (f : fact) :
    incl (fact_ins f) (fact_args f).
  Proof. apply incl_skipn. Qed.

  Lemma appears_with_only_ins v (f : fact) :
    In v (vars_of_fact (with_only_ins f)) ->
    In v (vars_of_fact f).
  Proof.
    intros H. cbv [vars_of_fact] in *. simpl in *. cbv [fact_ins] in H.
    rewrite in_flat_map in *. fwd. eauto using In_skipn.
  Qed.

  Lemma barely_appears_with_only_ins v (f : fact) :
    In (var_expr v) (with_only_ins f).(fact_args) ->
    In (var_expr v) f.(fact_args).
  Proof.
    intros H. simpl in *. cbv [fact_ins] in H.
    apply In_skipn in H. assumption.
  Qed.

  Hint Resolve appears_with_only_ins barely_appears_with_only_ins vars_of_fact_relmap appears_in_agg_expr_with_bool good_agg_expr_relmap : core.

  Hint Resolve incl_fact_ins : core.

  Hint Extern 3 => progress simpl : core.

  Lemma appears_in_rule_add_hyp v r :
    goodish_rule r ->
    appears_in_rule v (add_hyp r) ->
    appears_in_rule v r.
  Proof.
    destruct r; cbv [appears_in_rule add_hyp]; simpl.
    intros Hgood. cbv [goodish_rule] in Hgood. simpl in Hgood. fwd.
    cbv [appears_in_rule] in *. simpl in *. intros [Hv| [Hv| [Hv|Hv]]]; fwd.
    - left. split; eauto. intros H'. apply Hvp0.
      fwd. simpl. eauto.
    - rewrite flat_map_map in Hv. rewrite vars_of_fact_relmap in Hv.
      erewrite flat_map_ext in Hv. 2: intros; apply vars_of_fact_relmap.
      apply in_app_iff in Hv. rewrite app_nil_r. destruct Hv as [Hv|Hv]; eauto.
      left. split; eauto. cbv [with_only_ins vars_of_fact] in Hv.
      simpl in Hv. intros H'. fwd. apply Hgoodp1. eauto.
    - invert_list_stuff. eauto.
    - invert_list_stuff. eauto 8.
  Qed.
  
  Lemma add_hyp_good r :
    goodish_rule r ->
    well_founded (depends_on_in_set_hyps (rule_set_hyps r)) ->
    good_rule (add_hyp r).
  Proof.
    intros HH H0. pose proof HH as (Hgood0&H). fwd. split.
    - intros v Hv. simpl. rewrite Hp0. simpl.
      apply appears_in_rule_add_hyp in Hv; [|assumption].
      apply Hp2 in Hv. rewrite flat_map_map. simpl. rewrite in_app_iff.
      destruct Hv as [Hv| [Hv|Hv]]; auto.
    - simpl. destruct (rule_agg r) as [(?&?)|]; simpl; fwd; auto.
  Qed.

  Lemma request_hyps_good r :
    goodish_rule r ->
    good_rule (request_hyps r).
  Proof.
    intros H. cbv [goodish_rule] in H. fwd. cbv [good_rule]. ssplit; cycle 1.
    - cbv [depends_on_in_set_hyps]. eapply wf_incl. 2: apply wf_empty.
      intros x y Hxy. fwd. cbv [rule_set_hyps] in Hxyp1. simpl in Hxyp1. contradiction.
    - constructor.
    - intros v Hv. simpl. rewrite Hp0. simpl. rewrite app_nil_r. left.
      destruct Hv as [Hv| [Hv| [Hv|Hv]]]; fwd; simpl in *.
      + cbv [vars_of_fact] in Hvp1. do 2 rewrite flat_map_map in Hvp1.
        simpl in Hvp1. apply Hp3. rewrite flat_map_flat_map. assumption.
      + apply Hp4. rewrite Hp0 in Hv. simpl in Hv. rewrite app_nil_r in Hv.
        rewrite vars_of_fact_relmap in Hv. apply Hv.
      + cbv [in_set_hyps] in Hv. simpl in Hv. destruct Hv; contradiction.
      + congruence.
  Qed.

  Lemma singleton_wf {U : Type} (R : U -> U -> Prop) y :
    (forall x' y', R x' y' -> y' = y /\ x' <> y) ->
    well_founded R.
  Proof.
    intros H y'. constructor. intros x Hx. apply H in Hx. fwd.
    constructor. intros z Hz. apply H in Hz. fwd. congruence.
  Qed.

  Lemma noop_rule_good :
    good_rule noop_rule.
  Proof.
    cbv [good_rule]. simpl. intuition auto.
    - cbv [appears_in_rule] in H. simpl in H. destruct H as [H| [H| [H|H]]]; fwd; auto.
      congruence.
    - eapply wf_incl. 2: apply wf_empty. intros x y Hxy.
      cbv [depends_on_in_set_hyps] in Hxy. simpl in Hxy. fwd. contradiction.
  Qed.

  Lemma request_agg_hyps_good r :
    good_index r ->
    goodish_rule r ->
    good_rule (request_agg_hyps r).
  Proof.
    intros Hidx H. cbv [good_index] in Hidx. cbv [goodish_rule] in H. fwd.
    rewrite Hp0 in *. simpl in *. rewrite app_nil_r in *.
    cbv [request_agg_hyps]. destruct (rule_agg r) as [(?&?)|]; [|apply noop_rule_good].
    fwd. cbv [good_rule]. simpl. ssplit; cycle 1.
    - cbv [depends_on_in_set_hyps]. cbv [rule_set_hyps request_agg_hyps].
      + eapply singleton_wf. intros x' y' H. fwd. simpl in Hp6.
        destruct Hp6; [|contradiction]. invert H. split; [reflexivity|].
        intro. subst. apply Hp5p1 in Hp5. apply Hidxp0. apply in_flat_map. eauto.
    - constructor.
    - intros v0 Hv0. simpl. rewrite Hp0. simpl. rewrite app_nil_r.
      destruct Hv0 as [Hv0| [Hv0| [Hv0|Hv0]]]; fwd; simpl in *.
      + cbv [vars_of_fact] in Hv0p1. do 2 rewrite flat_map_map in Hv0p1.
        rewrite <- flat_map_flat_map in Hv0p1. specialize (Hp5p2 v0). specialize' Hp5p2.
        { apply in_flat_map in Hv0p1. apply in_flat_map. fwd.
          apply in_flat_map in Hv0p1p0. fwd. simpl in Hv0p1p0p1. eexists.
          rewrite in_flat_map. eauto. }
        destruct Hp5p2 as [Hp5p2|Hp5p2]; subst; fwd; auto.
      + rewrite Hp0 in *. simpl in Hv0. rewrite app_nil_r in Hv0. left.
        apply Hp4. assumption.
      + cbv [in_set_hyps] in Hv0. simpl in Hv0. rewrite app_nil_r in Hv0.
        destruct Hv0 as [Hv0|Hv0].
        -- destruct Hv0; contradiction || subst. auto.
        -- left. apply Hp5p1. assumption.
      + congruence.
  Qed.

  Hint Resolve interp_fact_relmap : core.

  Hint Extern 1 => unfold fact'_relmap; match goal with
                  | |- context[let '(_, _) := ?x in _] => destruct x
                  end : core.

  Hint Resolve interp_agg_expr_relmap : core.

  Lemma rule_impl_add_hyp R r args' hyps' :
    goodish_rule r ->
    rule_impl r (R, args') hyps' ->
    rule_impl (add_hyp r) ((R, true), args')
      (((R, false), skipn (outs R) args') :: map (fact'_relmap plus_true) hyps').
  Proof.
    intros Hgood H. cbv [goodish_rule] in Hgood. fwd.
    cbv [rule_impl] in *. fwd. eexists _, (_ :: _), _. split.
    { simpl. f_equal. rewrite map_app. rewrite concat_map. (*what a goofy name*)
      reflexivity. }
    cbv [add_hyp]. invert Hp1.
    (*TODO I don't completely understand why i have to do this*)
    eapply mk_rule_impl' with (ctx := ctx) (ctx' := ctx'); simpl.
    { invert H; simpl; econstructor; auto. }
    { apply Exists_map. eapply Exists_impl; [|eassumption]. simpl. intros.
      eapply interp_fact_relmap in H3. Fail eassumption. Fail apply H3. exact H3. }
    2: assumption.
    rewrite Hgoodp0. simpl. constructor.
    2: { rewrite <- Forall2_map_l, <- Forall2_map_r. eauto using Forall2_impl. }
    cbv [with_only_ins]. rewrite Hgoodp0 in H0. invert_list_stuff.
    cbv [fact_relmap]. simpl. invert H4. constructor. simpl.
    eapply Forall2_skipn in H5. invert H; [eassumption|].
    symmetry in H0. fwd. eapply Forall2_impl_strong; [|eassumption].
    intros x y Hxy Hx _. eapply interp_expr_agree_on; eauto. apply Forall_forall.
    intros v Hv. cbv [agree_on]. rewrite map.get_put_dec.
    destr (var_eqb res v); auto. exfalso. apply Hgoodp1.
    do 2 eexists. split; [|eassumption].
    apply in_flat_map. eauto.
  Qed.

  Definition f (wanted : _ * ((rel * bool) * list T) -> Prop)
    (S : (rel * list T -> Prop) * (rel * list T) -> Prop)
    (Px : ((rel * bool) * list T -> Prop) * ((rel * bool) * list T)) :=
    let '(P, x) := Px in
    let '((R, b), args) := x in
    if b then S (fun '(R, args) => P ((R, true), args), (R, args)) else
      wanted (P, ((R, false), args)).

  Definition g (S' : ((rel * bool) * list T -> Prop) * ((rel * bool) * list T) -> Prop)
    (Px : ((rel * list T) -> Prop) * (rel * list T)) :=
    let '(P, x) := Px in
    let '(R, args) := x in
    S' (fun '((R', b'), args') => match b' with
                               | true => P (R', args')
                               | false => (R', args') = (R, skipn (outs R) args) end, ((R, true), args)).

  Goal forall w S x, g (f w S) x <-> S x.
    intros w S [P [R args]]. split.
    - simpl. admit. (*very true*)
    - simpl. admit. (*very true*)
  Abort.

  Lemma invert_rule_impl_request_hyps R r b ins' hyps' :
    rule_impl (request_hyps r) (R, b, ins') hyps' -> b = false.
  Proof.
    cbv [rule_impl]. intros H. fwd. invert Hp1. apply Exists_exists in H0. fwd.
    cbv [request_hyps] in H0p0. simpl in H0p0. rewrite in_map_iff in H0p0. fwd.
    apply in_map_iff in H0p0p1. fwd. invert H0p1. reflexivity.
  Qed.

  Lemma invert_rule_impl_request_agg_hyps R r b ins' hyps' :
    rule_impl (request_agg_hyps r) (R, b, ins') hyps' -> b = false.
  Proof.
    cbv [rule_impl]. intros H. fwd. invert Hp1. apply Exists_exists in H0. fwd.
    cbv [request_agg_hyps] in H0p0. destruct (rule_agg r) as [(?&?)|].
    - simpl in H0p0. rewrite in_map_iff in H0p0. fwd.
      apply in_map_iff in H0p0p1. fwd. invert H0p1. reflexivity.
    - simpl in H0p0. contradiction.
  Qed.

  Lemma rule_impl_request_hyps ctx r R args R' args' hyps' agg_hyps's :
    goodish_rule r (*very necessary, finally*)->
    rule_impl' ctx r (R, args) hyps' agg_hyps's ->
    In (R', args') hyps' ->
    rule_impl (request_hyps r) (R', false, skipn (outs R') args')
      [(R, false, skipn (outs R) args)].
  Proof.
    intros Hgood H Hin. cbv [goodish_rule] in Hgood. fwd. cbv [request_hyps].
    rewrite Hgoodp0. simpl. unfold with_only_ins at 2.
    unfold fact_relmap at 2. simpl. cbv [rule_impl] in H. fwd.
    cbv [rule_impl]. eexists _, [_], nil. split; [reflexivity|]. invert H.
    econstructor; simpl.
    - constructor.
    - do 2 rewrite Exists_map.
      apply Forall2_forget_l in H2. rewrite Forall_forall in H2.
      specialize (H2 _ ltac:(eassumption)). fwd. rewrite Exists_exists.
      eexists. split; [eassumption|]. invert H2p1. constructor.
      simpl. cbv [fact_ins]. apply Forall2_skipn. eassumption.
    - constructor; [|solve[constructor]]. rewrite Hgoodp0 in H1. invert_list_stuff.
      invert H4. constructor. simpl.
      eapply Forall2_skipn in H5. invert H0; [eassumption|].
      eapply Forall2_impl_strong; [|eassumption].
      intros x y Hxy Hx _. eapply interp_expr_agree_on; eauto. apply Forall_forall.
      intros v Hv. cbv [agree_on]. rewrite map.get_put_dec. symmetry in H.
      destr (var_eqb res v); auto. exfalso. apply Hgoodp1.
      do 2 eexists. split; [|eassumption].
      apply in_flat_map. eauto.
    - constructor.
  Qed.

  Lemma rule_impl_request_agg_hyps ctx r R args R' args' hyps' agg_hyps's :
    good_index r ->
    goodish_rule r ->
    rule_impl' ctx r (R, args) hyps' agg_hyps's ->
    Exists (fun agg_hyps' => In (R', args') agg_hyps') agg_hyps's ->
    rule_impl (request_agg_hyps r) (R', false, skipn (outs R') args')
      [(R, false, skipn (outs R) args)].
  Proof.
    intros Hidx Hgood H Hin. cbv [goodish_rule] in Hgood.
    cbv [good_index] in Hidx. fwd. cbv [request_agg_hyps].
    rewrite Hgoodp0 in *. simpl in *. rewrite app_nil_r in *.
    unfold with_only_ins at 2.
    unfold fact_relmap at 2. simpl. cbv [rule_impl] in H. fwd.
    cbv [rule_impl]. invert H. invert H0.
    { invert_list_stuff. }
    rewrite <- H in *. invert H6. simpl in *.
    apply Forall3_ignore12_strong in H5.
    rewrite Forall_forall in H5. apply Exists_exists in Hin. fwd.
    specialize (H5 _ ltac:(eassumption)). fwd.
    apply Forall2_forget_l in H5p2p1. rewrite Forall_forall in H5p2p1.
    specialize (H5p2p1 _ ltac:(eassumption)). fwd.
    eexists (map.put ctx i x0), [_], nil. split; [reflexivity|]. invert H.
    econstructor; simpl.
    - constructor.
    - do 2 rewrite Exists_map.
      rewrite Exists_exists. eexists. split; [eassumption|].
      eapply interp_fact_relmap with (g := plus_false) in H5p2p1p1. simpl in H5p2p1p1.
      invert H5p2p1p1. constructor. simpl. cbv [fact_ins]. eapply Forall2_impl_strong.
      2: apply Forall2_skipn; eassumption. intros x2 y2 Hx2y2 Hx2 Hy2.
      simpl in H7. move Hgoodp5p2 at bottom. Check interp_expr_agree_on.
      eapply interp_expr_agree_on; [eassumption|]. apply Forall_forall.
      intros v Hv. specialize (Hgoodp5p2 v). specialize' Hgoodp5p2.
      { apply in_flat_map. eexists. split; eauto. apply in_flat_map. eauto. }
      cbv [agree_on]. fwd. rewrite map.get_putmany_dec. do 2 rewrite map.get_put_dec.
      destr (var_eqb i v); [reflexivity|].
      destruct Hgoodp5p2 as [Hgoodp5p2|Hgoodp5p2]; [congruence|]. fwd.
      eapply map.not_in_of_list_zip_to_get_None in Hgoodp5p2p1; [|eassumption].
      rewrite Hgoodp5p2p1. reflexivity.
    - constructor; [|solve[constructor]]. rewrite Hgoodp0 in H1. invert_list_stuff.
      invert H5. constructor. simpl.
      eapply Forall2_skipn in H7.
      eapply Forall2_impl_strong; [|eassumption].
      intros x' y' Hx'y' Hx' _. eapply interp_expr_agree_on; eauto. apply Forall_forall.
      intros v Hv. cbv [agree_on]. rewrite map.get_put_dec. rewrite map.get_put_dec.
      destr (var_eqb res v).
      { exfalso. Search v. apply Hgoodp1. do 2 eexists. split; eauto.
        apply in_flat_map. eauto. }
      destr (var_eqb i v).
      { exfalso. apply Hidxp0. apply in_flat_map. eauto. }
      reflexivity.
    - constructor; [|constructor]. simpl. do 3 eexists. intuition eauto.
      + constructor. apply map.get_put_same.
      + eapply interp_expr_agree_on; [eassumption|]. apply Forall_forall.
        intros v Hv. Search s. apply Hgoodp5p1 in Hv. cbv [agree_on].
        symmetry. apply map.get_put_diff. intro. subst. apply Hidxp0.
        apply in_flat_map. eauto.
  Qed.

  Lemma rule_impl_request r R args R' args' hyps' :
    good_index r ->
    goodish_rule r ->
    rule_impl r (R, args) hyps' ->
    In (R', args') hyps' ->
    rule_impl (request_hyps r) (R', false, skipn (outs R') args')
      [(R, false, skipn (outs R) args)] \/
      rule_impl (request_agg_hyps r) (R', false, skipn (outs R') args')
        [(R, false, skipn (outs R) args)].
  Proof.
    intros H H0 H1 H2. cbv [rule_impl] in H1. fwd. apply in_app_iff in H2.
    destruct H2 as [H2|H2]; [left|right].
    - eapply rule_impl_request_hyps; eauto.
    - eapply rule_impl_request_agg_hyps; eauto.
      apply Exists_exists. apply in_concat in H2. fwd. eauto.
  Qed.

  Lemma agg_expr_relmap_id (ae : agg_expr) :
    agg_expr_relmap (fun x => x) ae = ae.
  Proof.
    destruct ae. cbv [agg_expr_relmap]. simpl. erewrite map_ext with (g := fun x => x).
    2: { intros f. destruct f. reflexivity. }
    rewrite map_id. reflexivity.
  Qed.

  Lemma agg_expr_relmap_comp {rel1_ rel2_ rel3_ var_ fn_ aggregator_ : Type} (ae : @Datalog.agg_expr rel1_ var_ fn_ aggregator_) (g : rel1_ -> rel2_) (f : rel2_ -> rel3_) :
    agg_expr_relmap f (agg_expr_relmap g ae) = agg_expr_relmap (fun x => f (g x)) ae.
  Proof.
    destruct ae. cbv [agg_expr_relmap]. simpl. rewrite map_map. reflexivity.
  Qed.
  
  Lemma invert_rule_impl_add_hyp r R b args' hyps' :
    goodish_rule r ->
    rule_impl (add_hyp r) ((R, b), args') hyps' ->
    b = true /\
      exists hyps0',
        hyps' = ((R, false), skipn (outs R) args') :: hyps0' /\
          Forall (fun x => snd (fst x) = true) hyps0' /\
          rule_impl r (R, args') (map (fact'_relmap (fun '(R, _) => R)) hyps0').
  Proof.
    intros Hgood H. cbv [goodish_rule] in Hgood. fwd. cbv [rule_impl add_hyp] in H.
    fwd. invert Hp1; simpl in *. rewrite Hgoodp0 in *. simpl in *. invert_list_stuff.
    invert H3. split; [reflexivity|].
    cbv [with_only_ins] in H5. cbv [fact_relmap] in H4.
    simpl in H4. simpl in *. invert H5. simpl. simpl in H0.
      assert (args'0 = skipn (outs (fact_R concl)) args').
      { move H at bottom. move H4 at bottom. simpl in H4.
        eapply Forall2_skipn in H4. eapply Forall2_unique_r. 1: exact H0.
        2: apply interp_expr_det.
        invert H; [eassumption|].
        eapply Forall2_impl_strong; [|eassumption].
        intros x y Hxy Hx _. eapply interp_expr_agree_on; eauto. apply Forall_forall.
        intros v Hv. cbv [agree_on]. rewrite map.get_put_dec. symmetry in H1.
        destr (var_eqb res v); auto. exfalso. apply Hgoodp1. invert_list_stuff.
        do 2 eexists. split; [|eassumption].
        apply in_flat_map. eauto. }
      subst. eexists. split; [reflexivity|].
      apply interp_facts_relmap with (g := fst) in H7. fwd.
      rewrite map_map in H7p0. simpl in H7p0.
      eassert (H': forall x y, x = y -> map snd x = map snd y) by (intros; subst; reflexivity).
      apply H' in H7p0. clear H'. do 2 rewrite map_map in H7p0. simpl in H7p0.
      rewrite map_const in H7p0. eassert (H7p0': Forall _ _).
      { apply Forall_forall. intros x Hx. apply repeat_spec in Hx. exact Hx. }
      rewrite H7p0 in H7p0'. clear H7p0. apply Lists.List.Forall_map in H7p0'.
      invert H; simpl in *.
    - rewrite app_nil_r. symmetry in H5. apply option_map_None in H5. rewrite H5 in *.
      split; [assumption|]. cbv [rule_impl]. do 3 eexists.
      split; cycle 1.
      + eapply mk_rule_impl' with (ctx := ctx'); eauto.
        -- rewrite H5. constructor.
        -- rewrite Hgoodp0. constructor. constructor. assumption.
        -- rewrite map_map in H7p1. rewrite <- Forall2_map_l, <- Forall2_map_r in H7p1.
           erewrite <- Forall2_map_r. eapply Forall2_impl; [|eassumption]. simpl.
           intros. cbv [fact'_relmap fact_relmap] in H. simpl in H.
           instantiate (1 := fun _ => _). destruct a; simpl in *. exact H.
      + simpl. rewrite app_nil_r. cbv [fact'_relmap]. apply map_ext.
        intros [[? ?] ?]. reflexivity.
    - symmetry in H1. apply option_map_Some in H1. fwd. rewrite H1p0 in *.
      split.
      + apply Forall_app. split; [assumption|]. apply Forall_concat.
        invert H6. apply Forall3_ignore12 in H13. rewrite Forall_forall in *.
        intros x Hx. specialize (H13 _ Hx). simpl in *. fwd.
        apply Forall2_forget_l in H13p1. rewrite Forall_forall in *. intros z Hz.
        specialize (H13p1 _ Hz). fwd. apply in_map_iff in H13p1p0. fwd.
        invert H13p1p1. reflexivity.
      + cbv [rule_impl]. do 3 eexists. split.
        { rewrite map_app. rewrite concat_map. reflexivity. }
        eapply mk_rule_impl' with (ctx := ctx); eauto.
        -- rewrite H1p0. econstructor; eauto. eapply interp_agg_expr_relmap with (g := fst) in H6.
           rewrite agg_expr_relmap_comp in H6. rewrite agg_expr_relmap_id in H6.
           apply H6.
        -- rewrite Hgoodp0. constructor. constructor. assumption.
        -- rewrite map_map in H7p1. rewrite <- Forall2_map_l, <- Forall2_map_r in H7p1.
           erewrite <- Forall2_map_r. eapply Forall2_impl; [|eassumption]. simpl.
           intros. cbv [fact'_relmap fact_relmap] in H. simpl in H.
           destruct b as [[? ?] ?]; simpl in *. destruct a0. exact H.
  Qed.      

  Lemma request_hyps_hyps'_false r R b args hyps' :
    rule_impl (request_hyps r) (R, b, args) hyps' ->
    Forall (fun hyp' => snd (fst hyp') = false) hyps'.
  Proof.
    intros H. cbv [request_hyps rule_impl] in H. fwd. invert Hp1. simpl in *.
    apply Forall_forall.
    intros x Hx. invert H. rewrite app_nil_r in Hx. rewrite map_map in H1.
    apply Forall2_forget_l in H1. rewrite Forall_forall in H1.
    specialize (H1 _ ltac:(eassumption)). fwd.
    apply in_map_iff in H1p0. fwd. invert H1p1. reflexivity.
  Qed.

  Lemma request_agg_hyps_hyps'_false r R b args hyps' :
    rule_impl (request_agg_hyps r) (R, b, args) hyps' ->
    Forall (fun hyp' => snd (fst hyp') = false) hyps'.
  Proof.
    intros H. cbv [request_agg_hyps rule_impl] in H. fwd.
    destruct (rule_agg r) as [(?&?)|]; cycle 1.
    { invert Hp1. simpl in *. invert_list_stuff. }
    invert Hp1. simpl in *.
    apply Forall_forall.
    intros x Hx. invert H. rewrite app_nil_r in Hx. rewrite map_map in H1.
    apply Forall2_forget_l in H1. rewrite Forall_forall in H1.
    specialize (H1 _ ltac:(eassumption)). fwd.
    apply in_map_iff in H1p0. fwd. invert H1p1. reflexivity.
  Qed.

  Lemma f_fixpoint' r S w :
    goodish_rule r ->
    fp (F [request_hyps r; request_agg_hyps r]) w ->
    fp (F [r]) S ->
    fp (F [request_hyps r; request_agg_hyps r; add_hyp r]) (f w S).
  Proof.
    cbv [fp F]. intros Hgood Wfp H [P [[R b] args]] Hx. simpl.
    destruct Hx as [Hx| [Hx|Hx]]; auto.
    { destruct b; auto. }
    fwd. invert Hxp0.
    - simpl. pose proof H1 as H1'.
      apply invert_rule_impl_request_hyps in H1. subst. apply Wfp. right. right.
      exists hyps'. split.
      { constructor. assumption. }
      apply request_hyps_hyps'_false in H1'. rewrite Forall_forall in Hxp1, H1'.
      rewrite Forall_forall. intros x Hx. specialize (Hxp1 _ Hx). specialize (H1' _ Hx).
      destruct x as [ [R' b'] args']. simpl in Hxp1, H1'. subst. assumption.
    - invert H1.
      + simpl. rename H2 into H1. pose proof H1 as H1'.
        apply invert_rule_impl_request_agg_hyps in H1. subst. apply Wfp. right. right.
      exists hyps'. split.
      { apply Exists_cons_tl. constructor. assumption. }
      apply request_agg_hyps_hyps'_false in H1'. rewrite Forall_forall in Hxp1, H1'.
      rewrite Forall_forall. intros x Hx. specialize (Hxp1 _ Hx). specialize (H1' _ Hx).
      destruct x as [ [R' b'] args']. simpl in Hxp1, H1'. subst. assumption.
      + invert_list_stuff. eapply invert_rule_impl_add_hyp in H1; eauto. fwd. simpl.
        apply H. right. right. eexists. split; eauto. apply Forall_map. eapply Forall_impl.
      2: { eapply Forall_and. 1: apply Hxp1p1. apply H1p1p1. }
      simpl. intros [[R' b'] args']. simpl. intros. fwd. assumption.
  Qed.

  Lemma g_fixpoint' r S :
    good_index r ->
    goodish_rule r ->
    S_sane S ->
    fp (F [request_hyps r; request_agg_hyps r; add_hyp r]) S ->
    fp (F [r]) (g S).
  Proof.
    cbv [fp F]. intros Hidx Hgood (Sgood1&Sgood2) H [P x] Hx.
    destruct Hx as [Hx| [Hx|Hx]]; auto.
    fwd. destruct x as [R args]. invert_list_stuff.
    pose proof rule_impl_add_hyp as H1'. specialize H1' with (1 := Hgood) (2 := H1).
    simpl. apply H. right. right. eexists. split.
    { apply Exists_cons_tl. apply Exists_cons_tl. constructor. eassumption. }
    constructor.
    { auto. }
    apply Forall_map. pose proof Hxp1 as H'. rewrite Forall_forall in H'.
    rewrite Forall_forall. intros [R' args'] Hx. specialize H' with (1 := Hx).
    simpl in H'. cbv [fact'_relmap]. eapply Sgood2; [eassumption|]. simpl.
    clear H'. intros y Hy. destruct y as [ [Ry By] argsy]. destruct By.
    { apply H; auto. }
    invert Hy. apply H. right. right. exists [(R, false, skipn (outs R) args)]. split.
    2: eauto. eapply rule_impl_request in H1; try eassumption.
    destruct H1; auto.
  Qed.

  Lemma f_sane w S :
    (forall x P, P x -> S (P, x)) ->
    (forall x P, P x -> w (P, x)) ->
    (forall x P, P x -> f w S (P, x)).
  Proof. intros H1 H2 [[R b] args] P. simpl. destruct b; eauto. Qed.

  Hint Resolve f_sane : core.
  Hint Unfold S_sane : core.

  Lemma f_fixpoint w p S :
    S_sane w ->
    S_sane S ->
    Forall goodish_rule p ->
    fp (F p) S ->
    fp (F (map request_hyps p ++ map request_agg_hyps p)) w ->
    fp (F (make_good p)) (f w S).
  Proof.
    intros (Wgood1&Wgood2) (Sgood1&Sgood2) H1 H2 HP. pose proof f_fixpoint' as H'.
    rewrite Forall_forall in H1.
    assert (forall r, In r p -> fp (F [request_hyps r; request_agg_hyps r]) w).
    { intros r Hr. rewrite <- split_fixpoint in HP by auto.
      rewrite <- split_fixpoint by auto. intros r' Hr'.
      destruct Hr' as [Hr'| [Hr'|Hr']]; [subst|subst|contradiction].
      - apply HP. apply in_app_iff. left. apply in_map. assumption.
      - apply HP. apply in_app_iff. right. apply in_map. assumption. }
    apply split_fixpoint; auto. cbv [make_good]. intros r Hr.
    apply in_app_iff in Hr. destruct Hr as [Hr|Hr].
    - apply in_map_iff in Hr. fwd. rewrite <- split_fixpoint in H2 by auto.
      specialize (H' _ _ _ ltac:(eauto) ltac:(eauto) ltac:(eauto)). 
      rewrite <- split_fixpoint in H' by auto. simpl in *. intros. apply H'. tauto.
    - apply in_app_iff in Hr. destruct Hr as [Hr|Hr]; apply in_map_iff in Hr; fwd.
      + apply split_fixpoint; auto. rewrite <- split_fixpoint in H2 by auto.
        specialize (H' _ _ _ ltac:(eauto) ltac:(eauto) ltac:(eauto)).
        rewrite <- split_fixpoint in H' by auto. simpl in *. intros. apply H'. tauto.
      + apply split_fixpoint; auto. rewrite <- split_fixpoint in H2 by auto.
        specialize (H' _ _ _ ltac:(eauto) ltac:(eauto) ltac:(eauto)).
        rewrite <- split_fixpoint in H' by auto. simpl in *. intros. apply H'. tauto.
  Qed.

  Lemma g_sane S :
    (forall x P, P x -> S (P, x)) ->
    (forall x P, P x -> g S (P, x)).
  Proof. intros H [R args] P HP. simpl. auto. Qed.

  Hint Resolve g_sane : core.

  Lemma g_fixpoint p S :
    Forall good_index p ->
    Forall goodish_rule p ->
    S_sane S ->
    fp (F (make_good p)) S ->
    fp (F p) (g S).
  Proof.
    intros Hidx H1 (Sgood1&Sgood2) H2. pose proof g_fixpoint' as H'.
    rewrite Forall_forall in Hidx, H1.
    apply split_fixpoint; auto. cbv [make_good]. intros r Hr.
    apply H'; auto.
    apply split_fixpoint; auto.
    intros r' Hr'. rewrite <- split_fixpoint in H2 by auto.
    destruct Hr' as [Hr' | [Hr' | [ Hr' | ] ] ]; [| | |exfalso; auto]; subst; apply H2; cbv [make_good]; do 2 rewrite in_app_iff; auto using in_map.
  Qed.

  Lemma g_mono S1 S2 :
    (forall x, S1 x -> S2 x) ->
    forall x, g S1 x -> g S2 x.
  Proof. cbv [g]. intros H [P [R args]] Hx. auto. Qed.

  Lemma gf_id w S :
    S_sane S ->
    equiv S (g (f w S)).
  Proof. (*note: here i just use weakening, which follows from Sgood1 and Sgood2, but Sgood1 and Sgood2 together are stronger than weakening*)
    intros (Sgood1&Sgood2). cbv [equiv g f]. intros [P [R args]].
    intuition eauto. (*because eauto doesn't know how to unfold <-> ?*)
  Qed.

  Hint Resolve fp_lfp F_mono S_sane_lfp : core.

  Lemma lfp_preimage p :
    Forall good_index p ->
    Forall goodish_rule p ->
    equiv (g (lfp (F (make_good p)))) (lfp (F p)).
  Proof.
    intros Hidx Hgood. eapply lfp_preimage'.
    - exact g_mono.
    - apply f_fixpoint with (w := lfp (F (map request_hyps p ++ map request_agg_hyps p))); eauto.
    - apply g_fixpoint; eauto.
    - apply gf_id; eauto.
  Qed.

  Lemma equiv_trans {U : Type} (A B C : U -> _) :
    equiv A B -> equiv B C -> equiv A C.
  Proof. cbv [equiv]. intros. rewrite H, <- H0. reflexivity. Qed.

  Lemma equiv_symm {U : Type} (A B : U -> _) :
    equiv A B -> equiv B A.
  Proof. cbv [equiv]. intros. rewrite H. reflexivity. Qed.

  Lemma g_ext A B : equiv A B -> equiv (g A) (g B).
  Proof. cbv [equiv g]. intros H [P [R args]]. apply H. Qed.
      
  Lemma phase_correct p :
    Forall good_index p ->
    Forall goodish_rule p ->
    equiv (fun '(P, f) => prog_impl_implication p P f) (g (fun '(P, f) => prog_impl_implication (make_good p) P f)).
  Proof.
    intros. eapply equiv_trans.
    { apply prog_impl_fact_lfp. }
    eapply equiv_trans.
    { apply equiv_symm. apply lfp_preimage; assumption. }
    apply equiv_symm. apply g_ext. apply prog_impl_fact_lfp.
  Qed. 

  Lemma source_impl_target p Q R args :
    Forall good_index p ->
    Forall goodish_rule p ->
    prog_impl_implication p Q (R, args) ->
    prog_impl_implication (make_good p)
      (fun '((R0, b0), args0) => if b0 then Q (R0, args0) else (R0, args0) = (R, skipn (outs R) args))
      ((R, true), args).
  Proof.
    intros Hidx H1 H2. pose proof phase_correct _ Hidx H1 as H3. cbv [equiv] in H3.
    rewrite (H3 (_, _)) in H2. clear H3. simpl in H2. assumption.
  Qed.

  Lemma target_impl_source p R args Q :
    Forall good_index p ->
    Forall goodish_rule p ->
    prog_impl_implication (make_good p) Q ((R, true), args) ->
    prog_impl_implication p (fun '(R, args) => Q ((R, true), args)) (R, args).
  Proof.
    intros Hidx H1 H2. pose proof phase_correct _ Hidx H1 as H3. cbv [equiv] in H3.
    rewrite (H3 (_, _)). clear H3. simpl. remember (R, true, args) as x eqn:E.
    revert R args E. (*TODO factor following out into lemma*)induction H2; intros; subst.
    - apply partial_in. assumption.
    - eapply partial_step. 1: apply H. cbv [make_good] in H.
      apply Exists_app in H. destruct H as [H|H]; cycle 1.
      { clear -H. exfalso. rewrite Exists_app in H. do 2 rewrite Exists_map in H.
        destruct H as [H|H].
        - apply Exists_exists in H.
          fwd. apply invert_rule_impl_request_hyps in Hp1. congruence.
        - apply Exists_exists in H.
          fwd. apply invert_rule_impl_request_agg_hyps in Hp1. congruence. }
      rewrite Forall_forall in H1. rewrite Exists_map in H. apply Exists_exists in H.
      fwd. rewrite Forall_forall in H0. apply invert_rule_impl_add_hyp in Hp1; auto.
      fwd. constructor.
      2: { rewrite Forall_forall in *. intros [[R' b'] args'] H.
           specialize (Hp1p1p1 _ ltac:(eassumption)). simpl in Hp1p1p1. subst.
           apply partial_pftree_trans. eapply partial_pftree_weaken.
           1: apply H2p1; eauto. intros [[Ry By] argsy]. intros Hy. destruct By.
           - apply partial_in. assumption.
           - clear H2p0. invert Hy. eapply partial_step.
             { cbv [make_good]. apply Exists_app. right.
               eapply rule_impl_request in Hp1p1p2; eauto.
               2: { apply in_map_iff. eexists (_, _, _). eauto. }
               apply Exists_app.
               destruct Hp1p1p2 as [Hp1p1p2|Hp1p1p2]; [left|right];
                 apply Exists_map; apply Exists_exists; eauto. }
             constructor; [|constructor]. apply partial_in. reflexivity. }
      apply partial_in. reflexivity.
  Qed.
End Transform.
