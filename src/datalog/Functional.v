From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Permutation.

From Stdlib Require Import Wellfounded.Inclusion.
From Stdlib Require Import Wellfounded Wellfounded.Wellfounded Wellfounded.Transitive_Closure.
From Stdlib Require Import Wellfounded.Inverse_Image.
From Stdlib Require Import Relations.Relation_Definitions.

From Datalog Require Import Datalog TypedDatalog Map Tactics Fp List Interpreter Pftree RelMap.
From GraphSearch Require Import Dag.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List.

Import ListNotations.

Section __.
  Context `{params : datalog_params} {query_sig : query.signature}.

  Definition agree Q (p : program) (r1 r2 : rule) :=
    forall R (args1 args2 : list value) hyps1 hyps2,
      rule.interp r1 (normal_fact.mk R args1) hyps1 ->
      rule.interp r2 (normal_fact.mk R args2) hyps2 ->
      Forall (program.interp p Q) hyps1 ->
      Forall (program.interp p Q) hyps2 ->
      query.inputs R args1 = query.inputs R args2 ->
      args1 = args2.

  (* Lemma agree_weaken Q p1 p2 r1 r2 : *)
  (*   agree Q p1 r1 r2 -> *)
  (*   False -> *)
  (*   agree Q p2 r1 r2. *)
  (* Proof. contradiction. Qed. *)

  Definition pairs_satisfy {X : Type} (P : X -> X -> Prop) (l : list X) :=
    forall x1 x2, In x1 l -> In x2 l -> x1 = x2 \/ P x1 x2.

  Lemma pairs_satisfy_weaken {X : Type} P1 P2 (l1 l2 : list X) :
    pairs_satisfy P1 l1 ->
    (forall x y, In x l2 -> In y l2 -> P1 x y -> P2 x y) ->
    incl l2 l1 ->
    pairs_satisfy P2 l2.
  Proof.
    cbv [pairs_satisfy]. intros H1 H2 H3 x y Hx Hy.
    specialize (H1 x y ltac:(eauto) ltac:(eauto)). destruct H1; auto.
  Qed.

  Definition functional (S : fact -> Prop) :=
    forall R args1 args2,
      S (fact.normal (normal_fact.mk R args1)) ->
      S (fact.normal (normal_fact.mk R args2)) ->
      query.inputs R args1 = query.inputs R args2 ->
      args1 = args2.

  Hint Resolve pairs_satisfy_weaken (*agree_weaken*) : core.

  Lemma hyp_ins_det r nf1 nf2 hyps1 hyps2 :
    rule.is_almost_bottomup r ->
    rule.interp r nf1 (map fact.normal hyps1) ->
    rule.interp r nf2 (map fact.normal hyps2) ->
    normal_fact.with_only_inputs nf1 = normal_fact.with_only_inputs nf2 ->
    Forall2 (fun h1 h2 => normal_fact.with_only_inputs h1 = normal_fact.with_only_inputs h2)
      hyps1 hyps2.
  Proof.
    intros Hgood H1 H2 Hins.
    invert H1; [|destruct hyps1; discriminate]. invert H2.
    apply map_inj in H; [|congruence]. apply map_inj in H4; [|congruence]. subst.
    destruct rule_concls as [|concl [|]]; cbv [rule.is_almost_bottomup] in Hgood;
      [contradiction| |contradiction].
    destruct Hgood as [Hgood _]. invert_list_stuff.
    apply clause.interp_with_only_inputs in H1, H2. rewrite Hins in H2.
    assert (Hagree : forall v,
               In v (flat_map expr.vars (flat_map clause.query_inputs (concl :: rule_hyps))) ->
               agree_on ctx ctx0 v).
    { intros v Hv. apply Hgood in Hv. eapply clause.interp_same_agree; eassumption. }
    rewrite flat_map_flat_map in Hagree.
    apply Forall2_flip in H5. eapply Forall2_Forall2_Forall3 in H8; [|exact H5].
    apply Forall3_ignore2 in H8. eapply Forall2_impl; [exact H8|].
    intros nf1' nf2' (h & Hh & Hnf1 & Hnf2). apply clause.interp_with_only_inputs in Hnf1, Hnf2.
    eapply clause.interp_det'; [exact Hnf1|exact Hnf2|].
    apply Forall_forall. intros v Hv. apply Hagree. apply in_flat_map. eauto using in_cons.
  Qed.

  Lemma agree_functional p Q :
    dag (rel_graph p) ->
    Forall goodish_rule p ->
    pairs_satisfy (agree p) p ->
    functional (program.interp p Q).
  Proof.
    intros H1 H2 H3. cbv [functional]. intros R.
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
End __.
