From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Permutation.


From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics.

From Datalog Require Import Datalog Map Tactics Fp List.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List.

From Stdlib Require Import Relations.Relation_Operators Relations.Operators_Properties Relations.Relations.

Import ListNotations.

Section __.
Context {V : Type}.
Implicit Type v : V.
Implicit Type e : V * V.
Implicit Type g : list (V * V).

Definition not_in_fst g v :=
  ~In v (map fst g).

Definition not_in_snd g v :=
  ~In v (map snd g).

(*adding g1 to g2 definitely doesn't create any cycles*)
Definition no_cycles g1 g2 :=
  Forall (not_in_snd g2) (map fst g1).

Definition edge_rel g x y := In (y, x) g.

Lemma edge_rel_weaken g1 g2 x y :
  edge_rel g1 x y ->
  incl g1 g2 ->
  edge_rel g2 x y.
Proof. cbv [edge_rel incl]. auto. Qed.

Definition dag g := well_founded (edge_rel g).

Inductive dag' : list (V * V) -> Prop :=
| dag'_nil : dag' []
| dag'_cons g1 g2 e :
  dag' (g1 ++ g2) ->
  not_in_snd (e :: g1 ++ g2) (fst e) ->
  dag' (g1 ++ e :: g2).

Inductive dag'_alt : list (V * V) -> Prop :=
| dag'_alt_nil : dag'_alt []
| dag'_alt_cons g1 g2 e :
  dag'_alt (g1 ++ g2) ->
  not_in_fst (e :: g1 ++ g2) (snd e) ->
  dag'_alt (g1 ++ e :: g2).
Hint Constructors dag' dag'_alt : core.

Lemma subrel_Acc {X : Type} R1 R2 (z : X) :
  Acc R2 z ->
  (forall x y, R1 x y -> R2 x y) ->
  Acc R1 z.
Proof. induction 1. constructor. auto. Qed.

Lemma subrel_Acc_strong {X : Type} P R1 R2 (z : X) :
  Acc R2 z ->
  P z ->
  (forall x y, R1 x y -> P y -> R2 x y /\ P x) ->
  Acc R1 z.
Proof.
  intros H1 H2 H. induction H1. constructor. intros y Hy.
  specialize (H _ _ ltac:(eassumption) ltac:(eassumption)). fwd. auto.
Qed.

Lemma subrel_wf {X : Type} (R1 R2 : X -> X -> Prop) :
  well_founded R2 ->
  (forall x y, R1 x y -> R2 x y) ->
  well_founded R1.
Proof. cbv [well_founded]. eauto using subrel_Acc. Qed.

Lemma Acc_not_symm {X : Type} (R : X -> X -> Prop) x :
  Acc R x ->
  R x x ->
  False.
Proof. induction 1; eauto. Qed.

Lemma dag'_dag g :
  dag' g ->
  dag g.
Proof.
  induction 1.
  - constructor. destruct 1.
  - constructor. intros y Hy. cbv [edge_rel] in Hy.
    eapply subrel_Acc_strong with (P := fun x => x <> fst e).
    + apply IHdag'.
    + intros H'. subst. apply H0. apply in_map_iff.
      eexists (_, _). split; [reflexivity|].
      simpl. rewrite in_app_iff in *. simpl in Hy.
      destruct Hy as [? | [?|?] ]; eauto.
    + intros. cbv [edge_rel] in *. clear Hy. rewrite in_app_iff in *. simpl in *. split.
      -- destruct H1 as [? | [?|?] ]; auto. subst. simpl in H2. congruence.
      -- intro. subst. apply H0. apply in_map_iff.
         eexists (_, _). split; [reflexivity|].
         simpl. rewrite in_app_iff. destruct H1 as [? | [?|?] ]; eauto.
Qed.

Lemma dag_incl g1 g2 :
  dag g2 ->
  incl g1 g2 ->
  dag g1.
Proof.
  cbv [incl dag edge_rel].
  intros H1 H2. eapply subrel_wf; eauto.
  simpl. eauto.
Qed.

Lemma dag'_app g1 g2 :
  no_cycles g1 g2 ->
  dag g1 ->
  dag g2 ->
  dag (g1 ++ g2).
Proof.
  intros H1 H2 H3.
  TODO
Qed.

Lemma concl_same_dag v g :
  Forall (fun '(x, y) => x = v /\ y <> v) g ->
  dag g.
Proof.
  intros H. constructor. intros y Hy. constructor. intros z Hz.
  exfalso. rewrite Forall_forall in H. apply H in Hy, Hz. fwd. congruence.
Qed.

Inductive path (g : list (V * V)) : V -> list V -> Prop :=
| path_nil x : path _ x []
| path_cons x y l :
  In (x, y) g ->
  path _ y l ->
  path _ x (y :: l).

Definition path_alt g l :=
  forall l1 x y l2,
    l = l1 ++ x :: y :: l2 ->
    In (x, y) g.

Lemma path_path_alt g x l :
  path g x l ->
  path_alt g (x :: l).
Proof.
  intros H. induction H.
  - cbv [path_alt]. intros. destruct l1; try discriminate H.
    destruct l1; discriminate H.
  - cbv [path_alt]. intros l1 x0 y0 l2 H'. destruct l1 as [|z l1].
    + simpl in H'. invert_list_stuff. assumption.
    + simpl in H'. invert_list_stuff. eapply IHpath. eassumption.
Qed.

Lemma path_alt_tl x l g :
  path_alt g (x :: l) ->
  path_alt g l.
Proof.
  cbv [path_alt] in *. intros. subst. eapply (H (_ :: _)). reflexivity.
Qed.
  
Lemma path_alt_path g x l :
  path_alt g (x :: l) ->
  path g x l.
Proof.
  revert x. induction l.
  - intros. constructor.
  - intros. constructor; eauto using path_alt_tl.
    eapply (H nil). reflexivity.
Qed.

Lemma clos_trans_list x y l g :
  path g x l ->
  In y l ->
  clos_trans _ (edge_rel g) y x.
Proof.
  intros H. induction H.
  - simpl. contradiction.
  - intros [H'|H'].
    + apply t_step. subst. assumption.
    + apply IHpath in H'. clear IHpath. eapply t_trans; eauto. apply t_step. assumption.
Qed.

Search clos_trans Acc. (*nothing?*)
Lemma Acc_clos_trans {X : Type} (R : X -> X -> Prop) x :
  Acc R x ->
  Acc (clos_trans _ R) x.
Proof.
  induction 1. constructor. intros y Hy. clear H. induction Hy; auto.
  apply IHHy1; auto. intros. apply IHHy2; auto. eauto using t_trans, t_step.
Qed.

Lemma dags_have_no_cycles' x l g :
  dag g ->
  path g x l ->
  ~In x l.
Proof.
  intros H1 H2 H3. eapply Acc_not_symm.
  - apply Acc_clos_trans. apply H1.
  - eapply clos_trans_list; eassumption.
Qed.

Lemma dags_have_no_cycles x l g :
  dag g ->
  path g x l ->
  NoDup (x :: l).
Proof.
  intros H. induction 1.
  - repeat constructor. simpl. auto.
  - constructor; [|assumption]. eapply dags_have_no_cycles'; eauto.
    constructor; assumption.
Qed.

Lemma path_incl x l g :
  path g x l ->
  incl l (map snd g).
Proof.
  induction 1; auto with incl. apply incl_cons; auto with incl.
  apply in_map_iff. eexists. split; eauto. reflexivity.
Qed.

Lemma dag_paths_short x l g :
  dag g ->
  path g x l ->
  length l <= length g.
Proof.
  intros H1 H2. eapply dags_have_no_cycles in H1; eauto.
  apply path_incl in H2. Search incl NoDup. rewrite <- (length_map snd).
  invert H1. apply NoDup_incl_length; assumption.
Qed.
End __.
