(*copied from https://velus.inria.fr/emsoft2021/html/Velus.Common.CommonList.html*)
From Stdlib Require Import Lists.List.
From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics.
Require Import coqutil.Datatypes.List.

Import ListNotations.

Section Forall3.
  Context {A B C : Type}.
  Variable R : A -> B -> C -> Prop.

  Inductive Forall3 : list A -> list B -> list C -> Prop :=
  | Forall3_nil : Forall3 [] [] []
  | Forall3_cons : forall (x : A) (y : B) (z: C)
                     (l0 : list A) (l1 : list B) (l2 : list C),
      R x y z ->
      Forall3 l0 l1 l2 ->
      Forall3 (x :: l0) (y :: l1) (z :: l2).

  Lemma Forall3_length :
    forall (l1 : list A) (l2 : list B) (l3 : list C),
      Forall3 l1 l2 l3 ->
      length l1 = length l2
      /\ length l2 = length l3.
  Proof. intros l1 l2 l3 H. induction H; simpl; firstorder. Qed.


  Lemma Forall3_in_right:
    forall (xs : list A)
      (ys : list B) (zs : list C) (z : C),
      Forall3 xs ys zs ->
      In z zs -> exists (x : A) (y : B), In x xs /\ In y ys /\ R x y z.
  Proof.
    induction 1; simpl.
    { contradiction. }
    destruct 1 as [Heq|Hin].
    { now subst; exists x, y; auto. }
    apply IHForall3 in Hin. destruct Hin as (x' & y' & Hin & Hin' & HP).
    exists x', y'. eauto.
  Qed.


  Remark Forall3_tl:
    forall (x : A)
      (y : B) (z : C) (l0 : list A) (l1 : list B) (l2 : list C),
      Forall3 (x :: l0) (y :: l1) (z :: l2) -> Forall3 l0 l1 l2.
  Proof.
      intros * HF. invert HF. auto.
  Qed.

  Fixpoint forall3b (f : A -> B -> C -> bool) l1 l2 l3 :=
    match l1, l2, l3 with
    | nil, nil, nil => true
    | e1 :: l1, e2 :: l2, e3 :: l3 => andb (f e1 e2 e3) (forall3b f l1 l2 l3)
    | _, _, _ => false
    end.

  Lemma Forall3_ignore23:
    forall xs ys zs,
      Forall3 xs ys zs ->
      Forall (fun x => exists y z, R x y z) xs.
  Proof. induction 1; eauto. Qed.

  Lemma Forall3_ignore13:
    forall xs ys zs,
      Forall3 xs ys zs ->
      Forall (fun y => exists x z, R x y z) ys.
  Proof. induction 1; eauto. Qed.

  Lemma Forall3_ignore12:
    forall xs ys zs,
      Forall3 xs ys zs ->
      Forall (fun z => exists x y, R x y z) zs.
  Proof. induction 1; eauto. Qed.

  Lemma Forall3_ignore2:
    forall xs ys zs,
      Forall3 xs ys zs ->
      Forall2 (fun x z => exists y, R x y z) xs zs.
  Proof. induction 1; eauto. Qed.

  Lemma Forall3_ignore3:
    forall xs ys zs,
      Forall3 xs ys zs ->
      Forall2 (fun x y => exists z, R x y z) xs ys.
  Proof. induction 1; eauto. Qed.

  Lemma Forall3_zip3 xs ys f :
    Forall2 (fun x y => R x y (f x y)) xs ys ->
    Forall3 xs ys (zip f xs ys).
  Proof. induction 1; cbv [zip]; simpl; constructor; auto. Qed.    
End Forall3.

Lemma Forall3_impl {A B C} xs ys zs (R1 R2 : A -> B -> C -> Prop) :
  (forall x y z, R1 x y z -> R2 x y z) ->
  Forall3 R1 xs ys zs ->
  Forall3 R2 xs ys zs.
Proof. induction 2; constructor; eauto. Qed.
