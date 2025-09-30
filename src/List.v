From Stdlib Require Import Lists.List.
From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics.
Require Import coqutil.Datatypes.List coqutil.Tactics.fwd coqutil.Tactics.destr.

Import ListNotations.
Section __.
Context {A : Type}.
Context (eqb : A -> A -> bool) {eqb_spec :  forall x0 y0 : A, BoolSpec (x0 = y0) (x0 <> y0) (eqb x0 y0)}.

(*I would like to do some magic to make this infer the eqb to use, but idk how*)
(*hmm i am making my compiler take quadratic time.  i guess it already did though.*)
Definition subsetb (l1 l2 : list A) :=
  forallb (fun x => existsb (eqb x) l2) l1.

Definition subset (l1 l2 : list A) :=
  (forall a, In a l1 -> In a l2).

Lemma Forall_subset P l1 l2 :
  Forall P l2 ->
  subset l1 l2 ->
  Forall P l1.
Proof. do 2 rewrite Forall_forall. auto. Qed.

Lemma subsetb_subset l1 l2 :
  subsetb l1 l2 = true <-> subset l1 l2.
Proof.
  cbv [subsetb]. rewrite forallb_forall. split.
  - intros H a H0. apply H in H0. rewrite existsb_exists in H0. fwd. auto.
  - intros. rewrite existsb_exists. eexists ?[x0]. destr (eqb x ?x0); eauto.
Qed.

Lemma subset_refl x : subset x x.
Proof. cbv [subset]. auto. Qed.

Lemma subset_trans x y z :
  subset x y ->
  subset y z ->
  subset x z.
Proof. cbv [subset]. auto. Qed.

Lemma subset_app_app x1 y1 x2 y2 :
  subset x1 x2 ->
  subset y1 y2 ->
  subset (x1 ++ y1) (x2 ++ y2).
Proof. cbv [subset]. intros. repeat rewrite in_app_iff in *. intuition auto. Qed.
End __.
