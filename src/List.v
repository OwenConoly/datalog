From Stdlib Require Import Lists.List.
From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics.
From Lower Require Import ListMisc.
From coqutil Require Import Datatypes.List Tactics.fwd Tactics.destr Tactics.
Require Import Datalog.Tactics Datalog.Forall3.

Import ListNotations.
Section subset.
Context {A : Type}.
Context (eqb : A -> A -> bool) {eqb_spec :  forall x0 y0 : A, BoolSpec (x0 = y0) (x0 <> y0) (eqb x0 y0)}.

(*I would like to do some magic to make this infer the eqb to use, but idk how*)
(*hmm i am making my compiler take quadratic time.  i guess it already did though.*)
Definition inclb (l1 l2 : list A) :=
  forallb (fun x => existsb (eqb x) l2) l1.

Lemma inclb_incl l1 l2 :
  inclb l1 l2 = true <-> incl l1 l2.
Proof.
  cbv [inclb]. rewrite forallb_forall. split.
  - intros H a H0. apply H in H0. rewrite existsb_exists in H0. fwd. auto.
  - intros. rewrite existsb_exists. eexists ?[x0]. destr (eqb x ?x0); eauto.
Qed.

Lemma incl_app_app (x1 : list A) y1 x2 y2 :
  incl x1 x2 ->
  incl y1 y2 ->
  incl (x1 ++ y1) (x2 ++ y2).
Proof. cbv [incl]. intros. repeat rewrite in_app_iff in *. intuition auto. Qed.
End subset.

Section Forall.
Context {A B C : Type}.
Implicit Type xs : list A.
Implicit Type ys : list B.
Implicit Type zs : list C.

Lemma Forall2_forget_l R xs ys :
  Forall2 R xs ys ->
  Forall (fun y => exists x, In x xs /\ R x y) ys.
Proof.
  induction 1; eauto. simpl. econstructor; eauto.
  eapply Forall_impl; [|eassumption]. simpl. intros. fwd. eauto.
Qed.

Lemma Forall2_forget_r R xs ys :
  Forall2 R xs ys ->
  Forall (fun x => exists y, In y ys /\ R x y) xs.
Proof.
  induction 1; eauto. simpl. econstructor; eauto.
  eapply Forall_impl; [|eassumption]. simpl. intros. fwd. eauto.
Qed.

Lemma Forall2_forget_r_strong R xs ys :
  Forall2 R xs ys ->
  Forall (fun x => exists y, In (x, y) (combine xs ys) /\ R x y) xs.
Proof.
  induction 1; eauto. simpl. econstructor; eauto.
  eapply Forall_impl; [|eassumption]. simpl. intros. fwd. eauto.
Qed.

Lemma Forall_exists_r_Forall2 R xs :
  Forall (fun x => exists y, R x y) xs ->
  exists ys, Forall2 R xs ys.
Proof. induction 1; fwd; eauto. Qed.

Lemma Forall2_unique_r R xs ys ys' :
  Forall2 R xs ys ->
  Forall2 R xs ys' ->
  (forall x y y', R x y -> R x y' -> y = y') ->
  ys = ys'.
Proof.
  intros H. revert ys'. induction H; intros; invert_list_stuff; f_equal; eauto.
Qed.

Lemma Forall2_and R1 R2 xs ys :
  Forall2 R1 xs ys ->
  Forall2 R2 xs ys ->
  Forall2 (fun x y => R1 x y /\ R2 x y) xs ys.
Proof. induction 1; intros; invert_list_stuff; eauto. Qed.

Lemma Forall2_true xs ys :
  length xs = length ys ->
  Forall2 (fun _ _ => True) xs ys.
Proof. revert ys. induction xs; destruct ys; simpl; try congruence; eauto. Qed.

Lemma Forall2_map_l R (f : A -> B) (l1 : list A) (l2 : list C) :
  Forall2 (fun x => R (f x)) l1 l2 <->
    Forall2 R (map f l1) l2.
Proof.
  split; intros H.
  - induction H. 1: constructor. constructor; assumption.
  - remember (map f l1) as l1' eqn:E. revert l1 E. induction H; intros l1 Hl1.
    + destruct l1; inversion Hl1. constructor.
    + destruct l1; inversion Hl1. subst. constructor; auto.
Qed.

Lemma Forall2_flip_iff R (l1 : list A) (l2 : list B) :
  Forall2 (fun x y => R y x) l2 l1 <->
    Forall2 R l1 l2.
Proof.
  split; auto using Forall2_flip.
Qed.

Lemma in_combine_l_iff xs ys x (y : B) :
  (exists y, In (x, y) (combine xs ys)) <-> In x (firstn (length ys) xs).
Proof.
  revert ys. induction xs; simpl; intros; eauto.
  - destruct (length _); simpl; split; intros; fwd; eauto.
  - destruct ys; simpl; split; intros; fwd; eauto.
    + destruct H; fwd; eauto. rewrite <- IHxs. eauto.
    + destruct H; subst; fwd; eauto. rewrite <- IHxs in H. fwd. eauto.
Qed.

Lemma in_fst (x : A) (y : B) xys :
  In (x, y) xys ->
  In x (map fst xys).
Proof. induction xys; simpl; eauto. destruct 1; subst; eauto. Qed.

Lemma Forall3_combine12 R xs ys zs :
  Forall3 (fun x y => R (x, y)) xs ys zs ->
  Forall2 R (combine xs ys) zs.
Proof. induction 1; simpl; eauto. Qed.    
End Forall.

Section misc.
Context {A B : Type}.
Implicit Type xs : list A.  

Lemma invert_concat_same xss xss' :
  concat xss = concat xss' ->
  Forall2 (fun xs xs' => length xs = length xs') xss xss' ->
  xss = xss'.
Proof.
  induction 2; simpl in *; eauto. eapply invert_app in H; eauto.
  fwd. f_equal. eauto.
Qed.

Lemma invert_concat_same' xss xss' n :
  concat xss = concat xss' ->
  length xss = length xss' ->
  Forall (fun xs => length xs = n) xss ->
  Forall (fun xs => length xs = n) xss' ->
  xss = xss'.
Proof.
  intros H H0 H1 H2. apply invert_concat_same; auto.
  eapply Forall2_impl_strong; [|apply Forall2_true; auto].
  intros x y _ Hx Hy. rewrite Forall_forall in *. rewrite H1, H2; auto.
Qed.

Lemma incl_concat_l ls (l : list A) :
  incl (concat ls) l ->
  Forall (fun l' => incl l' l) ls.
Proof.
  cbv [incl]. intros H. apply Forall_forall.
  intros. apply H. apply in_concat. eauto.
Qed.

Lemma incl_flat_map_r (f : A -> list B) x xs :
  In x xs ->
  incl (f x) (flat_map f xs).
Proof.
  intros H. induction xs; simpl in *.
  - contradiction.
  - destruct H; subst; auto using incl_appr, incl_appl, incl_refl.
Qed.  

Lemma incl_flat_map_flat_map_strong (f g : A -> list B) l l' :
  incl l l' ->
  (forall x, incl (f x) (g x)) ->
  incl (flat_map f l) (flat_map g l').
Proof.
  induction l; simpl.
  - intros. apply incl_nil_l.
  - intros. apply incl_cons_inv in H. fwd.
    eauto using incl_app, incl_flat_map_r, incl_tran.
Qed.
End misc.

From Stdlib Require Import Lia.
Lemma list_sum_repeat n m :
  list_sum (repeat n m) = n * m.
Proof. induction m; simpl; lia. Qed.

Lemma Forall2_map_r {A B C} R (f : B -> C) (l1 : list A) (l2 : list B) :
  Forall2 (fun x y => R x (f y)) l1 l2 <->
    Forall2 R l1 (map f l2).
Proof.
  symmetry. rewrite <- Forall2_flip_iff, <- Forall2_map_l, <- Forall2_flip_iff.
  reflexivity.
Qed.
