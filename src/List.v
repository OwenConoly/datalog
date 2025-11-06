From Stdlib Require Import Lists.List Permutation.
From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics.
From Lower Require Import ListMisc.
From coqutil Require Import Datatypes.List Tactics.fwd Tactics.destr Tactics.
Require Import Datalog.Tactics.

Local Ltac invert_list_stuff' :=
  repeat match goal with
    | H: Forall _ (cons _ _) |- _ => invert H
    | H : Forall _ nil |- _ => invert H
    | H : Forall2 _ (cons _ _) _ |- _ => invert H
    | H : Forall2 _ _ (cons _ _) |- _ => invert H
    | H : Forall2 _ nil _ |- _ => invert H
    | H : Forall2 _ _ nil |- _ => invert H
    | H : Exists _ nil |- _ => invert H
    | H : Exists _ (cons _ nil) |- _ => invert H
    | H : Some _ = Some _ |- _ => invert H
    | H : Some _ = None |- _ => invert H
    | H : None = Some _ |- _ => invert H
    | H : [] = [] |- _ => invert H
    | H : _ :: _ = _ :: _ |- _ => invert H
    | H : _ :: _ = [] |- _ => discriminate H
    | H : [] = _ :: _ |- _ => discriminate H
  end.

Import ListNotations.
Section subset.
Context {A : Type}.
Context (eqb : A -> A -> bool) {eqb_spec :  forall x0 y0 : A, BoolSpec (x0 = y0) (x0 <> y0) (eqb x0 y0)}.
Implicit Type l : list A.

Lemma Permutation_incl l l' :
  Permutation l l' ->
  incl l l'.
Proof. cbv [incl]. eauto using Permutation_in. Qed.

Lemma incl_app_bw_l l l1 l2 :
  incl (l1 ++ l2) l ->
  incl l1 l.
Proof. intros H. cbv [incl] in *. intros. apply H. apply in_app_iff. auto. Qed.

Lemma incl_app_bw_r l l1 l2 :
  incl (l1 ++ l2) l ->
  incl l2 l.
Proof. intros H. cbv [incl] in *. intros. apply H. apply in_app_iff. auto. Qed.

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

Lemma incl_cons_idk x l1 l2 :
  incl l1 (x :: l2) ->
  exists l1',
    incl l1' l2 /\
      incl l1 (x :: l1') /\
      incl l1' l1.
Proof.
  intros H. induction l1.
  - exists nil. auto using incl_nil_l.
  - apply incl_cons_inv in H. fwd. simpl in Hp0. specialize (IHl1 Hp1).
    fwd. destruct Hp0.
    + subst. exists l1'. split; auto. split.
      -- apply incl_cons; simpl; auto.
      -- apply incl_tl. assumption.
    + exists (a :: l1'). ssplit.
      -- apply incl_cons; auto.
      -- apply incl_cons; simpl; auto. eapply incl_tran; [exact IHl1p1|].
         apply incl_cons; simpl; auto. do 2 apply incl_tl. apply incl_refl.
      -- apply incl_cons; simpl; auto. apply incl_tl. assumption.
Qed.
End subset.

Section Forall.
Context {A B C : Type}.
Implicit Type xs : list A.
Implicit Type ys : list B.
Implicit Type zs : list C.

Lemma Forall2_combine R xs ys :
  Forall2 R xs ys ->
  Forall (fun '(x, y) => R x y) (combine xs ys).
Proof. induction 1; simpl; eauto. Qed.

Lemma Forall_combine R xs ys :
  Forall2 (fun x y => R (x, y)) xs ys ->
  Forall R (combine xs ys).
Proof. induction 1; simpl; eauto. Qed.

Lemma Forall_zip (R : C -> Prop) xs ys f :
  Forall2 (fun x y => R (f x y)) xs ys ->
  Forall R (zip f xs ys).
Proof.
  intros. cbv [zip]. apply Forall_map.
  apply Forall_combine. assumption.
Qed.

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
  intros H. revert ys'. induction H; intros; invert_list_stuff'; f_equal; eauto.
Qed.

Lemma Forall2_and R1 R2 xs ys :
  Forall2 R1 xs ys ->
  Forall2 R2 xs ys ->
  Forall2 (fun x y => R1 x y /\ R2 x y) xs ys.
Proof. induction 1; intros; invert_list_stuff'; eauto. Qed.

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

Lemma Forall2_firstn R xs ys n :
  Forall2 R xs ys ->
  Forall2 R (firstn n xs) (firstn n ys).
Proof. intros H. revert n. induction H; destruct n; simpl; eauto. Qed.

Lemma Forall2_skipn R xs ys n :
  Forall2 R xs ys ->
  Forall2 R (skipn n xs) (skipn n ys).
Proof. intros H. revert n. induction H; destruct n; simpl; eauto. Qed.

Lemma Forall_or P Q xs :
  Forall (fun x => P x \/ Q x) xs ->
  Forall P xs \/ Exists Q xs.
Proof. induction 1; eauto. destruct H, IHForall; auto. Qed.

Lemma Forall2_rev R xs ys :
  Forall2 R xs ys ->
  Forall2 R (rev xs) (rev ys).
Proof. induction 1; simpl; auto using Forall2_app. Qed.

Lemma zip_ext_in (f : _ -> _ -> C) g xs ys :
  (forall x y, In (x, y) (combine xs ys) -> f x y = g x y) ->
  zip f xs ys = zip g xs ys.
Proof.
  intros. revert ys H. induction xs; eauto.
  intros ys. destruct ys; simpl; eauto. cbv [zip].
  simpl. intros. f_equal; eauto.
Qed.

Lemma zip_ext (f : _ -> _ -> C) g xs ys :
  (forall x y, f x y = g x y) ->
  zip f xs ys = zip g xs ys.
Proof.
  intros. apply zip_ext_in; auto.
Qed.


End Forall.

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

Lemma option_all_Forall2 X (xs : list (option X)) xs' :
  option_all xs = Some xs' ->
  Forall2 (fun x x' => x = Some x') xs xs'.
Proof.
  revert xs'. induction xs; simpl.
  1: invert 1; eauto.
  repeat (destruct_one_match; try congruence).
  invert 1. eauto.
Qed.

Lemma Forall2_option_all X (xs : list (option X)) xs' :
  Forall2 (fun x x' => x = Some x') xs xs' ->
  option_all xs = Some xs'.
Proof.
  intros H. induction H; simpl; eauto.
  repeat (destruct_one_match; try congruence).
Qed.    

Definition option_coalesce {X : Type} (x : option (option X)) :=
  match x with
  | Some (Some x) => Some x
  | _ => None
  end.

Lemma option_coalesce_Some X (x : option (option X)) x' :
  option_coalesce x = Some x' ->
  x = Some (Some x').
Proof.
  cbv [option_coalesce]. repeat (destruct_one_match; try congruence).
Qed.

Lemma option_map_Some X Y (f : X -> Y) x y :
  option_map f x = Some y ->
  exists x', x = Some x' /\ f x' = y.
Proof.
  cbv [option_map]. destruct_one_match; try congruence.
  invert 1. eauto.
Qed.

Lemma option_map_None X Y (f : X -> Y) x :
  option_map f x = None ->
  x = None.
Proof. cbv [option_map]. destruct_one_match; congruence. Qed.

(*copied from https://velus.inria.fr/emsoft2021/html/Velus.Common.CommonList.html*)
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
      Forall2 (fun x z => exists y, In y ys /\ R x y z) xs zs.
  Proof.
    induction 1; econstructor; simpl; eauto.
    eapply Forall2_impl; [|eassumption].
    simpl. intros. fwd. eauto.
  Qed.

  Lemma Forall3_ignore3:
    forall xs ys zs,
      Forall3 xs ys zs ->
      Forall2 (fun x y => exists z, R x y z) xs ys.
  Proof. induction 1; eauto. Qed.

  Lemma Forall3_zip3 xs ys f :
    Forall2 (fun x y => R x y (f x y)) xs ys ->
    Forall3 xs ys (zip f xs ys).
  Proof. induction 1; cbv [zip]; simpl; constructor; auto. Qed.

  Lemma Forall3_unique_2 xs ys ys' zs :
    Forall3 xs ys zs ->
    Forall3 xs ys' zs ->
    (forall x y y' z, R x y z -> R x y' z -> y = y') ->
    ys = ys'.
  Proof. intros H. revert ys'. induction H; invert 1; intros; f_equal; eauto. Qed.

  Lemma Forall3_firstn n xs ys zs :
    Forall3 xs ys zs ->
    Forall3 (firstn n xs) (firstn n ys) (firstn n zs).
  Proof. intros H. revert n. induction H; destruct n; simpl; constructor; eauto. Qed.
End Forall3.

Section misc.
Context {A B C D : Type}.
Implicit Type xs : list A.
Implicit Type ys : list B.
Implicit Type zs : list C.

Lemma nth_error_repeat' (x : A) y m n :
  nth_error (repeat x m) n = Some y ->
  x = y.
Proof.
  intros H. epose proof nth_error_Some as H1.
  specialize (H1 _ _ _ ltac:(eassumption)). pose proof nth_error_repeat as H2.
  rewrite repeat_length in H1. rewrite nth_error_repeat in H by lia. invert H.
  reflexivity.
Qed.

Lemma Forall2_flat_map xs ys R (f : A -> list C) (g : B -> list D) :
  Forall2 (fun x y => Forall2 R (f x) (g y)) xs ys ->
  Forall2 R (flat_map f xs) (flat_map g ys).
Proof. induction 1; simpl; eauto using Forall2_app. Qed.

Lemma In_skipn x n xs :
  In x (skipn n xs) ->
  In x xs.
Proof. intros. erewrite <- firstn_skipn. apply in_app_iff. eauto. Qed.

Lemma map_is_flat_map (f : A -> B) xs :
  map f xs = flat_map (fun x => [f x]) xs.
Proof. induction xs; eauto. Qed.

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

Lemma incl_flat_map_strong (f g : A -> list B) l l' :
  incl l l' ->
  (forall x, incl (f x) (g x)) ->
  incl (flat_map f l) (flat_map g l').
Proof.
  induction l; simpl.
  - intros. apply incl_nil_l.
  - intros. apply incl_cons_inv in H. fwd.
    eauto using incl_app, incl_flat_map_r, incl_tran.
Qed.

Hint Unfold incl : core.

Lemma incl_firstn (l : list A) n :
  incl (firstn n l) l.
Proof. eauto using in_firstn. Qed.

Lemma incl_skipn (l : list A) n :
  incl (skipn n l) l.
Proof. eauto using in_skipn. Qed.

Lemma flat_map_map (g : A -> B) (f : B -> list C) l :
  flat_map f (map g l) = flat_map (fun x => f (g x)) l.
Proof. induction l; simpl; f_equal; auto. Qed.

Lemma flat_map_flat_map (f : B -> list C) (g : A -> list B) l :
  flat_map f (flat_map g l) = flat_map (fun x => flat_map f (g x)) l.
Proof. induction l; simpl; eauto. rewrite flat_map_app. f_equal. assumption. Qed.

Lemma Forall3_impl xs ys zs R1 R2 :
  (forall x y z, R1 x y z -> R2 x y z) ->
  Forall3 R1 xs ys zs ->
  Forall3 R2 xs ys zs.
Proof. induction 2; constructor; eauto. Qed.

Lemma Forall3_swap23 R xs ys zs :
  Forall3 (fun x z y => R x y z) xs zs ys ->
  Forall3 R xs ys zs.
Proof. induction 1; constructor; eauto. Qed.

Lemma Forall3_combine12 R xs ys zs :
  Forall3 (fun x y => R (x, y)) xs ys zs ->
  Forall2 R (combine xs ys) zs.
Proof. induction 1; simpl; eauto. Qed.    

Lemma Forall2_Forall2_Forall3 R1 R2 xs ys zs :
  Forall2 R1 xs ys ->
  Forall2 R2 ys zs ->
  Forall3 (fun x y z => R1 x y /\ R2 y z) xs ys zs.
Proof.
  intros H. revert zs. induction H; invert 1; constructor; eauto.
Qed.

Lemma Forall2_eq_eq xs xs' :
  Forall2 eq xs xs' ->
  xs = xs'.
Proof. induction 1; subst; reflexivity. Qed.  

Lemma eq_Forall2_eq xs xs' :
  xs = xs' ->
  Forall2 eq xs xs'.
Proof. intros. subst. induction xs'; eauto. Qed.  

Lemma Forall2_concat R xss yss :
  Forall2 (fun xs ys => Forall2 R xs ys) xss yss ->
  Forall2 R (concat xss) (concat yss).
Proof. induction 1; simpl; eauto using Forall2_app. Qed.
End misc.

Lemma Forall3_map3 {A B C D} (f : C -> D) xs ys zs (R : A -> B -> D -> Prop) :
  Forall3 (fun x y z => R x y (f z)) xs ys zs <->
  Forall3 R xs ys (map f zs).
Proof.
  split.
  - induction 1; simpl; econstructor; eauto.
  - remember (map _ _) eqn:E. intros H. revert zs E.
    induction H; intros zs; destruct zs; intros; simpl in *; invert_list_stuff';
      econstructor; eauto.
Qed.

Lemma map_cons_eq {A B : Type} (f : A -> B) x l l' :
  map f l = l' ->
  map f (x :: l) = f x :: l'.
Proof. simpl. intros. f_equal. assumption. Qed.



Ltac invert_list_stuff :=
  repeat match goal with
    | H: option_map _ _ = None |- _ => apply option_map_None in H; fwd
    | H: option_map _ _ = Some _ |- _ => apply option_map_Some in H; fwd
    | H: option_coalesce _ = Some _ |- _ => apply option_coalesce_Some in H; fwd
    | _ => invert_list_stuff'
    end.

Hint Extern 0 => apply incl_app : incl.
Hint Immediate incl_refl incl_nil_l in_eq : incl.
Hint Resolve incl_app_bw_l incl_app_bw_r incl_flat_map_strong incl_map incl_app incl_appl incl_appr incl_tl incl_cons Permutation_incl Permutation_in Permutation_sym : incl.
  
