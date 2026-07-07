From Stdlib Require Import Lists.List Permutation Bool Arith.PeanoNat Morphisms.
From coqutil Require Import Datatypes.List Datatypes.Option Tactics.fwd Tactics.destr Tactics Eqb.
Require Import Datalog.Tactics Datalog.Eqb.
Import ListNotations.

Local Ltac invert_list_stuff' :=
  repeat match goal with
    | H : False \/ _ |- _ => destruct H as [[]|H]
    | H : _ \/ False |- _ => destruct H as [H|[]]
    | H : Forall _ (cons _ _) |- _ => invert H
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
    | H : In _ [_] |- _ => destruct H; [|contradiction]
    | H : In _ [] |- _ => contradiction
    end.

Definition is_list_set {X : Type} (S : X -> Prop) (l : list X) :=
  (forall x, S x <-> In x l) /\ NoDup l.

Lemma is_list_set_map X Y S l (f : X -> Y) :
  FinFun.Injective f ->
  is_list_set S l ->
  is_list_set (fun y => exists x, y = f x /\ S x) (map f l).
Proof.
  intros Hf [H1 H2]. split.
  - intros. split; intros H3; fwd.
    + apply in_map_iff. apply H1 in H3p1. eauto.
    + apply in_map_iff in H3. fwd. apply H1 in H3p1. eauto.
  - apply FinFun.Injective_map_NoDup; assumption.
Qed.

Lemma is_list_set_ext X (S1 S2 : X -> _) l :
  is_list_set S1 l ->
  (forall x, S1 x <-> S2 x) ->
  is_list_set S2 l.
Proof.
  intros [H1 H2] H3. split; auto. intros. rewrite <- H3. apply H1.
Qed.

Lemma is_list_set_perm X (S : X -> _) l1 l2 :
  is_list_set S l1 ->
  is_list_set S l2 ->
  Permutation.Permutation l1 l2.
Proof.
  intros [H1 H2] [H3 H4]. apply NoDup_Permutation; auto.
  intros. rewrite <- H1, H3. reflexivity.
Qed.

Import ListNotations.

#[export] Instance Permutation_filter {A} (q : A -> bool) :
  Proper (@Permutation A ==> @Permutation A) (filter q).
Proof.
  intros l l' HP. induction HP; cbn [filter].
  - apply Permutation_refl.
  - destruct (q x); [ apply perm_skip | ]; assumption.
  - destruct (q x), (q y); solve [ apply perm_swap | apply Permutation_refl ].
  - eapply perm_trans; eassumption.
Qed.

Lemma perm_ins {X : Type} (a b d s : list X) :
  Permutation (a ++ b) s -> Permutation (a ++ d ++ b) (d ++ s).
Proof.
  intros HP. transitivity (d ++ a ++ b); [ | apply Permutation_app_head; exact HP ].
  rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
Qed.

Lemma flat_map_all_nil {A B} (g : A -> list B) (l : list A) :
  (forall x, In x l -> g x = []) -> flat_map g l = [].
Proof.
  induction l as [|a l IHl]; cbn [flat_map]; intros Hall; [reflexivity|].
  rewrite (Hall a) by (left; reflexivity). cbn [app].
  apply IHl. intros x Hin. apply Hall. right. exact Hin.
Qed.

Lemma combine_map {A B C} (f : A -> B) (g : A -> C) (l : list A) :
  combine (map f l) (map g l) = map (fun x => (f x, g x)) l.
Proof. induction l as [|a l IH]; cbn [map combine]; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma Forall2_map_map {A B D} (R : B -> D -> Prop) (f : A -> B) (g : A -> D) (l : list A) :
  Forall (fun x => R (f x) (g x)) l -> Forall2 R (map f l) (map g l).
Proof.
  induction l as [|a l IH]; cbn [map]; intros HF; [constructor|].
  pose proof (Forall_inv HF) as Hhd. pose proof (Forall_inv_tail HF) as Htl.
  constructor; [ exact Hhd | exact (IH Htl) ].
Qed.

Section subset.
  Context {A : Type}.
  Context {eqb : Eqb A} {eqb_ok : Eqb_ok eqb}.
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

  Lemma Forall2_same R xs :
    Forall (fun x => R x x) xs ->
    Forall2 R xs xs.
  Proof. induction 1; auto. Qed.

  Lemma Forall2_combine R xs ys :
    Forall2 R xs ys ->
    Forall (fun '(x, y) => R x y) (combine xs ys).
  Proof. induction 1; simpl; eauto. Qed.

  Lemma Forall_combine_Forall2 R xs ys :
    Forall R (combine xs ys) ->
    length xs = length ys ->
    Forall2 (fun x y => R (x, y)) xs ys.
  Proof.
    revert ys.
    induction xs; intros ys H Hlen; destruct ys; simpl in Hlen; try discriminate;
      simpl in *; invert_list_stuff'; auto.
  Qed.

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

  Lemma Forall2_zip (R : C -> Prop) xs ys f :
    length xs = length ys ->
    Forall R (zip f xs ys) ->
    Forall2 (fun x y => R (f x y)) xs ys.
  Proof.
    revert ys. induction xs; intros [|y ys] H; try discriminate H; auto.
    cbv [zip]. simpl. invert 1. auto.
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

  Lemma map_eq_Forall2 (f : A -> C) (g : B -> C) (l1 : list A) (l2 : list B) :
    map f l1 = map g l2 ->
    Forall2 (fun x y => f x = g y) l1 l2.
  Proof.
    revert l2. induction l1 as [|x l1' IH]; destruct l2 as [|y l2']; simpl; intro H; try discriminate.
    - constructor.
    - injection H as Heq Htail. constructor.
      + exact Heq.
      + apply IH. exact Htail.
  Qed.

  Lemma Forall2_eq_map (f : B -> A) (l1 : list A) (l2 : list B) :
    Forall2 (fun x y => y = f x) l2 l1 <-> l1 = map f l2.
  Proof.
    split.
    - induction 1; simpl; congruence.
    - intros ->. induction l2; constructor; reflexivity || assumption.
  Qed.

  Lemma in_combine_l_iff xs ys x (y : B) :
    (exists y, In (x, y) (combine xs ys)) <-> In x (firstn (length ys) xs).
  Proof.
    revert ys. induction xs; simpl; intros; eauto.
    - destruct (length _); simpl; split; intros; fwd; eauto.
    - destruct ys; simpl; split; intros; fwd; eauto.
      + destruct H; fwd; eauto.
      + destruct H; subst; fwd; eauto. rewrite <- IHxs in H. fwd. eauto.
  Qed.

  Lemma in_fst (x : A) (y : B) xys :
    In (x, y) xys ->
    In x (map fst xys).
  Proof. induction xys; simpl; eauto. destruct 1; subst; eauto. Qed.

  Lemma in_snd (x : A) (y : B) xys :
    In (x, y) xys ->
    In y (map snd xys).
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

Definition partial_injective {A B} (f : A -> option B) : Prop :=
  forall x y v, f x = Some v -> f y = Some v -> x = y.

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

  Lemma Forall3_ignore12_strong:
    forall xs ys zs,
      Forall3 xs ys zs ->
      Forall (fun z => exists x y, In x xs /\ In y ys /\ R x y z) zs.
  Proof.
    induction 1; eauto.
    constructor; simpl; eauto 7.
    eapply Forall_impl; [|eassumption].
    simpl. intros. fwd. eauto 7.
  Qed.

  Lemma Forall3_ignore12 :
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

  Lemma Forall3_ignore3_strong:
    forall xs ys zs,
      Forall3 xs ys zs ->
      Forall2 (fun x y => exists z, In z zs /\ R x y z) xs ys.
  Proof.
    induction 1; econstructor; simpl; eauto.
    eapply Forall2_impl; [|eassumption].
    simpl. intros. fwd. eauto.
  Qed.

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

  Lemma Forall3_app xs1 ys1 zs1 xs2 ys2 zs2 :
    Forall3 xs1 ys1 zs1 ->
    Forall3 xs2 ys2 zs2 ->
    Forall3 (xs1 ++ xs2) (ys1 ++ ys2) (zs1 ++ zs2).
  Proof. induction 1; simpl; auto. constructor; auto. Qed.

  Lemma Forall3_app_inv_m xs ys1 ys2 zs :
    Forall3 xs (ys1 ++ ys2) zs ->
    exists xs1 xs2 zs1 zs2,
      xs = xs1 ++ xs2 /\ zs = zs1 ++ zs2 /\
      Forall3 xs1 ys1 zs1 /\ Forall3 xs2 ys2 zs2.
  Proof.
    revert xs zs. induction ys1 as [|y ys1 IH]; intros xs zs H.
    - exists nil, xs, nil, zs. simpl. ssplit; auto. constructor.
    - simpl in H. invert H.
      specialize (IH _ _ ltac:(eassumption)). fwd.
      exists (x :: xs1), xs2, (z :: zs1), zs2.
      ssplit; simpl; auto. constructor; auto.
  Qed.

  Lemma Forall3_app_middle xs1 x xs2 ys1 y ys2 zs1 z zs2 :
    Forall3 xs1 ys1 zs1 ->
    R x y z ->
    Forall3 xs2 ys2 zs2 ->
    Forall3 (xs1 ++ x :: xs2) (ys1 ++ y :: ys2) (zs1 ++ z :: zs2).
  Proof.
    intros H1 Hm H2. apply Forall3_app; auto. constructor; auto.
  Qed.

  Lemma Forall3_app_middle_inv_m xs ys1 y ys2 zs :
    Forall3 xs (ys1 ++ y :: ys2) zs ->
    exists xs1 x xs2 zs1 z zs2,
      xs = xs1 ++ x :: xs2 /\ zs = zs1 ++ z :: zs2 /\
      Forall3 xs1 ys1 zs1 /\ R x y z /\ Forall3 xs2 ys2 zs2.
  Proof.
    intros H. apply Forall3_app_inv_m in H. fwd.
    invert Hp3. do 6 eexists. ssplit; eauto.
  Qed.

  Lemma Forall3_app_inv_l xs1 xs2 ys zs :
    Forall3 (xs1 ++ xs2) ys zs ->
    exists ys1 ys2 zs1 zs2,
      ys = ys1 ++ ys2 /\ zs = zs1 ++ zs2 /\
      Forall3 xs1 ys1 zs1 /\ Forall3 xs2 ys2 zs2.
  Proof.
    revert ys zs. induction xs1 as [|x xs1 IH]; intros ys zs H.
    - exists nil, ys, nil, zs. simpl. ssplit; auto. constructor.
    - simpl in H. invert H.
      specialize (IH _ _ ltac:(eassumption)). fwd.
      exists (y :: ys1), ys2, (z :: zs1), zs2.
      ssplit; simpl; auto. constructor; auto.
  Qed.

  Lemma Forall3_app_middle_inv_l xs1 x xs2 ys zs :
    Forall3 (xs1 ++ x :: xs2) ys zs ->
    exists ys1 y ys2 zs1 z zs2,
      ys = ys1 ++ y :: ys2 /\ zs = zs1 ++ z :: zs2 /\
      Forall3 xs1 ys1 zs1 /\ R x y z /\ Forall3 xs2 ys2 zs2.
  Proof.
    intros H. apply Forall3_app_inv_l in H. fwd.
    invert Hp3. do 6 eexists. ssplit; eauto.
  Qed.
End Forall3.

Lemma app_split_at_length {A} (l1 l2 l3 l4 : list A) :
  l1 ++ l2 = l3 ++ l4 ->
  length l1 = length l3 ->
  l1 = l3 /\ l2 = l4.
Proof.
  revert l3. induction l1 as [|a l1 IH]; intros [|b l3] H Hlen;
    simpl in *; try discriminate; auto.
  injection H as -> H. specialize (IH _ H ltac:(lia)). fwd. auto.
Qed.

(* Wrappers for the common pattern of Forall3 ... xs ys (seq 0 (length ys)),
   i.e. an indexed Forall2 disguised as a Forall3.  After splitting one of
   the first two lists around a middle element, the seq splits at the
   corresponding length. *)
Lemma seq_app_middle base n m :
  seq base (n + S m) = seq base n ++ (base + n) :: seq (S (base + n)) m.
Proof.
  rewrite seq_app. simpl. reflexivity.
Qed.

Lemma Forall3_seq_app_middle_inv_m {A B} (R : A -> B -> nat -> Prop) xs ys1 y ys2 :
  Forall3 R xs (ys1 ++ y :: ys2) (seq 0 (length (ys1 ++ y :: ys2))) ->
  exists xs1 x xs2,
    xs = xs1 ++ x :: xs2 /\
    Forall3 R xs1 ys1 (seq 0 (length ys1)) /\
    R x y (length ys1) /\
    Forall3 R xs2 ys2 (seq (S (length ys1)) (length ys2)).
Proof.
  intros H. apply Forall3_app_middle_inv_m in H.
  destruct H as (xs1 & x & xs2 & zs1 & z & zs2 & Hxs & Hzs & H1 & Hm & H2).
  pose proof (Forall3_length _ _ _ _ H1) as (Hlx1 & Hlz1).
  pose proof (Forall3_length _ _ _ _ H2) as (Hlx2 & Hlz2).
  rewrite length_app in Hzs. simpl in Hzs.
  rewrite seq_app_middle in Hzs. simpl in Hzs.
  apply app_split_at_length in Hzs as (Hzs1 & Hzs_tail); [|rewrite length_seq; lia].
  injection Hzs_tail as Hz Hzs2.
  subst zs1 z zs2.
  exists xs1, x, xs2. ssplit; auto.
Qed.

Lemma Forall3_seq_app_middle_inv_l {A B} (R : A -> B -> nat -> Prop) xs1 x xs2 ys :
  Forall3 R (xs1 ++ x :: xs2) ys (seq 0 (length ys)) ->
  exists ys1 y ys2,
    ys = ys1 ++ y :: ys2 /\
    Forall3 R xs1 ys1 (seq 0 (length ys1)) /\
    R x y (length xs1) /\
    Forall3 R xs2 ys2 (seq (S (length xs1)) (length ys2)).
Proof.
  intros H. apply Forall3_app_middle_inv_l in H.
  destruct H as (ys1 & y & ys2 & zs1 & z & zs2 & Hys & Hzs & H1 & Hm & H2).
  pose proof (Forall3_length _ _ _ _ H1) as (Hly1 & Hlz1).
  pose proof (Forall3_length _ _ _ _ H2) as (Hly2 & Hlz2).
  rewrite Hys in Hzs. rewrite length_app in Hzs. simpl in Hzs.
  rewrite seq_app_middle in Hzs. simpl in Hzs.
  apply app_split_at_length in Hzs as (Hzs1 & Hzs_tail); [|rewrite length_seq; lia].
  injection Hzs_tail as Hz Hzs2.
  subst zs1 z zs2.
  exists ys1, y, ys2. rewrite Hly1. ssplit; assumption.
Qed.

Lemma Forall3_seq_app_middle {A B} (R : A -> B -> nat -> Prop) xs1 x xs2 ys1 y ys2 :
  Forall3 R xs1 ys1 (seq 0 (length ys1)) ->
  R x y (length ys1) ->
  Forall3 R xs2 ys2 (seq (S (length ys1)) (length ys2)) ->
  Forall3 R (xs1 ++ x :: xs2) (ys1 ++ y :: ys2) (seq 0 (length (ys1 ++ y :: ys2))).
Proof.
  intros H1 Hm H2. rewrite length_app. simpl. rewrite seq_app_middle. simpl.
  apply Forall3_app_middle; auto.
Qed.

(* Pointwise lookup for a seq-indexed Forall3.  Cleaner than the general
   Forall3_nth_error_fwd at sites where the third argument is fixed to
   [seq 0 (length ys)]: avoids the [nth_error_seq + Nat.ltb_lt] dance. *)
Lemma Forall3_seq_lookup {A B} (R : A -> B -> nat -> Prop) xs ys k x y :
  Forall3 R xs ys (seq 0 (length ys)) ->
  nth_error xs k = Some x ->
  nth_error ys k = Some y ->
  R x y k.
Proof.
  intros HF Hx Hy.
  apply nth_error_split in Hx as (xs1 & xs2 & Hxs & Hk_xs).
  rewrite Hxs in HF.
  apply Forall3_seq_app_middle_inv_l in HF
    as (ys1 & y' & ys2 & Hys & Hpre & Hmid & _).
  rewrite Hk_xs in Hmid.
  rewrite Hys in Hy.
  pose proof (Forall3_length _ _ _ _ Hpre) as (Hl_p & _).
  assert (Hl_ys1 : length ys1 = k) by lia.
  rewrite nth_error_app2 in Hy by lia.
  replace (k - length ys1) with 0 in Hy by lia. simpl in Hy.
  injection Hy as ->.
  exact Hmid.
Qed.

Section Existsn.
  Context {T : Type} (P : T -> Prop).
  Implicit Type l : list T.

  Inductive Existsn : nat -> list T -> Prop :=
  | Existsn_nil : Existsn 0 []
  | Existsn_no x n l :
    ~P x ->
    Existsn n l ->
    Existsn n (x :: l)
  | Existsn_yes x n l :
    P x ->
    Existsn n l ->
    Existsn (S n) (x :: l).
  Hint Constructors Existsn : core.

  Lemma Existsn_S n l :
    Existsn (S n) l ->
    exists l1 x l2,
      l = l1 ++ x :: l2 /\
        P x /\
        Existsn n (l1 ++ l2).
  Proof.
    induction l; invert 1.
    - specialize (IHl ltac:(assumption)). fwd. do 3 eexists. split.
      { apply app_comm_cons. }
      simpl. auto.
    - exists nil. simpl. eauto.
  Qed.

  Lemma Existsn_app n1 n2 l1 l2 :
    Existsn n1 l1 ->
    Existsn n2 l2 ->
    Existsn (n1 + n2) (l1 ++ l2).
  Proof.
    intros H1. revert n2 l2.
    induction H1; intros; simpl; eauto.
  Qed.

  Lemma Existsn_split n l1 l2 :
    Existsn n (l1 ++ l2) ->
    exists n1 n2,
      n = n1 + n2 /\
        Existsn n1 l1 /\
        Existsn n2 l2.
  Proof.
    revert n. induction l1; intros n H.
    - simpl in H. exists 0, n. auto.
    - invert H.
      + specialize (IHl1 _ ltac:(eassumption)). fwd. eauto 6.
      + specialize (IHl1 _ ltac:(eassumption)). fwd.
        do 2 eexists. split; [|eauto]. lia.
  Qed.

  Lemma Existsn_perm n l1 l2 :
    Existsn n l1 ->
    Permutation l1 l2 ->
    Existsn n l2.
  Proof.
    intros H Hperm. revert n H. induction Hperm; intros n H.
    - auto.
    - invert H; eauto.
    - do 2 match goal with
        | H: Existsn _ (_ :: _) |- _ => invert H
        end; auto.
    - eauto.
  Qed.

  Lemma Existsn_0_Forall_not l :
    Existsn 0 l ->
    Forall (fun x => ~P x) l.
  Proof. induction l; invert 1; auto. Qed.

  Lemma Forall_not_Existsn_0 l :
    Forall (fun x => ~P x) l ->
    Existsn 0 l.
  Proof. induction 1; auto. Qed.

  Lemma Existsn_unique n m l :
    Existsn n l ->
    Existsn m l ->
    n = m.
  Proof.
    intros H. revert m. induction H; invert 1; auto.
    all: exfalso; auto.
  Qed.
End Existsn.
Hint Constructors Existsn : core.

Section misc.
  Context {A B C D : Type}.
  Implicit Type xs : list A.
  Implicit Type ys : list B.
  Implicit Type zs : list C.

  Lemma map_inj (f : A -> B) (l1 l2 : list A) :
    (forall x y, f x = f y -> x = y) ->
    map f l1 = map f l2 ->
    l1 = l2.
  Proof.
    intros Hinj. revert l2. induction l1 as [|x xs IH]; intros [|y ys] H; simpl in H; auto; try discriminate.
    invert H. f_equal; auto.
  Qed.

  Lemma list_set_Existsn_1 S xs x :
    is_list_set S xs ->
    S x ->
    Existsn (eq x) 1 xs.
  Proof.
    intros Hls Hx. destruct Hls as [H1 H2].
    apply H1 in Hx. apply in_split in Hx. fwd.
    apply NoDup_remove_2 in H2. rewrite in_app_iff in H2.
    replace 1 with (0 + 1) by lia. apply Existsn_app.
    - apply Forall_not_Existsn_0. apply Forall_forall. intros ? ? ?. subst. auto.
    - apply Existsn_yes; auto.
      apply Forall_not_Existsn_0. apply Forall_forall. intros ? ? ?. subst. auto.
  Qed.

  Lemma Existsn_map P n xs (f : A -> B) :
    Existsn P n (map f xs) <-> Existsn (fun x => P (f x)) n xs.
  Proof.
    revert n. induction xs; intros n; simpl; split; invert 1; auto.
  Qed.

  Lemma Existsn_iff P1 P2 n xs :
    Existsn P1 n xs ->
    (forall x, P1 x <-> P2 x) ->
    Existsn P2 n xs.
  Proof.
    intros H1 H2. induction H1; auto.
  Qed.

  Lemma nth_error_repeat' (x : A) y m n :
    nth_error (repeat x m) n = Some y ->
    x = y.
  Proof.
    intros H. pose proof H as H0.
    apply nth_error_Some_bound_index in H0. rewrite repeat_length in H0.
    rewrite nth_error_repeat in H by lia. congruence.
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

  Lemma flat_map_map (g : A -> B) (f : B -> list C) l :
    flat_map f (map g l) = flat_map (fun x => f (g x)) l.
  Proof. induction l; simpl; f_equal; auto. Qed.

  Lemma flat_map_flat_map (f : B -> list C) (g : A -> list B) l :
    flat_map f (flat_map g l) = flat_map (fun x => flat_map f (g x)) l.
  Proof. induction l; simpl; eauto. rewrite flat_map_app. f_equal. assumption. Qed.

  Lemma app_inv_length1 (l1 l1' l2 l2' : list A) :
    l1 ++ l2 = l1' ++ l2' ->
    length l1 = length l1' ->
    l1 = l1' /\ l2 = l2'.
  Proof.
    revert l1'.
    induction l1; intros l1'; destruct l1'; simpl; intros; try lia; auto.
    fwd. specialize (IHl1 _ ltac:(eassumption) ltac:(eassumption)). fwd.
    split; f_equal; auto.
  Qed.

  Lemma invert_concat_same xss xss' :
    concat xss = concat xss' ->
    Forall2 (fun xs xs' => length xs = length xs') xss xss' ->
    xss = xss'.
  Proof.
    induction 2; simpl in *; eauto. apply app_inv_length1 in H; eauto.
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
  Proof. eauto using In_firstn_to_In. Qed.

  Lemma incl_skipn (l : list A) n :
    incl (skipn n l) l.
  Proof. eauto using In_skipn. Qed.

  Lemma seq_incl start len1 len2 :
    len1 <= len2 ->
    incl (seq start len1) (seq start len2).
  Proof.
    intros Hlen x Hx. apply in_seq in Hx. apply in_seq. lia.
  Qed.

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

  Lemma Forall2_nth_error R xs ys :
    length xs = length ys ->
    (forall n x y,
        nth_error xs n = Some x ->
        nth_error ys n = Some y ->
        R x y) ->
    Forall2 R xs ys.
  Proof.
    revert ys. induction xs; intros ys H1 H2.
    - destruct ys; [|discriminate H1]. constructor.
    - destruct ys; [discriminate H1|]. simpl in H1. invert H1.
      pose proof (H2 O _ _ ltac:(reflexivity) ltac:(reflexivity)).
      constructor; [assumption|]. apply IHxs; auto. intros n.
      specialize (H2 (S n)). simpl in H2. exact H2.
  Qed.

  Definition disjoint_lists (l1 l2 : list A) :=
    forall x, In x l1 -> In x l2 -> False.

  Definition same_set (l1 l2 : list A) :=
    forall x, In x l1 <-> In x l2.

  Lemma same_set_app_comm (p1 p2 : list A) :
    same_set (p1 ++ p2) (p2 ++ p1).
  Proof.
    cbv [same_set]. intros x. split; intro H;
      apply in_app_or in H; apply in_or_app; intuition idtac.
  Qed.

  Lemma disjoint_lists_comm (l1 l2 : list A) :
    disjoint_lists l1 l2 ->
    disjoint_lists l2 l1.
  Proof. cbv [disjoint_lists]. eauto. Qed.

  Lemma disjoint_lists_incl_l (l1 l1' l2 : list A) :
    disjoint_lists l1 l2 ->
    incl l1' l1 ->
    disjoint_lists l1' l2.
  Proof. cbv [disjoint_lists]. eauto. Qed.

  Lemma disjoint_lists_incl (l1 l1' l2 l2' : list A) :
    disjoint_lists l1 l2 ->
    incl l1' l1 ->
    incl l2' l2 ->
    disjoint_lists l1' l2'.
  Proof. cbv [disjoint_lists]. eauto. Qed.

  Lemma disjoint_lists_app_r (l1 l2 l3 : list A) :
    disjoint_lists l1 l2 ->
    disjoint_lists l1 l3 ->
    disjoint_lists l1 (l2 ++ l3).
  Proof.
    cbv [disjoint_lists]. intros ? ? ? ? H.
    rewrite in_app_iff in H. destruct H; eauto.
  Qed.

  Fixpoint choose_any_n n (fs : list A) :=
    match n with
    | S n' => flat_map (fun f => map (cons f) (choose_any_n n' fs)) fs
    | O => [[]]
    end.

  Lemma choose_n_spec n (hyps fs : list A) :
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

  Lemma disjoint_lists_alt (l1 l2 : list A) :
    Forall (fun x => Forall (fun y => y <> x) l2) l1 ->
    disjoint_lists l1 l2.
  Proof.
    cbv [disjoint_lists]. induction 1; simpl.
    - auto.
    - intros ? [?|?]; subst; eauto.
      rewrite Forall_forall in *. unfold not in *. eauto.
  Qed.

  Lemma option_all_map_Some (l : list A) :
    option_all (map Some l) = Some l.
  Proof.
    induction l; simpl; auto. rewrite IHl. reflexivity.
  Qed.

  Lemma option_all_map_Some' (l : list A) l' :
    option_all l' = Some l ->
    l' = map Some l.
  Proof.
    revert l. induction l'; simpl; intros l H; invert_list_stuff'; auto.
    fwd. simpl. f_equal. auto.
  Qed.

  Definition is_Some (x : option A) :=
    if x then true else false.
End misc.

Section misc.
  Context {A B C D : Type}.
  Implicit Type xs : list A.
  Implicit Type ys : list B.
  Implicit Type zs : list C.

  Definition submultiset (l1 l2 : list A) : Prop :=
    exists rest, Permutation l2 (l1 ++ rest).

  Lemma submultiset_refl l : submultiset l l.
  Proof. exists []. rewrite app_nil_r. apply Permutation_refl. Qed.

  Definition multiset_monotone (P : list A -> Prop) :=
    forall l1 l2, submultiset l1 l2 -> P l2 -> P l1.

  Lemma Forall2_same_r (R1 : A -> C -> Prop) (R2 : B -> C -> Prop) (l1 : list A) (l2 : list B) (l : list C) :
    Forall2 R1 l1 l ->
    Forall2 R2 l2 l ->
    Forall2 (fun x y => exists z, In z l /\ R1 x z /\ R2 y z) l1 l2.
  Proof.
    intros H1 H2. apply Forall2_flip in H2.
    eapply Forall2_Forall2_Forall3 in H2; [|eassumption].
    apply Forall3_ignore2 in H2. exact H2.
  Qed.

  Lemma forallb_map (f : B -> bool) (g : A -> B) (l : list A) :
    forallb f (map g l) = forallb (fun x => f (g x)) l.
  Proof.
    induction l; simpl; auto. f_equal. assumption.
  Qed.

  Lemma forallb_ext (f g : A -> bool) (l : list A) :
    (forall x, In x l -> f x = g x) ->
    forallb f l = forallb g l.
  Proof.
    intros Hext. induction l; simpl; auto.
    simpl in *. f_equal; auto.
  Qed.

  Lemma forallb_sound f xs :
    forallb f xs = true ->
    Forall (fun x => f x = true) xs.
  Proof. eauto using forallb_to_Forall. Qed.

  #[global] Instance forallb_spec f xs :
    BoolSpec (Forall (fun x => f x = true) xs) (Exists (fun x => f x = false) xs) (forallb f xs).
  Proof.
    destruct (forallb _ _) eqn:E; constructor.
    - apply forallb_sound. assumption.
    - assert (E': forallb f xs <> true) by congruence.
      rewrite forallb_forall in E'.
      rewrite <- Forall_forall in E'.
      rewrite <- Exists_Forall_neg in E'.
      2: intros; destruct (f _); auto.
      eapply Exists_impl; [|eassumption].
      simpl. intros. destruct (f _); congruence.
  Qed.

  #[global] Instance existsb_spec f xs :
    BoolSpec (Exists (fun x => f x = true) xs) (Forall (fun x => f x = false) xs) (existsb f xs).
  Proof.
    destruct (existsb _ _) eqn:E; constructor.
    - apply existsb_exists in E. fwd. apply Exists_exists. eauto.
    - assert (E': existsb f xs <> true) by congruence.
      rewrite existsb_exists in E'.
      rewrite <- Exists_exists in E'.
      rewrite <- Forall_Exists_neg in E'.
      eapply Forall_impl; [|eassumption].
      simpl. intros. destruct (f _); congruence.
  Qed.

  (*when l has length 2, this is like list_prod in stdlib*)
  Fixpoint cartesian_prod (l : list (list A)) : list (list A) :=
    match l with
    | [] => [[]]
    | xs :: xss =>
        let rest := cartesian_prod xss in
        flat_map (fun x => map (fun r => x :: r) rest) xs
    end.

  Lemma cartesian_product_spec l x :
    In x (cartesian_prod l) <-> Forall2 (@In _) x l.
  Proof.
    revert x. induction l; intros x; simpl.
    - split; intros H.
      + destruct H; subst; auto. contradiction.
      + invert H. auto.
    - rewrite in_flat_map. split; intros H.
      + fwd. rewrite in_map_iff in *. fwd. eauto.
      + invert H. eexists. rewrite in_map_iff. eauto.
  Qed.

  Fixpoint map2 (f : A -> B -> C) l1 l2 :=
    match l1, l2 with
    | x1 :: l1', x2 :: l2' => f x1 x2 :: map2 f l1' l2'
    | _, _ => []
    end.

  Lemma map2_eq_map_combine (f : A -> B -> C) (l1 : list A) (l2 : list B) :
    map2 f l1 l2 = map (fun '(a,b) => f a b) (combine l1 l2).
  Proof.
    revert l2. induction l1 as [|a l1 IH]; destruct l2; simpl; auto.
    f_equal. apply IH.
  Qed.

  Definition keep_Some : _ -> list A :=
    flat_map (fun x => match x with | Some y => [y] | None => [] end).

  Lemma in_keep_Some k l :
    In (Some k) l <-> In k (keep_Some l).
  Proof.
    cbv [keep_Some]. rewrite in_flat_map. split; intros H.
    - eexists (Some _). simpl. eauto.
    - fwd. destruct x; invert_list_stuff'; subst; auto.
  Qed.

  Lemma keep_Some_flat_map (f : B -> list (option A)) (l : list B) :
    keep_Some (flat_map f l) = flat_map (fun x => keep_Some (f x)) l.
  Proof. cbv [keep_Some]. apply flat_map_flat_map. Qed.

  (* Definition inb (x : A) (l : list A) : bool := *)
  (*   existsb (eqbA x) l. *)

  (* Print BoolSpec. *)
  (* Lemma inb_spec x l : *)
  (*   BoolSpec (In x l) (~In x l) (inb x l). *)
  (* Proof. *)
  (*   cbv [inb]. destruct (existsb _ _) eqn:E; constructor. *)
  (*   - apply existsb_exists in E. fwd. auto. *)
  (*   - Search existsb. About existsb_eqb_in. *)
  (*   split; intros H; fwd; eauto. *)
  (*   exists x. destr (eqbA x x); try congruence; auto. *)
  (* Qed. *)
End misc.

Lemma option_all_map2_Forall3 {A B C} (f : A -> B -> option C) xs ys zs :
  length xs = length ys ->
  option_all (map2 f xs ys) = Some zs ->
  Forall3 (fun x y z => f x y = Some z) xs ys zs.
Proof.
  revert ys zs. induction xs as [|x xs IH]; intros [|y ys] zs Hlen Hall;
    simpl in Hlen, Hall; try discriminate.
  - injection Hall as <-. constructor.
  - destruct (f x y) as [z|] eqn:Efxy; [|discriminate].
    destruct (option_all (map2 f xs ys)) as [zs'|] eqn:Erest; [|discriminate].
    injection Hall as <-. constructor; auto.
Qed.

Lemma Forall2_option_relation_keep_Some {A B} (R : A -> B -> Prop) l1 l2 :
  Forall2 (option_relation R) l1 l2 ->
  Forall2 R (keep_Some l1) (keep_Some l2).
Proof.
  induction 1; simpl; auto.
  cbv [option_relation] in H.
  destruct x, y; simpl; contradiction || congruence || auto.
Qed.

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

Lemma Forall3_map2 {A B B' C} (f : B -> B') xs ys zs (R : A -> B' -> C -> Prop) :
  Forall3 (fun x y z => R x (f y) z) xs ys zs ->
  Forall3 R xs (map f ys) zs.
Proof. induction 1; simpl; econstructor; eauto. Qed.

Lemma map_cons_eq {A B : Type} (f : A -> B) x l l' :
  map f l = l' ->
  map f (x :: l) = f x :: l'.
Proof. simpl. intros. f_equal. assumption. Qed.
Print invert_list_stuff'.
Ltac invert_list_stuff :=
  repeat match goal with
    | H: option_map _ _ = None |- _ => apply option_map_None in H; fwd
    | H: option_map _ _ = Some _ |- _ => apply option_map_Some in H; fwd
    | H: option_coalesce _ = Some _ |- _ => apply option_coalesce_Some in H; fwd
    | H: option_relation _ _ _ |- _ => progress (simpl in H; subst)
    | H: option_all _ = Some _ |- _ => apply option_all_map_Some' in H; subst
    | _ => invert_list_stuff'
    end.

Lemma nth_error_seq_Some n1 n2 n3 n4 :
  nth_error (seq n1 n2) n3 = Some n4 ->
  n4 = n1 + n3.
Proof.
  revert n1 n3 n4. induction n2; intros n1 n3 n4 H; simpl in *.
  - destruct n3; discriminate H.
  - destruct n3; simpl in H.
    + invert H. lia.
    + apply IHn2 in H. lia.
Qed.

Lemma NoDup_map_in_inj {A B} (f : A -> B) (l : list A) x1 x2 :
  NoDup (map f l) ->
  In x1 l ->
  In x2 l ->
  f x1 = f x2 ->
  x1 = x2.
Proof.
  intros Hnodup H1 H2 Heq.
  apply in_split in H1. destruct H1 as [l1 [l2 ->]].
  rewrite map_app in Hnodup. simpl in Hnodup.
  apply NoDup_remove_2 in Hnodup.

  apply in_app_or in H2. destruct H2 as [H2 | [H2 | H2]].
  - exfalso. apply Hnodup. apply in_or_app. left.
    rewrite Heq. apply in_map. exact H2.
  - exact H2.
  - exfalso. apply Hnodup. apply in_or_app. right.
    rewrite Heq. apply in_map. exact H2.
Qed.

Lemma NoDup_fst_In_inj {A B} (l : list (A * B)) k v1 v2 :
  NoDup (map fst l) ->
  In (k, v1) l ->
  In (k, v2) l ->
  v1 = v2.
Proof.
  intros Hnodup H1 H2.
  assert (Heq : (k, v1) = (k, v2)) by (eapply NoDup_map_in_inj; eauto).
  congruence.
Qed.

Lemma NoDup_snd_In_inj {A B} (l : list (A * B)) k v1 v2 :
  NoDup (map snd l) ->
  In (v1, k) l ->
  In (v2, k) l ->
  v1 = v2.
Proof.
  intros Hnodup H1 H2.
  assert (Heq : (v1, k) = (v2, k)) by (eapply NoDup_map_in_inj; eauto).
  congruence.
Qed.

#[global] Instance list_eqb {A} {aeqb : Eqb A} : Eqb (list A) :=
  fun x y => (length x =? length y) && forallb (eqb true) (map2 aeqb x y).

Lemma list_eqb_ok_strong {A} {aeqb : Eqb A} (x : list A) :
  Forall (fun a => forall b, if aeqb a b then a = b else a <> b) x ->
  forall y, if list_eqb x y then x = y else x <> y.
Proof.
  induction x as [|x0 x IH]; intros Hall [|y0 y];
    cbv [eqb list_eqb]; simpl; try congruence.
  inversion Hall as [|? ? Hx0 Hx]; subst.
  pose proof (Hx0 y0) as Ha.
  destruct (aeqb x0 y0); simpl.
  - subst. specialize (IH Hx y). cbv [eqb list_eqb] in IH.
    destruct (Nat.eqb_spec (length x) (length y)); simpl in IH; simpl;
      [|congruence].
    destruct (forallb _ _); simpl; congruence.
  - destruct (Nat.eqb (length x) (length y)); simpl; congruence.
Qed.

#[global] Instance list_eqb_ok {A} {aeqb : Eqb A} {aeqb_ok : Eqb_ok aeqb}
  : Eqb_ok list_eqb.
Proof.
  intros x. apply list_eqb_ok_strong.
  apply Forall_forall. intros a _ b. apply (eqb_spec a b).
Qed.

Fixpoint nodupb {T : Type} (eqb : T -> T -> bool) l :=
  match l with
  | x :: l' => if existsb (eqb x) l' then false else nodupb eqb l'
  | [] => true
  end.

#[global] Instance nodupb_correct {T} {eqb : Eqb T} {eqb_ok : Eqb_ok eqb} l :
  BoolSpec (NoDup l) (~NoDup l) (nodupb eqb l).
Proof.
  induction l; simpl in *.
  - constructor. constructor.
  - destr_sth existsb; fwd.
    + constructor. intros H'. invert H'. apply Exists_exists in E. fwd. auto.
    + rewrite Forall_forall in E. invert IHl; constructor.
      -- constructor; auto. intros H'. apply E in H'. fwd. congruence.
      -- intros H'. invert H'. auto.
Qed.

Lemma nodupb_sound {T} {eqb : Eqb T} {eqb_ok : Eqb_ok eqb} l :
  nodupb eqb l = true ->
  NoDup l.
Proof. intros. fwd. assumption. Qed.

Hint Extern 0 => apply incl_app : incl.
Hint Immediate incl_refl incl_nil_l in_eq : incl.
Hint Resolve seq_incl incl_app_bw_l incl_app_bw_r incl_flat_map_strong incl_map incl_app incl_appl incl_appr incl_tl incl_cons Permutation_incl Permutation_in Permutation_sym : incl.

Lemma choose_any_n_mono {A} n (xs ys : list A) :
  incl xs ys ->
  incl (choose_any_n n xs) (choose_any_n n ys).
Proof. induction n; simpl; auto with incl. Qed.
Hint Resolve choose_any_n_mono : incl.
