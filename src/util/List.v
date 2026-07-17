From Stdlib Require Import Lists.List Permutation Bool Arith.PeanoNat Morphisms RelationClasses Classical_Prop.
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

Lemma perm_recv {X : Type} (A ms1 : list X) (m : X) (ms2 : list X) :
  Permutation (A ++ ms1 ++ m :: ms2) (m :: A ++ ms1 ++ ms2).
Proof.
  rewrite (app_assoc A ms1 (m :: ms2)), (app_assoc A ms1 ms2).
  symmetry. apply Permutation_middle.
Qed.

Lemma perm_recv_l {X : Type} (A ms1 ms2 s : list X) (m : X) :
  Permutation (A ++ ms1 ++ m :: ms2) s -> Permutation (m :: A ++ ms1 ++ ms2) s.
Proof. intros H. transitivity (A ++ ms1 ++ m :: ms2); [ symmetry; apply perm_recv | exact H ]. Qed.

Lemma perm_send {X : Type} (a b s t : list X) (d : X) :
  Permutation (a ++ b) (s ++ t) -> Permutation (a ++ d :: b) (s ++ t ++ [d]).
Proof.
  intros H. transitivity (d :: a ++ b); [ symmetry; apply Permutation_middle | ].
  transitivity ((a ++ b) ++ [d]); [ apply Permutation_cons_append | ].
  transitivity ((s ++ t) ++ [d]); [ apply Permutation_app_tail; exact H | ].
  rewrite <- app_assoc. apply Permutation_refl.
Qed.

Lemma perm_nil_r {X : Type} (l : list X) : Permutation (l ++ []) l.
Proof. rewrite app_nil_r. apply Permutation_refl. Qed.

Lemma Permutation_concat {A} (l l' : list (list A)) :
  Permutation l l' -> Permutation (concat l) (concat l').
Proof.
  induction 1; cbn [concat].
  - reflexivity.
  - apply Permutation_app_head; assumption.
  - rewrite !app_assoc. apply Permutation_app_tail, Permutation_app_comm.
  - eapply Permutation_trans; eassumption.
Qed.

Create HintDb perm.
Hint Resolve perm_ins perm_recv perm_recv_l perm_send perm_nil_r Permutation_concat
     Permutation_app_head Permutation_app_comm Permutation_refl : perm.

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

Lemma impl_in_map {A B} (f : A -> B) x l y :
  In x l -> f x = y -> In y (map f l).
Proof. intros. apply in_map_iff. eauto. Qed.

Lemma impl_in_filter {A} (f : A -> bool) x l :
  In x l -> f x = true -> In x (filter f l).
Proof. intros. apply filter_In. auto. Qed.

Lemma Forall2_map_map {A B D} (R : B -> D -> Prop) (f : A -> B) (g : A -> D) (l : list A) :
  Forall (fun x => R (f x) (g x)) l -> Forall2 R (map f l) (map g l).
Proof.
  induction l as [|a l IH]; cbn [map]; intros HF; [constructor|].
  pose proof (Forall_inv HF) as Hhd. pose proof (Forall_inv_tail HF) as Htl.
  constructor; [ exact Hhd | exact (IH Htl) ].
Qed.

Lemma Forall2_map_map_inv {A B D} (R : B -> D -> Prop) (f : A -> B) (g : A -> D) (l : list A) :
  Forall2 R (map f l) (map g l) -> Forall (fun x => R (f x) (g x)) l.
Proof.
  induction l as [|a l IH]; cbn [map]; intros HF; [constructor|].
  inversion HF as [| ? ? ? ? Hhd Htl]; subst.
  constructor; [ exact Hhd | exact (IH Htl) ].
Qed.

Lemma incl_def {A} (x : A) (xs ys : list A) :
  incl xs ys -> In x xs -> In x ys.
Proof. auto. Qed.

(* The stdlib [Forall2_impl] takes the implication before the [Forall2]
   premise, so [eauto] tries to discharge the implication with the source
   relation still an unconstrained evar and gives up.  Putting the [Forall2]
   first lets [eauto] pin the relation from that hypothesis. *)
Lemma Forall2_impl {A B} (R1 R2 : A -> B -> Prop) x y :
  Forall2 R1 x y -> (forall a b, R1 a b -> R2 a b) -> Forall2 R2 x y.
Proof. intros. eapply Forall2_impl; eauto. Qed.

(* [eauto using Forall2_impl] cannot lift the [Forall2] here: the per-element
   step [In a l1 -> In a l2] needs [incl l1 l2], so the source relation stays an
   evar while the implication is attempted first.  The [_impl] with the [Forall2]
   premise first works. *)
Goal forall {A} (x y : list A) P1 P2,
    (P1 -> P2) -> Forall2 (fun _ _ => P1) x y -> Forall2 (fun a _ => P2) x y.
Proof. intros. Fail solve [eauto using Lists.List.Forall2_impl]. eauto using Forall2_impl. Qed.

(* Same story for the [In]-aware [Forall2_impl_strong] from coqutil: the
   [Forall2] premise goes first so [eauto] can pin the source relation. *)
Lemma Forall2_impl_strong {A B} (R1 R2 : A -> B -> Prop) xs ys :
  Forall2 R1 xs ys ->
  (forall x y, R1 x y -> In x xs -> In y ys -> R2 x y) ->
  Forall2 R2 xs ys.
Proof. intros. eapply Forall2_impl_strong; eauto. Qed.

Goal forall {A} (xs ys : list A) P1 P2,
    (P1 -> P2) -> Forall2 (fun _ _ => P1) xs ys -> Forall2 (fun a _ => P2) xs ys.
Proof.
  intros. Fail solve [eauto using coqutil.Datatypes.List.Forall2_impl_strong].
  eauto using Forall2_impl_strong.
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

Lemma list_sum_cons x l : list_sum (x :: l) = x + list_sum l.
Proof. reflexivity. Qed.

Lemma in_le_list_sum x l :
  In x l -> x <= list_sum l.
Proof. induction l as [|a l IH]; simpl; [contradiction | intros [->|Hin]; [lia | specialize (IH Hin); lia]]. Qed.

Lemma list_sum_zero l :
  Forall (eq 0) l -> list_sum l = 0.
Proof. induction 1; simpl; [reflexivity | subst; assumption]. Qed.

Lemma Permutation_list_sum l1 l2 : Permutation l1 l2 -> list_sum l1 = list_sum l2.
Proof. induction 1; rewrite ?list_sum_cons; lia. Qed.

Lemma Forall2_In_l {A B} (R : A -> B -> Prop) xs ys x :
  Forall2 R xs ys -> In x xs -> exists y, In (x, y) (combine xs ys) /\ R x y.
Proof.
  induction 1 as [| a b xs' ys' Hab HF IH]; [ contradiction | ].
  intros [-> | Hin].
  - exists b. split; [ left; reflexivity | exact Hab ].
  - destruct (IH Hin) as (y & Hcomb & Hy). exists y. split; [ right; exact Hcomb | exact Hy ].
Qed.

Lemma map_fst_combine {A B} (a : list A) (b : list B) :
  length a = length b -> map fst (combine a b) = a.
Proof.
  revert b. induction a as [| x a' IH]; intros [| y b'] Hlen; try discriminate; [ reflexivity | ].
  cbn [combine map fst]. f_equal. apply IH. cbn in Hlen. congruence.
Qed.

Section SenderCount.
  Context {K : Type} {eqbK : Eqb K} {eqbK_ok : Eqb_ok eqbK}.

  Lemma list_sum_map_filter_zero (f : K -> nat) (g : K -> bool) (l : list K) :
    (forall x, In x l -> g x = false -> f x = 0) ->
    list_sum (map f l) = list_sum (map f (filter g l)).
  Proof.
    induction l as [| a l' IH]; [ reflexivity | ]. intros Hz. cbn [filter].
    destruct (g a) eqn:Ega.
    - cbn [map]. rewrite !list_sum_cons. f_equal. apply IH. intros x Hx. apply Hz. right. exact Hx.
    - cbn [map]. rewrite list_sum_cons, (Hz a (or_introl eq_refl) Ega). cbn [Nat.add].
      apply IH. intros x Hx. apply Hz. right. exact Hx.
  Qed.

  Lemma Permutation_filter_mem (sub sup : list K) :
    NoDup sub -> NoDup sup -> incl sub sup ->
    Permutation (filter (fun k => existsb (eqb k) sub) sup) sub.
  Proof.
    intros Hsub Hsup Hincl. apply NoDup_Permutation.
    - apply NoDup_filter. exact Hsup.
    - exact Hsub.
    - intros x. rewrite filter_In. split.
      + intros [_ Hex]. apply existsb_exists in Hex. destruct Hex as (y & Hy & Heq).
        assert (x = y) by (destr (eqb x y); congruence). subst x. exact Hy.
      + intros Hx. split; [ apply Hincl; exact Hx | ].
        apply existsb_exists. exists x. split; [ exact Hx | ]. destr (eqb x x); congruence.
  Qed.

  Lemma list_sum_map_over_subset (f : K -> nat) (sub sup : list K) :
    NoDup sub -> NoDup sup -> incl sub sup -> (forall k, ~ In k sub -> f k = 0) ->
    list_sum (map f sup) = list_sum (map f sub).
  Proof.
    intros Hsub Hsup Hincl Hz.
    rewrite (list_sum_map_filter_zero f (fun k => existsb (eqb k) sub) sup).
    - apply Permutation_list_sum, Permutation_map, Permutation_filter_mem; assumption.
    - intros x _ Hg. apply Hz. intros Hin.
      assert (existsb (eqb x) sub = true)
        by (apply existsb_exists; exists x; split; [ exact Hin | destr (eqb x x); congruence ]).
      congruence.
  Qed.
End SenderCount.

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

Lemma option_map_option_map X Y Z (f : X -> Y) (g : Y -> Z) x :
  option_map g (option_map f x) = option_map (fun x => g (f x)) x.
Proof. destruct x; reflexivity. Qed.

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

  Lemma Forall3_ignore1:
    forall xs ys zs,
      Forall3 xs ys zs ->
      Forall2 (fun y z => exists x, R x y z) ys zs.
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
    eapply Forall2_impl; [ eassumption | ]. simpl. intros. fwd. eauto.
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
    eapply Forall2_impl; [ eassumption | ]. simpl. intros. fwd. eauto.
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

Lemma Forall3_Forall2_conj {A B C} (R1 : A -> B -> C -> Prop) (R2 : B -> C -> Prop) xs ys zs :
  Forall3 R1 xs ys zs -> Forall2 R2 ys zs ->
  Forall3 (fun x y z => R1 x y z /\ R2 y z) xs ys zs.
Proof.
  induction 1 as [| x y z xs' ys' zs' HR HF IH]; intros H2; [ constructor | ].
  inversion H2 as [| ? ? ? ? HR2 HF2]; subst.
  constructor; [ split; assumption | apply IH; assumption ].
Qed.

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

  Lemma Existsn_total l : exists n, Existsn n l.
  Proof.
    induction l as [| x l IH].
    - exists 0. constructor.
    - destruct IH as (n & Hn). destruct (classic (P x)).
      + exists (S n). apply Existsn_yes; assumption.
      + exists n. apply Existsn_no; assumption.
  Qed.

  Inductive Existsn_ge : nat -> list T -> Prop :=
  | Eg_zero l : Existsn_ge 0 l
  | Eg_skip x k l : Existsn_ge k l -> Existsn_ge k (x :: l)
  | Eg_take x k l : P x -> Existsn_ge k l -> Existsn_ge (S k) (x :: l).

  Inductive Existsn_le : nat -> list T -> Prop :=
  | El_nil k : Existsn_le k []
  | El_skip x k l : ~ P x -> Existsn_le k l -> Existsn_le k (x :: l)
  | El_take x k l : Existsn_le k l -> Existsn_le (S k) (x :: l).

  Hint Constructors Existsn_ge Existsn_le : core.

  Lemma Existsn_ge_mono_count j l : Existsn_ge j l -> forall i, i <= j -> Existsn_ge i l.
  Proof.
    induction 1 as [l | x k l Hk IH | x k l Hpx Hk IH]; intros i Hi.
    - assert (i = 0) as -> by lia. apply Eg_zero.
    - apply Eg_skip. apply IH. exact Hi.
    - destruct i as [|i']; [apply Eg_zero | apply Eg_take; [exact Hpx | apply IH; lia]].
  Qed.

  Lemma Existsn_le_mono_count i l : Existsn_le i l -> forall j, i <= j -> Existsn_le j l.
  Proof.
    induction 1 as [i | x i l Hnpx Hle IH | x i l Hle IH]; intros j Hj.
    - apply El_nil.
    - apply El_skip; [exact Hnpx | apply IH; exact Hj].
    - destruct j as [|j']; [lia | apply El_take; apply IH; lia].
  Qed.

  Lemma Existsn_ge_le_bound a b l : Existsn_ge a l -> Existsn_le b l -> a <= b.
  Proof.
    intros Hge. revert b.
    induction Hge as [l | x a l Hk IH | x a l Hpx Hk IH]; intros b Hle.
    - lia.
    - inversion Hle as [| x' b' l' Hnpx Hle' | x' b' l' Hle']; subst.
      + apply IH; exact Hle'.
      + specialize (IH b' Hle'). lia.
    - inversion Hle as [| x' b' l' Hnpx Hle' | x' b' l' Hle']; subst.
      + exfalso. apply Hnpx. exact Hpx.
      + specialize (IH b' Hle'). lia.
  Qed.

  Lemma Existsn_ge_of_Existsn n l : Existsn n l -> forall k, k <= n -> Existsn_ge k l.
  Proof.
    induction 1 as [| x n l Hnpx Hn IH | x n l Hpx Hn IH]; intros k Hk.
    - assert (k = 0) as -> by lia. apply Eg_zero.
    - apply Eg_skip. apply IH. exact Hk.
    - destruct k as [|k']; [apply Eg_zero | apply Eg_take; [exact Hpx | apply IH; lia]].
  Qed.

  Lemma Existsn_le_of_Existsn n l : Existsn n l -> forall k, n <= k -> Existsn_le k l.
  Proof.
    induction 1 as [| x n l Hnpx Hn IH | x n l Hpx Hn IH]; intros k Hk.
    - apply El_nil.
    - apply El_skip; [exact Hnpx | apply IH; exact Hk].
    - destruct k as [|k']; [lia | apply El_take; apply IH; lia].
  Qed.

  Lemma Existsn_ge_exact_bound k n l : Existsn_ge k l -> Existsn n l -> k <= n.
  Proof.
    intros Hge Hn.
    exact (Existsn_ge_le_bound k n l Hge (Existsn_le_of_Existsn n l Hn n (le_n n))).
  Qed.

  Lemma Existsn_le_exact_bound n k l : Existsn_le k l -> Existsn n l -> n <= k.
  Proof.
    intros Hle Hn.
    exact (Existsn_ge_le_bound n k l (Existsn_ge_of_Existsn n l Hn n (le_n n)) Hle).
  Qed.

  Lemma Existsn_le_0_Forall_not l : Forall (fun x => ~ P x) l -> Existsn_le 0 l.
  Proof. induction 1; [ apply El_nil | apply El_skip; assumption ]. Qed.

  Lemma Existsn_le_app a b l1 l2 :
    Existsn_le a l1 -> Existsn_le b l2 -> Existsn_le (a + b) (l1 ++ l2).
  Proof.
    intros H1 H2. induction H1; simpl.
    - eapply Existsn_le_mono_count; [ exact H2 | lia ].
    - apply El_skip; assumption.
    - apply El_take; assumption.
  Qed.

  Lemma Existsn_ge_app_l k l1 l2 : Existsn_ge k l1 -> Existsn_ge k (l1 ++ l2).
  Proof. induction 1; simpl; auto. Qed.

  Lemma Existsn_ge_app_r k l1 l2 : Existsn_ge k l2 -> Existsn_ge k (l1 ++ l2).
  Proof. intros H. induction l1 as [|x l1 IH]; simpl; [ exact H | apply Eg_skip; exact IH ]. Qed.

  Lemma Existsn_ge_app a b l1 l2 :
    Existsn_ge a l1 -> Existsn_ge b l2 -> Existsn_ge (a + b) (l1 ++ l2).
  Proof. intros H1 H2. induction H1; simpl; auto using Existsn_ge_app_r. Qed.

  Lemma Existsn_ge_1 x l : In x l -> P x -> Existsn_ge 1 l.
  Proof.
    intros Hin Hpx. apply in_split in Hin. destruct Hin as (l1 & l2 & ->).
    apply Existsn_ge_app_r. apply Eg_take; [ exact Hpx | apply Eg_zero ].
  Qed.

  Lemma Existsn_ge_app_inv k l1 l2 :
    Existsn_ge k (l1 ++ l2) ->
    exists k1 k2, k = k1 + k2 /\ Existsn_ge k1 l1 /\ Existsn_ge k2 l2.
  Proof.
    revert k. induction l1 as [|x l1 IH]; intros k H; simpl in H.
    - exists 0, k. split; [ reflexivity | split; [ apply Eg_zero | exact H ] ].
    - invert H.
      + exists 0, 0. split; [ reflexivity | split; apply Eg_zero ].
      + match goal with Hh : Existsn_ge _ (l1 ++ l2) |- _ =>
          apply IH in Hh; destruct Hh as (k1 & k2 & -> & H1 & H2) end.
        exists k1, k2. split; [ reflexivity | split; [ apply Eg_skip; exact H1 | exact H2 ] ].
      + match goal with Hh : Existsn_ge _ (l1 ++ l2) |- _ =>
          apply IH in Hh; destruct Hh as (k1 & k2 & -> & H1 & H2) end.
        exists (S k1), k2. split; [ reflexivity | split; [ apply Eg_take; [ assumption | exact H1 ] | exact H2 ] ].
  Qed.

  Lemma Existsn_ge_perm k l1 l2 : Permutation l1 l2 -> Existsn_ge k l1 -> Existsn_ge k l2.
  Proof.
    intros Hperm. revert k. induction Hperm; intros k H.
    - exact H.
    - invert H; eauto.
    - invert H; try (match goal with Hi : Existsn_ge _ (_ :: _) |- _ => invert Hi end); eauto.
    - eauto.
  Qed.

  Lemma Existsn_le_app_l k l1 l2 : Existsn_le k (l1 ++ l2) -> Existsn_le k l1.
  Proof.
    revert k. induction l1 as [|x l1 IH]; intros k H; [ apply El_nil | ].
    simpl in H. invert H.
    - apply El_skip; [ assumption | apply IH; assumption ].
    - apply El_take; apply IH; assumption.
  Qed.

  Lemma Existsn_le_perm k l1 l2 : Permutation l1 l2 -> Existsn_le k l1 -> Existsn_le k l2.
  Proof.
    intros Hperm. revert k. induction Hperm; intros k H.
    - exact H.
    - invert H; eauto.
    - invert H; try (match goal with Hi : Existsn_le _ (_ :: _) |- _ => invert Hi end); eauto.
    - eauto.
  Qed.

  Lemma Existsn_ge_concat mss es :
    Forall2 (fun ms e => Existsn_ge e ms) mss es -> Existsn_ge (list_sum es) (concat mss).
  Proof.
    induction 1 as [| ms e mss' es' Hge HF IH]; [ apply Eg_zero | ].
    cbn [concat]. rewrite list_sum_cons. apply Existsn_ge_app; assumption.
  Qed.

  Lemma Existsn_le_concat mss es :
    Forall2 (fun ms e => Existsn_le e ms) mss es -> Existsn_le (list_sum es) (concat mss).
  Proof.
    induction 1 as [| ms e mss' es' Hle HF IH]; [ apply El_nil | ].
    cbn [concat]. rewrite list_sum_cons. apply Existsn_le_app; assumption.
  Qed.

  Lemma Existsn_squeeze mss es :
    Existsn_ge (list_sum es) (concat mss) ->
    Forall2 (fun ms e => Existsn_le e ms) mss es ->
    Forall2 (fun ms e => Existsn_ge e ms) mss es.
  Proof.
    intros Hge Hle. revert Hge.
    induction Hle as [| ms e mss' es' Hle_head HF IH]; intros Hge; [ constructor | ].
    cbn [concat] in Hge. rewrite list_sum_cons in Hge.
    apply Existsn_ge_app_inv in Hge. destruct Hge as (a & b & Hsum & Hge_a & Hge_b).
    pose proof (Existsn_ge_le_bound _ _ _ Hge_a Hle_head) as Ha.
    pose proof (Existsn_ge_le_bound _ _ _ Hge_b (Existsn_le_concat _ _ HF)) as Hb.
    constructor.
    - eapply Existsn_ge_mono_count; [ exact Hge_a | lia ].
    - apply IH. eapply Existsn_ge_mono_count; [ exact Hge_b | lia ].
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
    eapply Forall2_impl_strong; [apply Forall2_true; auto|].
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

  Lemma incl_app_split (l k1 k2 : list A) :
    incl l (k1 ++ k2) ->
    exists la lb, Permutation l (la ++ lb) /\ incl la k1 /\ incl lb k2.
  Proof.
    induction l as [| x xs IH]; intros Hincl.
    - exists [], []. split; [ reflexivity | split; intros z Hz; destruct Hz ].
    - assert (Hx : In x (k1 ++ k2)) by (apply Hincl; left; reflexivity).
      assert (Hxs : incl xs (k1 ++ k2)) by (intros z Hz; apply Hincl; right; exact Hz).
      destruct (IH Hxs) as (la & lb & Hperm & Hla & Hlb).
      apply in_app_or in Hx. destruct Hx as [Hx | Hx].
      + exists (x :: la), lb. split; [ apply perm_skip; exact Hperm | ].
        split; [ apply incl_cons; [ exact Hx | exact Hla ] | exact Hlb ].
      + exists la, (x :: lb). split; [ apply Permutation_cons_app; exact Hperm | ].
        split; [ exact Hla | apply incl_cons; [ exact Hx | exact Hlb ] ].
  Qed.

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

  Definition multiset_union (l1 l2 l : list A) : Prop :=
    Permutation l (l1 ++ l2).

  Definition disj_union (l1 l2 l : list A) : Prop :=
    multiset_union l1 l2 l /\ (forall x, In x l1 -> ~ In x l2).

  Lemma submultiset_refl l : submultiset l l.
  Proof. exists []. rewrite app_nil_r. apply Permutation_refl. Qed.

  Lemma submultiset_app_mid l1 l2 l3 : submultiset (l1 ++ l3) (l1 ++ l2 ++ l3).
  Proof.
    exists l2. rewrite <- (app_assoc l1 l3 l2).
    apply Permutation_app_head, Permutation_app_comm.
  Qed.

  Lemma submultiset_perm l1 l2 : Permutation l1 l2 -> submultiset l1 l2.
  Proof. intros H. exists []. rewrite app_nil_r. symmetry. exact H. Qed.

  Lemma submultiset_trans l1 l2 l3 :
    submultiset l1 l2 -> submultiset l2 l3 -> submultiset l1 l3.
  Proof.
    intros (r1 & H1) (r2 & H2). exists (r1 ++ r2). rewrite app_assoc.
    transitivity (l2 ++ r2); [exact H2 | apply Permutation_app_tail; exact H1].
  Qed.

  Lemma submultiset_app_r l1 l2 : submultiset l1 (l1 ++ l2).
  Proof. exists l2. apply Permutation_refl. Qed.

  Lemma submultiset_cons a l : submultiset l (a :: l).
  Proof. exists [a]. apply Permutation_cons_append. Qed.

  Lemma submultiset_incl l1 l2 : submultiset l1 l2 -> incl l1 l2.
  Proof.
    intros (rest & H). apply Permutation_sym, Permutation_incl in H.
    intros x Hx. apply H, in_or_app. left. exact Hx.
  Qed.

  Lemma Existsn_ge_submultiset (P : A -> Prop) k l1 l2 :
    Existsn_ge P k l1 -> submultiset l1 l2 -> Existsn_ge P k l2.
  Proof.
    intros H (rest & Hperm).
    eapply Existsn_ge_perm; [ apply Permutation_sym; exact Hperm | ].
    apply Existsn_ge_app_l. exact H.
  Qed.

  Lemma Existsn_le_submultiset (P : A -> Prop) k l1 l2 :
    Existsn_le P k l2 -> submultiset l1 l2 -> Existsn_le P k l1.
  Proof.
    intros H (rest & Hperm).
    apply Existsn_le_app_l with (l2 := rest).
    eapply Existsn_le_perm; [ exact Hperm | exact H ].
  Qed.

  Lemma submultiset_nil_l l : submultiset [] l.
  Proof. exists l. reflexivity. Qed.

  Lemma submultiset_perm_r l m m' : Permutation m m' -> submultiset l m -> submultiset l m'.
  Proof. intros HP (rest & H). exists rest. rewrite <- HP. exact H. Qed.

  Lemma submultiset_app_head m l l' : submultiset l l' -> submultiset (m ++ l) (m ++ l').
  Proof. intros (rest & Hp). exists rest. rewrite <- app_assoc. apply Permutation_app_head. exact Hp. Qed.

  Lemma submultiset_app_inv_l m l l' : submultiset (m ++ l) (m ++ l') -> submultiset l l'.
  Proof.
    intros (rest & Hp). exists rest. rewrite <- app_assoc in Hp.
    apply Permutation_app_inv_l in Hp. exact Hp.
  Qed.

  Lemma submultiset_cons_mono a l l' : submultiset l l' -> submultiset (a :: l) (a :: l').
  Proof. intros (rest & Hp). exists rest. apply perm_skip. exact Hp. Qed.

  Lemma submultiset_cons_inv a l l' : submultiset (a :: l) (a :: l') -> submultiset l l'.
  Proof.
    intros (rest & Hp). exists rest. cbn [app] in Hp. apply Permutation_cons_inv in Hp. exact Hp.
  Qed.

  Local Ltac pmid :=
    solve [ apply Permutation_middle
          | symmetry; apply Permutation_middle
          | rewrite <- !app_assoc; apply Permutation_middle
          | rewrite <- !app_assoc; symmetry; apply Permutation_middle
          | rewrite !app_assoc; apply Permutation_middle
          | rewrite !app_assoc; symmetry; apply Permutation_middle ].

  Lemma submultiset_diff owed s Q :
    submultiset owed (s ++ Q) ->
    exists owed', submultiset owed' Q /\ submultiset owed (s ++ owed') /\ length owed' <= length owed.
  Proof.
    revert s Q. induction owed as [| x owed IH]; intros s Q Hsub.
    - exists []. split;
        [ apply submultiset_nil_l | split; [ apply submultiset_nil_l | reflexivity ] ].
    - assert (Hin : In x (s ++ Q))
        by (eapply submultiset_incl; [ exact Hsub | left; reflexivity ]).
      apply in_app_or in Hin. destruct Hin as [Hxs | HxQ].
      + apply in_split in Hxs. destruct Hxs as (s1 & s2 & ->).
        assert (Hsub' : submultiset owed ((s1 ++ s2) ++ Q)).
        { apply submultiset_cons_inv with (a := x).
          eapply submultiset_perm_r; [ | exact Hsub ]. pmid. }
        destruct (IH (s1 ++ s2) Q Hsub') as (owed' & HQ & Hos & Hlen).
        exists owed'. split; [ exact HQ | split ].
        * eapply submultiset_perm_r; [ | apply submultiset_cons_mono; exact Hos ]. pmid.
        * simpl. apply le_S. exact Hlen.
      + apply in_split in HxQ. destruct HxQ as (Q1 & Q2 & ->).
        assert (Hsub' : submultiset owed (s ++ (Q1 ++ Q2))).
        { apply submultiset_cons_inv with (a := x).
          eapply submultiset_perm_r; [ | exact Hsub ]. pmid. }
        destruct (IH s (Q1 ++ Q2) Hsub') as (owed' & HQ & Hos & Hlen).
        exists (x :: owed'). split; [ | split ].
        * eapply submultiset_perm_r; [ | apply submultiset_cons_mono; exact HQ ]. pmid.
        * eapply submultiset_perm_r; [ | apply submultiset_cons_mono; exact Hos ]. pmid.
        * simpl. apply le_n_S. exact Hlen.
  Qed.

  Lemma submultiset_perm_l l l' m : Permutation l l' -> submultiset l m -> submultiset l' m.
  Proof.
    intros HP (rest & H). exists rest.
    eapply perm_trans; [ exact H | apply Permutation_app_tail; exact HP ].
  Qed.

  Lemma submultiset_absorb base owed T Q a :
    submultiset (base ++ a :: owed) (T ++ Q) ->
    submultiset (base ++ [a]) T ->
    exists owed', submultiset owed' Q /\
                  submultiset (base ++ a :: owed) (T ++ owed') /\ length owed' <= length owed.
  Proof.
    intros H1 (s & HT).
    replace (base ++ a :: owed) with ((base ++ [a]) ++ owed) in *
      by (rewrite <- app_assoc; reflexivity).
    assert (Hos : submultiset owed (s ++ Q)).
    { apply (submultiset_app_inv_l (base ++ [a])).
      eapply submultiset_perm_r; [ | exact H1 ].
      eapply perm_trans; [ apply Permutation_app_tail; exact HT | ].
      rewrite <- !app_assoc. apply Permutation_refl. }
    destruct (submultiset_diff owed s Q Hos) as (owed' & HQ & Hos' & Hlen).
    exists owed'. split; [ exact HQ | split; [ | exact Hlen ] ].
    eapply submultiset_perm_r; [ | apply (submultiset_app_head (base ++ [a])); exact Hos' ].
    eapply perm_trans; [ | apply Permutation_app_tail; apply Permutation_sym; exact HT ].
    rewrite <- !app_assoc. apply Permutation_refl.
  Qed.

  Lemma submultiset_cons_of_not_in a X T Q :
    submultiset X T ->
    submultiset (X ++ [a]) (T ++ Q) ->
    ~ In a Q ->
    submultiset (X ++ [a]) T.
  Proof.
    intros (s & HT) H1 HnQ.
    assert (Hsub_a : submultiset [a] (s ++ Q)).
    { apply (submultiset_app_inv_l X). eapply submultiset_perm_r; [ | exact H1 ].
      eapply perm_trans; [ apply Permutation_app_tail; exact HT | ].
      rewrite <- app_assoc. apply Permutation_refl. }
    assert (Ha : In a (s ++ Q))
      by (eapply submultiset_incl; [ exact Hsub_a | left; reflexivity ]).
    apply in_app_or in Ha. destruct Ha as [Has | HaQ]; [ | contradiction ].
    apply in_split in Has. destruct Has as (s1 & s2 & ->).
    eapply submultiset_perm_r; [ apply Permutation_sym; exact HT | ].
    apply submultiset_app_head.
    exists (s1 ++ s2). cbn [app]. symmetry. apply Permutation_middle.
  Qed.

  Definition multiset_monotone_dec (P : list A -> Prop) :=
    forall l1 l2, P l2 -> submultiset l1 l2 -> P l1.

  Definition multiset_monotone_inc (P : list A -> Prop) :=
    forall l1 l2, P l1 -> submultiset l1 l2 -> P l2.

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

Create HintDb submultiset.
Hint Resolve submultiset_perm submultiset_refl submultiset_app_mid submultiset_app_r
     submultiset_cons submultiset_cons_mono submultiset_app_head submultiset_nil_l : submultiset.

Definition consistent_monotone {message} (consistent : list message -> list message -> Prop)
    (allowed : list message -> Prop) :=
  forall c l1 l2,
    allowed l1 ->
    allowed l2 ->
    submultiset l1 l2 ->
    consistent c l1 ->
    consistent c l2.

Lemma consistent_perm {A} (consistent : list A -> list A -> Prop) (allowed : list A -> Prop) :
  consistent_monotone consistent allowed ->
  forall c l1 l2,
    allowed l1 -> allowed l2 -> Permutation l1 l2 ->
    consistent c l1 -> consistent c l2.
Proof.
  intros Hcm c l1 l2 Hal1 Hal2 Hperm Hc.
  exact (Hcm c l1 l2 Hal1 Hal2 (submultiset_perm _ _ Hperm) Hc).
Qed.

Section incl_mod.
  Context {message : Type}.
  Context (equiv : message -> message -> Prop).
  Context {equiv_equiv : Equivalence equiv}.

  Definition incl_mod l1 l2 :=
    forall a,
      In a l1 ->
      exists b,
        In b l2 /\ equiv a b.

  Lemma incl_mod_refl l : incl_mod l l.
  Proof. intros a Ha. eexists. split; [|reflexivity]. assumption. Qed.

  Lemma incl_mod_of_incl l1 l2 : incl l1 l2 -> incl_mod l1 l2.
  Proof.
    destruct equiv_equiv as [Href _ _].
    intros Hincl a Ha. exists a. split; [apply Hincl, Ha | apply Href].
  Qed.

  Lemma incl_mod_trans l1 l2 l3 :
    incl_mod l1 l2 -> incl_mod l2 l3 -> incl_mod l1 l3.
  Proof.
    destruct equiv_equiv as [_ _ Htrans].
    intros H12 H23 a Ha.
    destruct (H12 a Ha) as (b & Hb & Hab).
    destruct (H23 b Hb) as (c & Hc & Hbc).
    exists c. split; [exact Hc | eapply Htrans; eassumption].
  Qed.

  Lemma incl_mod_of_submultiset l1 l2 : submultiset l1 l2 -> incl_mod l1 l2.
  Proof. intros H. apply incl_mod_of_incl, submultiset_incl, H. Qed.

  Lemma incl_mod_app l1 l2 l3 :
    incl_mod l1 l3 -> incl_mod l2 l3 -> incl_mod (l1 ++ l2) l3.
  Proof.
    intros H1 H2 a Ha. apply in_app_iff in Ha. destruct Ha; [apply H1 | apply H2]; assumption.
  Qed.

  Lemma incl_mod_insert a b c d :
    incl_mod (a ++ b) d -> incl_mod c d -> incl_mod (a ++ c ++ b) d.
  Proof.
    intros Hab Hc x Hx.
    apply in_app_or in Hx. destruct Hx as [Hx | Hx];
      [ apply Hab, in_or_app; left; exact Hx | ].
    apply in_app_or in Hx. destruct Hx as [Hx | Hx];
      [ apply Hc; exact Hx | apply Hab, in_or_app; right; exact Hx ].
  Qed.

  Lemma incl_mod_perm_l l1 l1' l2 :
    Permutation l1 l1' -> incl_mod l1 l2 -> incl_mod l1' l2.
  Proof.
    intros Hp H x Hx. apply H. eapply Permutation_in; [ apply Permutation_sym; exact Hp | exact Hx ].
  Qed.

  Lemma incl_mod_app_r l1 l2 l3 :
    incl_mod l1 l2 -> incl_mod l1 (l2 ++ l3).
  Proof.
    intros H a Ha. destruct (H a Ha) as (b & Hb & Hab).
    exists b. split; [apply in_or_app; left; exact Hb | exact Hab].
  Qed.

  Lemma incl_mod_Forall2 l1 l2 a :
    incl_mod l1 l2 -> incl a l1 ->
    exists b, incl b l2 /\ Forall2 equiv a b.
  Proof.
    intros Hw. induction a as [|x xs IH]; intros Hincl.
    - exists []. split; [ intros z Hz; inversion Hz | constructor ].
    - assert (In x l1) as Hx by (apply Hincl; left; reflexivity).
      destruct (Hw x Hx) as (y & Hy & Hxy).
      assert (incl xs l1) as Hxs by (intros z Hz; apply Hincl; right; exact Hz).
      destruct (IH Hxs) as (b & Hb & Hab).
      exists (y :: b). split.
      + intros z Hz. destruct Hz as [<- | Hz]; [ exact Hy | apply Hb; exact Hz ].
      + constructor; assumption.
  Qed.
End incl_mod.

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
