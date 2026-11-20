From coqutil Require Import sanity Map.Interface Map.SortedList Map.SortedListString.
From Stdlib Require Import Arith Lia List.
Import ListNotations.

Module strict_order_map.
  Section ___.
    Context {A : Type} {A_order : A -> A -> bool} {A_order_spec : SortedList.parameters.strict_order A_order}.

    Definition Build_parameters T := SortedList.parameters.Build_parameters A T A_order.

    #[export] Instance map T : map.map A T := SortedList.map (Build_parameters T) A_order_spec.

    #[export] Instance ok T : map.ok (map T).
    Proof. exact (@SortedList.map_ok (Build_parameters T) A_order_spec). Qed.
  End ___.
End strict_order_map. Export (hints) strict_order_map.

#[export] Instance Nat_strict_order : SortedList.parameters.strict_order Nat.ltb.
Proof. constructor; intros; rewrite ?Nat.ltb_lt, ?Nat.ltb_ge in *; lia. Qed.

#[export] Existing Instance SortedListString.string_strict_order.

Section ___.
Context {A : Type}.
Context {A_order : A -> A -> bool} {A_order_spec : SortedList.parameters.strict_order A_order}.

Fixpoint list_order (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | x1 :: xs1, x2 :: xs2 =>
      if A_order x1 x2 then true
      else if A_order x2 x1 then false
      else list_order xs1 xs2
  end.


Lemma list_order_irrefl: forall l, list_order l l = false.
Proof. induction l; auto. simpl. destruct A_order_spec.
       destruct (A_order a a) eqn:Haa; auto.
       pose proof (ltb_antirefl a). eauto.
Qed.

#[export] Instance list_strict_order: SortedList.parameters.strict_order list_order.
Proof.
  constructor.
  - intros l. apply (list_order_irrefl l).
  - intros l1. induction l1; intros l2 l3; intros.
    + destruct l2; destruct l3; auto.
    + destruct l2; destruct l3; destruct A_order_spec; auto; simpl in *; try discriminate.
      destruct (A_order a a1) eqn:Haa1; auto; try discriminate;
      destruct (A_order a1 a) eqn:Haa1'; auto; try discriminate;
      destruct (A_order a a0) eqn:Haa0; auto; try discriminate;
      destruct (A_order a0 a1) eqn:Ha0a1; auto; try discriminate.
      * pose proof (ltb_trans a a0 a1 Haa0 Ha0a1). rewrite H1 in Haa1. discriminate.
      * destruct (A_order a1 a0) eqn: Ha1a0; auto; try discriminate.
        pose proof (ltb_total a0 a1 Ha0a1 Ha1a0). subst. rewrite Haa0 in Haa1. discriminate.
      * destruct (A_order a0 a) eqn:Ha0a; auto.
        pose proof (ltb_total a a0 Haa0 Ha0a). subst. rewrite Ha0a1 in Haa1. discriminate.
      * destruct (A_order a0 a) eqn:Ha0a; auto.
        destruct (A_order a1 a0) eqn:Ha1a0; auto.
        pose proof (ltb_total a a0 Haa0 Ha0a). subst. pose proof (ltb_total a0 a1 Ha0a1 Ha1a0). subst.
        rewrite <- Haa1'. auto.
      * pose proof (ltb_trans a a0 a1 Haa0 Ha0a1). rewrite H1 in Haa1. discriminate.
      * destruct (A_order a1 a0) eqn: Ha1a0; auto; try discriminate.
        pose proof (ltb_total a0 a1 Ha0a1 Ha1a0). subst. rewrite Haa0 in Haa1. discriminate.
      * destruct (A_order a0 a) eqn:Ha0a; auto; try discriminate.
        pose proof (ltb_total a a1 Haa1 Haa1'). subst. rewrite Ha0a1 in Ha0a. discriminate.
      * destruct (A_order a0 a) eqn:Ha0a; auto; try discriminate.
        destruct (A_order a1 a0) eqn:Ha1a0; auto; try discriminate.
        eapply IHl1; eauto.
  - induction k1; destruct k2; simpl in *; intros; auto; try discriminate.
    destruct A_order_spec.
    destruct (A_order a a0) eqn:Haa0; auto; try discriminate;
    destruct (A_order a0 a) eqn:Haa0'; auto; try discriminate.
    pose proof (ltb_total a a0 Haa0 Haa0'). subst.
    specialize (IHk1 k2 H H0). subst. auto.
Qed.
End ___.

Section ___.
Context {p1 p2 : Type}.
Context {p1_order : p1 -> p1 -> bool} {p1_order_spec : SortedList.parameters.strict_order p1_order}.
Context {p2_order : p2 -> p2 -> bool} {p2_order_spec : SortedList.parameters.strict_order p2_order}.

Definition pair_order (x y : p1 * p2) : bool :=
  let (x1, x2) := x in
  let (y1, y2) := y in
  if p1_order x1 y1 then true else if p1_order y1 x1 then false else p2_order x2 y2.

Lemma pair_order_irrefl: forall x y, pair_order (x, y) (x, y) = false.
Proof. intros. unfold pair_order.
        destruct p1_order_spec. rewrite (ltb_antirefl x).
        destruct p2_order_spec. auto.
Qed.

#[export] Instance pair_strict_order: SortedList.parameters.strict_order pair_order.
Proof. constructor.
  - intros [x y]. apply (pair_order_irrefl x y).
  - intros [x1 x2] [y1 y2] [z1 z2] Hxy Hyz. unfold pair_order in *.
    destruct p1_order_spec. destruct p2_order_spec.
    destruct (p1_order x1 z1) eqn:Hx1z1; auto;
    destruct (p1_order z1 x1) eqn:Hz1x1; auto;
    destruct (p1_order x1 y1) eqn:Hx1y1; auto;
    destruct (p1_order y1 z1) eqn:Hy1z1; auto.
    + pose proof (ltb_trans x1 y1 z1 Hx1y1 Hy1z1). rewrite H in Hx1z1. discriminate.
    + destruct (p1_order z1 y1) eqn:Hz1y1; auto.
      pose proof (ltb_total y1 z1 Hy1z1 Hz1y1). subst. rewrite Hx1y1 in Hx1z1. discriminate.
    + destruct (p1_order y1 x1) eqn:Hy1x1; auto.
      pose proof (ltb_total x1 y1 Hx1y1 Hy1x1). subst. rewrite Hy1z1 in Hx1z1. discriminate.
    + destruct (p1_order y1 x1) eqn:Hy1x1; auto. destruct (p1_order z1 y1) eqn:Hz1y1; auto.
      pose proof (ltb_total x1 y1 Hx1y1 Hy1x1). subst. pose proof (ltb_total y1 z1 Hy1z1 Hz1y1). subst.
      rewrite Hx1z1 in Hz1x1. discriminate.
    + pose proof (ltb_total x1 z1 Hx1z1 Hz1x1). subst.
      pose proof (ltb_trans z1 y1 z1 Hx1y1 Hy1z1).
      pose proof (ltb_antirefl z1).
      rewrite H in H0. discriminate.
    + pose proof (ltb_total x1 z1 Hx1z1 Hz1x1). subst.
      destruct (p1_order z1 y1) eqn:Hz1y1; auto; try discriminate.
    + pose proof (ltb_total x1 z1 Hx1z1 Hz1x1). subst.
      rewrite Hy1z1 in Hxy. discriminate.
    + pose proof (ltb_total x1 z1 Hx1z1 Hz1x1). subst.
      rewrite Hy1z1 in Hxy.
      rewrite Hx1y1 in Hyz.
      eauto.
    - intros [x1 x2] [y1 y2] Hxy Hyz. unfold pair_order in *.
      destruct p1_order_spec. destruct p2_order_spec.
      destruct (p1_order x1 y1) eqn:Hx1y1; auto; try discriminate.
      destruct (p1_order y1 x1) eqn:Hy1x1; auto; try discriminate.
      pose proof (ltb_total x1 y1 Hx1y1 Hy1x1). subst.
      pose proof (ltb_total0 x2 y2 Hxy Hyz). subst. auto.
Qed.

End ___.

Section ___.
Context {A B : Type} (f : A -> B) (f_inj : forall x y, f x = f y -> x = y).
Context {B_order : B -> B -> bool} {B_order_spec : SortedList.parameters.strict_order B_order}.

Definition inj_order (x y : A) : bool := B_order (f x) (f y).

Lemma inj_strict_order : SortedList.parameters.strict_order inj_order.
Proof.
  destruct B_order_spec as [Hirr Htrans Htot]. constructor; unfold inj_order.
  - intros k. apply Hirr.
  - intros k1 k2 k3. apply Htrans.
  - intros k1 k2 H1 H2. apply f_inj, Htot; assumption.
Qed.

End ___.
