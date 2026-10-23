From Stdlib Require Import PeanoNat Peano_dec Lia List Finite.
From coqutil Require Import Eqb Tactics.
From Datalog Require Import Eqb Function.

Module fin.
  Section __.
    Context {n : nat}.
    Record fin := mk { val : nat; small : val < n }.

    Lemma ext (a b : fin) : val a = val b -> a = b.
    Proof.
      destruct a, b. simpl. intros. subst. f_equal. apply le_unique.
    Qed.

    #[export] Instance eqb : Eqb fin := fun a b => eqb (val a) (val b).

    #[export] Instance fin_eqb_ok : Eqb_ok eqb.
    Proof.
      intros a b. cbv [Eqb.eqb]. cbv [eqb]. destr (Eqb.eqb (val a) (val b)).
      - apply ext. assumption.
      - congruence.
    Qed.
  End __.
  Arguments fin : clear implicits.
  #[export] Typeclasses Opaque eqb.

  #[refine] Definition toS {n} (small : fin n) : fin (S n) :=
    {| val := small.(val) |}.
  Proof. abstract (destruct small; simpl; lia). Defined.

  (*i guess this is quadratic.  should i care?*)
  #[refine] Fixpoint all n : list (fin n) :=
    match n with
    | S n' => {| val := n' |} :: List.map toS (all n')
    | O => nil
    end.
  Proof. abstract lia. Defined.

  Lemma all_NoDup n : NoDup (all n).
  Proof.
    induction n; simpl; constructor.
    - rewrite in_map_iff. intros (x & Hx & _). apply (f_equal val) in Hx.
      destruct x. simpl in Hx. lia.
    - apply Injective_map_NoDup; [|assumption].
      intros x y H. apply ext. exact (f_equal val H).
  Qed.

  Lemma all_Full n : Full (all n).
  Proof.
    intros a. induction n.
    - destruct a. lia.
    - destruct a as [v Hv]. simpl. destruct (Nat.eq_dec v n).
      + left. apply ext. simpl. congruence.
      + right. apply in_map_iff. exists (mk (n := n) v ltac:(lia)). split.
        * apply ext. reflexivity.
        * apply IHn.
  Qed.

  Lemma all_Listing n : Listing (all n).
  Proof. split; [ apply all_NoDup | apply all_Full ]. Qed.

  Lemma Forall_all n (P : fin n -> Prop) : Forall P (all n) <-> forall x, P x.
  Proof.
    rewrite Forall_forall. split.
    - intros H x. apply H, all_Full.
    - auto.
  Qed.

  Lemma choice {B} n (P : fin n -> B -> Prop) :
    (forall x, exists y, P x y) ->
    exists f, forall x, P x (f x).
  Proof.
    intros H. destruct n as [|n].
    - exists (fun x => False_rect B (Nat.nlt_0_r _ (small x))).
      intros x. destruct (Nat.nlt_0_r _ (small x)).
    - destruct (H (mk (n := S n) 0 ltac:(lia))) as [y0 _].
      enough (Hl : forall l, exists f, forall x, In x l -> P x (f x)).
      { destruct (Hl (all (S n))) as [f Hf]. exists f. intros x. apply Hf, all_Full. }
      intros l. induction l as [|a l [f Hf]].
      + exists (fun _ => y0). intros _ [].
      + destruct (H a) as [ya Hya]. exists (fun_put f a ya). intros x Hx. cbv [fun_put].
        destr (Eqb.eqb x a); [ assumption | ].
        apply Hf. destruct Hx; [ congruence | assumption ].
  Qed.
End fin. Export (hints) fin. Abbreviation fin := fin.fin.
