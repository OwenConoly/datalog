From Stdlib Require Import List Lia.

Definition cardinality_at_least {T} (n : nat) (P : T -> Prop) :=
  exists l, NoDup l /\ n <= length l /\ Forall P l.

Definition cardinality_at_most {T} (n : nat) (P : T -> Prop) :=
  exists l, length l <= n /\ forall x, P x -> In x l.

Definition cardinality_exactly {T} (n : nat) (P : T -> Prop) :=
  exists l, NoDup l /\ length l = n /\ forall x, P x <-> In x l.

Lemma cardinality_at_most_In {T} n (P : T -> Prop) l x :
  cardinality_at_most n P ->
  NoDup l ->
  n <= length l ->
  Forall P l ->
  P x ->
  In x l.
Proof.
  intros (l' & Hlen & Hcover) Hl Hn HP Hx.
  apply NoDup_length_incl with (l' := l'); [assumption | lia | | auto].
  intros y Hy. apply Hcover. rewrite Forall_forall in HP. auto.
Qed.
