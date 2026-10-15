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

Lemma cardinality_at_least_impl {T} n (P Q : T -> Prop) :
  cardinality_at_least n P ->
  (forall x, P x -> Q x) ->
  cardinality_at_least n Q.
Proof.
  intros (l & Hl & Hn & HP) HPQ. exists l. split; [assumption|]. split; [assumption|].
  eapply Forall_impl; eassumption.
Qed.

Lemma cardinality_at_least_length {T} n (P : T -> Prop) l :
  cardinality_at_least n P ->
  (forall x, P x -> In x l) ->
  n <= length l.
Proof.
  intros (l' & Hl' & Hn & HP) Hcover. enough (length l' <= length l) by lia.
  apply NoDup_incl_length; [assumption|]. intros x Hx. apply Hcover.
  rewrite Forall_forall in HP. auto.
Qed.
