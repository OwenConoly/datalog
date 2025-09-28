From coqutil Require Import Map.Interface Map.Properties.
From ATL Require Import FrapWithoutSets.


Section Map.
  Context {key value : Type} {mp : map.map key value} {mp_ok : map.ok mp}.
  Context {key_eqb : key -> key -> bool} {key_eqb_correct : forall x y : key, BoolSpec (x = y) (x <> y) (key_eqb x y)}.
  
Lemma extends_putmany_putmany (m1 m2 m : mp) :
  map.extends m1 m2 ->
  map.extends (map.putmany m1 m) (map.putmany m2 m).
Proof.
  intros H. cbv [map.extends]. intros x y Hx.
  edestruct map.putmany_spec as [H'|H'].
  - destruct H' as [v (H1&H2)]. rewrite Hx in H2. invert H2.
    apply map.get_putmany_right. assumption.
  - destruct H' as (H1&H2). rewrite map.get_putmany_left.
    + rewrite H2 in Hx. apply H. assumption.
    + assumption.
Qed.

Lemma extends_putmany_right (m1 m2 : mp) :
  map.extends (map.putmany m1 m2) m2.
Proof.
  intros k v H. edestruct map.putmany_spec as [H'|H'].
  - destruct H' as (v0&H1&H2). rewrite H in H1. invert H1. exact H2.
  - rewrite H in H'. destruct H' as [H' _]. discriminate H'.
Qed.

Lemma extends_putmany_left (m1 m2 : mp) :
  map.disjoint m1 m2 ->
  map.extends (map.putmany m1 m2) m1.
Proof.
  intros H1 k v H2. edestruct map.putmany_spec as [H'|H'].
  - destruct H' as (v0&H3&H4). exfalso. eauto.
  - destruct H' as (?&?). rewrite H0. assumption.
Qed.

Lemma get_of_list_None l k :
  ~In k (map fst l) ->
  map.get (map.of_list (map := mp) l) k = None.
Proof.
  intros H. induction l.
  - simpl. apply map.get_empty.
  - simpl. destruct a. simpl in H. rewrite map.get_put_diff by auto. auto.
Qed.
End Map.
