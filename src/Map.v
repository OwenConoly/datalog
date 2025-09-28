From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics.
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

Lemma extends_trans (m1 m2 m3 : mp) :
  map.extends m1 m2 ->
  map.extends m2 m3 ->
  map.extends m1 m3.
Proof. cbv [map.extends]. auto. Qed.

Lemma extends_put (m : mp) k v :
  map.get m k = None ->
  map.extends (map.put m k v) m.
Proof. map_solver mp_ok. Qed.

Lemma putmany_None (m1 m2 : mp) k :
  map.get m1 k = None ->
  map.get m2 k = None ->
  map.get (map.putmany m1 m2) k = None.
Proof. map_solver mp_ok. Qed.

Definition fmap_of (m : mp) :=
  map.fold (@add _ _) $0 m.
Opaque fmap_of.

Lemma fmap_of_spec (m : mp) k :
  fmap_of m $? k = map.get m k.
Proof.
  cbv [fmap_of]. apply map.fold_spec.
  - rewrite map.get_empty, lookup_empty. reflexivity.
  - intros k0 v m0 r H H0. rewrite map.get_put_dec. destr (key_eqb k0 k).
    + apply lookup_add_eq. reflexivity.
    + rewrite lookup_add_ne by auto. auto.
Qed.
    
Lemma add_fmap_of m k v :
  fmap_of m $+ (k, v) = fmap_of (map.put m k v).
Proof.
  apply fmap_ext. intros. rewrite fmap_of_spec.
  rewrite map.get_put_dec. destr (key_eqb k k0).
  - rewrite lookup_add_eq; auto.
  - rewrite lookup_add_ne; auto. apply fmap_of_spec.
Qed.
End Map.
