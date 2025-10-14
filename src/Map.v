From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd.
From ATL Require Import FrapWithoutSets.
From Datalog Require Import Tactics.


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

Lemma fmap_of_empty :
  fmap_of map.empty = $0.
Proof.
  apply fmap_ext. intros.
  rewrite fmap_of_spec, map.get_empty, lookup_empty.
  reflexivity.
Qed.
    
Lemma add_fmap_of m k v :
  fmap_of m $+ (k, v) = fmap_of (map.put m k v).
Proof.
  apply fmap_ext. intros. rewrite fmap_of_spec.
  rewrite map.get_put_dec. destr (key_eqb k k0).
  - rewrite lookup_add_eq; auto.
  - rewrite lookup_add_ne; auto. apply fmap_of_spec.
Qed.

Definition agree_on (m1 m2 : mp) k :=
  map.get m1 k = map.get m2 k.

Lemma agree_on_putmany m1 m2 m1' m2' k :
  agree_on m1 m1' k ->
  agree_on m2 m2' k ->
  agree_on (map.putmany m1 m2) (map.putmany m1' m2') k.
Proof. cbv [agree_on]. map_solver mp_ok. Qed.

Lemma agree_on_refl m k :
  agree_on m m k.
Proof. reflexivity. Qed.

Lemma get_of_list_None_bw k l :
  map.get (map := mp) (map.of_list l) k = None -> ~In k (map fst l).
Proof.
  intros H. induction l as [|(k0&v0) l']; subst; simpl in *; auto.
  intros [H'|H']; subst.
  - rewrite map.get_put_same in H. discriminate H.
  - apply IHl'; auto. rewrite map.get_put_dec in *.
    destruct_one_match_hyp; intuition congruence.
Qed.

Lemma getmany_of_list_ext (m1 m2 : mp) ks vs :
  map.getmany_of_list m1 ks = Some vs ->
  Forall (agree_on m1 m2) ks ->
  map.getmany_of_list m2 ks = Some vs.
Proof.
  cbv [map.getmany_of_list]. revert vs.
  induction ks; simpl in *; intros; auto.
  do 2 (destruct_one_match_hyp; try congruence; []).
  invert_list_stuff. rewrite <- H3, E. erewrite IHks by eauto.
  reflexivity.
Qed.

Lemma putmany_of_list_ext (m m1' m2' : mp) ks vs vs' :
  map.putmany_of_list_zip ks vs m = Some m1' ->
  map.putmany_of_list_zip ks vs' m = Some m2' ->
  Forall (agree_on m1' m2') ks ->
  m1' = m2'.
Proof.
  revert m m1' m2' vs vs'.
  induction ks; intros m m1' m2' vs vs'; destruct vs, vs'; simpl; try congruence.
  intros. invert_list_stuff.
  epose proof map.only_differ_putmany as H'. specialize (H' _ _ _ _ H).
  epose proof map.only_differ_putmany as H0'. specialize (H0' _ _ _ _ H0).
  Print map.only_differ. apply map.map_ext. intros k.
  specialize (H' k). specialize (H0' k). eassert (H1: _ \/ _).
  { destruct H' as [H'|H']. 1: left; exact H'. destruct H0' as [H0'|H0'].
    1: left; exact H0'. right. exact (conj H' H0'). }
  clear H0' H'. destruct H1 as [H1|H1].
  - cbv [PropSet.elem_of PropSet.of_list] in H1. rewrite Forall_forall in H5.
    apply H5. assumption.
  - fwd. rewrite map.get_put_dec in H1p0, H1p1. destr (key_eqb a k).
    + apply H4.
    + rewrite <- H1p0, <- H1p1. reflexivity.
Qed.

Lemma agree_on_putmany_r (m m1 m2 : mp) k :
  agree_on (map.putmany m m1) (map.putmany m m2) k ->
  agree_on m1 m2 k.
Proof.
  cbv [agree_on]. do 2 rewrite map.get_putmany_dec. repeat destruct_one_match; try congruence. Abort.

Lemma of_list_Some_in kvs k v :
  map.get (map := mp) (map.of_list kvs) k = Some v ->
  In (k, v) kvs.
Proof.
  intros. induction kvs as [|(k0&v0)]; simpl in *.
  - map_solver mp_ok.
  - rewrite map.get_put_dec in H. destr (key_eqb k0 k); intuition congruence.
Qed.

Lemma in_of_list_Some_strong k kvs :
  In k (map fst kvs) ->
  exists v,
    map.get (map := mp) (map.of_list kvs) k = Some v /\
      In (k, v) kvs.
Proof.
  induction kvs as [|(k0&v0)]; simpl; [contradiction|].
  intros [H|H]; subst.
  - eauto using map.get_put_same.
  - apply IHkvs in H. fwd. rewrite map.get_put_dec. destr (key_eqb k0 k); eauto.
Qed.

Lemma in_of_list_Some k kvs :
  In k (map fst kvs) ->
  exists v,
    map.get (map := mp) (map.of_list kvs) k = Some v.
Proof.
  intros H. apply in_of_list_Some_strong in H. fwd. eauto.
Qed.

Lemma putmany_extends_idk (m1 m2 m2' : mp) :
  map.extends (map.putmany m1 m2) m2' ->
  map.extends m2' m2 ->
  map.putmany m1 m2 = map.putmany m1 m2'.
Proof.
  intros. apply map.map_ext. map_solver mp_ok.
  (*this feels vulnerable to slight changes in map_solver :( *)
  match goal with
  | H: _ |- _ => specialize (H _ eq_refl); discriminate H
  end.
Qed.

Lemma zipped_lookup_notin_None (k : key) ks (vs : list value) :
  ~ In k ks ->
  map.zipped_lookup (key_eqb := key_eqb) ks vs k = None.
Proof.
  intros. destruct (map.zipped_lookup ks vs k) eqn:E; [|reflexivity].
  Search map.zipped_lookup. apply map.zipped_lookup_Some_in in E. exfalso. auto.
Qed.
End Map.
