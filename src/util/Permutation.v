From Stdlib Require Import Lists.List Arith.PeanoNat Sorting.Sorted Sorting.Permutation Lia.
From coqutil Require Import Sorting.OrderToPermutation Datatypes.List.
From Datalog Require Import List.
Import ListNotations.

Definition invert_permutation (p : list nat) : list nat :=
  order_to_permutation p.

Lemma fst_zip_with_start_index {A} (l : list A) start :
  map fst (zip_with_start_index start l) = l.
Proof.
  revert start. induction l; simpl; intros; f_equal; auto.
Qed.

Lemma fst_zip_with_index {A} (l : list A) : map fst (zip_with_index l) = l.
Proof. apply fst_zip_with_start_index. Qed.

Lemma in_zip_with_start_index_iff {A} (l : list A) start a n :
  In (a, n) (zip_with_start_index start l) <-> In (n, a) (enumerate start l).
Proof.
  revert start. induction l; intros start.
  - reflexivity.
  - rewrite enumerate_cons. simpl. rewrite IHl. intuition congruence.
Qed.

Lemma enumerate_map_snd {A} (l : list (nat * A)) start n :
  map fst l = seq start n -> enumerate start (map snd l) = l.
Proof.
  revert start n. induction l as [|[m a] l IH]; intros start [|n] H; try discriminate.
  - reflexivity.
  - injection H as -> H. cbn [map snd]. rewrite enumerate_cons. f_equal. eauto.
Qed.

Lemma sorted_le_perm_eq l1 l2 :
  Sorted le l1 -> Sorted le l2 -> Permutation l1 l2 -> l1 = l2.
Proof.
  intros H1 H2. apply Sorted_StronglySorted in H1, H2; try exact Nat.le_trans.
  revert l2 H2. induction H1 as [|a l1 _ IH Ha]; intros l2 H2 Hp.
  - symmetry. apply Permutation_nil, Hp.
  - destruct H2 as [|b l2 H2 Hb].
    + apply Permutation_sym, Permutation_nil in Hp. discriminate.
    + rewrite Forall_forall in Ha, Hb.
      assert (a = b) as <-.
      { apply Nat.le_antisymm.
        - destruct (Permutation_in b (Permutation_sym Hp) (in_eq _ _)); [lia | auto].
        - destruct (Permutation_in a Hp (in_eq _ _)); [lia | auto]. }
      f_equal. eauto using Permutation_cons_inv.
Qed.

Lemma StronglySorted_filter {A} (R : A -> A -> Prop) f l :
  StronglySorted R l -> StronglySorted R (filter f l).
Proof.
  induction 1; simpl.
  - constructor.
  - destruct (f a); eauto using SSorted_cons, incl_Forall, incl_filter.
Qed.

Lemma StronglySorted_seq start n : StronglySorted le (seq start n).
Proof.
  revert start. induction n; intros start; simpl; constructor; auto.
  apply Forall_forall. intros x Hx. apply in_seq in Hx. lia.
Qed.

Lemma sorted_fst_of_locally_sorted (s : list (nat * nat)) :
  LocallySorted (fun x y => is_true (FstNatOrder.leb x y)) s -> Sorted le (map fst s).
Proof.
  intros Hs. apply Sorted_LocallySorted_iff.
  induction Hs as [| |[a1 b1] [a2 b2]]; constructor; auto.
  apply Nat.leb_le. assumption.
Qed.

Lemma fst_sort_zip_with_index p :
  Permutation p (seq 0 (length p)) ->
  map fst (FstNatSorting.sort (zip_with_index p)) = seq 0 (length p).
Proof.
  intros Hp. apply sorted_le_perm_eq.
  - apply sorted_fst_of_locally_sorted, FstNatSorting.LocallySorted_sort.
  - apply StronglySorted_Sorted, StronglySorted_seq.
  - rewrite <- FstNatSorting.Permuted_sort, fst_zip_with_index. assumption.
Qed.

Lemma nth_error_invert_permutation p i j :
  Permutation p (seq 0 (length p)) ->
  nth_error (invert_permutation p) i = Some j <-> nth_error p j = Some i.
Proof.
  intros Hp.
  rewrite <- !in_enumerate_0_iff, <- (in_zip_with_start_index_iff p).
  cbv [invert_permutation order_to_permutation].
  erewrite enumerate_map_snd by (apply fst_sort_zip_with_index; assumption).
  rewrite <- FstNatSorting.Permuted_sort. reflexivity.
Qed.

Lemma length_order_to_permutation p : length (order_to_permutation p) = length p.
Proof.
  rewrite (Permutation_length (order_to_permutation_is_Permutation p)). apply length_seq.
Qed.

Lemma length_invert_permutation p : length (invert_permutation p) = length p.
Proof. apply length_order_to_permutation. Qed.

Lemma invert_permutation_in_range p i :
  In i (invert_permutation p) -> i < length p.
Proof.
  intros Hi. apply (Permutation_in _ (order_to_permutation_is_Permutation p)), in_seq in Hi.
  lia.
Qed.

Lemma nth_invert_permutation_inv p i :
  Permutation p (seq 0 (length p)) ->
  i < length p ->
  nth (nth i (invert_permutation p) 0) p 0 = i.
Proof.
  intros Hp Hi. apply nth_error_nth, nth_error_invert_permutation, nth_error_nth'.
  - assumption.
  - rewrite length_invert_permutation. assumption.
Qed.

Lemma length_apply_permutation_with_default {A} p (l : list A) d :
  length (apply_permutation_with_default p l d) = length p.
Proof. apply length_map. Qed.

Lemma nth_apply_permutation_with_default {A} p (l : list A) d d' i :
  i < length p ->
  nth i (apply_permutation_with_default p l d) d' = nth (nth i p 0) l d.
Proof.
  intros Hi.
  rewrite nth_indep with (d' := nth 0 l d)
    by (rewrite length_apply_permutation_with_default; assumption).
  apply (map_nth (fun j => nth j l d)).
Qed.

Lemma apply_permutation_with_default_indep {A} p (l : list A) d1 d2 :
  Forall (fun j => j < length l) p ->
  apply_permutation_with_default p l d1 = apply_permutation_with_default p l d2.
Proof.
  intros Hp. rewrite Forall_forall in Hp. apply map_ext_in. auto using nth_indep.
Qed.

Lemma apply_permutation_eq_with_default {A} p (l : list A) d :
  Forall (fun j => j < length l) p ->
  apply_permutation p l = apply_permutation_with_default p l d.
Proof.
  intros Hp. destruct l as [|a l].
  - destruct Hp; [reflexivity|]. simpl in *. lia.
  - apply apply_permutation_with_default_indep. assumption.
Qed.

Lemma length_apply_permutation {A} p (l : list A) :
  Permutation p (seq 0 (length l)) ->
  length (apply_permutation p l) = length l.
Proof.
  intros Hp. symmetry. apply Permutation_length, apply_permutation_is_Permutation, Hp.
Qed.

Lemma nth_apply_permutation {A} p (l : list A) d i :
  Permutation p (seq 0 (length l)) ->
  i < length p ->
  nth i (apply_permutation p l) d = nth (nth i p 0) l d.
Proof.
  intros Hp Hi. rewrite (apply_permutation_eq_with_default _ _ d).
  - apply nth_apply_permutation_with_default, Hi.
  - apply Forall_forall. intros j Hj. apply (Permutation_in _ Hp), in_seq in Hj. lia.
Qed.

Lemma apply_invert_permutation {A} p (l : list A) :
  Permutation p (seq 0 (length l)) ->
  apply_permutation (invert_permutation p) (apply_permutation p l) = l.
Proof.
  intros Hp.
  assert (Hlen : length p = length l).
  { rewrite (Permutation_length Hp). apply length_seq. }
  assert (Hq : Permutation (invert_permutation p) (seq 0 (length (apply_permutation p l)))).
  { rewrite length_apply_permutation, <- Hlen by assumption.
    apply order_to_permutation_is_Permutation. }
  destruct l as [|d l].
  - destruct p; [reflexivity | discriminate].
  - apply nth_ext with (d := d) (d' := d).
    + rewrite !length_apply_permutation by assumption. reflexivity.
    + intros i Hi. rewrite !length_apply_permutation, <- Hlen in Hi by assumption.
      assert (i < length (invert_permutation p)) by (rewrite length_invert_permutation; assumption).
      rewrite !nth_apply_permutation, nth_invert_permutation_inv;
        auto using invert_permutation_in_range, nth_In.
      rewrite Hlen. assumption.
Qed.

Lemma apply_order_to_permutation l :
  apply_permutation (order_to_permutation l) l = map fst (FstNatSorting.sort (zip_with_index l)).
Proof.
  rewrite (apply_permutation_eq_with_default _ _ 0).
  - change (apply_permutation_with_default ?p l 0) with (map (fun i => nth i l 0) p).
    cbv [order_to_permutation]. rewrite map_map. apply map_ext_in. intros [a b] Hab.
    apply nth_error_nth, in_enumerate_0_iff, in_zip_with_start_index_iff.
    exact (Permutation_in _ (Permutation_sym (FstNatSorting.Permuted_sort _)) Hab).
  - apply Forall_forall, invert_permutation_in_range.
Qed.

Lemma Sorted_apply_order_to_permutation l :
  Sorted le (apply_permutation (order_to_permutation l) l).
Proof.
  rewrite apply_order_to_permutation.
  apply sorted_fst_of_locally_sorted, FstNatSorting.LocallySorted_sort.
Qed.
