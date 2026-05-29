From Stdlib Require Import Lists.List Arith.PeanoNat
  Sorting.Sorted Sorting.Mergesort Sorting.Permutation Lia.
From coqutil Require Import Sorting.OrderToPermutation Datatypes.List.
Import ListNotations.

Definition invert_permutation (p : list nat) : list nat :=
  order_to_permutation p.

Lemma fst_zip_with_start_index : forall A (l : list A) start,
  map fst (zip_with_start_index start l) = l.
Proof.
  induction l; intros; simpl; [reflexivity|].
  f_equal. apply IHl.
Qed.

Lemma fst_zip_with_index : forall A (l : list A),
  map fst (zip_with_index l) = l.
Proof. intros. apply fst_zip_with_start_index. Qed.

Lemma length_zip_with_start_index : forall A (l : list A) start,
  length (zip_with_start_index start l) = length l.
Proof.
  intros. rewrite <- (length_map fst). rewrite fst_zip_with_start_index.
  reflexivity.
Qed.

Lemma length_zip_with_index : forall A (l : list A),
  length (zip_with_index l) = length l.
Proof. intros. apply length_zip_with_start_index. Qed.

Lemma length_order_to_permutation : forall p,
  length (order_to_permutation p) = length p.
Proof.
  intros p. unfold order_to_permutation.
  rewrite (length_map snd).
  rewrite <- (length_zip_with_index _ p).
  apply Permutation_length.
  apply Permutation_sym, FstNatSorting.Permuted_sort.
Qed.

Lemma length_invert_permutation : forall p,
  length (invert_permutation p) = length p.
Proof. intros. apply length_order_to_permutation. Qed.

Lemma length_apply_permutation_with_default : forall p A (l : list A) d,
  length (apply_permutation_with_default p l d) = length p.
Proof.
  intros. unfold apply_permutation_with_default, my_list_map.
  apply (length_map (fun i => List.nth i l d)).
Qed.

Lemma sorted_le_perm_seq_eq : forall l start n,
  Sorted le l ->
  Permutation l (seq start n) ->
  l = seq start n.
Proof.
  induction l as [|a l' IH]; intros start n Hsorted Hperm.
  - apply Permutation_nil in Hperm.
    destruct n; [reflexivity | discriminate].
  - assert (Hlen := Permutation_length Hperm).
    simpl in Hlen. rewrite length_seq in Hlen.
    destruct n as [|n']; [discriminate|].
    assert (Ha : a = start). {
      assert (Ha_in : In a (seq start (S n'))) by
        (eapply Permutation_in; [exact Hperm | left; reflexivity]).
      apply in_seq in Ha_in.
      assert (Hstart_in : In start (a :: l')). {
        eapply Permutation_in; [apply Permutation_sym; exact Hperm|].
        apply in_seq. lia.
      }
      destruct Hstart_in as [Heq | Hstart_l'].
      + congruence.
      + apply Sorted_StronglySorted in Hsorted; [|red; lia].
        inversion Hsorted as [|? ? _ Hall]; subst.
        rewrite Forall_forall in Hall.
        specialize (Hall _ Hstart_l'). lia.
    }
    subst a.
    rewrite <- cons_seq. f_equal.
    apply IH.
    + apply Sorted_inv in Hsorted as [? _]. assumption.
    + rewrite <- cons_seq in Hperm.
      eapply Permutation_cons_inv. exact Hperm.
Qed.

Lemma sorted_fst_of_locally_sorted :
  forall (s : list (nat * nat)),
    LocallySorted (fun x y => is_true (FstNatOrder.leb x y)) s ->
    Sorted le (map fst s).
Proof.
  intros s Hs.
  apply Sorted_LocallySorted_iff.
  induction Hs as [|[a b]|[a1 b1] [a2 b2] s' Hs' IH Hrel].
  - constructor.
  - constructor.
  - simpl in *.
    constructor; [exact IH|].
    unfold is_true, FstNatOrder.leb in Hrel.
    apply Nat.leb_le in Hrel. exact Hrel.
Qed.

Lemma fst_sort_zip_with_index : forall p,
  Permutation p (seq 0 (length p)) ->
  map fst (FstNatSorting.sort (zip_with_index p)) = seq 0 (length p).
Proof.
  intros p Hp.
  apply (sorted_le_perm_seq_eq _ 0 (length p)).
  - apply sorted_fst_of_locally_sorted.
    apply FstNatSorting.LocallySorted_sort.
  - eapply Permutation_trans.
    + apply Permutation_map.
      apply Permutation_sym, FstNatSorting.Permuted_sort.
    + rewrite fst_zip_with_index. exact Hp.
Qed.

Lemma in_zip_with_start_index :
  forall A (l : list A) start a b,
    In (a, b) (zip_with_start_index start l) ->
    start <= b < start + length l /\ nth (b - start) l a = a.
Proof.
  induction l; intros start a' b H; simpl in H.
  - contradiction.
  - destruct H as [Heq | Hin].
    + inversion Heq. subst.
      split; [simpl; lia | rewrite Nat.sub_diag; reflexivity].
    + apply IHl in Hin as [Hbound Hnth].
      split; [simpl; lia|].
      destruct (b - start) as [|n] eqn:E.
      * lia.
      * replace n with (b - S start) by lia. exact Hnth.
Qed.

Lemma in_zip_with_index_nth : forall A (l : list A) a b,
  In (a, b) (zip_with_index l) ->
  b < length l /\ nth b l a = a.
Proof.
  intros. apply in_zip_with_start_index in H as [Hbound Hnth].
  rewrite Nat.sub_0_r in Hnth. split; [lia | exact Hnth].
Qed.

Lemma nth_apply_permutation_with_default :
  forall p A (l : list A) d d' i,
    i < length p ->
    nth i (apply_permutation_with_default p l d) d' = nth (nth i p 0) l d.
Proof.
  unfold apply_permutation_with_default, my_list_map, my_list_nth.
  induction p as [|x p IH]; intros A l d d' i Hi; simpl in *.
  - lia.
  - destruct i.
    + reflexivity.
    + apply IH. lia.
Qed.

Lemma apply_permutation_with_default_indep :
  forall p A (l : list A) d1 d2,
    Forall (fun j => j < length l) p ->
    apply_permutation_with_default p l d1 = apply_permutation_with_default p l d2.
Proof.
  intros p A l d1 d2 Hp.
  unfold apply_permutation_with_default, my_list_map, my_list_nth.
  apply map_ext_in. intros i Hi.
  rewrite Forall_forall in Hp. specialize (Hp _ Hi).
  apply nth_indep. exact Hp.
Qed.

Lemma apply_permutation_eq_with_default :
  forall p A (l : list A) d,
    Forall (fun j => j < length l) p ->
    apply_permutation p l = apply_permutation_with_default p l d.
Proof.
  intros p A l d Hp.
  unfold apply_permutation.
  destruct l as [|a l'].
  - (* l = [] forces p = [] *)
    assert (p = []). {
      destruct p as [|x p']; [reflexivity|].
      rewrite Forall_forall in Hp. specialize (Hp x (or_introl eq_refl)).
      simpl in Hp. lia.
    }
    subst p. reflexivity.
  - apply apply_permutation_with_default_indep. assumption.
Qed.

Lemma nth_invert_permutation_inv :
  forall p i,
    Permutation p (seq 0 (length p)) ->
    i < length p ->
    nth (nth i (invert_permutation p) 0) p 0 = i.
Proof.
  intros p i Hp Hi.
  unfold invert_permutation, order_to_permutation.
  set (s := FstNatSorting.sort (zip_with_index p)).
  assert (Hs_len : length s = length p).
  { unfold s. rewrite <- (Permutation_length (FstNatSorting.Permuted_sort _)).
    apply length_zip_with_index. }
  destruct (nth i s (0, 0)) as [a b] eqn:Epair.
  assert (Hb : nth i (map snd s) 0 = b). {
    rewrite (nth_indep _ _ (snd (0, 0))) by (rewrite length_map; lia).
    rewrite map_nth. rewrite Epair. reflexivity.
  }
  rewrite Hb.
  assert (Hin : In (a, b) s). {
    rewrite <- Epair. apply nth_In. lia.
  }
  assert (Hin_zip : In (a, b) (zip_with_index p)). {
    eapply Permutation_in.
    - apply Permutation_sym. unfold s. apply FstNatSorting.Permuted_sort.
    - exact Hin.
  }
  apply in_zip_with_index_nth in Hin_zip as [Hblt Hnth].
  assert (Ha : a = i). {
    pose proof (fst_sort_zip_with_index _ Hp) as Hfst.
    fold s in Hfst.
    assert (Hfst_nth : nth i (map fst s) 0 = i). {
      rewrite Hfst. rewrite seq_nth by lia. lia.
    }
    rewrite (nth_indep _ _ (fst (0, 0))) in Hfst_nth by (rewrite length_map; lia).
    rewrite map_nth in Hfst_nth. rewrite Epair in Hfst_nth. simpl in Hfst_nth.
    auto.
  }
  subst a.
  rewrite (nth_indep _ _ i) by lia.
  exact Hnth.
Qed.

Lemma invert_permutation_in_range : forall p i,
  Permutation p (seq 0 (length p)) ->
  In i (invert_permutation p) ->
  i < length p.
Proof.
  intros p i Hp Hin.
  unfold invert_permutation, order_to_permutation in Hin.
  apply in_map_iff in Hin as [[a b] [Hb Hpair]].
  simpl in Hb. subst i.
  assert (In (a, b) (zip_with_index p)). {
    eapply Permutation_in.
    - apply Permutation_sym, FstNatSorting.Permuted_sort.
    - exact Hpair.
  }
  apply in_zip_with_index_nth in H as [? _]. assumption.
Qed.

Lemma length_apply_permutation : forall p A (l : list A),
  Permutation p (seq 0 (length l)) ->
  length (apply_permutation p l) = length l.
Proof.
  intros p A l Hp.
  apply Permutation_length.
  apply Permutation_sym, apply_permutation_is_Permutation. exact Hp.
Qed.

Lemma nth_apply_permutation : forall p A (l : list A) d i,
  Permutation p (seq 0 (length l)) ->
  i < length p ->
  nth i (apply_permutation p l) d = nth (nth i p 0) l d.
Proof.
  intros p A l d i Hp Hi.
  assert (Hpi_lt : nth i p 0 < length l). {
    assert (In (nth i p 0) p) by (apply nth_In; exact Hi).
    assert (In (nth i p 0) (seq 0 (length l))) by
      (eapply Permutation_in; [exact Hp | exact H]).
    apply in_seq in H0. lia.
  }
  unfold apply_permutation.
  destruct l as [|a l'].
  - simpl in Hpi_lt. lia.
  - rewrite (nth_apply_permutation_with_default _ _ _ a d _ Hi).
    apply nth_indep. exact Hpi_lt.
Qed.

Lemma apply_invert_permutation : forall p A (l : list A),
  Permutation p (seq 0 (length l)) ->
  apply_permutation (invert_permutation p) (apply_permutation p l) = l.
Proof.
  intros p A l Hp.
  pose proof (Permutation_length Hp) as Hlen_p.
  rewrite length_seq in Hlen_p.
  assert (Hp' : Permutation p (seq 0 (length p))) by (rewrite Hlen_p; exact Hp).
  pose proof (length_apply_permutation _ _ _ Hp) as Hlen_app.
  assert (Hq : Permutation (invert_permutation p)
                           (seq 0 (length (apply_permutation p l)))). {
    rewrite Hlen_app. rewrite <- Hlen_p.
    unfold invert_permutation. apply order_to_permutation_is_Permutation.
  }
  pose proof (length_apply_permutation _ _ _ Hq) as Hlen_outer.
  destruct l as [|d l'].
  - simpl in Hlen_p. assert (p = []) by (destruct p; [reflexivity | discriminate]).
    subst p. reflexivity.
  - apply nth_ext with (d := d) (d' := d).
    + rewrite Hlen_outer. exact Hlen_app.
    + intros i Hi.
      rewrite Hlen_outer in Hi. rewrite Hlen_app in Hi.
      rewrite (nth_apply_permutation _ _ _ d i Hq) by
        (rewrite length_invert_permutation; lia).
      rewrite (nth_apply_permutation _ _ _ d _ Hp).
      * f_equal.
        apply nth_invert_permutation_inv; [exact Hp'|]. lia.
      * apply invert_permutation_in_range; [exact Hp'|].
        apply nth_In. rewrite length_invert_permutation. lia.
Qed.
