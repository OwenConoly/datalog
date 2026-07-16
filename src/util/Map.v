From ATL Require Import FrapWithoutSets.
From coqutil Require Import Map.Interface Map.Properties Map.Solver Map.MapKeys Tactics Tactics.fwd Datatypes.Option Datatypes.List Eqb.
From Datalog Require Import Eqb.
From Datalog Require Import Tactics List.
From Stdlib Require Import Permutation.

Section MapKeysExtra.
  Context {key key' value : Type}.
  Context {mp : map.map key value} {mp_ok : map.ok mp}.
  Context {mp' : map.map key' value} {mp'_ok : map.ok mp'}.
  Context {key'_eqb : Eqb key'} {key'_eqb_ok : Eqb_ok key'_eqb}.

  (* coqutil's [get_map_keys_always_invertible] characterizes [get (map_keys g m)]
     only on keys in the image of [g]; this covers the rest. *)
  Lemma get_map_keys_None (g : key -> key') (m : mp) (k0 : key') :
    (forall k, g k <> k0) -> map.get (map.map_keys (map' := mp') g m) k0 = None.
  Proof.
    intros Hg. unfold map.map_keys. eapply map.fold_spec.
    - apply map.get_empty.
    - intros k v m' r Hk IH. rewrite map.get_put_dec. destr (eqb (g k) k0).
      + specialize (Hg k). congruence.
      + exact IH.
  Qed.
End MapKeysExtra.

Lemma Permutation_concat {A} (l l' : list (list A)) :
  Permutation l l' -> Permutation (concat l) (concat l').
Proof.
  induction 1; cbn [concat].
  - reflexivity.
  - apply Permutation_app_head; assumption.
  - rewrite !app_assoc. apply Permutation_app_tail, Permutation_app_comm.
  - eapply Permutation_trans; eassumption.
Qed.


Section Maps.
  Context {key : Type}.
  Context {value1 : Type} {mp1 : map.map key value1} {mp1_ok : map.ok mp1}.
  Context {value2 : Type} {mp2 : map.map key value2} {mp2_ok : map.ok mp2}.
  Context {value3 : Type} {mp3 : map.map key value3} {mp3_ok : map.ok mp3}.
  Context {value4 : Type} {mp4 : map.map key value4} {mp4_ok : map.ok mp4}.
  Context {key_eqb : Eqb key} {key_eqb_ok : Eqb_ok key_eqb}.

  Definition Forall_map (R : key -> value1 -> Prop) (m : mp1) : Prop :=
    forall k v, map.get m k = Some v -> R k v.

  Definition values (m : mp1) : list value1 := map.fold (fun acc _ v => cons v acc) nil m.

  Lemma values_eq_tuples (m : mp1) : values m = map snd (map.tuples m).
  Proof.
    unfold values. rewrite map.fold_to_tuples_fold.
    generalize (map.tuples m) as l. induction l as [| [k v] l IH]; cbn; congruence.
  Qed.

  Lemma values_empty : values (map.empty : mp1) = [].
  Proof. unfold values. apply map.fold_empty. Qed.

  Lemma In_values (m : mp1) v :
    In v (values m) <-> exists k, map.get m k = Some v.
  Proof.
    rewrite values_eq_tuples, in_map_iff. split.
    - intros ([k v'] & Hsnd & Hin). cbn in Hsnd. subst v'.
      exists k. apply map.tuples_spec. exact Hin.
    - intros (k & Hget). exists (k, v).
      split; [ reflexivity | apply map.tuples_spec; exact Hget ].
  Qed.

  Lemma tuples_put_perm (m : mp1) k v :
    map.get m k = None ->
    Permutation (map.tuples (map.put m k v)) ((k, v) :: map.tuples m).
  Proof.
    intros Hk. apply NoDup_Permutation.
    - apply map.tuples_NoDup.
    - constructor.
      + intro Hin. apply map.tuples_spec in Hin. congruence.
      + apply map.tuples_NoDup.
    - intros [k0 v0]. exact (map.tuples_put m k v Hk k0 v0).
  Qed.

  Lemma values_put_None (m : mp1) k v :
    map.get m k = None ->
    Permutation (values (map.put m k v)) (v :: values m).
  Proof.
    intros Hk. rewrite !values_eq_tuples.
    change (v :: map snd (map.tuples m)) with (map snd ((k, v) :: map.tuples m)).
    apply Permutation_map, tuples_put_perm, Hk.
  Qed.

  Lemma values_remove (m : mp1) k v0 :
    map.get m k = Some v0 ->
    Permutation (values m) (v0 :: values (map.remove m k)).
  Proof.
    intros Hk.
    transitivity (values (map.put (map.remove m k) k v0)).
    - rewrite map.put_remove_same, (map.put_noop k v0 m Hk). reflexivity.
    - apply values_put_None, map.get_remove_same.
  Qed.

  Lemma values_put (m : mp1) k v :
    Permutation (values (map.put m k v)) (v :: values (map.remove m k)).
  Proof.
    rewrite <- (map.put_remove_same m k v).
    apply values_put_None, map.get_remove_same.
  Qed.

  Lemma values_Forall (P : value1 -> Prop) (m : mp1) :
    Forall_map (fun _ v => P v) m -> Forall P (values m).
  Proof.
    intros H. rewrite values_eq_tuples. apply Forall_forall.
    intros x Hx. apply in_map_iff in Hx. destruct Hx as ([k v] & Hsnd & Hin).
    cbn in Hsnd. subst x. apply map.tuples_spec in Hin. exact (H k v Hin).
  Qed.

  Lemma Forall_map_put R (m : mp1) k v :
    Forall_map (fun k' w => k <> k' -> R k' w) m ->
    R k v ->
    Forall_map R (map.put m k v).
  Proof.
    intros H HR k0 v0 Hget. rewrite map.get_put_dec in Hget. destr (eqb k k0).
    - injection Hget as Hv. subst. exact HR.
    - apply H; assumption.
  Qed.

  Definition Forall2_map (R : key -> value1 -> value2 -> Prop) (m1 : mp1) (m2 : mp2) : Prop :=
    forall k,
      match map.get m1 k, map.get m2 k with
      | None, None => True
      | Some v1, Some v2 => R k v1 v2
      | _, _ => False
      end.

  (* can't use coqutil's map.same_domain because it requires mp1 = mp2. *)
  Definition same_domain (m1 : mp1) (m2 : mp2) : Prop :=
    Forall2_map (fun _ _ _ => True) m1 m2.

  Lemma Forall2_map_impl_strong (R R' : key -> value1 -> value2 -> Prop) (m1 : mp1) (m2 : mp2) :
    Forall2_map R m1 m2 ->
    (forall k v1 v2,
        map.get m1 k = Some v1 ->
        map.get m2 k = Some v2 ->
        R k v1 v2 -> R' k v1 v2) ->
    Forall2_map R' m1 m2.
  Proof.
    intros H HRR k. specialize (H k).
    destruct (map.get m1 k) as [v1|] eqn:E1; destruct (map.get m2 k) as [v2|] eqn:E2;
      try exact H.
    apply HRR; assumption.
  Qed.

  Lemma Forall2_map_impl (R R' : key -> value1 -> value2 -> Prop) (m1 : mp1) (m2 : mp2) :
    Forall2_map R m1 m2 ->
    (forall k v1 v2, R k v1 v2 -> R' k v1 v2) ->
    Forall2_map R' m1 m2.
  Proof. eauto using Forall2_map_impl_strong. Qed.

  Lemma Forall2_map_put_l R (m1 : mp1) (m2 : mp2) k v1 v2 :
    Forall2_map (fun k' w1 w2 => k <> k' -> R k' w1 w2) m1 m2 ->
    map.get m2 k = Some v2 ->
    R k v1 v2 ->
    Forall2_map R (map.put m1 k v1) m2.
  Proof.
    intros H Hget HR k0. specialize (H k0). rewrite map.get_put_dec. destr (eqb k k0).
    - subst. rewrite Hget. exact HR.
    - destruct (map.get m1 k0) as [w1|]; destruct (map.get m2 k0) as [w2|]; try exact H.
      apply H. assumption.
  Qed.

  Lemma Forall2_map_put_r R (m1 : mp1) (m2 : mp2) k v1 v2 :
    Forall2_map (fun k' w1 w2 => k <> k' -> R k' w1 w2) m1 m2 ->
    map.get m1 k = Some v1 ->
    R k v1 v2 ->
    Forall2_map R m1 (map.put m2 k v2).
  Proof.
    intros H Hget HR k0. specialize (H k0). rewrite map.get_put_dec. destr (eqb k k0).
    - subst. rewrite Hget. exact HR.
    - destruct (map.get m1 k0) as [w1|]; destruct (map.get m2 k0) as [w2|]; try exact H.
      apply H. assumption.
  Qed.

  Lemma Forall2_map_get_l R (m1 : mp1) (m2 : mp2) k v1 :
    Forall2_map R m1 m2 ->
    map.get m1 k = Some v1 ->
    exists v2, map.get m2 k = Some v2 /\ R k v1 v2.
  Proof.
    intros H Hget. specialize (H k). rewrite Hget in H.
    destruct (map.get m2 k) as [v2|].
    - exists v2. split; [reflexivity | exact H].
    - contradiction.
  Qed.

  Lemma Forall2_map_get_r R (m1 : mp1) (m2 : mp2) k v2 :
    Forall2_map R m1 m2 ->
    map.get m2 k = Some v2 ->
    exists v1, map.get m1 k = Some v1 /\ R k v1 v2.
  Proof.
    intros H Hget. specialize (H k). rewrite Hget in H.
    destruct (map.get m1 k) as [v1|].
    - exists v1. split; [reflexivity | exact H].
    - contradiction.
  Qed.

  Lemma Forall2_map_get_None R (m1 : mp1) (m2 : mp2) k :
    Forall2_map R m1 m2 ->
    (map.get m1 k = None <-> map.get m2 k = None).
  Proof.
    intros H. specialize (H k).
    destruct (map.get m1 k); destruct (map.get m2 k);
      try contradiction; split; intros; congruence.
  Qed.

  Lemma Forall2_map_intro R (m1 : mp1) (m2 : mp2) :
    (forall k, map.get m1 k = None <-> map.get m2 k = None) ->
    (forall k v1 v2, map.get m1 k = Some v1 -> map.get m2 k = Some v2 -> R k v1 v2) ->
    Forall2_map R m1 m2.
  Proof.
    intros Hdom HR k. specialize (Hdom k).
    destruct (map.get m1 k) as [v1|] eqn:E1; destruct (map.get m2 k) as [v2|] eqn:E2.
    - exact (HR _ _ _ E1 E2).
    - discriminate (proj2 Hdom eq_refl).
    - discriminate (proj1 Hdom eq_refl).
    - exact I.
  Qed.

  Definition Forall3_map (R : key -> value1 -> value2 -> value3 -> Prop)
    (m1 : mp1) (m2 : mp2) (m3 : mp3) : Prop :=
    forall k,
      match map.get m1 k, map.get m2 k, map.get m3 k with
      | None, None, None => True
      | Some v1, Some v2, Some v3 => R k v1 v2 v3
      | _, _, _ => False
      end.

  Lemma Forall3_map_impl_strong (R R' : key -> value1 -> value2 -> value3 -> Prop)
    (m1 : mp1) (m2 : mp2) (m3 : mp3) :
    Forall3_map R m1 m2 m3 ->
    (forall k v1 v2 v3,
        map.get m1 k = Some v1 ->
        map.get m2 k = Some v2 ->
        map.get m3 k = Some v3 ->
        R k v1 v2 v3 -> R' k v1 v2 v3) ->
    Forall3_map R' m1 m2 m3.
  Proof.
    intros H HRR k. specialize (H k).
    destruct (map.get m1 k) as [v1|] eqn:E1; destruct (map.get m2 k) as [v2|] eqn:E2;
      destruct (map.get m3 k) as [v3|] eqn:E3; try exact H.
    apply HRR; assumption.
  Qed.

  Lemma Forall3_map_impl (R R' : key -> value1 -> value2 -> value3 -> Prop)
    (m1 : mp1) (m2 : mp2) (m3 : mp3) :
    Forall3_map R m1 m2 m3 ->
    (forall k v1 v2 v3, R k v1 v2 v3 -> R' k v1 v2 v3) ->
    Forall3_map R' m1 m2 m3.
  Proof. eauto using Forall3_map_impl_strong. Qed.

  Lemma Forall3_map_put_l R (m1 : mp1) (m2 : mp2) (m3 : mp3) k v1 v2 v3 :
    Forall3_map (fun k' w1 w2 w3 => k <> k' -> R k' w1 w2 w3) m1 m2 m3 ->
    map.get m2 k = Some v2 ->
    map.get m3 k = Some v3 ->
    R k v1 v2 v3 ->
    Forall3_map R (map.put m1 k v1) m2 m3.
  Proof.
    intros H Hg2 Hg3 HR k0. specialize (H k0). rewrite map.get_put_dec. destr (eqb k k0).
    - subst. rewrite Hg2, Hg3. exact HR.
    - destruct (map.get m1 k0) as [w1|]; destruct (map.get m2 k0) as [w2|];
        destruct (map.get m3 k0) as [w3|]; try exact H.
      apply H. assumption.
  Qed.

  Lemma Forall3_map_put_m R (m1 : mp1) (m2 : mp2) (m3 : mp3) k v1 v2 v3 :
    Forall3_map (fun k' w1 w2 w3 => k <> k' -> R k' w1 w2 w3) m1 m2 m3 ->
    map.get m1 k = Some v1 ->
    map.get m3 k = Some v3 ->
    R k v1 v2 v3 ->
    Forall3_map R m1 (map.put m2 k v2) m3.
  Proof.
    intros H Hg1 Hg3 HR k0. specialize (H k0). rewrite map.get_put_dec. destr (eqb k k0).
    - subst. rewrite Hg1, Hg3. exact HR.
    - destruct (map.get m1 k0) as [w1|]; destruct (map.get m2 k0) as [w2|];
        destruct (map.get m3 k0) as [w3|]; try exact H.
      apply H. assumption.
  Qed.

  Lemma Forall3_map_put_r R (m1 : mp1) (m2 : mp2) (m3 : mp3) k v1 v2 v3 :
    Forall3_map (fun k' w1 w2 w3 => k <> k' -> R k' w1 w2 w3) m1 m2 m3 ->
    map.get m1 k = Some v1 ->
    map.get m2 k = Some v2 ->
    R k v1 v2 v3 ->
    Forall3_map R m1 m2 (map.put m3 k v3).
  Proof.
    intros H Hg1 Hg2 HR k0. specialize (H k0). rewrite map.get_put_dec. destr (eqb k k0).
    - subst. rewrite Hg1, Hg2. exact HR.
    - destruct (map.get m1 k0) as [w1|]; destruct (map.get m2 k0) as [w2|];
        destruct (map.get m3 k0) as [w3|]; try exact H.
      apply H. assumption.
  Qed.

  Lemma Forall3_map_get_l R (m1 : mp1) (m2 : mp2) (m3 : mp3) k v1 :
    Forall3_map R m1 m2 m3 ->
    map.get m1 k = Some v1 ->
    exists v2 v3, map.get m2 k = Some v2 /\ map.get m3 k = Some v3 /\ R k v1 v2 v3.
  Proof.
    intros H Hget. specialize (H k). rewrite Hget in H.
    destruct (map.get m2 k) as [v2|]; destruct (map.get m3 k) as [v3|]; try contradiction.
    exists v2, v3. split; [reflexivity | split; [reflexivity | exact H]].
  Qed.

  Lemma Forall3_map_get_m R (m1 : mp1) (m2 : mp2) (m3 : mp3) k v2 :
    Forall3_map R m1 m2 m3 ->
    map.get m2 k = Some v2 ->
    exists v1 v3, map.get m1 k = Some v1 /\ map.get m3 k = Some v3 /\ R k v1 v2 v3.
  Proof.
    intros H Hget. specialize (H k). rewrite Hget in H.
    destruct (map.get m1 k) as [v1|]; destruct (map.get m3 k) as [v3|]; try contradiction.
    exists v1, v3. split; [reflexivity | split; [reflexivity | exact H]].
  Qed.

  Lemma Forall3_map_get_r R (m1 : mp1) (m2 : mp2) (m3 : mp3) k v3 :
    Forall3_map R m1 m2 m3 ->
    map.get m3 k = Some v3 ->
    exists v1 v2, map.get m1 k = Some v1 /\ map.get m2 k = Some v2 /\ R k v1 v2 v3.
  Proof.
    intros H Hget. specialize (H k). rewrite Hget in H.
    destruct (map.get m1 k) as [v1|]; destruct (map.get m2 k) as [v2|]; try contradiction.
    exists v1, v2. split; [reflexivity | split; [reflexivity | exact H]].
  Qed.

  Definition Forall4_map (R : key -> value1 -> value2 -> value3 -> value4 -> Prop)
    (m1 : mp1) (m2 : mp2) (m3 : mp3) (m4 : mp4) : Prop :=
    forall k,
      match map.get m1 k, map.get m2 k, map.get m3 k, map.get m4 k with
      | None, None, None, None => True
      | Some v1, Some v2, Some v3, Some v4 => R k v1 v2 v3 v4
      | _, _, _, _ => False
      end.
End Maps.

Section ListValuedMap.
  Context {key A : Type}.
  Context {mp : map.map key (list A)} {mp_ok : map.ok mp}.
  Context {key_eqb : Eqb key} {key_eqb_ok : Eqb_ok key_eqb}.

  Lemma concat_values_put (m : mp) k w :
    Permutation (concat (values (map.put m k w))) (w ++ concat (values (map.remove m k))).
  Proof.
    eapply Permutation_trans; [ apply Permutation_concat, values_put | ].
    cbn [concat]. apply Permutation_refl.
  Qed.

  Lemma concat_values_get (m : mp) k v0 :
    map.get m k = Some v0 ->
    Permutation (concat (values m)) (v0 ++ concat (values (map.remove m k))).
  Proof.
    intros H. eapply Permutation_trans; [ apply Permutation_concat, (values_remove _ _ _ H) | ].
    cbn [concat]. apply Permutation_refl.
  Qed.

  Lemma incl_concat_values (m : mp) k v0 :
    map.get m k = Some v0 -> incl v0 (concat (values m)).
  Proof.
    intros H x Hx. eapply Permutation_in.
    - apply Permutation_sym, (concat_values_get _ _ _ H).
    - apply in_or_app. left. exact Hx.
  Qed.

  Lemma In_concat_values (m : mp) x :
    In x (concat (values m)) <-> exists k v, map.get m k = Some v /\ In x v.
  Proof.
    rewrite in_concat. split.
    - intros (vs & Hvs & Hx). apply In_values in Hvs. destruct Hvs as (k & Hget). eauto.
    - intros (k & v & Hget & Hx). exists v. split; [ apply In_values; eauto | exact Hx ].
  Qed.
End ListValuedMap.

Section MapKeysInj.
  Context {key key' value : Type}.
  Context {mp : map.map key value} {mp_ok : map.ok mp}.
  Context {mp' : map.map key' value} {mp'_ok : map.ok mp'}.
  Context {key_eqb : Eqb key} {key_eqb_ok : Eqb_ok key_eqb}.
  Context {key'_eqb : Eqb key'} {key'_eqb_ok : Eqb_ok key'_eqb}.

  (* Rekeying by an injective [g] permutes the value multiset (no collisions). *)
  Lemma values_map_keys (g : key -> key') (Hinj : forall a b, g a = g b -> a = b) (m : mp) :
    Permutation (values (map.map_keys (map' := mp') g m)) (values m).
  Proof.
    enough (Permutation (values (map.map_keys (map' := mp') g m)) (values m)
            /\ (forall j, map.get (map.map_keys (map' := mp') g m) (g j) = map.get m j))
      as [H _] by exact H.
    unfold map.map_keys.
    apply (map.fold_spec (fun m0 r => Permutation (values r) (values m0)
                                      /\ (forall j, map.get r (g j) = map.get m0 j))).
    - split; [ rewrite !values_empty; reflexivity | intro j; rewrite !map.get_empty; reflexivity ].
    - intros k v m0 r Hk [HP Hget]. split.
      + transitivity (v :: values r).
        { apply values_put_None. rewrite Hget. exact Hk. }
        transitivity (v :: values m0); [ apply perm_skip; exact HP | ].
        symmetry. apply values_put_None. exact Hk.
      + intro j. rewrite !map.get_put_dec, Hget, (eqb_map_inj g Hinj). reflexivity.
  Qed.
End MapKeysInj.

Lemma Forall2_map_dup {key value} {mp : map.map key value}
  (R : key -> value -> value -> Prop) (m : mp) :
  Forall_map (fun k v => R k v v) m ->
  Forall2_map R m m.
Proof.
  intros H k. destruct (map.get m k) as [v|] eqn:E.
  - exact (H k v E).
  - exact I.
Qed.

Lemma Forall2_map_refl {key value} {mp : map.map key value}
  (R : key -> value -> value -> Prop) (m : mp) :
  (forall k v, R k v v) ->
  Forall2_map R m m.
Proof. intros H k. destruct (map.get m k); [ apply H | exact I ]. Qed.

Lemma Forall2_map_trans {key value} {mp : map.map key value}
  (R : key -> value -> value -> Prop) (m1 m2 m3 : mp) :
  (forall k a b c, R k a b -> R k b c -> R k a c) ->
  Forall2_map R m1 m2 -> Forall2_map R m2 m3 -> Forall2_map R m1 m3.
Proof.
  intros Htrans H12 H23 k. specialize (H12 k); specialize (H23 k).
  destruct (map.get m1 k), (map.get m2 k), (map.get m3 k);
    try contradiction; try exact I. eapply Htrans; eassumption.
Qed.

Lemma Forall3_map_dup_23 {key value1 value2}
  {mp1 : map.map key value1} {mp2 : map.map key value2}
  (R : key -> value1 -> value2 -> value2 -> Prop) (m1 : mp1) (m2 : mp2) :
  Forall2_map (fun k v1 v2 => R k v1 v2 v2) m1 m2 ->
  Forall3_map R m1 m2 m2.
Proof.
  intros H k. specialize (H k).
  destruct (map.get m1 k) as [v1|]; destruct (map.get m2 k) as [v2|]; exact H.
Qed.

Section Map.
  Context {key value : Type} {mp : map.map key value} {mp_ok : map.ok mp}.
  Context {value' : Type} {mp' : map.map key value'} {mp'_ok : map.ok mp'}.
  Context {key_eqb : Eqb key} {key_eqb_ok : Eqb_ok key_eqb}.
  Implicit Type m : mp.

  Definition preimage m (test : _ -> bool) :=
    map.fold (fun (l : list key) k v => if test v then k :: l else l) [] m.

  Definition map_values' (f : key -> value -> value') (m : mp) : mp' :=
    map.fold (fun (m' : mp') k v => map.put m' k (f k v)) map.empty m.

  (*d is a default value... basically, we consider the map to be total, with not-included values mapping to d*)
  Definition mupd_total d m k f :=
    match map.get m k with
    | Some v => map.put m k (f v)
    | None => map.put m k (f d)
    end.

  Definition mupd m k f :=
    match map.get m k with
    | Some v => map.put m k (f v)
    | None => m
    end.

  Definition val_sat (m : mp) (k : key) (P : value -> Prop) : Prop :=
    exists v, map.get m k = Some v /\ P v.

  Definition vals_sat (m1 : mp) (m2 : mp') (k : key) (P : value -> value' -> Prop) : Prop :=
    exists v1 v2, map.get m1 k = Some v1 /\ map.get m2 k = Some v2 /\ P v1 v2.

  Lemma get_mupd (m : mp) (k : key) (f : value -> value) (k' : key) :
    map.get (mupd m k f) k' =
      if eqb k k' then option_map f (map.get m k) else map.get m k'.
  Proof.
    cbv [mupd]. destruct (map.get m k) as [v|] eqn:E; cbn [option_map].
    - rewrite map.get_put_dec. reflexivity.
    - destr (eqb k k'); [subst; exact E | reflexivity].
  Qed.

  Lemma get_map_values' (f : key -> value -> value') (m : mp) (k : key) :
    map.get (map_values' f m) k = option_map (f k) (map.get m k).
  Proof.
    cbv [map_values']. revert k.
    eapply map.fold_spec with
      (P := fun m acc =>
              forall k, map.get acc k = option_map (f k) (map.get m k)).
    - intros k0. rewrite ?map.get_empty. reflexivity.
    - intros k0 v m0 acc Hnone IH k1.
      rewrite ?map.get_put_dec. destr (eqb k0 k1).
      + reflexivity.
      + apply IH.
  Qed.

  Lemma map_values'_put (f : key -> value -> value') (m : mp) k v :
    map_values' f (map.put m k v) = map.put (map_values' f m) k (f k v).
  Proof.
    apply map.map_ext. intro j.
    rewrite get_map_values', !map.get_put_dec, get_map_values'.
    destr (eqb k j); cbn [option_map]; congruence.
  Qed.

  Lemma map_values'_remove (f : key -> value -> value') (m : mp) k :
    map_values' f (map.remove m k) = map.remove (map_values' f m) k.
  Proof.
    apply map.map_ext. intro j.
    rewrite get_map_values', !map.get_remove_dec, get_map_values'.
    destr (eqb k j); cbn [option_map]; congruence.
  Qed.

  Lemma keys_eq_tuples (m : mp) : map.keys m = List.map fst (map.tuples m).
  Proof.
    unfold map.keys, map.tuples.
    eapply map.fold_two_spec with (P := fun _ l1 l2 => l1 = List.map fst l2).
    - reflexivity.
    - intros k v m0 r1 r2 _ IH. cbn [List.map fst]. rewrite IH. reflexivity.
  Qed.

  Lemma Forall2_map_map_values'_r {value1} {mp1 : map.map key value1}
      (R' : key -> value1 -> value' -> Prop)
      (g : key -> value -> value') (m1 : mp1) (m2 : mp) :
    Forall2_map (fun k v1 v2 => R' k v1 (g k v2)) m1 m2 ->
    Forall2_map R' m1 (map_values' g m2).
  Proof.
    intros H k. specialize (H k). rewrite get_map_values'. revert H.
    destruct (map.get m1 k); destruct (map.get m2 k); cbn [option_map]; auto.
  Qed.

  Lemma Forall2_map_map_values'_l {value1} {mp1 : map.map key value1}
      (R' : key -> value' -> value1 -> Prop)
      (g : key -> value -> value') (m1 : mp) (m2 : mp1) :
    Forall2_map (fun k v1 v2 => R' k (g k v1) v2) m1 m2 ->
    Forall2_map R' (map_values' g m1) m2.
  Proof.
    intros H k. specialize (H k). rewrite get_map_values'. revert H.
    destruct (map.get m1 k); destruct (map.get m2 k); cbn [option_map]; auto.
  Qed.

  Lemma Forall2_map_mupd_r {value1} {mp1 : map.map key value1}
      (R : key -> value1 -> value -> Prop) (k0 : key) (g : value -> value)
      (m1 : mp1) (m2 : mp) :
    (forall v1 v2, R k0 v1 v2 -> R k0 v1 (g v2)) ->
    Forall2_map R m1 m2 ->
    Forall2_map R m1 (mupd m2 k0 g).
  Proof.
    intros Hg H k. specialize (H k). rewrite get_mupd. destr (eqb k0 k); [| exact H].
    revert H. destruct (map.get m1 k); destruct (map.get m2 k); cbn [option_map]; auto using Hg.
  Qed.

Definition set_contains m k :=
  match map.get m k with
  | Some _ => true
  | None => false
  end.

Lemma extends_putmany_putmany (m1 m2 m : mp) :
  map.extends m1 m2 ->
  map.extends (map.putmany m1 m) (map.putmany m2 m).
Proof.
  intros H. cbv [map.extends]. intros x y Hx.
  edestruct (map.putmany_spec m2 m x) as [H'|H'].
  - destruct H' as [v (H1&H2)]. rewrite Hx in H2. invert H2.
    apply map.get_putmany_right. assumption.
  - destruct H' as (H1&H2). rewrite map.get_putmany_left.
    + rewrite H2 in Hx. apply H. assumption.
    + assumption.
Qed.

Lemma extends_putmany_right (m1 m2 : mp) :
  map.extends (map.putmany m1 m2) m2.
Proof.
  intros k v H. edestruct (map.putmany_spec m1 m2 k) as [H'|H'].
  - destruct H' as (v0&H1&H2). rewrite H in H1. invert H1. exact H2.
  - rewrite H in H'. destruct H' as [H' _]. discriminate H'.
Qed.

Lemma extends_putmany_left (m1 m2 : mp) :
  map.disjoint m1 m2 ->
  map.extends (map.putmany m1 m2) m1.
Proof.
  intros H1 k v H2. edestruct (map.putmany_spec m1 m2 k) as [H'|H'].
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

Lemma extends_None (m1 m2 : mp) k :
  map.extends m1 m2 ->
  map.get m1 k = None ->
  map.get m2 k = None.
Proof.
  intros. destr (map.get m2 k); auto. apply H in E. congruence.
Qed.

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
  - intros k0 v m0 r H H0. rewrite map.get_put_dec. destr (eqb k0 k).
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
  rewrite map.get_put_dec. destr (eqb k k0).
  - rewrite lookup_add_eq; auto.
  - rewrite lookup_add_ne; auto. apply fmap_of_spec.
Qed.

Lemma fmap_of_extends_includes m1 m2 :
  map.extends m2 m1 ->
  fmap_of m1 $<= fmap_of m2.
Proof.
  intros H. apply includes_intro. intros k v Hkv.
  rewrite fmap_of_spec in *. auto.
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
  epose proof (map.only_differ_putmany _ _ _ _ H) as H'.
  epose proof (map.only_differ_putmany _ _ _ _ H0) as H0'.
  apply map.map_ext. intros k.
  specialize (H' k). specialize (H0' k). eassert (H1: _ \/ _).
  { destruct H' as [H'|H']. 1: left; exact H'. destruct H0' as [H0'|H0'].
    1: left; exact H0'. right. exact (conj H' H0'). }
  clear H0' H'. destruct H1 as [H1|H1].
  - cbv [PropSet.elem_of PropSet.of_list] in H1. rewrite Forall_forall in H5.
    apply H5. assumption.
  - fwd. rewrite map.get_put_dec in H1p0, H1p1. destr (eqb a k).
    + apply H4.
    + rewrite <- H1p0, <- H1p1. reflexivity.
Qed.

Lemma of_list_zip_ext (m1 m2 : mp) ks vs vs' :
  map.of_list_zip ks vs = Some m1 ->
  map.of_list_zip ks vs' = Some m2 ->
  Forall (agree_on m1 m2) ks ->
  m1 = m2.
Proof. intros. eapply putmany_of_list_ext; eauto. Qed.

Lemma of_list_zip_ext' (m1 m2 : mp) ks vs vs' k :
  map.of_list_zip ks vs = Some m1 ->
  map.of_list_zip ks vs' = Some m2 ->
  (In k ks -> map.get m1 k = map.get m2 k) ->
  map.get m1 k = map.get m2 k.
Proof.
  intros H1 H2 H3. do 2 erewrite map.get_of_list_zip in * by eassumption.
  destruct (map.zipped_lookup _ vs _) eqn:E1, (map.zipped_lookup _ vs' _) eqn:E2; auto.
  - apply H3. exact (map.zipped_lookup_Some_in _ _ _ _ E1).
  - apply map.zipped_lookup_Some_in in E1.
    apply map.zipped_lookup_None_notin in E2; auto. Search map.putmany_of_list Datatypes.length.
    eapply map.putmany_of_list_zip_sameLength. eassumption.
  - apply map.zipped_lookup_Some_in in E2.
    apply map.zipped_lookup_None_notin in E1; auto.
    eapply map.putmany_of_list_zip_sameLength. eassumption.
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
  - rewrite map.get_put_dec in H. destr (eqb k0 k); intuition congruence.
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
  - apply IHkvs in H. fwd. rewrite map.get_put_dec. destr (eqb k0 k); eauto.
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
  apply map.zipped_lookup_Some_in in E. exfalso. auto.
Qed.

Definition disjointb (m1 m2 : mp) :=
  map.forallb (fun k1 _ => map.forallb (fun k2 _ => negb (eqb k1 k2)) m2) m1.

Lemma disjointb_disjoint m1 m2 :
  disjointb m1 m2 = true ->
  map.disjoint m1 m2.
Proof.
  cbv [map.disjoint]. intros H k **. eapply map.get_forallb in H; eauto.
  eapply map.get_forallb in H; eauto. destr (eqb k k); simpl in *; congruence.
Qed.

Definition agree_on_overlap (m1 m2 : mp) : Prop :=
  forall k v1 v2, map.get m1 k = Some v1 -> map.get m2 k = Some v2 -> v1 = v2.

Context {value_eqb : Eqb value} {value_eqb_ok : Eqb_ok value_eqb}.

Definition map_contains m k v :=
  match map.get m k with
  | Some v' => value_eqb v v'
  | None => false
  end.

Definition agree_on_overlapb (m1 m2 : mp) : bool :=
  map.forallb (fun k v1 =>
                 match map.get m2 k with
                 | Some v2 => value_eqb v1 v2
                 | None => true
                 end) m1.

Lemma agree_on_overlapb_sound m1 m2 :
  agree_on_overlapb m1 m2 = true ->
  agree_on_overlap m1 m2.
Proof.
  cbv [agree_on_overlapb agree_on_overlap]. intros H k v1 v2 H1 H2.
  eapply map.get_forallb in H; eauto.
  rewrite H2 in H.
  destr (value_eqb v1 v2); [reflexivity | discriminate].
Qed.

Definition compatible_union (m1 m2 : mp) : option mp :=
  if agree_on_overlapb m1 m2 then Some (map.putmany m1 m2) else None.

Lemma compatible_union_sound (m1 m2 m : mp) :
  compatible_union m1 m2 = Some m ->
  agree_on_overlap m1 m2 /\ m = map.putmany m1 m2.
Proof.
  cbv [compatible_union].
  destruct (agree_on_overlapb m1 m2) eqn:E; intros H.
  - inversion H; subst; clear H.
    split; [|reflexivity].
    apply agree_on_overlapb_sound. assumption.
  - discriminate H.
Qed.

Definition compatible_union_of_list (ms : list mp) : option mp :=
  fold_right (fun x y => option_coalesce (option_map (compatible_union x) y)) (Some map.empty) ms.

Definition compatible_union_of_list_option ms :=
  option_coalesce (option_map compatible_union_of_list (option_all ms)).

Lemma compatible_union_get m1 m2 m k v :
  compatible_union m1 m2 = Some m ->
  map.get m k = Some v <-> map.get m1 k = Some v \/ map.get m2 k = Some v.
Proof.
  intros H. apply compatible_union_sound in H. destruct H as [Hagree ->].
  rewrite map.get_putmany_dec.
  destruct (map.get m2 k) eqn:E2.
  - split; intros H.
    + invert_list_stuff. auto.
    + destruct H.
      * f_equal. symmetry. eapply Hagree; eassumption.
      * invert_list_stuff. reflexivity.
  - split; auto. intros [?|?]; invert_list_stuff; auto.
Qed.

Lemma compatible_union_of_list_get ms m :
  compatible_union_of_list ms = Some m ->
  forall k v, map.get m k = Some v <-> (exists m', In m' ms /\ map.get m' k = Some v).
Proof.
  revert m. induction ms as [| m_head ms' IH]; simpl; intros m H k v.
  - invert_list_stuff. split; intros H.
    + rewrite map.get_empty in H. discriminate H.
    + destruct H as [m' [Hin _]]. contradiction.
  - destruct (compatible_union_of_list ms') as [m_tail|] eqn:Etail; [|discriminate H].
    simpl in H. fwd.
    eapply compatible_union_get in E.
    split; intros Hget.
    + apply E in Hget. destruct Hget as [Hhead | Htail].
      * eauto.
      * apply IH in Htail; auto. fwd. eauto.
    + fwd. destruct Hgetp0 as [Heq | Hin].
      * subst. apply E. auto.
      * apply E. right. apply IH; eauto.
Qed.
End Map.

(* How [concat (values (map_values' F ·))] transforms under [put]/[get] — the
   general fact behind every fwd_total / output_total step lemma. *)
Section ConcatValuesMapValues.
  Context {key value A : Type}.
  Context {mp : map.map key value} {mp_ok : map.ok mp}.
  Context {mp' : map.map key (list A)} {mp'_ok : map.ok mp'}.
  Context {key_eqb : Eqb key} {key_eqb_ok : Eqb_ok key_eqb}.

  Lemma concat_values_map_values'_put (F : key -> value -> list A) (m : mp) k w :
    Permutation (concat (values (map_values' (mp' := mp') F (map.put m k w))))
                (F k w ++ concat (values (map_values' (mp' := mp') F (map.remove m k)))).
  Proof.
    rewrite map_values'_put, map_values'_remove. apply concat_values_put.
  Qed.

  Lemma concat_values_map_values'_get (F : key -> value -> list A) (m : mp) k v :
    map.get m k = Some v ->
    Permutation (concat (values (map_values' (mp' := mp') F m)))
                (F k v ++ concat (values (map_values' (mp' := mp') F (map.remove m k)))).
  Proof.
    intros H. rewrite map_values'_remove.
    apply concat_values_get. rewrite get_map_values', H. reflexivity.
  Qed.
End ConcatValuesMapValues.
