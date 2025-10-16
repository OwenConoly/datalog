From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Permutation.


From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics.

From Datalog Require Import Datalog Map Tactics Fp List.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List.

Import ListNotations.

Section __.
Context {V : Type}.
Implicit Type v : V.
Implicit Type e : V * V.
Implicit Type g : list (V * V).

Definition not_in_fst g v :=
  ~In v (map fst g).

Definition not_in_snd g v :=
  ~In v (map snd g).

(*adding g1 to g2 definitely doesn't create any cycles*)
Definition no_cycles g1 g2 :=
  Forall (not_in_snd g2) (map fst g1).

(*not only is it a dag, but it's in topological order*)
Inductive dag : list (V * V) -> Prop :=
| dag_nil : dag []
| dag_cons e g :
  dag g ->
  not_in_snd (e :: g) (fst e) ->
  dag (e :: g).

Inductive dag' : list (V * V) -> Prop :=
| dag'_nil : dag' []
| dag'_cons g1 g2 e :
  dag' (g1 ++ g2) ->
  not_in_snd (e :: g1 ++ g2) (fst e) ->
  dag' (g1 ++ e :: g2).

Inductive dag'_alt : list (V * V) -> Prop :=
| dag'_alt_nil : dag'_alt []
| dag'_alt_cons g1 g2 e :
  dag'_alt (g1 ++ g2) ->
  not_in_fst (e :: g1 ++ g2) (snd e) ->
  dag'_alt (g1 ++ e :: g2).

Hint Constructors dag dag' dag'_alt : core.

Lemma not_in_snd_app v g1 g2:
  not_in_snd g1 v ->
  not_in_snd g2 v ->
  not_in_snd (g1 ++ g2) v.
Proof.
  intros H1 H2. cbv [not_in_snd] in *. rewrite map_app. rewrite in_app_iff.
  intros [?|?]; auto.
Qed.

Lemma not_in_fst_incl v g1 g2 :
  not_in_fst g2 v ->
  incl g1 g2 ->
  not_in_fst g1 v.
Proof.
  intros H1 H2. cbv [not_in_fst] in *. eapply incl_map in H2. eauto.
Qed.

Lemma not_in_snd_incl v g1 g2 :
  not_in_snd g2 v ->
  incl g1 g2 ->
  not_in_snd g1 v.
Proof.
  intros H1 H2. cbv [not_in_snd] in *. eapply incl_map in H2. eauto.
Qed.

Hint Resolve not_in_snd_app not_in_snd_incl not_in_fst_incl : core.
(* Hint Extern 3 (In _ _) => let H := fresh "H" in eassert (incl _ _) as H; [|eapply H] : incl. *)

Lemma dag'_dag g' :
  dag' g' ->
  exists g, Permutation g g' /\ dag g.
Proof.
  intros H. induction H.
  - eauto with incl. 
  - fwd. exists (e :: g). split.
    + apply Permutation_cons_app. assumption.
    + constructor; auto. eapply not_in_snd_incl; eauto. auto with incl.
Qed.

Lemma dag_dag' g :
  dag g ->
  dag' g.
Proof.
  intros H. induction H; eauto. apply (dag'_cons nil); auto.
Qed.

Search Permutation repeat. (*wow that is exactly what i was looking for*)

Lemma dag'_permutation g1 g2 :
  Permutation g1 g2 ->
  dag' g1 ->
  dag' g2.
Proof.
  revert g2. remember (length g1) as n eqn:E. revert g1 E. induction n.
  - intros g1 E g2 H1 H2. apply Permutation_length in H1.
    destruct g2; simpl in *; try congruence. constructor.
  - intros g1 E g2 H1 H2. invert H2; try discriminate E.
    pose proof Permutation_in as H'. specialize H' with (1 := H1).
    specialize (H' e). specialize (H' ltac:(apply in_elt)).
    apply in_split in H'. fwd. apply Permutation_app_inv in H1. constructor.
    + eapply IHn; eauto. rewrite length_app in *. simpl in *. lia.
    + eapply not_in_snd_incl. 1: eauto with incl. auto with incl.
Qed.

Lemma dag'_consn n e g :
  not_in_snd (e :: g) (fst e) ->
  dag' g ->
  dag' (repeat e n ++ g).
Proof.
  intros. induction n.
  - assumption.
  - simpl. apply (dag'_cons nil); simpl; try assumption.
    eapply not_in_snd_incl; [eassumption|]. apply incl_cons; auto with incl.
    apply incl_app; auto with incl. cbv [incl]. intros r' Hr'. Search In repeat.
    apply repeat_spec in Hr'. subst. simpl. auto.
Qed.

Lemma dag'_incl g1 g2 :
  dag' g2 ->
  incl g1 g2 ->
  dag' g1.
Proof.
  intros H2 H1. revert g1 H1. induction H2; intros g0 H0.
  - apply incl_l_nil in H0. subst. constructor.
  - Search Permutation repeat. eassert (incl _ (e :: g1 ++ g2)) as H'.
    { eapply incl_tran; [eassumption|]. auto with incl. }
    clear H0. apply Permutation_incl_cons_inv_r in H'.
    fwd. eapply dag'_permutation; [apply Permutation_sym; eassumption|].
    apply dag'_consn.
    + eauto using not_in_snd_incl with incl.
    + apply IHdag'. assumption.
Qed.

Lemma dag'_app g1 g2 :
  no_cycles g1 g2 ->
  dag' g1 ->
  dag' g2 ->
  dag' (g1 ++ g2).
Proof.
  intros H1 H2 H3. cbv [no_cycles] in H1. rewrite Lists.List.Forall_map in H1. induction H2.
  - assumption.
  - rewrite <- app_assoc. simpl. apply Forall_app in H1. fwd.
    rewrite Forall_app in IHdag'. specialize (IHdag' ltac:(auto)).
    rewrite <- app_assoc in IHdag'. constructor; [assumption|].
    rewrite app_assoc. rewrite app_comm_cons. auto with incl.
Qed.

Definition swap {A B : Type} (x : A * B) := (snd x, fst x).

Lemma dag_at_start g e :
  dag g ->
  not_in_fst (e :: g) (snd e) ->
  dag (g ++ [e]).
Proof.
  intros H1. induction H1; intros H2.
  - simpl. repeat constructor. cbv [not_in_fst not_in_snd] in *.
    simpl in *. intros [?|?]; auto.
  - simpl. constructor.
    + apply IHdag. eauto with incl.
    + rewrite app_comm_cons. apply not_in_snd_app; auto. clear -H2.
      cbv [not_in_fst not_in_snd] in *. simpl. simpl in *. intros [?|?]; auto.
Qed.

Lemma dag'_at_start g e :
  dag' g ->
  not_in_fst (e :: g) (snd e) ->
  dag' (e :: g).
Proof.
  intros H1 H2. apply dag'_dag in H1. fwd. eapply dag_at_start in H1p1.
  2: { eapply not_in_fst_incl; eauto. auto with incl. }
  apply dag_dag' in H1p1. eapply dag'_incl; eauto. apply incl_cons; auto with incl.
  apply in_app_iff. simpl. auto.
Qed.
  
Lemma dag'_alt_dag' g :
  dag'_alt g ->
  dag' g.
Proof.
  intros H. induction H; auto.
  enough (dag' (e :: g1 ++ g2)).
  { eapply dag'_incl; eauto. Fail solve [eauto with incl]. auto with incl. (*what have i done*) }
  apply dag'_at_start; assumption.
Qed.

Lemma nis_swap_nif g v :
  not_in_snd g v ->
  not_in_fst (map swap g) v.
Proof.
  cbv [not_in_fst not_in_snd]. rewrite map_map. auto.
Qed.

Lemma nif_swap_nis g v :
  not_in_fst g v ->
  not_in_snd (map swap g) v.
Proof.
  cbv [not_in_fst not_in_snd]. rewrite map_map. auto.
Qed.

Lemma dag'_flip_to_alt g :
  dag' g ->
  dag'_alt (map swap g).
Proof.
  intros H. induction H.
  - simpl. constructor.
  - apply nis_swap_nif in H0. simpl in *. rewrite map_app in *. simpl. auto.
Qed.

Lemma dag'_alt_flip_to g :
  dag'_alt g ->
  dag' (map swap g).
Proof.
  intros H. induction H.
  - simpl. constructor.
  - apply nif_swap_nis in H0. simpl in *. rewrite map_app in *. simpl. auto.
Qed.

Lemma dag'_dag_alt g :
  dag' g ->
  dag'_alt g.
Proof.
  intros H. apply dag'_flip_to_alt in H. apply dag'_alt_dag' in H.
  apply dag'_flip_to_alt in H. rewrite map_map in H. erewrite map_ext, map_id in H.
  - assumption.
  - intros [? ?]. reflexivity.
Qed.

Lemma dag'_swap g :
  dag' g ->
  dag' (map swap g).
Proof.
  intros. apply dag'_alt_dag'. apply dag'_flip_to_alt. assumption.
Qed.
End __.
