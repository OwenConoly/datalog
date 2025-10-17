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

Lemma not_in_snd_cons v e g :
  v <> snd e ->
  not_in_snd g v ->
  not_in_snd (e :: g) v.
Proof.
  cbv [not_in_snd]. intros H1 H2 H3. simpl in H3. destruct H3; subst; auto.
Qed.

Lemma not_in_snd_nil v :
  not_in_snd [] v.
Proof. cbv [not_in_snd]. simpl. auto. Qed.

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

Lemma concl_same_dag v g :
  Forall (fun '(x, y) => x = v /\ y <> v) g ->
  dag g.
Proof.
  intros H. induction H; eauto. destruct x. fwd. constructor; eauto.
  simpl. apply not_in_snd_cons; auto. rewrite Forall_forall in H0.
  cbv [not_in_snd]. intros H'. rewrite in_map_iff in H'. fwd. apply H0 in H'p1.
  destruct x. fwd. eauto.
Qed.

Inductive path (g : list (V * V)) : V -> list V -> Prop :=
| path_nil x : path _ x []
| path_cons x y l :
  In (x, y) g ->
  path _ y l ->
  path _ x (y :: l).

Definition path_alt g l :=
  forall l1 x y l2,
    l = l1 ++ x :: y :: l2 ->
    In (x, y) g.

Lemma path_path_alt g x l :
  path g x l ->
  path_alt g (x :: l).
Proof.
  intros H. induction H.
  - cbv [path_alt]. intros. destruct l1; try discriminate H.
    destruct l1; discriminate H.
  - cbv [path_alt]. intros l1 x0 y0 l2 H'. destruct l1 as [|z l1].
    + simpl in H'. invert_list_stuff. assumption.
    + simpl in H'. invert_list_stuff. eapply IHpath. eassumption.
Qed.

Lemma path_alt_tl x l g :
  path_alt g (x :: l) ->
  path_alt g l.
Proof.
  cbv [path_alt] in *. intros. subst. eapply (H (_ :: _)). reflexivity.
Qed.
  
Lemma path_alt_path g x l :
  path_alt g (x :: l) ->
  path g x l.
Proof.
  revert x. induction l.
  - intros. constructor.
  - intros. constructor; eauto using path_alt_tl.
    eapply (H nil). reflexivity.
Qed.

Definition edge_rel g x y := In (y, x) g.

Lemma edge_rel_weaken g1 g2 x y :
  edge_rel g1 x y ->
  incl g1 g2 ->
  edge_rel g2 x y.
Proof. cbv [edge_rel incl]. auto. Qed.

Lemma dag_wf'' e g x :
  not_in_snd g (fst e) ->
  x <> fst e ->
  Acc (edge_rel g) x ->
  Acc (edge_rel (e :: g)) x.
Proof.
  intros H1 H2 H3. induction H3. constructor. intros y Hy. cbv [edge_rel] in Hy.
  simpl in Hy. destruct Hy as [Hy|Hy].
  { subst. simpl in *. congruence. }
  apply H0; auto. intros H'. subst. apply H1. apply in_map_iff. eexists. split; eauto.
  simpl. reflexivity.
Qed.

Lemma dag_wf g :
  dag g ->
  well_founded (edge_rel g).
Proof.
  intros H. induction H.
  - cbv [edge_rel]. simpl. intros ?. constructor. contradiction.
  - cbv [well_founded] in *. intros x. constructor. intros y Hy.
    apply dag_wf''; auto.
    + eauto with incl.
    + intros ?. subst. cbv [edge_rel] in Hy. cbv [not_in_snd] in H0. apply H0.
      apply in_map_iff. eexists (_, _). simpl. eauto.
Qed.

From Stdlib Require Import Relations.Relation_Operators Relations.Operators_Properties Relations.Relations.

Lemma clos_trans_list x y l g :
  path g x l ->
  In y l ->
  clos_trans _ (edge_rel g) y x.
Proof.
  intros H. induction H.
  - simpl. contradiction.
  - intros [H'|H'].
    + apply t_step. subst. assumption.
    + apply IHpath in H'. clear IHpath. eapply t_trans; eauto. apply t_step. assumption.
Qed.


Search clos_trans Acc. (*nothing?*)
Lemma Acc_clos_trans {X : Type} (R : X -> X -> Prop) x :
  Acc R x ->
  Acc (clos_trans _ R) x.
Proof.
  induction 1. constructor. intros y Hy. clear H. induction Hy; auto.
  apply IHHy1; auto. intros. apply IHHy2; auto. eauto using t_trans, t_step.
Qed.

Lemma Acc_not_symm {X : Type} (R : X -> X -> Prop) x :
  Acc R x ->
  R x x ->
  False.
Proof. induction 1; eauto. Qed.
      
Lemma dags_have_no_cycles' x l g :
  dag g ->
  path g x l ->
  ~In x l.
Proof.
  intros H1 H2 H3. eapply Acc_not_symm.
  - apply Acc_clos_trans. apply dag_wf. eassumption.
  - eapply clos_trans_list; eassumption.
Qed.

Lemma dags_have_no_cycles x l g :
  dag g ->
  path g x l ->
  NoDup (x :: l).
Proof.
  intros H. induction 1.
  - repeat constructor. simpl. auto.
  - constructor; [|assumption]. eapply dags_have_no_cycles'; eauto.
    constructor; assumption.
Qed.

Lemma path_incl x l g :
  path g x l ->
  incl l (map snd g).
Proof.
  induction 1; auto with incl. apply incl_cons; auto with incl.
  apply in_map_iff. eexists. split; eauto. reflexivity.
Qed.

Lemma dag_paths_short x l g :
  dag g ->
  path g x l ->
  length l <= length g.
Proof.
  intros H1 H2. eapply dags_have_no_cycles in H1; eauto.
  apply path_incl in H2. Search incl NoDup. rewrite <- (length_map snd).
  invert H1. apply NoDup_incl_length; assumption.
Qed.
End __.
