From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From ATL Require Import Tactics FrapWithoutSets.
From Datalog Require Import Tactics List.
From coqutil Require Import Tactics Tactics.fwd Datatypes.List.

From Stdlib Require Import Relations.Relation_Operators Relations.Operators_Properties Relations.Relations.
From Stdlib Require Import Wellfounded.Union.
From Stdlib Require Import Wellfounded.Inclusion.
From Stdlib Require Import Wellfounded Wellfounded.Wellfounded Wellfounded.Transitive_Closure.
From Stdlib Require Import Wellfounded.Inverse_Image.

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

(*adding g1 to g2 definitely doesn't create any cycles*)
Definition no_cycles g1 g2 :=
  Forall (not_in_snd g2) (map fst g1).

Definition edge_rel g x y := In (y, x) g.

Lemma edge_rel_weaken g1 g2 x y :
  edge_rel g1 x y ->
  incl g1 g2 ->
  edge_rel g2 x y.
Proof. cbv [edge_rel incl]. auto. Qed.

Definition dag g := well_founded (edge_rel g).
Definition dag_alt g := well_founded (fun x y => edge_rel g y x).
Lemma wf_empty {T : Type} : well_founded (fun (_ _ : T) => False).
Proof. intro. constructor. contradiction. Qed.

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
Hint Constructors dag' dag'_alt : core.

Lemma subrel_Acc_strong {X : Type} P R1 R2 (z : X) :
  Acc R2 z ->
  P z ->
  (forall x y, R1 x y -> P y -> R2 x y /\ P x) ->
  Acc R1 z.
Proof.
  intros H1 H2 H. induction H1. constructor. intros y Hy.
  specialize (H _ _ ltac:(eassumption) ltac:(eassumption)). fwd. auto.
Qed.

Lemma Acc_not_symm {X : Type} (R : X -> X -> Prop) x :
  Acc R x ->
  R x x ->
  False.
Proof. induction 1; eauto. Qed.

Lemma dag_cons g1 g2 e :
  dag (g1 ++ g2) ->
  not_in_snd (e :: g1 ++ g2) (fst e) ->
  dag (g1 ++ e :: g2).
Proof.
  intros IHdag' H0 H.
  constructor. intros y Hy. cbv [edge_rel] in Hy.
    eapply subrel_Acc_strong with (P := fun x => x <> fst e).
    + apply IHdag'.
    + intros H'. subst. apply H0. apply in_map_iff.
      eexists (_, _). split; [reflexivity|].
      simpl. rewrite in_app_iff in *. simpl in Hy.
      destruct Hy as [? | [?|?] ]; eauto.
    + intros. cbv [edge_rel] in *. clear Hy. rewrite in_app_iff in *. simpl in *. split.
      -- destruct H1 as [? | [?|?] ]; auto. subst. simpl in H2. congruence.
      -- intro. subst. apply H0. apply in_map_iff.
         eexists (_, _). split; [reflexivity|].
         simpl. rewrite in_app_iff. destruct H1 as [? | [?|?] ]; eauto.
Qed.

Lemma dag'_dag g :
  dag' g ->
  dag g.
Proof.
  induction 1.
  - constructor. destruct 1.
  - apply dag_cons; assumption.
Qed.

Lemma dag_incl g1 g2 :
  dag g2 ->
  incl g1 g2 ->
  dag g1.
Proof.
  cbv [incl dag edge_rel].
  intros H1 H2. eapply wf_incl; eauto.
  cbv [inclusion]. simpl. eauto.
Qed.

Lemma dag_irrefl g v :
  dag g ->
  clos_trans _ (edge_rel g) v v ->
  False.
Proof.
  intros H1 H2. eapply Acc_not_symm. 2: exact H2. apply Acc_clos_trans. apply H1.
Qed.

(* Lemma dag_dag_alt g : *)
(*   dag g -> *)
(*   dag_alt g. *)
(* Proof. *)
(*   induction g. *)
(*   - intros. apply wf_empty. *)
(*   - intros. specialize' IHg. *)
(*     { eauto using dag_incl with incl. } *)
(*     intros v. specialize (IHg v). induction IHg as [v H1 H2]. clear H1. *)
(*     constructor. intros u Hu. cbv [edge_rel] in Hu. simpl in Hu. *)
(*     destruct Hu as [Hu|Hu]. *)
(*     + subst. apply H2.  *)
(*       cbv [dag_alt]. *)
(*   intros H. cbv [dag_alt]. intro v.  *)
(*   Search well_founded. Check wf_inverse_rel. *)


Lemma no_cycles_commut g1 g2 :
  no_cycles g2 g1 ->
  commut _ (edge_rel g1) (edge_rel g2).
Proof.
  cbv [no_cycles]. intros H. cbv [commut]. intros x y Hx z Hz.
  exfalso. cbv [edge_rel] in Hx, Hz. rewrite Forall_forall in H.
  apply in_fst in Hz. apply H in Hz. cbv [not_in_snd] in Hz.
  apply Hz. apply in_map_iff. eexists (_, _). simpl. eauto.
Qed.

Lemma dag_app g1 g2 :
  no_cycles g1 g2 ->
  dag g1 ->
  dag g2 ->
  dag (g1 ++ g2).
Proof.
  intros H1 H2 H3. eapply wf_incl; cycle 1.
  - eapply wf_union; eauto using no_cycles_commut.
  - cbv [inclusion]. intros ? ? H. apply in_app_iff in H.
    cbv [union edge_rel]. destruct H; auto.
Qed.

Hint Constructors clos_trans : core.
Lemma clos_trans_monotone {T : Type} (R1 R2 : T -> T -> Prop) :
  (forall x y, R1 x y -> R2 x y) ->
  (forall x y, clos_trans _ R1 x y -> clos_trans _ R2 x y).
Proof. induction 2; eauto. Qed.

Lemma irrefl_dag g :
  (forall v, clos_trans _ (edge_rel g) v v -> False) ->
  dag g.
Proof.
  induction g.
  - intros. apply wf_empty.
  - intros H. specialize' IHg.
    { intros. eapply H. eapply clos_trans_monotone; [|eassumption].
      intros. eapply edge_rel_weaken; [eassumption|]. auto with incl. }
    pose proof IHg as Hwf.
    intros v. specialize (IHg v). induction IHg as [v _ Hv].
    constructor. intros u Hu. cbv [edge_rel] in Hu. simpl in Hu.
    destruct Hu as [Hu|Hu]; cycle 1.
    { apply Hv. apply Hu. }
    subst.
    eapply subrel_Acc_strong with (P := fun v' => clos_trans _ (edge_rel ((v, u) :: g)) v' v).
    + apply Hwf.
    + apply t_step. cbv [edge_rel]. simpl. auto.
    + intros x y H1 H2. cbv [edge_rel] in H1. simpl in H1.
      destruct H1 as [H1|H1].
      { exfalso. invert H1. eapply H. apply H2. }
      split.
      -- exact H1.
      -- eapply t_trans. 2: eassumption. apply t_step. cbv [edge_rel]. simpl. auto.
Qed.

Lemma clos_trans_swap {T : Type} (R1 R2 : T -> T -> Prop) :
  (forall x y, R1 x y -> R2 y x) ->
  forall x y, clos_trans _ R1 x y -> clos_trans _ R2 y x.
Proof. induction 2; eauto. Qed.

Lemma dag_dag_alt g :
  dag g ->
  dag_alt g.
Proof.
  intros H. enough (H': dag (map (fun '(x, y) => (y, x)) g)).
  - eapply wf_incl; [|eassumption]. cbv [inclusion]. intros.
    cbv [edge_rel] in *. apply in_map_iff. eexists (_, _). eauto.
  - apply irrefl_dag. intros. eapply dag_irrefl; [eassumption|].
    eapply clos_trans_swap; [|eassumption]. intros ? ? H'. cbv [edge_rel] in *.
    apply in_map_iff in H'. fwd. auto.
Qed.

Lemma dag_alt_dag g :
  dag_alt g ->
  dag g.
Proof.
  intros H. enough (H': dag (map (fun '(x, y) => (y, x)) g)).
  - eapply irrefl_dag. intros. eapply dag_irrefl; [eassumption|].
    eapply clos_trans_swap; [|eassumption]. intros ? ? H1. cbv [edge_rel] in *.
    apply in_map_iff. fwd. eexists (_, _). eauto.
  - eapply wf_incl; [|eassumption]. cbv [inclusion]. intros ? ? H'.
    cbv [edge_rel] in *. apply in_map_iff in H'. fwd. auto.
Qed.

Lemma concl_same_dag v g :
  Forall (fun '(x, y) => x = v /\ y <> v) g ->
  dag g.
Proof.
  intros H. constructor. intros y Hy. constructor. intros z Hz.
  exfalso. rewrite Forall_forall in H. apply H in Hy, Hz. fwd. congruence.
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

Lemma clos_trans_list x y l g :
  path g x l ->
  In y l ->
  clos_trans _ (edge_rel g) y x.
Proof.
  intros H. induction H.
  - simpl. contradiction.
  - intros [H'|H']; subst; eauto.
Qed.

Lemma dags_have_no_cycles' x l g :
  dag g ->
  path g x l ->
  ~In x l.
Proof.
  intros H1 H2 H3. eapply Acc_not_symm.
  - apply Acc_clos_trans. apply H1.
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
  apply path_incl in H2. rewrite <- (length_map snd).
  invert H1. apply NoDup_incl_length; assumption.
Qed.
End __.
