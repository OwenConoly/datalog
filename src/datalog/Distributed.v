From Stdlib Require Import List.
From coqutil Require Import OmniSmallstepCombinators.
From Datalog Require Import Datalog Node Graph2WithIO IOGraph Smallstep List Eqb Tactics FinTypeclass.
From coqutil Require Import Tactics Tactics.fwd Eqb.
Import ListNotations.
Import node.

Section Distributed.
  Context `{params : datalog_params}.
  Context {node : nodeT} {node_eqb : Eqb node} {node_eqb_ok : Eqb_ok node_eqb} {node_finite : Fin.Fin node}.
  Context (graph_prog : node -> program).
  Context (Hmrv : forall n, program.meta_rules_valid (graph_prog n)).
  Context (is_input : rel -> bool).
  Context (Hp_good : forall n, Forall (fun R => is_input R = false) (program.concl_rels (graph_prog n))).

  #[local] Instance sender_label : sender_labelT := source.

  Definition rel_forward (d : destn) (R : rel) : bool :=
    match d with
    | output_destn => true (*TODO: don't output everything*)
    | node_destn nd => inb R (program.hyp_rels (graph_prog nd))
    end.

  Definition forward (s : source) (d : destn) (f : message) :=
    rel_forward d (message.rel f).

  Lemma forward_rel_level s d f g :
    message.rel f = message.rel g -> forward s d f = forward s d g.
  Proof. intros. cbv [forward]. congruence. Qed.

  Definition sends (R : rel) (s : source) : bool :=
    match s with
    | input_source => is_input R
    | node_source n => inb R (program.normal_concl_rels (graph_prog n))
    end.

  Definition R_senders (R : rel) : list source := filter (sends R) (Fin.all _).

  Lemma R_senders_NoDup R : NoDup (R_senders R).
  Proof. apply NoDup_filter, Fin.all_NoDup. Qed.

  Lemma node_sends_concl_rels k R :
    In R (program.normal_concl_rels (graph_prog k)) ->
    In (node_source k) (R_senders R).
  Proof. intros HR. apply filter_In. split; [ apply Fin.all_Full | apply inb_true_iff, HR ]. Qed.

  Lemma node_sends_concl_rels_inv k R :
    In (node_source k) (R_senders R) ->
    In R (program.normal_concl_rels (graph_prog k)).
  Proof. intros Hin. apply filter_In in Hin. destruct Hin as [_ Hin]. apply inb_true_iff, Hin. Qed.

  Local Abbreviation nallowed := (node.safe_inputs R_senders).

  Lemma meta_locate pat ojs n cnt :
    (forall s, safe_output R_senders s (ojs s)) ->
    In (message.done_with pat n cnt) (flat_map ojs (Fin.all _)) ->
    In (message.done_with pat n cnt) (ojs n) /\ Existsn_le (message.matches pat) cnt (ojs n).
  Proof.
    intros HF Hin. apply in_flat_map in Hin. destruct Hin as (k & _ & Hin).
    destruct (HF k) as (Hall & _). specialize (Hall _ _ _ Hin). fwd. auto.
  Qed.

  Lemma no_R_matches_off_senders pat ojs n :
    (forall s, safe_output R_senders s (ojs s)) ->
    ~ In n (R_senders pat.(fact_pattern.rel)) ->
    Forall (fun f => ~ message.matches pat f) (ojs n).
  Proof.
    intros HF Hnin. apply Forall_forall. intros f Hf Hmatch. apply Hnin.
    destruct f as [nf |]; [| destruct Hmatch]. destruct (HF n) as (_ & Hsend).
    destruct Hmatch as (Hrel & _). rewrite Hrel. exact (Hsend _ Hf).
  Qed.

  Lemma allowed_of_outputs ojs :
    (forall s, safe_output R_senders s (ojs s)) -> nallowed (flat_map ojs (Fin.all _)).
  Proof.
    intros HF pat ems Hems.
    apply Existsn_le_flat_map_filter with (p := sends pat.(fact_pattern.rel)).
    - intros k _ Hk. apply no_R_matches_off_senders; [ assumption | ].
      intros Hin. apply filter_In in Hin. destruct Hin. congruence.
    - apply Existsn_le_flat_map. eapply Forall2_impl; [ exact Hems | ].
      intros k e Hin. eapply meta_locate in Hin; [ | eassumption ]. fwd. assumption.
  Qed.

  Lemma allowed_of_safe_inputs d inps :
    Graph2WithIO.safe_inputs forward (safe_output R_senders) d inps -> nallowed inps.
  Proof.
    intros (ojs & Hsafe & Hperm) pat ems Hems.
    eapply Existsn_le_perm; [ symmetry; exact Hperm | ].
    apply allowed_of_outputs with (ojs := fun s => filter (forward s d) (ojs s)).
    - intros s. eapply safe_output_mono; [ apply Hsafe | apply filter_submultiset ].
    - eapply Forall2_impl; [ exact Hems | ]. intros. eapply Permutation.Permutation_in; eassumption.
  Qed.

  Definition graph_sat :=
    graph_sat forward claim.interp (fun n => can_claim R_senders (graph_prog n)) (safe_output R_senders).

  Definition graph_step :=
    graph_step forward (fun n => step R_senders (graph_prog n) (node_source n)).

  Lemma distributed_graph_sat_sound loc P t gs :
    star graph_step (init_graph_state (fun _ => init)) t gs ->
    safe_output R_senders input_source (flat_map inputs_of t) ->
    graph_sat (flat_map inputs_of t) loc P ->
    eventually (will_step graph_step (safe_output R_senders input_source)) (fun '(gs', t') => claim.interp loc P (outputs_at gs' t' loc)) (gs, t).
  Proof.
    intros. eapply graph_sat_sound; try eassumption.
    - intros n s m. eexists. apply input_step.
    - apply claim.interp_mono.
    - intros n. apply safe_output_mono.
    - intros n. split; intros; contradiction.
    - intros. eapply safe_preserved; try eassumption.
      intros. apply node_sends_concl_rels. assumption.
    - intros. eapply eventually_will_step_weaken_allowed.
      + eapply can_claim_sound; try eassumption.
        * apply Hmrv.
        * eapply allowed_of_safe_inputs; eassumption.
      + apply allowed_of_safe_inputs.
    - intros. cbv beta in *. eapply can_claim_mono_inc; try eassumption.
      eapply allowed_of_safe_inputs; eassumption.
  Qed.

End Distributed.
