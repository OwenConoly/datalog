From Stdlib Require Import List.
From coqutil Require Import Eqb Tactics Tactics.fwd.
From Datalog Require Import Map Datalog Pftree Node Smallstep Graph2WithIO IOGraph List Distributed Tactics FinTypeclass.
From coqutil Require Import Semantics.OmniSmallstepCombinators.

Import ListNotations.
Import node.

Section __.
  Context `{params : datalog_params}.
  Context (is_input : rel -> bool).
  Context (p : program).
  Context (Hmeta_rules : program.meta_rules_valid p).
  Context (Hp_good : Forall (fun R => is_input R = false) (program.concl_rels p)).

  Context {node : nodeT} {node_eqb : Eqb node} {node_eqb_ok : Eqb_ok node_eqb} {node_finite : Fin.Fin node}.

  #[local] Instance sender_label : sender_labelT := source.

  Context (graph_prog : node -> program).

  Local Abbreviation graph_senders := (Distributed.R_senders graph_prog is_input).
  Local Abbreviation distributed_step := (Distributed.distributed_step graph_prog is_input).
  Local Abbreviation initial_graph_state := (init_graph_state (fun _ => init)).
  Local Abbreviation distributed_sat := (distributed_sat graph_prog is_input).
  Local Abbreviation distributed_output_sat := (distributed_output_sat graph_prog is_input).

  Definition graph_prog_distributes_normal_rules (prog : program) :=
    forall r, In r prog.(program.rules) <-> exists n, In r (graph_prog n).(program.rules).

  Definition graph_prog_distributes_meta_rules (prog : program) :=
    forall mr,
      In mr prog.(program.meta_rules) ->
      forall n R,
        In R (meta_rule.concl_rels mr) ->
        In R (program.normal_concl_rels (graph_prog n)) ->
        In mr (graph_prog n).(program.meta_rules).

  Context (Hlayout_normal : graph_prog_distributes_normal_rules p).
  Context (Hlayout_meta : graph_prog_distributes_meta_rules p).

  Definition claim_holds_at_node inputs (c : claim) (n : node) :=
    exists hyps,
      program.interp_step (graph_prog n) c hyps /\
        Forall (program.interp p (knows_fact graph_senders inputs)) hyps.

  Definition claim_holds_at_source inputs (c : claim) (s : source) :=
    match s with
    | input_source => knows_fact graph_senders inputs c
    | node_source n => claim_holds_at_node inputs c n
    end.

  Lemma is_input_graph_senders R :
    is_input R = true ->
    graph_senders R = [input_source].
  Proof.
    cbv [graph_senders Fin.all]. simpl. intros H. rewrite H. f_equal.
    apply filter_eq_nil. intros s Hs. apply in_map_iff in Hs. fwd. simpl.
    rewrite_false (inb _ _); [reflexivity|].
    rewrite Forall_forall in Hp_good. intros H'. cbv [graph_prog_distributes_normal_rules] in Hlayout_normal.
    enough (is_input R = false) by congruence. apply Hp_good. Search program.concl_rels.
    apply program.normal_concl_rel_concl. cbv [program.normal_concl_rels] in H'.
    apply in_flat_map in H'. fwd.
    apply in_flat_map. eexists. split.
    { apply Hlayout_normal. eauto. }
    assumption.
  Qed.

  Lemma interp_input_source_knows_fact inputs c  :
    claim.interp input_source c inputs ->
    safe_output graph_senders input_source inputs ->
    knows_fact graph_senders inputs c.
  Proof.
    intros H Hsafe. cbv [claim.interp] in H.
    destruct (is_input (fact.rel c)) eqn:E.
    { eapply knows_fact_senders_ext; [eassumption|].
      symmetry. apply is_input_graph_senders. assumption. }
    admit.
  Admitted.

  Definition guaranteed_by_claims (cs : source -> list claim) (f : fact) :=
    match f with
    | fact.normal nf =>
        exists src, In (fact.normal nf) (cs src)
    | fact.meta mf =>
        exists mf_sets,
        Forall2 (fun src set => In (fact.meta (meta_fact.mk mf.(meta_fact.pattern) set)) (cs src))
          (graph_senders mf.(meta_fact.pattern).(fact_pattern.rel)) mf_sets /\
          (forall nf,
              meta_fact.matches mf nf <-> Exists (fun set => meta_fact.matches (meta_fact.mk mf.(meta_fact.pattern) set) nf) mf_sets)
    end.

  Lemma suffices_charac n Pjs P cs :
    suffices (forward graph_prog) claim.interp_conj
      (fun n' => can_claim_conj graph_senders (graph_prog n')) (safe_output graph_senders) n Pjs P ->
    Forall (fun c =>
              exists hyps,
                program.interp_step (graph_prog n) c hyps /\
                  Forall (guaranteed_by_claims cs) hyps)
      P.
  Proof.
    intros H. cbv [suffices] in H. apply Forall_forall. intros c Hc.
    especialize H. 1: admit. cbv [can_claim_conj] in H. rewrite Forall_forall in H.
    specialize (H _ Hc). cbv [can_claim] in H. fwd. eexists. split; [eassumption|].


  Lemma layout_sound inputs Ps src :
    distributed_sat inputs src Ps ->
    Forall (fun P => claim_holds_at_source inputs P src) Ps.
  Proof.
    induction 1.
    - fold distributed_sat in H. simpl. cbv [suffices] in H1. Print claim_holds_at_node.
      eassert (Hojs: exists (ojs : source -> list message), _).
      { eapply Fin.choice.
        intros n. specialize (H0 n). Print claim_holds_at_node. Search Forall Forall2 concat.
      cbv [suffices] in H1. eapply Forall_impl. 1: apply H1.

      admit.
    - cbv [claim.interp_conj] in H. eapply Forall_impl; [eassumption|]. simpl.
      intros c Hc. cbv [claim.interp] in Hc. destruct c; fwd; simpl in *; contradiction.
    - cbv [claim.interp_conj] in H. eapply Forall_impl; [eassumption|]. simpl.
      intros c Hc.
      cbv [claim.interp] in Hc. cbv [knows_fact]. cbv [knows_meta_fact]. cbv [expects_num_facts].
      Print R_senders. Print sends.graph_senders. Search claim.interp.
  Abort.

  Lemma layout_sound_out inputs f :
    distributed_output_sat inputs (fun outs => knows_fact graph_senders outs f) ->
    program.interp p (knows_fact graph_senders inputs) f.
  Proof. Abort.

  Lemma layout_complete inputs f :
    program.interp p (knows_fact graph_senders inputs) f ->
    distributed_output_sat inputs (fun outs => knows_fact graph_senders outs f).
  Proof. Abort.
End __.
