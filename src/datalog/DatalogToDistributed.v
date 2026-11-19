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
  Context (Hgraph_good : forall n, Forall (fun R => is_input R = false) (program.concl_rels (graph_prog n))).

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
    match c with
    | fact.normal nf =>
        program.interp p (knows_fact graph_senders inputs) (fact.normal nf)
    | fact.meta mf =>
        forall nf,
          fact_pattern.matches mf.(meta_fact.pattern) nf ->
          fset.contains mf.(meta_fact.set) nf.(normal_fact.args) <->
            exists hyps,
              program.interp_step (graph_prog n) (fact.normal nf) hyps /\
                Forall (program.interp p (knows_fact graph_senders inputs)) hyps
    end.

  Definition claim_holds_at_source inputs (c : claim) (s : source) :=
    match s with
    | input_source => (*TODO this sounds weird, seems to be correct almost by accident*) knows_fact graph_senders inputs c
    | node_source n => claim_holds_at_node inputs c n
    end.

  Lemma layout_sound inputs Ps src :
    distributed_sat inputs src Ps ->
    Forall (fun P => claim_holds_at_source inputs P src) Ps.
  Proof.
    induction 1.
    -

  Lemma layout_sound_out inputs f :
    distributed_output_sat inputs (fun outs => knows_fact graph_senders outs f) ->
    program.interp p (knows_fact graph_senders inputs) f.
  Proof. Abort.

  Lemma layout_complete inputs f :
    program.interp p (knows_fact graph_senders inputs) f ->
    distributed_output_sat inputs (fun outs => knows_fact graph_senders outs f).
  Proof. Abort.
End __.
