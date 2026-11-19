From Stdlib Require Import List.
From coqutil Require Import Eqb Tactics Tactics.fwd.
From Datalog Require Import Datalog Node Smallstep Graph2WithIO IOGraph List Distributed Tactics FinTypeclass.
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

  Definition all_rules :=
    flat_map (fun n => (graph_prog n).(program.rules)) (Fin.all _).

  Definition graph_prog_distributes_normal_rules (prog : program) :=
    forall r, In r prog.(program.rules) <-> In r all_rules.

  Definition graph_prog_distributes_meta_rules (prog : program) :=
    forall mr,
      In mr prog.(program.meta_rules) ->
      forall n R,
        In R (meta_rule.concl_rels mr) ->
        In R (program.normal_concl_rels (graph_prog n)) ->
        In mr (graph_prog n).(program.meta_rules).

  Context (Hlayout_normal : graph_prog_distributes_normal_rules p).
  Context (Hlayout_meta : graph_prog_distributes_meta_rules p).

End __.
