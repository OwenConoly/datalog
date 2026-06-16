From coqutil Require Import Map.Interface.
Definition node_id := nat.
Section __.
  Context {node_prog : Type} {graph_prog : map.map node_id node_prog}.
  Context {node_state : Type} {node_states : map.map node_id node_state}.
  Context {message : Type}.
  Context (p : graph_prog).

  Variant IO_event :=
    | I_event (_ : message)
    | O_event (_ : message).

  Context (node_step : node_prog -> node_state -> list IO_event -> node_state -> Prop).

  Record graph_state :=
    { g_nodes : node_states;
      g_messages : list (node_id (*destination*) * message) }.

  Inductive graph_step : graph_state -> list IO_event -> graph_state -> Prop :=
  | gstep_input
