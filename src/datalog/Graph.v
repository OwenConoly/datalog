From coqutil Require Import Map.Interface.
From Stdlib Require Import List.
Import ListNotations.

Definition node_id := nat.
Section __.
  Context {message : Type}.
  Context (input_allowed : node_id -> message -> bool).
  Context (forward : node_id -> message -> list node_id).
  Context (output_visible : node_id -> message -> bool).

  Section graph.
    Context {node_prog : Type} {graph_prog : map.map node_id node_prog}.
    Context {node_state : Type} {node_states : map.map node_id node_state}.
    Context (p : graph_prog).

    Variant IO_event :=
      | I_event (_ : message)
      | O_event (_ : list message).

    Context (node_step : node_prog -> node_state -> list IO_event -> node_state -> Prop).

    Record graph_state :=
      { g_nodes : node_states;
        g_messages : list (node_id (*destination*) * message) }.

    Inductive graph_step : graph_state -> option IO_event -> graph_state -> Prop :=
    | gstep_input gs n m :
      input_allowed n m = true ->
      graph_step gs
        [I_event m]
        {| g_nodes := gs.(g_nodes);
          g_messages := (n, m) :: gs.(g_messages) |}
    | gstep_run gs n np ns ns' outs :
      map.get p n = Some np ->
      map.get gs.(g_nodes) n = Some ns ->
      node_step np ns [O_event outs] ns' ->
      graph_step gs
        [O_event (filter (output_visible n) outs)]
        {| g_nodes := map.put gs.(g_nodes) n ns';
          g_messages := gs.(g_messages) ++
                             flat_map (fun m => map (fun n' => (n', m)) (forward n m))
                             outs |}
    | gstep_receive gs n np ns ns' m ms1 ms2 :
      map.get p n = Some np ->
      map.get gs.(g_nodes) n = Some ns ->
      node_step np ns [I_event m] ns' ->
      gs.(g_messages) = ms1 ++ (n, m) :: ms2 ->
      graph_step gs
        []
        {| g_nodes := map.put gs.(g_nodes) n ns';
          g_messages := ms1 ++ ms2 |}.
  End graph.

  Section graphs.
    Context {node_prog1 : Type} {graph_prog1 : map.map node_id node_prog1}.
    Context {node_state1 : Type} {node_states1 : map.map node_id node_state1}.
    Context (p1 : graph_prog1).

    Context {node_prog2 : Type} {graph_prog2 : map.map node_id node_prog2}.
    Context {node_state2 : Type} {node_states2 : map.map node_id node_state2}.
    Context (p2 : graph_prog2).
