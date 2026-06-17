From coqutil Require Import Map.Interface.
From coqutil Require Import Semantics.OmniSmallstepCombinators.
From Stdlib Require Import List.
From Datalog Require Import Smallstep Map.
Import ListNotations.

Definition node_id := nat.
Section __.
  Context {message : Type}.
  Context (A : list message -> message -> Prop).
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

    Context (node_step : node_prog -> node_state -> IO_event -> node_state -> Prop).

    Record graph_state :=
      { g_nodes : node_states;
        g_messages : list (node_id (*destination*) * message) }.

    Inductive graph_step : graph_state -> IO_event -> graph_state -> Prop :=
    | gstep_input gs n m :
      input_allowed n m = true ->
      graph_step gs (I_event m)
                 {| g_nodes := gs.(g_nodes);
                   g_messages := (n, m) :: gs.(g_messages) |}
    | gstep_run gs n np ns ns' outs :
      map.get p n = Some np ->
      map.get gs.(g_nodes) n = Some ns ->
      node_step np ns (O_event outs) ns' ->
      graph_step gs (O_event (filter (output_visible n) outs))
                 {| g_nodes := map.put gs.(g_nodes) n ns';
                   g_messages := gs.(g_messages) ++
                                      flat_map (fun m => map (fun n' => (n', m)) (forward n m))
                                      outs |}
    | gstep_receive gs n np ns ns' m ms1 ms2 :
      map.get p n = Some np ->
      map.get gs.(g_nodes) n = Some ns ->
      node_step np ns (I_event m) ns' ->
      gs.(g_messages) = ms1 ++ (n, m) :: ms2 ->
      graph_step gs (O_event [])
                 {| g_nodes := map.put gs.(g_nodes) n ns';
                   g_messages := ms1 ++ ms2 |}.
  End graph.

  Section node.
    Context {node_state : Type}.
    Context (node_step : node_state -> IO_event -> node_state -> Prop).
    Context (D : list message (*inputs*) -> message (*output*) -> Prop).
    Context (initial_ns : node_state).

    Definition inputs_of (t : list IO_event) :=
      flat_map (fun e => match e with I_event m => [m] | _ => [] end) t.

    Definition output_in_trace (output : message) (t : list IO_event) :=
      exists outs, In (O_event outs) t /\ In output outs.

    Definition event_guaranteed (e : IO_event) :=
      match e with
      | O_event _ => True
      | I_event _ => False
      end.

    Definition allowed_IO_event (t : list IO_event) (e : IO_event) :=
      match e with
      | O_event _ => True
      | I_event inp => A (inputs_of t) inp
      end.

    Definition allowed_trace t :=
      forall t1 e t2,
        t = t2 ++ e :: t1 ->
        allowed_IO_event t1 e.

    Definition node_might_output start t (output : message) : Prop :=
      exists t' ns,
        star node_step start t' ns /\
          allowed_trace (t' ++ t) /\
          output_in_trace output t.

    Definition node_will_output start t (output : message) : Prop :=
      eventually (can_step node_step allowed_trace (fun _ => event_guaranteed))
        (fun '(_, t') => output_in_trace output t')
        (start, t).

    Definition monotone :=
      forall inputs1 inputs2 output,
        D inputs1 output ->
        incl inputs1 inputs2 ->
        D inputs2 output.

    Definition node_described_by :=
      forall t ns,
        star node_step initial_ns t ns ->
        (forall output,
            D (inputs_of t) output ->
            node_will_output ns t output) /\
          (forall output,
              node_might_output ns t output ->
              D (inputs_of t) output).
  End node.

  Section nodes.
    Context {node_state1 : Type}.
    Context (node_step1 : node_state1 -> IO_event -> node_state1 -> Prop).
    Context (initial_ns1 : node_state1).

    Context {node_state2 : Type}.
    Context (node_step2 : node_state2 -> IO_event -> node_state2 -> Prop).
    Context (initial_ns2 : node_state2).

    Check node_described_by.
    Definition nodes_equiv :=
      exists D,
        node_described_by node_step1 D initial_ns1 /\
          node_described_by node_step2 D initial_ns2.
  End nodes.

  Section graphs.
    Context {node_prog1 : Type} {graph_prog1 : map.map node_id node_prog1}.
    Context {node_state1 : Type} {node_states1 : map.map node_id node_state1}.
    Context (p1 : graph_prog1).
    Context (node_step1 : node_prog1 -> node_state1 -> IO_event -> node_state1 -> Prop).
    Context (initial_ns1 : node_states1).

    Context {node_prog2 : Type} {graph_prog2 : map.map node_id node_prog2}.
    Context {node_state2 : Type} {node_states2 : map.map node_id node_state2}.
    Context (p2 : graph_prog2).
    Context (node_step2 : node_prog2 -> node_state2 -> IO_event -> node_state2 -> Prop).
    Context (initial_ns2 : node_states2).

    Definition initial_gs1 : @graph_state node_state1 node_states1 :=
      {| g_nodes := initial_ns1; g_messages := [] |}.

    Definition initial_gs2 : @graph_state node_state2 node_states2 :=
      {| g_nodes := initial_ns2; g_messages := [] |}.

    Theorem graphs_might_equiv D :
      Forall4_map
        (fun n np1 np2 ns1 ns2 =>
           nodes_equiv (node_step1 np1) ns1 (node_step2 np2) ns2)
        p1 p2 initial_ns1 initial_ns2 ->
      node_described_by (graph_step p1 node_step1) D initial_gs1 ->
      node_described_by (graph_step p2 node_step2) D initial_gs2.
    Proof. Abort.
  End graphs.
End __.
