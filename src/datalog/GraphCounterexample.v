(** * Counterexample: graphs_equiv is FALSE as originally stated.

    The original theorem statement (before the fix) was, schematically:

        Forall4_map (fun n np1 np2 ns1 ns2 =>
                      nodes_equiv (node_step1 np1) ns1 (node_step2 np2) ns2)
          p1 p2 initial_ns1 initial_ns2 ->
        monotone D ->
        node_described_by (graph_step p1 node_step1) D initial_gs1 ->
        node_described_by (graph_step p2 node_step2) D initial_gs2.

    where (importantly) [nodes_equiv] used the outer [A : list message -> message -> Prop]
    as the rely at the NODE level — i.e., [allowed_IO_event] used [A] both when
    testing nodes in isolation and when checking graph traces.

    The theorem is false.  The root cause: [A] is an environment-rely.  Tested
    in isolation, [A] restricts what inputs a node can see.  But inside a
    graph, a node also receives inter-node messages forwarded by [forward],
    and these need not satisfy [A].  Two nodes that look equivalent under
    [A]-restricted inputs can disagree on inter-node messages, and the graph
    routes those messages between them, exposing the difference.

    ** Counterexample (informal).

    Take [message := nat], [A inputs inp := (inp = 0)] (only 0 is allowed
    from the environment).

    Define two node implementations [A1] and [A2] over [state := option nat],
    initial [None].  Shared transitions:
      - (s, I_event m, Some m)  for any s, m         (* "store input" *)
      - (s, O_event [], s)      for any s            (* "idle" *)
    Distinct transition:
      - A1: (Some 1, O_event [42], None)             (* emit 42 iff state = 1 *)
      - A2: (Some n, O_event [42], None) when n<>0   (* emit 42 iff state<>0 *)

    Tested in isolation under [allowed_trace] (with [A]), the only inputs
    are 0, so the only reachable states are [None] and [Some 0].  Neither A1
    nor A2 ever reaches the state that lets it emit 42.  Both are described
    by [D_n := empty] (vacuous must, vacuous may), so [nodes_equiv] holds.

    Now put each into a 2-node graph paired with a sender [B] that can
    always emit [O_event [2]].  Set [forward 0 _ := [1]] so B's output 2
    is routed to the A-slot.  Set [input_allowed n m := (n =? 0 && m =? 0)]
    and [output_visible _ _ := true].

    In graph 1 (with [A1]): B emits 2, A1 receives 2, A1 sits in state
    [Some 2], A1 never emits 42 (its trigger is [Some 1]).
    In graph 2 (with [A2]): B emits 2, A2 receives 2, A2 sits in state
    [Some 2], A2 CAN emit 42 (state is non-zero) — and at graph level the
    O_event [42] is fully visible.

    Choose [D inputs x := (x = 2)].  Then:
      - [monotone D]: trivial (constant in [inputs]).
      - graph 1 |= D: must side is satisfied (B always emits 2); may side is
        satisfied (only 2 is ever a visible may-output).
      - graph 2 |/= D: may side fails — 42 is a may-output via the A2 path,
        but D(_, 42) is false.

    So the original [graphs_equiv] would assert graph 2 |= D, but it doesn't.

    ** Why the fix works.

    The fix tests [nodes_equiv] under the UNIVERSAL rely [fun _ _ => True]
    rather than the outer [A].  Under universal rely, [A1] and [A2] disagree
    on input 2 (A2 emits 42, A1 doesn't), so they are not described by any
    common D, and [nodes_equiv] fails for the counterexample — the hypothesis
    is unsatisfied and the theorem can no longer be falsified by it.

    More generally, [nodes_equiv] under universal rely means "behave the
    same for ANY input pattern", which is what compositionality wants: a
    node's graph context can subject it to arbitrary messages from other
    nodes, and the equivalence must continue to hold.

    ** Coq disproof — schematic.

    A full mechanization would require concrete [map.map nat _] instances
    (the project doesn't import one for [nat]).  Below we *sketch* what
    the disproof would prove, leaving the concrete map setup as the missing
    piece.  The mathematical content above is what matters; the schematic
    captures it.

    (The fix is applied in Graph.v.)

    Note: we deliberately do not Import the Graph module here, because
    after the fix the original [nodes_equiv]-with-[A] no longer exists as
    a Coq definition; the counterexample is preserved as documentation. *)
