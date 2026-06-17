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
          output_in_trace output (t' ++ t).

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
        allowed_trace t ->
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

    Definition nodes_equiv :=
      exists D,
        monotone D /\
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

    (* Under universal A, [allowed_trace] is trivially True everywhere, so we
       can drop it from both [node_described_by] hypotheses and from
       [node_might_output] / the [can_step] inside [node_will_output]. *)

    (* The two halves of [node_described_by] each reduce to a clean
       statement that the two graphs have matching {may-outputs, will-outputs}
       sets at initial state.  Per-node [nodes_equiv] + the routing structure
       is what would prove these set equalities, and we leave them as
       [Admitted].  Once they are proved, the conclusion drops out via
       [monotone D] + [graph 1 ⊨ D]. *)

    (* The two graphs ever-produce the same outputs. *)
    Lemma ever_produces_same :
      (forall t m, A t m) ->
      Forall4_map
        (fun n np1 np2 ns1 ns2 =>
           nodes_equiv (node_step1 np1) ns1 (node_step2 np2) ns2)
        p1 p2 initial_ns1 initial_ns2 ->
      forall o,
        (exists T1 gs1, star (graph_step p1 node_step1) initial_gs1 T1 gs1
                        /\ output_in_trace o T1) <->
        (exists T2 gs2, star (graph_step p2 node_step2) initial_gs2 T2 gs2
                        /\ output_in_trace o T2).
    Proof. Admitted.

    (* When graph 1 from a state reachable with the same inputs will output o,
       graph 2 from any state reachable via t will too. *)
    Lemma will_output_transport :
      (forall t m, A t m) ->
      Forall4_map
        (fun n np1 np2 ns1 ns2 =>
           nodes_equiv (node_step1 np1) ns1 (node_step2 np2) ns2)
        p1 p2 initial_ns1 initial_ns2 ->
      forall t gs2 o,
        star (graph_step p2 node_step2) initial_gs2 t gs2 ->
        (exists T1 gs1,
           star (graph_step p1 node_step1) initial_gs1 T1 gs1 /\
           inputs_of T1 = inputs_of t /\
           node_will_output (graph_step p1 node_step1) gs1 T1 o) ->
        node_will_output (graph_step p2 node_step2) gs2 t o.
    Proof. Admitted.

    (* An env-only trace using the env-input sequence of an existing trace
       is always reachable in graph 1.  This is the easy direction of
       input-only lifting: env inputs don't depend on node behavior, so any
       env-input sequence allowed under [input_allowed] is reachable. *)
    Lemma env_only_lift :
      forall t gs2,
        star (graph_step p2 node_step2) initial_gs2 t gs2 ->
        exists T1 gs1,
          star (graph_step p1 node_step1) initial_gs1 T1 gs1 /\
          inputs_of T1 = inputs_of t.
    Proof. Admitted.

    Lemma star_app {st ev} (step : st -> ev -> st -> Prop) s1 t1 s2 t2 s3 :
      star step s1 t1 s2 -> star step s2 t2 s3 -> star step s1 (t1 ++ t2) s3.
    Proof.
      induction 1; cbn; [auto|].
      econstructor; eauto.
    Qed.

    Lemma output_in_trace_app o (l1 l2 : list IO_event) :
      output_in_trace o (l1 ++ l2) <-> output_in_trace o l1 \/ output_in_trace o l2.
    Proof.
      unfold output_in_trace; split.
      - intros (outs & Hin & Hino).
        apply in_app_or in Hin as [Hin|Hin]; [left|right]; eauto.
      - intros [(outs & Hin & Hino)|(outs & Hin & Hino)];
          exists outs; (split; [apply in_or_app|exact Hino]); auto.
    Qed.

    Lemma allowed_trace_universal :
      (forall t m, A t m) -> forall t, allowed_trace t.
    Proof.
      intros Au t. unfold allowed_trace, allowed_IO_event; intros.
      destruct e; auto.
    Qed.

    Theorem graphs_equiv D :
      (forall t m, A t m) ->
      Forall4_map
        (fun n np1 np2 ns1 ns2 =>
           nodes_equiv (node_step1 np1) ns1 (node_step2 np2) ns2)
        p1 p2 initial_ns1 initial_ns2 ->
      monotone D ->
      node_described_by (graph_step p1 node_step1) D initial_gs1 ->
      node_described_by (graph_step p2 node_step2) D initial_gs2.
    Proof.
      intros A_univ Hcorr Hmono H1.
      pose proof (allowed_trace_universal A_univ) as Ha.
      intros t gs2 Hstar2 _.
      split.
      - (* MUST: D(inputs_of t, o) -> node_will_output graph_step2 gs2 t o.
           Plan: env-only-lift t to a graph 1 trace T1 with the same env
           inputs; apply graph 1 ⊨ D's must side to get the graph 1
           will-output proof; then transport across via the per-node
           simulation. *)
        intros o Hd.
        destruct (env_only_lift _ _ Hstar2) as (T1 & gs1 & HT1star & Heqinputs).
        eapply will_output_transport; try eassumption.
        exists T1, gs1; repeat split; auto.
        destruct (H1 _ _ HT1star (Ha _)) as [Hmust1 _].
        apply Hmust1.
        rewrite Heqinputs; exact Hd.
      - (* MAY: node_might_output graph_step2 gs2 t o -> D(inputs_of t, o).
           Use Hmono [] (inputs_of t) o; the smaller-input D([], o) is then
           obtained from graph 1 ⊨ D's may side at the INITIAL state.  The
           may-witness for graph 1 (any trace producing o from initial) is
           obtained from graph 2 via [ever_produces_same]. *)
        intros o Hmight.
        destruct Hmight as (t' & gs2' & Hstar' & _ & Hout).
        apply (Hmono [] (inputs_of t) o); [|apply incl_nil_l].
        destruct (H1 [] initial_gs1 (star_refl _ _) (Ha _)) as [_ Hmay1].
        apply Hmay1.
        assert (exists T2 gs2'',
                   star (graph_step p2 node_step2) initial_gs2 T2 gs2'' /\
                   output_in_trace o T2) as Hgraph2_out.
        { exists (t ++ t'), gs2'. split.
          - eapply star_app; eauto.
          - apply output_in_trace_app.
            apply output_in_trace_app in Hout as [|]; auto. }
        apply (proj2 (ever_produces_same A_univ Hcorr o)) in Hgraph2_out.
        destruct Hgraph2_out as (T1 & gs1 & HT1star & HT1out).
        exists T1, gs1; repeat split; auto.
        rewrite app_nil_r; exact HT1out.
    Qed.
  End graphs.
End __.
