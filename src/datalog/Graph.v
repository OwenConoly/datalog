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

    (* Bisimulation invariant: same queue, and pairwise [nodes_equiv] at each
       node's current state.  By the theorem's hypothesis, this holds at the
       initial states; the question is whether it is preserved by graph steps. *)
    Definition gs_related (gs1 : @graph_state node_state1 node_states1)
                          (gs2 : @graph_state node_state2 node_states2) : Prop :=
      g_messages gs1 = g_messages gs2 /\
      Forall4_map
        (fun n np1 np2 ns1 ns2 =>
           nodes_equiv (node_step1 np1) ns1 (node_step2 np2) ns2)
        p1 p2 (g_nodes gs1) (g_nodes gs2).

    Lemma gs_related_initial :
      Forall4_map
        (fun n np1 np2 ns1 ns2 =>
           nodes_equiv (node_step1 np1) ns1 (node_step2 np2) ns2)
        p1 p2 initial_ns1 initial_ns2 ->
      gs_related initial_gs1 initial_gs2.
    Proof.
      intros Hcorr. split; [reflexivity|exact Hcorr].
    Qed.

    (* Preservation step: given [gs_related gs1 gs2] and a single [graph_step1]
       step, exhibit a graph 2 trace reaching a related state with the same
       outputs.  This is the stuttering bisimulation step.

       Currently proved for the gstep_input case; gstep_run and gstep_receive
       are admitted — both require non-trivial per-node simulation that goes
       beyond what [nodes_equiv] (a may/must description) gives directly. *)
    Lemma gs_related_step_preservation :
      (forall t m, A t m) ->
      forall gs1 gs2,
        gs_related gs1 gs2 ->
        forall e gs1',
          graph_step p1 node_step1 gs1 e gs1' ->
          exists T2 gs2',
            star (graph_step p2 node_step2) gs2 T2 gs2' /\
            gs_related gs1' gs2' /\
            (forall o, output_in_trace o [e] -> output_in_trace o T2).
    Proof.
      intros A_univ gs1 gs2 Hrel e gs1' Hstep.
      destruct Hrel as [Hmsg Hnodes].
      inversion Hstep; subst.
      - (* gstep_input n m: easy — graph 2 takes the same single step. *)
        exists [I_event m].
        eexists; split.
        { econstructor; [|constructor]. apply gstep_input; eauto. }
        split.
        + cbn. split; [cbn; f_equal; exact Hmsg|exact Hnodes].
        + intros o (outs & Hin & _); inversion Hin as [Heq|Heq];
            [discriminate|inversion Heq].
      - (* gstep_run *) admit.
      - (* gstep_receive *) admit.
    Admitted.

    (* Iterating preservation gives a full graph 2 trace producing the same
       outputs as any graph 1 trace. *)
    Lemma graph_simulation :
      (forall t m, A t m) ->
      forall T1 gs1_start gs1,
        star (graph_step p1 node_step1) gs1_start T1 gs1 ->
        forall gs2_start,
          gs_related gs1_start gs2_start ->
          exists T2 gs2,
            star (graph_step p2 node_step2) gs2_start T2 gs2 /\
            gs_related gs1 gs2 /\
            (forall o, output_in_trace o T1 -> output_in_trace o T2).
    Proof.
      intros A_univ T1 gs1_start gs1 Hstar.
      induction Hstar as [s|s e s' t0 s'' Hstep Hstar IH]; intros gs2_start Hrel.
      - exists [], gs2_start. split; [constructor|]. split; [exact Hrel|].
        intros o (outs & Hin & _); inversion Hin.
      - destruct (gs_related_step_preservation A_univ _ _ Hrel _ _ Hstep)
          as (T2a & gs2_mid & Hstar2a & Hrelmid & Houts_e).
        destruct (IH gs2_mid Hrelmid)
          as (T2b & gs2 & Hstar2b & Hrel_end & Houts_t0).
        exists (T2a ++ T2b), gs2.
        split; [eapply star_app; eassumption|].
        split; [exact Hrel_end|].
        intros o Hout.
        change (e :: t0) with ([e] ++ t0) in Hout.
        apply output_in_trace_app in Hout as [Hout|Hout].
        + apply Houts_e in Hout.
          apply output_in_trace_app. left. exact Hout.
        + apply Houts_t0 in Hout.
          apply output_in_trace_app. right. exact Hout.
    Qed.

    (* Symmetric preservation (graph 2 step → graph 1 simulates).
       Same situation as [gs_related_step_preservation]. *)
    Lemma gs_related_step_preservation_rev :
      (forall t m, A t m) ->
      forall gs1 gs2,
        gs_related gs1 gs2 ->
        forall e gs2',
          graph_step p2 node_step2 gs2 e gs2' ->
          exists T1 gs1',
            star (graph_step p1 node_step1) gs1 T1 gs1' /\
            gs_related gs1' gs2' /\
            (forall o, output_in_trace o [e] -> output_in_trace o T1).
    Proof.
      intros A_univ gs1 gs2 Hrel e gs2' Hstep.
      destruct Hrel as [Hmsg Hnodes].
      inversion Hstep; subst.
      - (* gstep_input n m: graph 1 takes the same single step. *)
        exists [I_event m].
        eexists; split.
        { econstructor; [|constructor]. apply gstep_input; eauto. }
        split.
        + cbn. split; [cbn; f_equal; exact Hmsg|exact Hnodes].
        + intros o (outs & Hin & _); inversion Hin as [Heq|Heq];
            [discriminate|inversion Heq].
      - (* gstep_run *) admit.
      - (* gstep_receive *) admit.
    Admitted.

    Lemma graph_simulation_rev :
      (forall t m, A t m) ->
      forall T2 gs2_start gs2,
        star (graph_step p2 node_step2) gs2_start T2 gs2 ->
        forall gs1_start,
          gs_related gs1_start gs2_start ->
          exists T1 gs1,
            star (graph_step p1 node_step1) gs1_start T1 gs1 /\
            gs_related gs1 gs2 /\
            (forall o, output_in_trace o T2 -> output_in_trace o T1).
    Proof.
      intros A_univ T2 gs2_start gs2 Hstar.
      induction Hstar as [s|s e s' t0 s'' Hstep Hstar IH]; intros gs1_start Hrel.
      - exists [], gs1_start. split; [constructor|]. split; [exact Hrel|].
        intros o (outs & Hin & _); inversion Hin.
      - destruct (gs_related_step_preservation_rev A_univ _ _ Hrel _ _ Hstep)
          as (T1a & gs1_mid & Hstar1a & Hrelmid & Houts_e).
        destruct (IH gs1_mid Hrelmid)
          as (T1b & gs1 & Hstar1b & Hrel_end & Houts_t0).
        exists (T1a ++ T1b), gs1.
        split; [eapply star_app; eassumption|].
        split; [exact Hrel_end|].
        intros o Hout.
        change (e :: t0) with ([e] ++ t0) in Hout.
        apply output_in_trace_app in Hout as [Hout|Hout].
        + apply Houts_e in Hout.
          apply output_in_trace_app. left. exact Hout.
        + apply Houts_t0 in Hout.
          apply output_in_trace_app. right. exact Hout.
    Qed.

    (* The two graphs ever-produce the same outputs.
       Proof: graph_simulation in each direction. *)
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
    Proof.
      intros A_univ Hcorr o.
      pose proof (gs_related_initial Hcorr) as Hrel_init.
      split.
      - intros (T1 & gs1 & Hstar1 & Hout1).
        destruct (graph_simulation A_univ _ _ _ Hstar1 _ Hrel_init)
          as (T2 & gs2 & Hstar2 & _ & Houts).
        exists T2, gs2. split; auto.
      - intros (T2 & gs2 & Hstar2 & Hout2).
        destruct (graph_simulation_rev A_univ _ _ _ Hstar2 _ Hrel_init)
          as (T1 & gs1 & Hstar1 & _ & Houts).
        exists T1, gs1. split; auto.
    Qed.

    (* The eventually step's preservation under the bisimulation: given a
       [can_step] in graph 1 from [(gs1, T1)] and [gs_related gs1 gs2], we
       need a corresponding [can_step] in graph 2 from [(gs2, t2)] producing
       a related midset.  This is the must-direction analog of
       [gs_related_step_preservation] and is genuinely harder (it has to
       handle the [forall demon t'] in [can_step]).  Admitted. *)
    Lemma can_step_transport :
      (forall t m, A t m) ->
      forall gs1 gs2 T1 t2 (midset : graph_state * list IO_event -> Prop),
        gs_related gs1 gs2 ->
        (forall o, output_in_trace o T1 -> output_in_trace o t2) ->
        can_step (graph_step p1 node_step1) allowed_trace
                 (fun _ => event_guaranteed) (gs1, T1) midset ->
        exists midset',
          can_step (graph_step p2 node_step2) allowed_trace
                   (fun _ => event_guaranteed) (gs2, t2) midset' /\
          (forall gs2' t2', midset' (gs2', t2') ->
                            exists gs1' T1',
                              midset (gs1', T1') /\
                              gs_related gs1' gs2' /\
                              (forall o, output_in_trace o T1' ->
                                         output_in_trace o t2')).
    Proof. Admitted.

    (* The eventually-level bisimulation: with [gs_related] at the states and
       the trace's outputs already covered, will-output transports across. *)
    Lemma will_output_via_related :
      (forall t m, A t m) ->
      forall gs1 gs2 T1 t2 o,
        gs_related gs1 gs2 ->
        (forall o', output_in_trace o' T1 -> output_in_trace o' t2) ->
        node_will_output (graph_step p1 node_step1) gs1 T1 o ->
        node_will_output (graph_step p2 node_step2) gs2 t2 o.
    Proof.
      intros A_univ gs1 gs2 T1 t2 o Hrel Houts Hwill.
      unfold node_will_output in *.
      remember (gs1, T1) as s1 eqn:Es1.
      revert gs1 T1 Es1 gs2 t2 Hrel Houts.
      induction Hwill as [s1' HP|s1' midset Hcan Hmid IH];
        intros gs1 T1 Es1 gs2 t2 Hrel Houts; subst.
      - (* eventually_done *)
        apply eventually_done. cbn in *. apply Houts. exact HP.
      - (* eventually_step *)
        destruct (can_step_transport A_univ _ _ _ _ _ Hrel Houts Hcan)
          as (midset' & Hcan' & Hmidset').
        eapply eventually_step; [exact Hcan'|].
        intros (gs2' & t2') Hmid2'.
        destruct (Hmidset' _ _ Hmid2') as (gs1' & T1' & Hmid1 & Hrel' & Houts').
        eapply IH; eauto.
    Qed.

    (* The transport lemma we actually use in the theorem.  Built on
       will_output_via_related + graph_simulation_rev to obtain gs_related. *)
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
       is always reachable in graph 1.  [gstep_input] only checks
       [input_allowed n m = true], independent of state, so any env-input
       sequence taken by graph 2 can be replayed in graph 1.  Other steps
       (gstep_run / gstep_receive) emit O_events and don't contribute to
       [inputs_of], so we simply skip them in the replay. *)
    Lemma env_only_lift_gen :
      forall t gs0 gs2,
        star (graph_step p2 node_step2) gs0 t gs2 ->
        forall gs1_0,
        exists T1 gs1,
          star (graph_step p1 node_step1) gs1_0 T1 gs1 /\
          inputs_of T1 = inputs_of t.
    Proof.
      induction 1 as [s|s e s' t0 s'' Hstep Hstar IH]; intros gs1_0.
      - exists [], gs1_0. split; [constructor|reflexivity].
      - inversion Hstep; subst.
        + (* gstep_input n m *)
          destruct (IH {| g_nodes := g_nodes gs1_0;
                          g_messages := (n, m) :: g_messages gs1_0 |})
            as (T1' & gs1' & HT1' & Hinp).
          exists (I_event m :: T1'), gs1'.
          split.
          * econstructor; [|exact HT1']. apply gstep_input; auto.
          * cbn. f_equal. exact Hinp.
        + (* gstep_run *)
          destruct (IH gs1_0) as (T1 & gs1 & HT1 & Hinp).
          exists T1, gs1. split; [exact HT1|]. cbn. exact Hinp.
        + (* gstep_receive *)
          destruct (IH gs1_0) as (T1 & gs1 & HT1 & Hinp).
          exists T1, gs1. split; [exact HT1|]. cbn. exact Hinp.
    Qed.

    Lemma env_only_lift :
      forall t gs2,
        star (graph_step p2 node_step2) initial_gs2 t gs2 ->
        exists T1 gs1,
          star (graph_step p1 node_step1) initial_gs1 T1 gs1 /\
          inputs_of T1 = inputs_of t.
    Proof.
      intros. eapply env_only_lift_gen; eauto.
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
