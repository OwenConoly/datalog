From coqutil Require Import Map.Interface.
From coqutil Require Import Semantics.OmniSmallstepCombinators.
From Stdlib Require Import List PeanoNat.
From Datalog Require Import Smallstep Map.
Import ListNotations.

Definition node_id := nat.
Section __.
  Context {message : Type}.
  Context (input_allowed : node_id -> message -> bool).
  Context (forward : node_id -> message -> list node_id).
  Context (output_visible : node_id -> message -> bool).

  Context (A : list message -> Prop).
  (*domain is multisets*)

  Local Notation IO_event := (IO_event message).

  Section graph.
    Context {node_prog : Type} {graph_prog : map.map node_id node_prog}.
    Context {node_state : Type} {node_states : map.map node_id node_state}.
    Context (p : graph_prog).
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

  Local Notation allowed_trace := (allowed_trace A).

  Section nodes.
    Context {node_state1 : Type}.
    Context (node_step1 : node_state1 -> IO_event -> node_state1 -> Prop).
    Context (initial_ns1 : node_state1).

    Context {node_state2 : Type}.
    Context (node_step2 : node_state2 -> IO_event -> node_state2 -> Prop).
    Context (initial_ns2 : node_state2).

    (*is this just the converse of nodes_corresp_sound?
      yes, obviously---this is why you defined nodes_bicorresp the way it is.
     *)
    Definition nodes_corresp_complete :=
      forall t1 t2 ns1 ns2,
        star node_step1 initial_ns1 t1 ns1 ->
        star node_step2 initial_ns2 t2 ns2 ->
        allowed_trace t1 ->
        allowed_trace t2 ->
        inputs_of t1 = inputs_of t2 ->
        forall output,
          output_in_trace output t1 ->
          can_output node_step2 ns2 t2 output.

    Definition nodes_corresp_sound :=
      forall t2 ns2 output,
        star node_step2 initial_ns2 t2 ns2 ->
        allowed_trace t2 ->
        output_in_trace output t2 ->
        exists t1 ns1,
          star node_step1 initial_ns1 t1 ns1 /\
          inputs_of t1 = inputs_of t2 /\
            output_in_trace output t1.

    Lemma complete_sound D :
      input_total node_step1 ->
      complete_weak node_step1 A initial_ns1 D ->
      nodes_corresp_complete ->
      complete_weak node_step2 A initial_ns2 D.
    Proof.
      intros Hit1 Hcw1 Hcorresp t2 ns2 Hstar2 Hall2 o HD.
      destruct (star_recv node_step1 Hit1 (inputs_of t2) initial_ns1)
        as (t1 & ns1 & Hstar1 & Hinp1).
      assert (Hall1 : allowed_trace t1).
      { unfold allowed_trace in Hall2 |- *. rewrite Hinp1. exact Hall2. }
      assert (HD1 : D (inputs_of t1) o) by (rewrite Hinp1; exact HD).
      apply (Hcw1 _ _ Hstar1 Hall1) in HD1.
      destruct HD1 as (t' & ns' & Hstar' & Hinpt' & Hout).
      pose proof (star_app _ _ _ _ _ _ Hstar1 Hstar') as Hstar_full.
      apply (Hcorresp (t1 ++ t') t2 ns' ns2); auto.
      - unfold allowed_trace in Hall1 |- *.
        rewrite inputs_of_app, Hinpt', app_nil_r. exact Hall1.
      - rewrite inputs_of_app, Hinpt', app_nil_r. exact Hinp1.
      - apply output_in_trace_app. apply output_in_trace_app in Hout.
        destruct Hout as [Hout|Hout]; [right|left]; exact Hout.
    Qed.

    Lemma sound_sound D :
      sound node_step1 A initial_ns1 D ->
      nodes_corresp_sound ->
      sound node_step2 A initial_ns2 D.
     Proof.
      intros Hs1 Hcorresp t2 s2 Hstar2 Hall2 o Hout2.
      destruct (Hcorresp _ _ _ Hstar2 Hall2 Hout2)
        as (t1 & s1 & Hstar1 & Hinp & Hout1).
      assert (Hall1 : allowed_trace t1).
      { unfold allowed_trace in Hall2 |- *. rewrite Hinp. exact Hall2. }
      pose proof (Hs1 _ _ Hstar1 Hall1 _ Hout1) as HD.
      rewrite Hinp in HD. exact HD.
    Qed.

    Definition nodes_bicorresp :=
      forall t1 t2 ns1 ns2,
        star node_step1 initial_ns1 t1 ns1 ->
        star node_step2 initial_ns2 t2 ns2 ->
        allowed_trace t1 ->
        allowed_trace t2 ->
        inputs_of t1 = inputs_of t2 ->
        forall output,
          can_output node_step1 ns1 t1 output <->
          can_output node_step2 ns2 t2 output.

    Lemma sound_complete_bicorresp :
      monotone' node_step1 initial_ns1 ->
      nodes_corresp_complete ->
      nodes_corresp_sound ->
      nodes_bicorresp.
    Proof.
      intros Hmono Hcomp Hsound t1 t2 ns1 ns2 Hstar1 Hstar2 Hall1 Hall2 Heq o.
      split.
      - intros (t' & ns' & Hstar' & Hinpt' & Hout).
        pose proof (star_app _ _ _ _ _ _ Hstar1 Hstar') as Hstar1'.
        apply (Hcomp (t1 ++ t') t2 ns' ns2); auto.
        + unfold allowed_trace.
          rewrite inputs_of_app, Hinpt', app_nil_r. exact Hall1.
        + rewrite inputs_of_app, Hinpt', app_nil_r. exact Heq.
        + apply output_in_trace_app. apply output_in_trace_app in Hout.
          destruct Hout as [Hout|Hout]; [right|left]; exact Hout.
      - intros (t' & ns' & Hstar' & Hinpt' & Hout).
        pose proof (star_app _ _ _ _ _ _ Hstar2 Hstar') as Hstar2'.
        assert (Hall2' : allowed_trace (t2 ++ t')).
        { unfold allowed_trace.
          rewrite inputs_of_app, Hinpt', app_nil_r. exact Hall2. }
        assert (Hout2' : output_in_trace o (t2 ++ t')).
        { apply output_in_trace_app. apply output_in_trace_app in Hout.
          destruct Hout as [Hout|Hout]; [right|left]; exact Hout. }
        destruct (Hsound _ _ _ Hstar2' Hall2' Hout2')
          as (t1' & ns1' & Hstar1' & Heqinp & Hout1).
        assert (Hcan1' : can_output node_step1 ns1' t1' o).
        { exists [], ns1'. split; [constructor|].
          split; [reflexivity|exact Hout1]. }
        apply (Hmono t1' t1 ns1' ns1 o Hstar1' Hstar1); auto.
        rewrite Heqinp, inputs_of_app, Hinpt', app_nil_r, <- Heq.
        apply incl_refl.
    Qed.

    Fail Fail Definition nodes_equiv :=
      exists D,
        (*monotone D /\*)
        described_by node_step1 A initial_ns1 D /\
          described_by node_step2 A initial_ns2 D.
  End nodes.

  Section nodes.
    Context {node_state1 : Type}.
    Context (node_step1 : node_state1 -> IO_event -> node_state1 -> Prop).
    Context (initial_ns1 : node_state1).

    Context {node_state2 : Type}.
    Context (node_step2 : node_state2 -> IO_event -> node_state2 -> Prop).
    Context (initial_ns2 : node_state2).

    Lemma sound_impl_complete :
      nodes_corresp_sound node_step1 initial_ns1 node_step2 initial_ns2 ->
      nodes_corresp_complete node_step2 initial_ns2 node_step1 initial_ns1.
    Proof. Abort.

    Lemma complete_impl_sound :
      nodes_corresp_complete node_step2 initial_ns2 node_step1 initial_ns1 ->
      nodes_corresp_sound node_step1 initial_ns1 node_step2 initial_ns2.
    Proof. Abort.
  End nodes.

  Section graph.
    Context {node_prog : Type} {graph_prog : map.map node_id node_prog}.
    Context {node_state : Type} {node_states : map.map node_id node_state}.
    Context (p : graph_prog) (initial_ns : node_states).
    Context (node_step : node_prog -> node_state -> IO_event -> node_state -> Prop).

    Definition initial_graph_state : graph_state :=
      {| g_nodes := initial_ns; g_messages := [] |}.

    Lemma graph_can_implies_will :
      Forall2_map (fun _ np ns => can_implies_will (node_step np) A ns) p initial_ns ->
      can_implies_will (graph_step p node_step) A initial_graph_state.
    Proof.
      (* Per-node can_implies_will lifts to graph can_implies_will via a
         drive_node_must-style helper: identify the node n producing o, apply
         per-node can_implies_will at n to get node-level will_output, then
         lift via a graph<-node simulation (project graph traces to node n's
         trace, replay node-level eventually as graph-level eventually with
         gstep_run for n).  The lifting requires either A universal or a
         per-node-trace-respects-allowed_trace argument.  Past commits had
         this machinery (drive_node_must, project_node_gen, env_only_lift) but
         these were removed in the recent refactor and not yet re-ported. *)
    Admitted.
  End graph.

End __.

Definition translate_event {M M'} (t : M' -> M) (ev : IO_event M') : IO_event M :=
  match ev with
  | I_event m' => I_event (t m')
  | O_event ms' => O_event (map t ms')
  end.

Definition translate_step {NS M M'} (t : M' -> M)
  (step : NS -> IO_event M -> NS -> Prop)
  : NS -> IO_event M' -> NS -> Prop :=
  fun ns ev ns' => step ns (translate_event t ev) ns'.
