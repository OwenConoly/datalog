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

  Definition inputs_of (t : list IO_event) :=
    flat_map (fun e => match e with I_event m => [m] | _ => [] end) t.

  Definition output_in_trace (output : message) (t : list IO_event) :=
    exists outs, In (O_event outs) t /\ In output outs.

  Definition event_guaranteed (e : IO_event) :=
    match e with
    | O_event _ => True
    | I_event _ => False
    end.

  Definition allowed_trace t :=
    A (inputs_of t).

  Lemma output_in_trace_app o (l1 l2 : list IO_event) :
    output_in_trace o (l1 ++ l2) <-> output_in_trace o l1 \/ output_in_trace o l2.
  Proof.
    unfold output_in_trace; split.
    - intros (outs & Hin & Hino).
      apply in_app_or in Hin as [Hin|Hin]; [left|right]; eauto.
    - intros [(outs & Hin & Hino)|(outs & Hin & Hino)];
        exists outs; (split; [apply in_or_app|exact Hino]); auto.
  Qed.

  Lemma output_in_trace_rev o (l : list IO_event) :
    output_in_trace o (rev l) <-> output_in_trace o l.
  Proof.
    unfold output_in_trace; split; intros (outs & Hin & Hino); exists outs;
      (split; [|exact Hino]); apply in_rev; auto.
    rewrite rev_involutive. exact Hin.
  Qed.

  Lemma allowed_trace_universal :
    (forall t, A t) -> forall t, allowed_trace t.
  Proof. unfold allowed_trace; auto. Qed.

  Lemma inputs_of_app t1 t2 :
    inputs_of (t1 ++ t2) = inputs_of t1 ++ inputs_of t2.
  Proof. apply flat_map_app. Qed.

  Lemma inputs_of_event_guaranteed t :
    Forall event_guaranteed t -> inputs_of t = [].
  Proof.
    induction 1; auto.
    destruct x; cbn; auto. contradiction.
  Qed.

  Lemma output_in_trace_swap o l1 e l2 :
    output_in_trace o (l1 ++ e :: l2) <-> output_in_trace o (e :: l1 ++ l2).
  Proof.
    unfold output_in_trace.
    split; intros (outs & Hin & Hino); exists outs; (split; [|exact Hino]).
    - apply in_app_or in Hin. destruct Hin as [Hin | [Hin | Hin]].
      + right. apply in_or_app. left. exact Hin.
      + left. exact Hin.
      + right. apply in_or_app. right. exact Hin.
    - destruct Hin as [Hin | Hin].
      + apply in_or_app. right. left. exact Hin.
      + apply in_app_or in Hin. destruct Hin as [Hin | Hin].
        * apply in_or_app. left. exact Hin.
        * apply in_or_app. right. right. exact Hin.
  Qed.

  Section node.
    Context {node_state : Type}.
    Context (node_step : node_state -> IO_event -> node_state -> Prop).
    Context (D : list message (*inputs*) -> message (*output*) -> Prop).
    Context (initial_ns : node_state).

    Fail Fail Definition node_might_output start t (output : message) : Prop :=
      exists t' ns,
        star node_step start t' ns /\
          allowed_trace (t' ++ t) /\
          output_in_trace output (t' ++ t).

    Definition node_will_output start t (output : message) : Prop :=
      eventually (can_step node_step allowed_trace (fun _ => event_guaranteed))
        (fun '(_, t') => output_in_trace output t')
        (start, t).

    Definition node_can_output start t output :=
      exists t' ns,
        star node_step start t' ns /\
          Forall event_guaranteed t' /\
          output_in_trace output (t' ++ t).

    Fail Fail Definition monotone :=
      forall inputs1 inputs2 output,
        D inputs1 output ->
        incl inputs1 inputs2 ->
        D inputs2 output.

    Definition node_complete :=
      forall t ns,
        star node_step initial_ns t ns ->
        allowed_trace t ->
        (forall output,
            D (inputs_of t) output ->
            node_will_output ns t output).

    Definition node_sound :=
      forall t ns,
        star node_step initial_ns t ns ->
        allowed_trace t ->
        forall output,
          output_in_trace output t ->
          D (inputs_of t) output.

    Definition node_described_by :=
      node_sound /\ node_complete.

    Fail Fail CoInductive stream {T} :=
    | scons : T -> stream -> stream.
    Fail Arguments stream : clear implicits.

    Fail Definition allowed (s : stream IO_event) :=
        forall o,
          In o s <-> exists inps, D inps o /\ forall i, In i inps -> In i s.

    (*wrong, since angelic nondeterminism*)
    Fail Definition node_described_by_omni :=
      forall s,
        ~allowed s ->
        eventually (can_step node_step1 allowed_trace (fun _ => event_guaranteed))
          (fun '(_, t) => ~prefix t s)
          (initial_ns, []).

    Definition node_complete_weak :=
      forall t ns,
        star node_step initial_ns t ns ->
        allowed_trace t ->
        forall output,
          D (inputs_of t) output ->
          node_can_output ns t output.

    Definition node_described_by_weak :=
      node_sound /\ node_complete_weak.

    (*TODO: does having this for each node imply it for the graph?*)
    (*TODO: this is definitely a property we want to prove about our Datalog nodes.*)
    Definition can_implies_will :=
      forall t ns o,
        star node_step initial_ns t ns ->
        allowed_trace t ->
        node_can_output ns t o ->
        node_will_output ns t o.

    Definition node_monotone :=
      forall t1 t2 ns1 ns2 o,
        star node_step initial_ns t1 ns1 ->
        star node_step ns1 t2 ns2 ->
        allowed_trace t1 ->
        allowed_trace (t2 ++ t1) ->
        node_can_output ns1 t1 o ->
        node_can_output ns2 (t2 ++ t1) o.

    From Datalog Require Import Tactics.
    From coqutil Require Import Tactics.fwd.

    Lemma will_implies_can :
      forall ns t o,
        allowed_trace t ->
        node_will_output ns t o ->
        node_can_output ns t o.
    Proof.
      intros ns0 t0 o Hall Hwill.
      cbv [node_will_output] in Hwill.
      remember (ns0, t0) as st eqn:Est.
      revert ns0 t0 Hall Est.
      induction Hwill as [[ns' t'] HP | [ns' t'] midset Hcan Hmid IH];
        intros ns0 t0 Hall [= -> ->].
      - exists [], ns0. split; [constructor|].
        split; [constructor|exact HP].
      - cbv [can_step] in Hcan.
        specialize (Hcan ns0 [] (star_refl _ _)).
        cbn in Hcan. specialize (Hcan Hall).
        destruct Hcan as (ns'' & e & Hguar & Hstep & Hmidset).
        cbn in Hguar.
        assert (Hall' : allowed_trace (e :: t0)).
        { unfold allowed_trace; cbn. destruct e; auto. contradiction. }
        destruct (IH _ Hmidset ns'' (e :: t0) Hall' eq_refl)
          as (t'' & ns''' & Hstar'' & Hforall'' & Hout'').
        exists (e :: t''), ns'''.
        split; [econstructor; eassumption|].
        split; [constructor; auto|].
        cbn. apply output_in_trace_swap. exact Hout''.
    Qed.

    Lemma ciw_monotone :
      can_implies_will ->
      node_monotone.
    Proof.
      cbv [can_implies_will node_monotone].
      intros Hciw t1 t2 ns1 ns2 o Hstar1 Hstar2 Hall1 Hallt Hcan.
      apply (Hciw _ _ _ Hstar1 Hall1) in Hcan.
      cbv [node_will_output] in Hcan.
      invert Hcan.
      - exists [], ns2. split; [constructor|].
        split; [constructor|].
        cbn. apply output_in_trace_app. right. exact H.
      - cbv [can_step] in H.
        specialize (H _ _ Hstar2 Hallt).
        destruct H as (ns'' & e & Hguar & Hstep & Hmidset).
        cbn in Hguar.
        specialize (H0 _ Hmidset).
        assert (Hall' : allowed_trace (e :: t2 ++ t1)).
        { unfold allowed_trace; cbn. destruct e; auto. contradiction. }
        apply (will_implies_can _ _ _ Hall') in H0.
        destruct H0 as (t' & ns''' & Hstar' & Hforall' & Hout').
        exists (e :: t'), ns'''.
        split; [econstructor; eassumption|].
        split; [constructor; auto|].
        cbn. apply output_in_trace_swap. exact Hout'.
    Qed.

    Fail Fail Definition node_monotone' :=
      forall t1 t2 ns1 ns2 o,
        star node_step initial_ns t1 ns1 ->
        star node_step initial_ns t2 ns2 ->
        incl (inputs_of t1) (inputs_of t2) ->
        node_can_output ns1 t1 o ->
        node_can_output ns2 t2 o.

    (*we want something like this?  idk, anyway we want to find a hypothesis that is
      the difference node_described_by - can_implies_will.
      actually, ideally, we want node_described_by - can_implies_will - node_monotone
     *)
    Lemma node_complete_weak_implies_strong :
      node_complete_weak ->
      can_implies_will ->
      node_complete.
    Proof.
      intros Hweak Hcan t ns Hstar Hall o HD.
      apply Hcan; auto.
    Qed.
  End node.

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
          node_can_output node_step2 ns2 t2 output.

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
      node_complete_weak node_step1 D initial_ns1 ->
      nodes_corresp_complete ->
      node_complete_weak node_step2 D initial_ns2.
    Proof. Abort.

    (*no good (eventually is not expressive enough), since angelic nondeterminism*)
    Fail Fail Definition nodes_corresp_omni :=
      forall P,
        eventually (can_step node_step1 allowed_trace (fun _ => event_guaranteed))
          P (initial_ns1, []) ->
        eventually (can_step node_step2 allowed_trace (fun _ => event_guaranteed))
          (fun '(_, t2) =>
             exists ns1 t1,
               P (ns1, t1) /\
                 incl (inputs_of t1) (inputs_of t2) /\
                 forall o,
                   output_in_trace o t1 ->
                   output_in_trace o t2)
          (initial_ns2, []).

    Definition nodes_bicorresp :=
      forall t1 t2 ns1 ns2,
        star node_step1 initial_ns1 t1 ns1 ->
        star node_step2 initial_ns2 t2 ns2 ->
        allowed_trace t1 ->
        allowed_trace t2 ->
        inputs_of t1 = inputs_of t2 ->
        forall output,
          node_can_output node_step1 ns1 t1 output <->
          node_can_output node_step2 ns2 t2 output.

    Lemma sound_complete_bicorresp :
      nodes_corresp_complete ->
      nodes_corresp_sound ->
      nodes_bicorresp.
    Proof.
      intros Hcomp Hsound t1 t2 ns1 ns2 Hstar1 Hstar2 Hall1 Hall2 Heq o.
      split.
      - intros (t' & ns' & Hstar' & Hguar & Hout).
        pose proof (star_app _ _ _ _ _ _ Hstar1 Hstar') as Hstar1'.
        assert (Hinpt' : inputs_of t' = []) by (apply inputs_of_event_guaranteed; auto).
        apply (Hcomp (t1 ++ t') t2 ns' ns2); auto.
        + unfold allowed_trace.
          rewrite inputs_of_app, Hinpt', app_nil_r. exact Hall1.
        + rewrite inputs_of_app, Hinpt', app_nil_r. exact Heq.
        + apply output_in_trace_app. apply output_in_trace_app in Hout.
          destruct Hout as [Hout|Hout]; [right|left]; exact Hout.
      - intros (t' & ns' & Hstar' & Hguar & Hout).
        pose proof (star_app _ _ _ _ _ _ Hstar2 Hstar') as Hstar2'.
        assert (Hinpt' : inputs_of t' = []) by (apply inputs_of_event_guaranteed; auto).
        assert (Hall2' : allowed_trace (t2 ++ t')).
        { unfold allowed_trace.
          rewrite inputs_of_app, Hinpt', app_nil_r. exact Hall2. }
        assert (Hout2' : output_in_trace o (t2 ++ t')).
        { apply output_in_trace_app. apply output_in_trace_app in Hout.
          destruct Hout as [Hout|Hout]; [right|left]; exact Hout. }
        destruct (Hsound _ _ _ Hstar2' Hall2' Hout2')
          as (t1' & ns1' & Hstar1' & Heqinp & Hout1).
        (* Stuck: have output_in_trace o t1' for a t1' starting from init1,
           but need extension of t1 from ns1.  The existential in sound gives
           an unrelated branch.  Cf. discussion: sound is not the dual of
           complete. *)
    Abort.

    Fail Fail Definition nodes_equiv :=
      exists D,
        (*monotone D /\*)
        node_described_by node_step1 D initial_ns1 /\
          node_described_by node_step2 D initial_ns2.
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
      nodes_corresp_complete node_step2 initial_ns2 node_step1 initial_ns1 .
    Proof. Abort.

    Lemma complete_impl_sound :
      nodes_corresp_complete node_step2 initial_ns2 node_step1 initial_ns1 ->
      nodes_corresp_sound node_step1 initial_ns1 node_step2 initial_ns2.
    Proof. Abort.

    Lemma sound_sound D :
      nodes_corresp_sound node_step1 initial_ns1 node_step2 initial_ns2 ->
      node_sound node_step2 D initial_ns2 ->
      node_sound node_step2 D initial_ns2.
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
      Forall2_map (fun _ np ns => can_implies_will (node_step np) ns) p initial_ns ->
      can_implies_will (graph_step p node_step) initial_graph_state.
    Proof. Abort.
  End graph.

  Section graphs.
    Context {node_prog1 : Type} {graph_prog1 : map.map node_id node_prog1}.
    Context {node_state1 : Type} {node_states1 : map.map node_id node_state1}.
    Context {node_states1_ok : map.ok node_states1}.
    Context (p1 : graph_prog1).
    Context (node_step1 : node_prog1 -> node_state1 -> IO_event -> node_state1 -> Prop).
    Context (initial_ns1 : node_states1).

    Context {node_prog2 : Type} {graph_prog2 : map.map node_id node_prog2}.
    Context {node_state2 : Type} {node_states2 : map.map node_id node_state2}.
    Context {node_states2_ok : map.ok node_states2}.
    Context (p2 : graph_prog2).
    Context (node_step2 : node_prog2 -> node_state2 -> IO_event -> node_state2 -> Prop).
    Context (initial_ns2 : node_states2).

    Theorem graphs_sound :
      (forall t, A t) ->
      Forall4_map
        (fun n np1 np2 ns1 ns2 =>
           nodes_corresp_sound (node_step1 np1) ns1 (node_step2 np2) ns2)
        p1 p2 initial_ns1 initial_ns2 ->
      nodes_corresp_sound (graph_step p1 node_step1) (initial_graph_state initial_ns1) (graph_step p2 node_step2) (initial_graph_state initial_ns2).
    Proof. Abort.

    Theorem graphs_complete :
      (forall t, A t) ->
      Forall4_map
        (fun n np1 np2 ns1 ns2 =>
           nodes_corresp_complete (node_step1 np1) ns1 (node_step2 np2) ns2)
        p1 p2 initial_ns1 initial_ns2 ->
      nodes_corresp_complete (graph_step p1 node_step1) (initial_graph_state initial_ns1) (graph_step p2 node_step2) (initial_graph_state initial_ns2).
    Proof. Abort.
  End graphs.
End __.
Arguments IO_event : clear implicits.

Definition translate_event {M M'} (t : M' -> M) (ev : IO_event M') : IO_event M :=
  match ev with
  | I_event m' => I_event (t m')
  | O_event ms' => O_event (map t ms')
  end.

Definition translate_step {NS M M'} (t : M' -> M)
  (step : NS -> IO_event M -> NS -> Prop)
  : NS -> IO_event M' -> NS -> Prop :=
  fun ns ev ns' => step ns (translate_event t ev) ns'.
