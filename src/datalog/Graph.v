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

  Context (A : list message -> Prop).
  (*domain is multisets*)

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

    Fail Fail Definition node_monotone :=
      forall t1 t2 ns1 ns2 o,
        star node_step initial_ns t1 ns1 ->
        star node_step ns1 t2 ns2 ->
        node_can_output ns1 t1 o ->
        node_can_output ns2 (t2 ++ t1) o.

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
    Proof. (*very easy*) Abort.
  End node.

  Section nodes.
    Context {node_state1 : Type}.
    Context (node_step1 : node_state1 -> IO_event -> node_state1 -> Prop).
    Context (initial_ns1 : node_state1).

    Context {node_state2 : Type}.
    Context (node_step2 : node_state2 -> IO_event -> node_state2 -> Prop).
    Context (initial_ns2 : node_state2).

    Definition nodes_corresp :=
      forall t1 t2 ns1 ns2,
        star node_step1 initial_ns1 t1 ns1 ->
        star node_step2 initial_ns2 t2 ns2 ->
        allowed_trace t1 ->
        allowed_trace t2 ->
        inputs_of t1 = inputs_of t2 ->
        forall output,
          output_in_trace output t1 ->
          node_can_output node_step2 ns2 t2 output.

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

    Definition nodes_equiv :=
      exists D,
        (*monotone D /\*)
        node_described_by node_step1 D initial_ns1 /\
          node_described_by node_step2 D initial_ns2.
  End nodes.

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

    Definition initial_gs1 : @graph_state node_state1 node_states1 :=
      {| g_nodes := initial_ns1; g_messages := [] |}.

    Definition initial_gs2 : @graph_state node_state2 node_states2 :=
      {| g_nodes := initial_ns2; g_messages := [] |}.

    Lemma will_output_transport :
      (forall t, A t) ->
      Forall4_map
        (fun n np1 np2 ns1 ns2 =>
           nodes_equiv (node_step1 np1) ns1 (node_step2 np2) ns2)
        p1 p2 initial_ns1 initial_ns2 ->
      forall T1 gs1 t gs2 o,
        star (graph_step p1 node_step1) initial_gs1 T1 gs1 ->
        star (graph_step p2 node_step2) initial_gs2 t gs2 ->
        node_will_output (graph_step p1 node_step1) gs1 T1 o ->
        node_will_output (graph_step p2 node_step2) gs2 t o.
    Proof.
      intros A_univ Hcorr T1 gs1 t gs2 o HT1 Hstar2 Hwill1.
      pose proof (allowed_trace_universal A_univ []) as Hnil.
      destruct (eventually_can_step_to_star (graph_step p1 node_step1) _ _ _ gs1 T1
                  (fun _ => allowed_trace_universal A_univ _) Hwill1)
        as (gs1' & tr & Hstar_extra & Hout_extra).
      assert (output_in_trace o (T1 ++ tr)) as Hout_full.
      { apply output_in_trace_app.
        apply output_in_trace_app in Hout_extra as [Hout|Hout];
          [right; apply output_in_trace_rev; exact Hout|left; exact Hout]. }
      destruct (graph_emits_implies_node_emits p1 node_step1 _ _ _
                  (star_app _ _ _ _ _ _ HT1 Hstar_extra) _ Hout_full)
        as (n & np1 & ns1 & Hp1 & Hg1 & Hvis & tau1 & ns_end1 & Htau1 & Hout_tau1).
      cbn in Hg1.
      pose proof (Hcorr n) as Hn. rewrite Hp1, Hg1 in Hn.
      destruct (map.get p2 n) as [np2|] eqn:Hp2; [|contradiction].
      destruct (map.get initial_ns2 n) as [ns2|] eqn:Hg2; [|contradiction].
      destruct Hn as (D & Hmono & Hd1 & Hd2).
      destruct (Hd1 [] _ (star_refl _ _) Hnil) as [_ Hmay].
      destruct (project_node p2 node_step2 _ _ _ Hstar2 n np2 _ Hp2 Hg2)
        as (tau2 & ns_at_gs2 & Htau2 & Hg_gs2 & Hpres2).
      destruct (Hd2 tau2 _ Htau2 (allowed_trace_universal A_univ _)) as [Hmust _].
      assert (D [] o) as HD0.
      { apply Hmay. exists tau1, ns_end1. repeat split;
          [exact Htau1|apply allowed_trace_universal; auto
          |rewrite app_nil_r; exact Hout_tau1]. }
      apply (drive_node_must p2 node_step2 A_univ np2 n o Hp2 Hvis
                             (ns_at_gs2, tau2)
                             (Hmust o (Hmono _ _ _ HD0 (incl_nil_l _)))
                             gs2 t Hg_gs2).
      intros Hout. apply Hpres2; assumption.
    Qed.

    Lemma env_only_lift :
      forall t gs0_2 gs2,
        star (graph_step p2 node_step2) gs0_2 t gs2 ->
        forall gs0_1,
        exists T1 gs1,
          star (graph_step p1 node_step1) gs0_1 T1 gs1 /\
          inputs_of T1 = inputs_of t.
    Proof.
      induction 1 as [|s e s' t0 s'' Hstep Hstar IH]; intros gs0_1;
        [exists [], gs0_1; split; [constructor|reflexivity]|].
      inversion Hstep; subst.
      - destruct (IH {| g_nodes := g_nodes gs0_1;
                        g_messages := (n, m) :: g_messages gs0_1 |})
          as (T1' & gs1' & HT1' & Hinp).
        exists (I_event m :: T1'), gs1'.
        split; [econstructor; [apply gstep_input|exact HT1']
               |cbn; f_equal; exact Hinp]; auto.
      - destruct (IH gs0_1) as (T1 & gs1 & HT1 & Hinp).
        exists T1, gs1. split; [exact HT1|exact Hinp].
      - destruct (IH gs0_1) as (T1 & gs1 & HT1 & Hinp).
        exists T1, gs1. split; [exact HT1|exact Hinp].
    Qed.

    Theorem graphs_equiv D :
      (forall t, A t) ->
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
      - intros o Hd.
        destruct (env_only_lift _ _ _ Hstar2 initial_gs1) as (T1 & gs1 & HT1star & Heqinputs).
        destruct (H1 _ _ HT1star (Ha _)) as [Hmust1 _].
        apply (will_output_transport A_univ Hcorr _ _ _ _ _ HT1star Hstar2).
        apply Hmust1. rewrite Heqinputs; exact Hd.
      - intros o (t' & gs2' & Hstar' & _ & Hout).
        apply (Hmono [] (inputs_of t) o); [|apply incl_nil_l].
        destruct (H1 [] initial_gs1 (star_refl _ _) (Ha _)) as [_ Hmay1].
        apply Hmay1.
        edestruct (ever_produces_same p2 node_step2 initial_ns2 p1 node_step1 initial_ns1
                                      A_univ) as (T1 & gs1 & HT1 & HT1out).
        { intros n. specialize (Hcorr n).
          destruct (map.get p1 n), (map.get p2 n),
                   (map.get initial_ns1 n), (map.get initial_ns2 n);
            try contradiction; auto using nodes_equiv_sym. }
        { eapply star_app; eauto. }
        { apply output_in_trace_app.
          apply output_in_trace_app in Hout as [Houtl|Houtr];
            [right; exact Houtl|left; exact Houtr]. }
        exists T1, gs1. rewrite app_nil_r. repeat split; auto.
    Qed.
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
