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
    Context {node_states_ok : map.ok node_states}.
    Context (p : graph_prog) (initial_ns : node_states).
    Context (node_step : node_prog -> node_state -> IO_event -> node_state -> Prop).

    Definition initial_graph_state : graph_state :=
      {| g_nodes := initial_ns; g_messages := [] |}.

    (* Project a graph trace to the trace of a specific node n.  Each gstep_run
       and gstep_receive for n contribute to n's trace; gstep_input and steps for
       other nodes do not change n's state. *)
    Lemma project_node_gen :
      forall T gs0 gs,
        star (graph_step p node_step) gs0 T gs ->
        forall n np ns_at_gs0,
          map.get p n = Some np ->
          map.get gs0.(g_nodes) n = Some ns_at_gs0 ->
          exists tau ns_at_gs,
            star (node_step np) ns_at_gs0 tau ns_at_gs /\
            map.get gs.(g_nodes) n = Some ns_at_gs /\
            (forall o, output_visible n o = true ->
                       output_in_trace o tau -> output_in_trace o T).
    Proof.
      intros T gs0 gs Hstar.
      induction Hstar as [s|s e s' t0 s'' Hstep Hstar IH];
        intros n np ns_at_gs0 Hp Hg0.
      - exists [], ns_at_gs0. split; [constructor|]. split; [exact Hg0|].
        intros o _ (outs & Hin & _); inversion Hin.
      - inversion Hstep; subst.
        + (* gstep_input: g_nodes unchanged *)
          destruct (IH n np ns_at_gs0 Hp Hg0) as (tau & ns_at_gs & Htau & Hg & Hpres).
          exists tau, ns_at_gs. split; [exact Htau|]. split; [exact Hg|].
          intros o Hvis Hout. specialize (Hpres o Hvis Hout).
          destruct Hpres as (outs' & Hin & Hino).
          exists outs'. split; [right; exact Hin|exact Hino].
        + (* gstep_run *)
          destruct (Nat.eq_dec n0 n) as [Heq|Hne].
          * subst n0.
            assert (np0 = np) by congruence. subst np0.
            assert (ns = ns_at_gs0) by congruence. subst ns_at_gs0.
            destruct (IH n np ns') as (tau & ns_at_gs & Htau & Hg & Hpres);
              [exact H | cbn; apply map.get_put_same|].
            exists (O_event outs :: tau), ns_at_gs.
            split; [econstructor; [exact H1|exact Htau]|]. split; [exact Hg|].
            intros o Hvis (outs' & Hin & Hino).
            cbn in Hin. destruct Hin as [Heq|Hin_rest].
            -- injection Heq as Heq_outs. subst outs'.
               exists (filter (output_visible n) outs).
               split; [left; reflexivity|].
               apply filter_In. split; [exact Hino|exact Hvis].
            -- specialize (Hpres o Hvis (ex_intro _ outs' (conj Hin_rest Hino))).
               destruct Hpres as (outs'' & Hin'' & Hino'').
               exists outs''. split; [right; exact Hin''|exact Hino''].
          * destruct (IH n np ns_at_gs0 Hp) as (tau & ns_at_gs & Htau & Hg & Hpres).
            { cbn. rewrite map.get_put_diff by auto. exact Hg0. }
            exists tau, ns_at_gs. split; [exact Htau|]. split; [exact Hg|].
            intros o Hvis Hout. specialize (Hpres o Hvis Hout).
            destruct Hpres as (outs' & Hin & Hino).
            exists outs'. split; [right; exact Hin|exact Hino].
        + (* gstep_receive *)
          destruct (Nat.eq_dec n0 n) as [Heq|Hne].
          * subst n0.
            assert (np0 = np) by congruence. subst np0.
            assert (ns = ns_at_gs0) by congruence. subst ns_at_gs0.
            destruct (IH n np ns') as (tau & ns_at_gs & Htau & Hg & Hpres);
              [exact H | cbn; apply map.get_put_same|].
            exists (I_event m :: tau), ns_at_gs.
            split; [econstructor; [exact H1|exact Htau]|]. split; [exact Hg|].
            intros o Hvis (outs' & Hin & Hino).
            cbn in Hin. destruct Hin as [Heq|Hin_rest]; [discriminate|].
            specialize (Hpres o Hvis (ex_intro _ outs' (conj Hin_rest Hino))).
            destruct Hpres as (outs'' & Hin'' & Hino'').
            exists outs''. split; [right; exact Hin''|exact Hino''].
          * destruct (IH n np ns_at_gs0 Hp) as (tau & ns_at_gs & Htau & Hg & Hpres).
            { cbn. rewrite map.get_put_diff by auto. exact Hg0. }
            exists tau, ns_at_gs. split; [exact Htau|]. split; [exact Hg|].
            intros o Hvis Hout. specialize (Hpres o Hvis Hout).
            destruct Hpres as (outs' & Hin & Hino).
            exists outs'. split; [right; exact Hin|exact Hino].
    Qed.

    (* Lift a node-level will_output for node n to a graph-level will_output,
       provided o is visible from n and the graph's node n is at the right state. *)
    Lemma drive_node_must :
      (forall t, A t) ->
      forall (np : node_prog) (n : node_id) (o : message),
        map.get p n = Some np ->
        output_visible n o = true ->
        forall (s : node_state * list IO_event),
          eventually (can_step (node_step np) A)
                     (fun '(_, t') => output_in_trace o t') s ->
          forall gs t,
            map.get gs.(g_nodes) n = Some (fst s) ->
            (output_in_trace o (snd s) -> output_in_trace o t) ->
            eventually (can_step (graph_step p node_step) A)
                       (fun '(_, t') => output_in_trace o t') (gs, t).
    Proof.
      intros A_univ np n o Hp Hvis s Hwill.
      induction Hwill as [[ns_curr trace_curr] HP|
                          [ns_curr trace_curr] midset Hcan Hmid IH];
        intros gs t Hg Hout_proj.
      - apply eventually_done. cbn. apply Hout_proj. exact HP.
      - cbn in Hg.
        apply eventually_step_cps.
        intros gs_demon t_demon Hstar_demon Hallow_g.
        destruct (project_node_gen _ _ _ Hstar_demon n np _ Hp Hg)
          as (tau_d & ns_d & Htau_d & Hg_d & Hpres_d).
        pose proof (Hcan ns_d tau_d Htau_d) as Hcan'.
        assert (Hallow_n : allowed_trace (tau_d ++ trace_curr))
          by (unfold allowed_trace; auto).
        specialize (Hcan' Hallow_n).
        destruct Hcan' as (s'' & outs & Hns_step & Hmidset_at).
        set (gs_next :=
               {| g_nodes := map.put gs_demon.(g_nodes) n s'';
                  g_messages :=
                    gs_demon.(g_messages) ++
                    flat_map (fun m0 => map (fun n' => (n', m0))
                                            (forward n m0)) outs |}).
        exists gs_next, (filter (output_visible n) outs).
        split.
        { eapply gstep_run; eauto. }
        apply (IH (s'', O_event outs :: tau_d ++ trace_curr) Hmidset_at gs_next).
        + cbn. apply map.get_put_same.
        + intros (outs' & Hin & Hino).
          cbn in Hin. destruct Hin as [Heq|Hin_rest].
          * injection Heq as Heq_outs. subst outs'.
            exists (filter (output_visible n) outs).
            split; [left; reflexivity|].
            apply filter_In. split; [exact Hino|exact Hvis].
          * apply in_app_or in Hin_rest as [Hin_d|Hin_curr].
            -- specialize (Hpres_d o Hvis
                          (ex_intro _ outs' (conj Hin_d Hino))).
               destruct Hpres_d as (outs'' & Hin'' & Hino'').
               exists outs''. split.
               { right. apply in_or_app. left. exact Hin''. }
               exact Hino''.
            -- assert (Hcurr : output_in_trace o trace_curr)
                 by (exists outs'; split; [exact Hin_curr|exact Hino]).
               specialize (Hout_proj Hcurr).
               destruct Hout_proj as (outs'' & Hin'' & Hino'').
               exists outs''. split; [right; apply in_or_app; right; exact Hin''|exact Hino''].
    Qed.

    Lemma graph_can_implies_will :
      (forall t, A t) ->
      Forall2_map (fun _ np ns => can_implies_will (node_step np) A ns) p initial_ns ->
      can_implies_will (graph_step p node_step) A initial_graph_state.
    Proof.
      (* Strategy: with helpers project_node_gen and drive_node_must above,
         the proof should identify the producing node n0 from t', use
         project_node_gen on (Hstar ++ prefix of Hstar') to get the per-node
         trace tau_pre and state ns_pre right before the producing gstep_run,
         show per-node can_output o at (ns_pre, tau_pre) (single emit witness),
         apply Hpernode at n0 to get per-node will_output, then drive_node_must
         lifts to graph will_output at the intermediate gs_pre.  Bridging from
         (gs, t) to (gs_pre, ...) requires angel-replaying the prefix steps —
         straightforward but tedious.  Not yet completed. *)
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
