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

    (*note that this isn't actually a good way to write these semantics, since some IO_events are distinguishable from each other!
      the problem is that inputting to one node is not the same as inputting to another node.
      so instead, we should have graph_step : _ -> IO_event (message * node_id) -> _ -> Prop. *)
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
      monotone' node_step1 A initial_ns1 ->
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
        + (* allowed_trace t1' *)
          unfold allowed_trace. rewrite Heqinp. exact Hall2'.
        + (* incl *)
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

    (* Strengthening of project_node_gen: besides the projected node trace, every
       message the node has emitted (output_in_trace mu tau) has been forwarded, so
       for each downstream n'' it is either still queued or already delivered to n''
       (n'' reached from its gs0-state via a trace whose inputs contain mu). *)
    Definition node_received (gs0 gs : @graph_state node_state node_states)
        (n'' : node_id) (mu : message) : Prop :=
      exists np'' ns0'' tau'' ns'',
        map.get p n'' = Some np'' /\
        map.get gs0.(g_nodes) n'' = Some ns0'' /\
        map.get gs.(g_nodes) n'' = Some ns'' /\
        star (node_step np'') ns0'' tau'' ns'' /\ In mu (inputs_of tau'').

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

    (* Generalization of drive_node_must that targets an arbitrary STATE property
       R of node n (rather than a visible output appearing in the trace).  Given a
       per-node will to reach a node-state satisfying R, lift it to a graph will to
       reach a graph-state where node n satisfies R.  The graph demon is handled by
       projecting its drive onto node n and using the per-node will-tree. *)
    Lemma drive_node_to_state :
      (forall t, A t) ->
      forall (np : node_prog) (n : node_id) (R : node_state -> Prop),
        map.get p n = Some np ->
        forall (s : node_state * list IO_event),
          eventually (can_step (node_step np) A) (fun '(ns', _) => R ns') s ->
          forall gs t,
            map.get gs.(g_nodes) n = Some (fst s) ->
            eventually (can_step (graph_step p node_step) A)
                       (fun '(gs', _) => exists ns', map.get gs'.(g_nodes) n = Some ns' /\ R ns')
                       (gs, t).
    Proof.
      intros A_univ np n R Hp s Hwill.
      induction Hwill as [[ns_curr trace_curr] HP | [ns_curr trace_curr] midset Hcan Hmid IH];
        intros gs t Hg.
      - apply eventually_done. cbn in *. exists ns_curr. split; [exact Hg | exact HP].
      - cbn in Hg. apply eventually_step_cps.
        intros gs_demon t_demon Hstar_demon Hallow_g.
        destruct (project_node_gen _ _ _ Hstar_demon n np _ Hp Hg)
          as (tau_d & ns_d & Htau_d & Hg_d & Hpres_d).
        pose proof (Hcan ns_d tau_d Htau_d) as Hcan'.
        assert (Hallow_n : allowed_trace (tau_d ++ trace_curr)) by (unfold allowed_trace; auto).
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
        cbn. apply map.get_put_same.
    Qed.

    Lemma eventually_swap :
      forall (o' : message) (s : graph_state) (t1 t2 : list IO_event),
        inputs_of t1 = inputs_of t2 ->
        (forall x, output_in_trace x t1 <-> output_in_trace x t2) ->
        eventually (can_step (graph_step p node_step) A)
                   (fun '(_, t') => output_in_trace o' t') (s, t1) ->
        eventually (can_step (graph_step p node_step) A)
                   (fun '(_, t') => output_in_trace o' t') (s, t2).
    Proof.
      intros o' s t1 t2 Hinp Hout Hev.
      remember (s, t1) as st eqn:Est.
      revert s t1 t2 Hinp Hout Est.
      induction Hev as [[s' t'] HP | [s' t'] midset Hcan Hmid IH];
        intros s_orig t1 t2 Hinp Hout [= -> ->].
      - apply eventually_done. cbn. apply Hout. exact HP.
      - apply eventually_step_cps.
        intros s'_d t_d Hstar_d Hallow_d.
        assert (Hallow_d' : allowed_trace (t_d ++ t1)).
        { unfold allowed_trace in *. rewrite !inputs_of_app in *. rewrite Hinp.
          exact Hallow_d. }
        specialize (Hcan s'_d t_d Hstar_d Hallow_d').
        destruct Hcan as (s'' & outs & Hstep & Hmidset).
        exists s'', outs. split; [exact Hstep|].
        apply (IH _ Hmidset s'' (O_event outs :: t_d ++ t1)
                  (O_event outs :: t_d ++ t2)).
        + change (inputs_of (t_d ++ t1) = inputs_of (t_d ++ t2)).
          rewrite !inputs_of_app, Hinp. reflexivity.
        + intros x.
          change (O_event outs :: t_d ++ t1) with ([O_event outs] ++ (t_d ++ t1)).
          change (O_event outs :: t_d ++ t2) with ([O_event outs] ++ (t_d ++ t2)).
          rewrite !output_in_trace_app.
          pose proof (Hout x). tauto.
        + reflexivity.
    Qed.

    (* Replay a graph star with extra messages injected at any position in
       g_messages.  The injection position can drift as the star evolves, but
       the injected messages stay together as a block. *)
    Lemma star_inject_msgs :
      forall gs0 T gs,
        star (graph_step p node_step) gs0 T gs ->
        forall (msgs_inj : list (node_id * message)) ms1_0 ms2_0,
          gs0.(g_messages) = ms1_0 ++ ms2_0 ->
          exists ms1 ms2,
            gs.(g_messages) = ms1 ++ ms2 /\
            star (graph_step p node_step)
                 {| g_nodes := gs0.(g_nodes);
                    g_messages := ms1_0 ++ msgs_inj ++ ms2_0 |}
                 T
                 {| g_nodes := gs.(g_nodes);
                    g_messages := ms1 ++ msgs_inj ++ ms2 |}.
    Proof.
      intros gs0 T gs Hstar.
      induction Hstar as [s|s e s' t0 s'' Hstep Hstar IH];
        intros msgs_inj ms1_0 ms2_0 Hsplit.
      - exists ms1_0, ms2_0. split; [exact Hsplit|]. destruct s. cbn in *. subst.
        constructor.
      - inversion Hstep; subst.
        + (* gstep_input n m *)
          cbn in Hsplit.
          specialize (IH msgs_inj ((n, m) :: ms1_0) ms2_0).
          cbn in IH.
          destruct IH as [ms1 [ms2 [Hmsgs_final Hstar_rest]]];
            [rewrite Hsplit; reflexivity|].
          exists ms1, ms2. split; [exact Hmsgs_final|].
          eapply star_step.
          * eapply gstep_input. exact H.
          * cbn. exact Hstar_rest.
        + (* gstep_run n np ns ns' outs *)
          cbn in Hsplit.
          (* New g_messages after run: (ms1_0 ++ msgs_inj ++ ms2_0) ++ extras *)
          specialize (IH msgs_inj ms1_0
                          (ms2_0 ++ flat_map (fun m => map (fun n' => (n', m)) (forward n m)) outs)).
          cbn in IH.
          destruct IH as [ms1 [ms2 [Hmsgs_final Hstar_rest]]].
          { rewrite Hsplit, app_assoc. reflexivity. }
          exists ms1, ms2. split; [exact Hmsgs_final|].
          eapply star_step.
          * eapply gstep_run; eassumption.
          * cbn. rewrite <- !app_assoc. exact Hstar_rest.
        + (* gstep_receive n np ns ns' m rms1 rms2 (consume (n, m) from somewhere). *)
          rename ms1 into rms1, ms2 into rms2.
          cbn in Hsplit. rewrite H2 in Hsplit.
          (* rms1 ++ (n, m) :: rms2 = ms1_0 ++ ms2_0.
             Apply app_eq_app to split into cases. *)
          apply app_eq_app in Hsplit as [l [[Hrms1 Hms2_0] | [Hms1_0 Hrest]]].
          * (* rms1 = ms1_0 ++ l, ms2_0 = l ++ (n, m) :: rms2 *)
            subst rms1 ms2_0.
            specialize (IH msgs_inj ms1_0 (l ++ rms2)).
            destruct IH as [ms1 [ms2 [Hmsgs_final Hstar_rest]]].
            { rewrite app_assoc. reflexivity. }
            exists ms1, ms2. split; [exact Hmsgs_final|].
            eapply star_step.
            -- eapply gstep_receive with (ms1 := ms1_0 ++ msgs_inj ++ l)
                                         (ms2 := rms2);
                 try eassumption.
               cbn. rewrite <- !app_assoc. reflexivity.
            -- cbn. rewrite <- !app_assoc. exact Hstar_rest.
          * (* ms1_0 = rms1 ++ l, (n, m) :: rms2 = l ++ ms2_0 *)
            subst ms1_0. destruct l as [|y l'].
            -- (* l = []: ms2_0 = (n, m) :: rms2 *)
               cbn in Hrest. subst ms2_0. rewrite app_nil_r.
               specialize (IH msgs_inj rms1 rms2).
               destruct IH as [ms1 [ms2 [Hmsgs_final Hstar_rest]]];
                 [reflexivity|].
               exists ms1, ms2. split; [exact Hmsgs_final|].
               eapply star_step.
               ++ eapply gstep_receive with (ms1 := rms1 ++ msgs_inj)
                                            (ms2 := rms2);
                    try eassumption.
                  cbn. rewrite <- !app_assoc. reflexivity.
               ++ cbn. rewrite <- !app_assoc. exact Hstar_rest.
            -- (* l = (n, m) :: l': ms1_0 = rms1 ++ (n, m) :: l', rms2 = l' ++ ms2_0 *)
               cbn in Hrest. inversion Hrest as [[Hyeq Hl'eq]].
               subst y. subst rms2.
               specialize (IH msgs_inj (rms1 ++ l') ms2_0).
               destruct IH as [ms1 [ms2 [Hmsgs_final Hstar_rest]]].
               { rewrite <- app_assoc. reflexivity. }
               exists ms1, ms2. split; [exact Hmsgs_final|].
               eapply star_step.
               ++ eapply gstep_receive with (ms1 := rms1)
                                            (ms2 := l' ++ msgs_inj ++ ms2_0);
                    try eassumption.
                  cbn. rewrite <- !app_assoc. cbn. reflexivity.
               ++ cbn. rewrite <- app_assoc in Hstar_rest. exact Hstar_rest.
    Qed.

    (* (a) for gstep_input case: input doesn't change node states, just adds a
       message. can_output preservation follows by replaying the angel's star
       in the augmented graph. *)
    Lemma can_output_after_gstep_input :
      forall gs n m,
        input_allowed n m = true ->
        forall T o,
          can_output (graph_step p node_step) gs T o ->
          can_output (graph_step p node_step)
            {| g_nodes := gs.(g_nodes); g_messages := (n, m) :: gs.(g_messages) |}
            (I_event m :: T) o.
    Proof.
      intros gs n m Hinp T o (T_a & s_f & Hstar & HinpT_a & Hout).
      pose proof (star_inject_msgs _ _ _ Hstar [(n, m)] [] gs.(g_messages))
        as Hinj.
      cbn in Hinj.
      destruct Hinj as [ms1 [ms2 [Hmsgs_final Hstar_inj]]]; [reflexivity|].
      exists T_a, {| g_nodes := s_f.(g_nodes);
                     g_messages := ms1 ++ (n, m) :: ms2 |}.
      split; [exact Hstar_inj|]. split; [exact HinpT_a|].
      (* output_in_trace o (T_a ++ I_event m :: T) follows from output_in_trace o (T_a ++ T). *)
      apply output_in_trace_swap. cbn.
      destruct Hout as (outs & Hin & Hino).
      exists outs. split; [right; exact Hin | exact Hino].
    Qed.

    (* Helper: find the producing step inside an angel's path. *)
    Lemma find_producing_step :
      forall (gs_start : graph_state) (T : list IO_event) (s_f : graph_state),
        star (graph_step p node_step) gs_start T s_f ->
        inputs_of T = [] ->
        forall o,
          output_in_trace o T ->
          exists (T_pre T_post : list IO_event)
                 (n_o : node_id) (np_o : node_prog)
                 (ns_o ns_o' : node_state)
                 (outs_o : list message)
                 (gs_pre gs_post : graph_state),
            T = T_pre ++ O_event (filter (output_visible n_o) outs_o) :: T_post /\
            star (graph_step p node_step) gs_start T_pre gs_pre /\
            graph_step p node_step gs_pre
                       (O_event (filter (output_visible n_o) outs_o)) gs_post /\
            star (graph_step p node_step) gs_post T_post s_f /\
            inputs_of T_pre = [] /\
            map.get p n_o = Some np_o /\
            map.get gs_pre.(g_nodes) n_o = Some ns_o /\
            node_step np_o ns_o (O_event outs_o) ns_o' /\
            In o outs_o /\
            output_visible n_o o = true.
    Proof.
      intros gs_start T s_f Hstar Hinp o.
      induction Hstar as [s|s e s' t0 s'' Hstep Hstar IH]; intros Hout.
      - cbv [output_in_trace] in Hout. destruct Hout as (? & Hin & _). inversion Hin.
      - cbn in Hinp. destruct e as [m|outs_e]; [discriminate|]. cbn in Hinp.
        change (O_event outs_e :: t0) with ([O_event outs_e] ++ t0) in Hout.
        apply output_in_trace_app in Hout as [Hout_head|Hout_rest].
        + (* o is in the head event *)
          destruct Hout_head as (outs0 & Hin0 & Hino0).
          cbn in Hin0. destruct Hin0 as [Heq|]; [|contradiction].
          injection Heq as Heq_outs. subst outs0.
          inversion Hstep as [
            | gs0 n0 np0 ns0 ns0' outs_full Hp0 Hg0 Hns0
            | gs0 n0 np0 ns0 ns0' m0 ms1 ms2 Hp0 Hg0 Hns0 Hmsg ]; subst.
          * (* gstep_run for n0 *)
            rewrite filter_In in Hino0. destruct Hino0 as [Hino_full Hvis].
            exists [], t0, n0, np0, ns0, ns0', outs_full, s,
              {| g_nodes := map.put s.(g_nodes) n0 ns0';
                 g_messages := s.(g_messages) ++
                   flat_map (fun m => map (fun n' => (n', m)) (forward n0 m)) outs_full |}.
            split; [reflexivity|]. split; [constructor|].
            split; [eapply gstep_run; eassumption|].
            split; [exact Hstar|]. split; [reflexivity|].
            split; [exact Hp0|]. split; [exact Hg0|].
            split; [exact Hns0|]. split; [exact Hino_full | exact Hvis].
          * (* gstep_receive: outs = [] contradicts Hino0 *)
            cbn in Hino0. contradiction.
        + (* o is deeper *)
          specialize (IH Hinp Hout_rest).
          destruct IH as (T_pre & T_post & n_o & np_o & ns_o & ns_o' & outs_o
                          & gs_pre & gs_post & Heq_T & Hstar_pre & Hstep_prod
                          & Hstar_post & Hinp_pre & Hp_o & Hg_o & Hns_o
                          & Hino_o & Hvis_o).
          exists (O_event outs_e :: T_pre), T_post, n_o, np_o, ns_o, ns_o', outs_o,
                 gs_pre, gs_post.
          split; [cbn; rewrite Heq_T; reflexivity|].
          split; [econstructor; [exact Hstep|exact Hstar_pre]|].
          split; [exact Hstep_prod|]. split; [exact Hstar_post|].
          split; [cbn; exact Hinp_pre|].
          split; [exact Hp_o|]. split; [exact Hg_o|].
          split; [exact Hns_o|]. split; [exact Hino_o | exact Hvis_o].
    Qed.

    (* Relaxed variant of find_producing_step (no inputs_of constraint),
       suitable for use when the trace may contain gstep_input events. *)
    Lemma find_producing_step' :
      forall (gs_start : graph_state) (T : list IO_event) (s_f : graph_state),
        star (graph_step p node_step) gs_start T s_f ->
        forall o,
          output_in_trace o T ->
          exists (T_pre T_post : list IO_event)
                 (n_o : node_id) (np_o : node_prog)
                 (ns_o ns_o' : node_state)
                 (outs_o : list message)
                 (gs_pre gs_post : graph_state),
            T = T_pre ++ O_event (filter (output_visible n_o) outs_o) :: T_post /\
            star (graph_step p node_step) gs_start T_pre gs_pre /\
            graph_step p node_step gs_pre
                       (O_event (filter (output_visible n_o) outs_o)) gs_post /\
            star (graph_step p node_step) gs_post T_post s_f /\
            map.get p n_o = Some np_o /\
            map.get gs_pre.(g_nodes) n_o = Some ns_o /\
            node_step np_o ns_o (O_event outs_o) ns_o' /\
            In o outs_o /\
            output_visible n_o o = true.
    Proof.
      intros gs_start T s_f Hstar o.
      induction Hstar as [s|s e s' t0 s'' Hstep Hstar IH]; intros Hout.
      - cbv [output_in_trace] in Hout. destruct Hout as (? & Hin & _). inversion Hin.
      - change (e :: t0) with ([e] ++ t0) in Hout.
        apply output_in_trace_app in Hout as [Hout_head|Hout_rest].
        + (* o is in the head event: e must be O_event *)
          destruct e as [m|outs_e].
          * (* I_event: contradiction since output_in_trace o [I_event m] is false *)
            destruct Hout_head as (outs0 & Hin0 & _).
            cbn in Hin0. destruct Hin0 as [Heq|]; [discriminate Heq|contradiction].
          * (* O_event outs_e: must come from gstep_run for some n_o *)
            destruct Hout_head as (outs0 & Hin0 & Hino0).
            cbn in Hin0. destruct Hin0 as [Heq|]; [|contradiction].
            injection Heq as Heq_outs. subst outs0.
            inversion Hstep as [
              | gs0 ni0 npi0 nsi0 nsi0' outs_full Hpi0 Hgi0 Hnsi0
              | gs0 ni0 npi0 nsi0 nsi0' mi0 ms1 ms2 Hpi0 Hgi0 Hnsi0 Hmsg0 ]; subst.
            -- (* gstep_run *)
               rewrite filter_In in Hino0. destruct Hino0 as [Hino_full Hvis].
               exists [], t0, ni0, npi0, nsi0, nsi0', outs_full, s,
                 {| g_nodes := map.put s.(g_nodes) ni0 nsi0';
                    g_messages := s.(g_messages) ++
                      flat_map (fun m => map (fun n' => (n', m)) (forward ni0 m)) outs_full |}.
               split; [reflexivity|]. split; [constructor|].
               split; [eapply gstep_run; eassumption|].
               split; [exact Hstar|].
               split; [exact Hpi0|]. split; [exact Hgi0|].
               split; [exact Hnsi0|]. split; [exact Hino_full | exact Hvis].
            -- (* gstep_receive: outs = [] contradicts Hino0 *)
               cbn in Hino0. contradiction.
        + (* o is deeper; recurse *)
          specialize (IH Hout_rest).
          destruct IH as (T_pre & T_post & n_o & np_o & ns_o & ns_o' & outs_o
                          & gs_pre & gs_post & Heq_T & Hstar_pre & Hstep_prod
                          & Hstar_post & Hp_o & Hg_o & Hns_o
                          & Hino_o & Hvis_o).
          exists (e :: T_pre), T_post, n_o, np_o, ns_o, ns_o', outs_o, gs_pre, gs_post.
          split; [cbn; rewrite Heq_T; reflexivity|].
          split; [econstructor; [exact Hstep|exact Hstar_pre]|].
          split; [exact Hstep_prod|]. split; [exact Hstar_post|].
          split; [exact Hp_o|]. split; [exact Hg_o|].
          split; [exact Hns_o|]. split; [exact Hino_o | exact Hvis_o].
    Qed.

    (* Message provenance: a message queued at gs is, after any graph evolution,
       either still queued, or has been delivered to its destination node n (whose
       state then advanced via a node-trace whose inputs contain m). *)
    Lemma queue_fate :
      forall gs T gs',
        star (graph_step p node_step) gs T gs' ->
        forall n m np ns_gs,
          map.get p n = Some np ->
          map.get gs.(g_nodes) n = Some ns_gs ->
          In (n, m) gs.(g_messages) ->
          In (n, m) gs'.(g_messages) \/
          (exists tau ns', star (node_step np) ns_gs tau ns' /\
                           map.get gs'.(g_nodes) n = Some ns' /\ In m (inputs_of tau)).
    Proof.
      intros gs T gs' Hstar.
      induction Hstar as [s | s e s' T' s'' Hstep Hstar IH];
        intros n m np ns_gs Hp Hgs Hin.
      - left. exact Hin.
      - inversion Hstep as [ gs0 ni mi Hia
                           | gs0 ni npi nsi nsi' outsi Hpi Hgi Hsi
                           | gs0 ni npi nsi nsi' mi msa msb Hpi Hgi Hsi Hmsg ]; subst;
          cbn in IH, Hgs |- *.
        + (* gstep_input ni mi *)
          edestruct (IH n m np ns_gs) as [Hq | (tau & ns' & Hst & Hg' & Hinm)].
          * exact Hp.
          * exact Hgs.
          * right. exact Hin.
          * left. exact Hq.
          * right. exists tau, ns'. auto.
        + (* gstep_run ni outsi *)
          destruct (Nat.eq_dec n ni) as [Heq | Hne].
          * subst ni. assert (nsi = ns_gs) by congruence. subst nsi.
            assert (npi = np) by congruence. subst npi.
            edestruct (IH n m np nsi') as [Hq | (tau & ns' & Hst & Hg' & Hinm)].
            -- exact Hp.
            -- apply map.get_put_same.
            -- apply in_or_app; left; exact Hin.
            -- left. exact Hq.
            -- right. exists (O_event outsi :: tau), ns'. split; [|split].
               ++ econstructor; [exact Hsi | exact Hst].
               ++ exact Hg'.
               ++ cbn. exact Hinm.
          * edestruct (IH n m np ns_gs) as [Hq | (tau & ns' & Hst & Hg' & Hinm)].
            -- exact Hp.
            -- rewrite map.get_put_diff by auto. exact Hgs.
            -- apply in_or_app; left; exact Hin.
            -- left. exact Hq.
            -- right. exists tau, ns'. auto.
        + (* gstep_receive ni mi *)
          rewrite Hmsg in Hin. apply in_app_or in Hin.
          destruct (Nat.eq_dec n ni) as [Heq | Hne].
          * subst ni. assert (nsi = ns_gs) by congruence. subst nsi.
            assert (npi = np) by congruence. subst npi.
            destruct Hin as [Hin_a | Hin_mid].
            -- edestruct (IH n m np nsi') as [Hq | (tau & ns' & Hst & Hg' & Hinm)].
               ++ exact Hp.
               ++ apply map.get_put_same.
               ++ apply in_or_app; left; exact Hin_a.
               ++ left. exact Hq.
               ++ right. exists (I_event mi :: tau), ns'. split; [|split].
                  ** econstructor; [exact Hsi | exact Hst].
                  ** exact Hg'.
                  ** cbn. right. exact Hinm.
            -- cbn in Hin_mid. destruct Hin_mid as [Heq2 | Hin_b].
               ++ injection Heq2 as Hmeq. subst mi.
                  edestruct (project_node_gen _ _ _ Hstar n np nsi' Hp)
                    as (tau' & ns' & Hst' & Hg' & _).
                  { cbn. apply map.get_put_same. }
                  right. exists (I_event m :: tau'), ns'. split; [|split].
                  ** econstructor; [exact Hsi | exact Hst'].
                  ** exact Hg'.
                  ** cbn. left. reflexivity.
               ++ edestruct (IH n m np nsi') as [Hq | (tau & ns' & Hst & Hg' & Hinm)].
                  ** exact Hp.
                  ** apply map.get_put_same.
                  ** apply in_or_app; right; exact Hin_b.
                  ** left. exact Hq.
                  ** right. exists (I_event mi :: tau), ns'. split; [|split].
                     --- econstructor; [exact Hsi | exact Hst].
                     --- exact Hg'.
                     --- cbn. right. exact Hinm.
          * edestruct (IH n m np ns_gs) as [Hq | (tau & ns' & Hst & Hg' & Hinm)].
            -- exact Hp.
            -- rewrite map.get_put_diff by auto. exact Hgs.
            -- apply in_or_app. destruct Hin as [Hin_a | Hin_mid].
               ++ left. exact Hin_a.
               ++ cbn in Hin_mid. destruct Hin_mid as [Heq2 | Hin_b].
                  ** injection Heq2 as Hnieq Hmieq. subst. contradiction Hne; reflexivity.
                  ** right. exact Hin_b.
            -- left. exact Hq.
            -- right. exists tau, ns'. auto.
    Qed.

    (* A graph step preserves the node domain. *)
    Lemma graph_step_dom :
      forall gs e gs', graph_step p node_step gs e gs' ->
      forall k, map.get gs.(g_nodes) k = None <-> map.get gs'.(g_nodes) k = None.
    Proof.
      intros gs e gs' Hstep k.
      inversion Hstep as [ gs1 ni mi Hia
                         | gs1 ni npi nsi nsi' outsi Hpi Hgi Hsi
                         | gs1 ni npi nsi nsi' mi msa msb Hpi Hgi Hsi Hmsg ]; subst; cbn.
      - reflexivity.
      - destruct (Nat.eq_dec k ni) as [->|Hne].
        + rewrite map.get_put_same, Hgi. split; intro HH; discriminate.
        + rewrite map.get_put_diff by auto. reflexivity.
      - destruct (Nat.eq_dec k ni) as [->|Hne].
        + rewrite map.get_put_same, Hgi. split; intro HH; discriminate.
        + rewrite map.get_put_diff by auto. reflexivity.
    Qed.

    Lemma project_node_saturated :
      forall T gs0 gs,
        star (graph_step p node_step) gs0 T gs ->
        (forall k, map.get p k = None <-> map.get gs0.(g_nodes) k = None) ->
        forall n np ns_at_gs0,
          map.get p n = Some np ->
          map.get gs0.(g_nodes) n = Some ns_at_gs0 ->
          exists tau ns_at_gs,
            star (node_step np) ns_at_gs0 tau ns_at_gs /\
            map.get gs.(g_nodes) n = Some ns_at_gs /\
            (forall mu n'' np'',
               output_in_trace mu tau ->
               In n'' (forward n mu) ->
               map.get p n'' = Some np'' ->
               In (n'', mu) gs.(g_messages) \/ node_received gs0 gs n'' mu).
    Proof.
      intros T gs0 gs Hstar.
      induction Hstar as [s | s e s' t0 s'' Hstep Hstar IH];
        intros Hwf n np ns_at_gs0 Hp Hg0.
      - exists [], ns_at_gs0. split; [constructor|]. split; [exact Hg0|].
        intros mu n'' np'' (outs & Hin & _) _ _; inversion Hin.
      - assert (Hwf' : forall k, map.get p k = None <-> map.get s'.(g_nodes) k = None)
          by (intro k; split; intro HH;
              [ apply (graph_step_dom _ _ _ Hstep); apply Hwf; exact HH
              | apply Hwf; apply (graph_step_dom _ _ _ Hstep); exact HH ]).
        assert (Hconv : forall n'' mu, node_received s' s'' n'' mu -> node_received s s'' n'' mu).
        { intros n'' mu (np'' & ns0'' & tau'' & ns'' & Hp'' & Hgs'0 & Hgs'' & Hst'' & Hinmu).
          inversion Hstep as [ gs1 ni mi Hia
                             | gs1 ni npi nsi nsi' outsi Hpi Hgi Hsi
                             | gs1 ni npi nsi nsi' mi msa msb Hpi Hgi Hsi Hmsg ]; subst.
          - exists np'', ns0'', tau'', ns''. cbn in Hgs'0.
            split; [exact Hp''|]. split; [exact Hgs'0|]. split; [exact Hgs''|].
            split; [exact Hst''|exact Hinmu].
          - destruct (Nat.eq_dec n'' ni) as [Heq|Hne].
            + subst ni. cbn in Hgs'0. rewrite map.get_put_same in Hgs'0.
              injection Hgs'0 as Hgs'0. subst nsi'.
              assert (npi = np'') by congruence. subst npi.
              exists np'', nsi, (O_event outsi :: tau''), ns''.
              split; [exact Hp''|]. split; [exact Hgi|]. split; [exact Hgs''|].
              split; [econstructor; [exact Hsi | exact Hst'']|]. cbn. exact Hinmu.
            + cbn in Hgs'0. rewrite map.get_put_diff in Hgs'0 by auto.
              exists np'', ns0'', tau'', ns''.
              split; [exact Hp''|]. split; [exact Hgs'0|]. split; [exact Hgs''|].
              split; [exact Hst''|exact Hinmu].
          - destruct (Nat.eq_dec n'' ni) as [Heq|Hne].
            + subst ni. cbn in Hgs'0. rewrite map.get_put_same in Hgs'0.
              injection Hgs'0 as Hgs'0. subst nsi'.
              assert (npi = np'') by congruence. subst npi.
              exists np'', nsi, (I_event mi :: tau''), ns''.
              split; [exact Hp''|]. split; [exact Hgi|]. split; [exact Hgs''|].
              split; [econstructor; [exact Hsi | exact Hst'']|]. cbn. right. exact Hinmu.
            + cbn in Hgs'0. rewrite map.get_put_diff in Hgs'0 by auto.
              exists np'', ns0'', tau'', ns''.
              split; [exact Hp''|]. split; [exact Hgs'0|]. split; [exact Hgs''|].
              split; [exact Hst''|exact Hinmu]. }
        inversion Hstep as [ gs1 ni mi Hia
                           | gs1 ni npi nsi nsi' outsi Hpi Hgi Hsi
                           | gs1 ni npi nsi nsi' mi msa msb Hpi Hgi Hsi Hmsg ]; subst.
        + destruct (IH Hwf' n np ns_at_gs0 Hp Hg0)
            as (tau & ns_at_gs & Htau & Hg & Hsat).
          exists tau, ns_at_gs. split; [exact Htau|]. split; [exact Hg|].
          intros mu n'' np'' Hout Hfwd Hpn''.
          destruct (Hsat mu n'' np'' Hout Hfwd Hpn'') as [Hq | Hr];
            [left; exact Hq | right; apply Hconv; exact Hr].
        + destruct (Nat.eq_dec n ni) as [Heq|Hne].
          * subst ni. assert (nsi = ns_at_gs0) by congruence. subst nsi.
            assert (npi = np) by congruence. subst npi.
            destruct (IH Hwf' n np nsi') as (tau & ns_at_gs & Htau & Hg & Hsat);
              [exact Hp | cbn; apply map.get_put_same|].
            exists (O_event outsi :: tau), ns_at_gs.
            split; [econstructor; [exact Hsi | exact Htau]|]. split; [exact Hg|].
            intros mu n'' np'' Hout Hfwd Hpn''.
            change (O_event outsi :: tau) with ([O_event outsi] ++ tau) in Hout.
            apply output_in_trace_app in Hout as [Hhead | Hrest].
            -- destruct Hhead as (outs0 & Hin0 & Hino0).
               cbn in Hin0. destruct Hin0 as [Heq0|[]]. injection Heq0 as Heq0. subst outs0.
               assert (Hins' : In (n'', mu)
                         (g_messages s ++
                          flat_map (fun m => map (fun n' => (n', m)) (forward n m)) outsi)).
               { apply in_or_app. right.
                 apply in_flat_map. exists mu. split; [exact Hino0|].
                 apply in_map_iff. exists n''. split; [reflexivity | exact Hfwd]. }
               destruct (map.get (map.put (g_nodes s) n nsi') n'') as [ns'n''|] eqn:Hg'n''.
               2:{ exfalso. apply (proj2 (Hwf' n'')) in Hg'n''.
                   rewrite Hpn'' in Hg'n''. discriminate. }
               destruct (queue_fate _ _ _ Hstar n'' mu np'' ns'n'' Hpn'' Hg'n'' Hins')
                 as [Hq | (tauq & nsq & Hstq & Hgq & Hinq)].
               ++ left. exact Hq.
               ++ right. apply Hconv. exists np'', ns'n'', tauq, nsq.
                  split; [exact Hpn''|]. split; [exact Hg'n''|]. split; [exact Hgq|].
                  split; [exact Hstq|exact Hinq].
            -- destruct (Hsat mu n'' np'' Hrest Hfwd Hpn'') as [Hq | Hr];
                 [left; exact Hq | right; apply Hconv; exact Hr].
          * destruct (IH Hwf' n np ns_at_gs0 Hp) as (tau & ns_at_gs & Htau & Hg & Hsat).
            { cbn. rewrite map.get_put_diff by auto. exact Hg0. }
            exists tau, ns_at_gs. split; [exact Htau|]. split; [exact Hg|].
            intros mu n'' np'' Hout Hfwd Hpn''.
            destruct (Hsat mu n'' np'' Hout Hfwd Hpn'') as [Hq | Hr];
              [left; exact Hq | right; apply Hconv; exact Hr].
        + destruct (Nat.eq_dec n ni) as [Heq|Hne].
          * subst ni. assert (nsi = ns_at_gs0) by congruence. subst nsi.
            assert (npi = np) by congruence. subst npi.
            destruct (IH Hwf' n np nsi') as (tau & ns_at_gs & Htau & Hg & Hsat);
              [exact Hp | cbn; apply map.get_put_same|].
            exists (I_event mi :: tau), ns_at_gs.
            split; [econstructor; [exact Hsi | exact Htau]|]. split; [exact Hg|].
            intros mu n'' np'' Hout Hfwd Hpn''.
            change (I_event mi :: tau) with ([I_event mi] ++ tau) in Hout.
            apply output_in_trace_app in Hout as [Hhead | Hrest].
            -- destruct Hhead as (outs0 & Hin0 & _). cbn in Hin0.
               destruct Hin0 as [Heq0|[]]. discriminate Heq0.
            -- destruct (Hsat mu n'' np'' Hrest Hfwd Hpn'') as [Hq | Hr];
                 [left; exact Hq | right; apply Hconv; exact Hr].
          * destruct (IH Hwf' n np ns_at_gs0 Hp) as (tau & ns_at_gs & Htau & Hg & Hsat).
            { cbn. rewrite map.get_put_diff by auto. exact Hg0. }
            exists tau, ns_at_gs. split; [exact Htau|]. split; [exact Hg|].
            intros mu n'' np'' Hout Hfwd Hpn''.
            destruct (Hsat mu n'' np'' Hout Hfwd Hpn'') as [Hq | Hr];
              [left; exact Hq | right; apply Hconv; exact Hr].
    Qed.

    (* Per-node ciw' gives per-node ciw. *)
    Lemma pernode_ciw :
      Forall2_map (fun _ np ns => can_implies_will' (node_step np) A ns) p initial_ns ->
      forall n_o np_o ns_init,
        map.get p n_o = Some np_o ->
        map.get initial_ns n_o = Some ns_init ->
        can_implies_will (node_step np_o) A ns_init.
    Proof.
      intros Hpernode n_o np_o ns_init Hp_o Hns_init.
      pose proof (Hpernode n_o) as Hp_n.
      rewrite Hp_o, Hns_init in Hp_n.
      apply (ciw'_iff_ciw_and_monotone' (node_step np_o) A ns_init) in Hp_n.
      apply Hp_n.
    Qed.

    (* Per-node ciw' gives per-node monotone'. *)
    Lemma pernode_monotone' :
      Forall2_map (fun _ np ns => can_implies_will' (node_step np) A ns) p initial_ns ->
      forall n_o np_o ns_init,
        map.get p n_o = Some np_o ->
        map.get initial_ns n_o = Some ns_init ->
        monotone' (node_step np_o) A ns_init.
    Proof.
      intros Hpernode n_o np_o ns_init Hp_o Hns_init.
      pose proof (Hpernode n_o) as Hp_n.
      rewrite Hp_o, Hns_init in Hp_n.
      apply (ciw'_iff_ciw_and_monotone' (node_step np_o) A ns_init) in Hp_n.
      apply Hp_n.
    Qed.

    (* If o' does not appear (as output) in the past trace tau, then can_output
       with past tau collapses to can_output with empty past ("armed"). *)
    Lemma can_output_drop_past :
      forall (np : node_prog) (ns : node_state) (tau : list IO_event) (o' : message),
        ~ output_in_trace o' tau ->
        can_output (node_step np) ns tau o' ->
        can_output (node_step np) ns [] o'.
    Proof.
      intros np ns tau o' Hno (t' & s' & Hstar' & Hinp' & Hout').
      exists t', s'. split; [exact Hstar'|]. split; [exact Hinp'|].
      rewrite app_nil_r.
      apply output_in_trace_app in Hout' as [Hout|Hout]; [exact Hout | contradiction].
    Qed.

    (* cap_transfer: capability is monotone in the received-input set.  If node n
       reaches ns_W via tau_W and ns_act via tau_act (both from its init), and
       tau_W's inputs are included in tau_act's, then anything ns_W can output (with
       past tau_W) ns_act can too (with past tau_act). Direct from monotone'. *)
    Lemma cap_transfer :
      (forall t, A t) ->
      Forall2_map (fun _ np ns => can_implies_will' (node_step np) A ns) p initial_ns ->
      forall n np ns0,
        map.get p n = Some np ->
        map.get initial_ns n = Some ns0 ->
        forall tau_W ns_W tau_act ns_act o',
          star (node_step np) ns0 tau_W ns_W ->
          star (node_step np) ns0 tau_act ns_act ->
          incl (inputs_of tau_W) (inputs_of tau_act) ->
          can_output (node_step np) ns_W tau_W o' ->
          can_output (node_step np) ns_act tau_act o'.
    Proof.
      intros A_univ Hpernode n np ns0 Hp Hns0 tau_W ns_W tau_act ns_act o'
             HsW Hsact Hincl Hcan.
      pose proof (pernode_monotone' Hpernode n np ns0 Hp Hns0) as Hmono.
      apply (Hmono tau_W tau_act ns_W ns_act o' HsW Hsact
               (allowed_trace_universal A A_univ tau_W)
               (allowed_trace_universal A A_univ tau_act) Hincl Hcan).
    Qed.

    (* L2: if node n_o is "armed" for o (node-level can_output o from its current
       state, with empty past trace) and o is visible from n_o, then the graph can
       force o.  This is the final-emission step of the orchestration. *)
    Lemma armed_node_drives :
      (forall t, A t) ->
      Forall2_map (fun _ np ns => can_implies_will' (node_step np) A ns) p initial_ns ->
      forall (t : list IO_event) (gs : graph_state),
        star (graph_step p node_step) initial_graph_state t gs ->
        forall (n_o : node_id) (np_o : node_prog) (ns_o : node_state) (o : message),
          map.get p n_o = Some np_o ->
          map.get gs.(g_nodes) n_o = Some ns_o ->
          output_visible n_o o = true ->
          can_output (node_step np_o) ns_o [] o ->
          will_output (graph_step p node_step) A gs t o.
    Proof.
      intros A_univ Hpernode t gs Hstar n_o np_o ns_o o Hp_o Hg_o Hvis Harmed.
      destruct (map.get initial_ns n_o) as [ns_init|] eqn:Hns_init.
      2:{ pose proof (Hpernode n_o) as Hp_n. rewrite Hp_o, Hns_init in Hp_n.
          contradiction. }
      pose proof (pernode_ciw Hpernode n_o np_o ns_init Hp_o Hns_init) as Hciw_node.
      destruct (project_node_gen _ _ _ Hstar n_o np_o ns_init Hp_o Hns_init)
        as (tau & ns_at_gs & Htau & Hg_at_gs & Hpres).
      assert (ns_at_gs = ns_o) by congruence. subst ns_at_gs.
      assert (Hcan_tau : can_output (node_step np_o) ns_o tau o).
      { destruct Harmed as (t' & s' & Hstar' & Hinp' & Hout').
        exists t', s'. split; [exact Hstar'|]. split; [exact Hinp'|].
        apply output_in_trace_app. left. rewrite app_nil_r in Hout'. exact Hout'. }
      pose proof (Hciw_node tau ns_o o Htau (allowed_trace_universal A A_univ tau) Hcan_tau)
        as Hwill_node.
      apply (drive_node_must A_univ np_o n_o o Hp_o Hvis (ns_o, tau) Hwill_node gs t).
      - cbn. exact Hg_o.
      - cbn. intros Hout_tau. apply Hpres; [exact Hvis | exact Hout_tau].
    Qed.

    (* A node's output-only run lifts to a graph run of that node: other nodes are
       untouched, the queue only grows (and every forwarded message lands in it),
       and the node's visible outputs appear in the graph trace.  Used to splice a
       node's own production into a graph path during the witness replay. *)
    Lemma lift_node_outputs :
      forall (n : node_id) (np : node_prog),
        map.get p n = Some np ->
        forall (ns : node_state) (tau : list IO_event) (ns' : node_state),
          star (node_step np) ns tau ns' ->
          inputs_of tau = [] ->
          forall gs, map.get gs.(g_nodes) n = Some ns ->
          exists (T : list IO_event) (gs' : graph_state),
            star (graph_step p node_step) gs T gs' /\
            inputs_of T = [] /\
            map.get gs'.(g_nodes) n = Some ns' /\
            (forall n2, n2 <> n -> map.get gs'.(g_nodes) n2 = map.get gs.(g_nodes) n2) /\
            (exists extra, gs'.(g_messages) = gs.(g_messages) ++ extra) /\
            (forall outs mu n'', In (O_event outs) tau -> In mu outs ->
                In n'' (forward n mu) -> In (n'', mu) gs'.(g_messages)) /\
            (forall o', output_visible n o' = true -> output_in_trace o' tau ->
                output_in_trace o' T).
    Proof.
      intros n np Hp ns tau ns' Hstar.
      induction Hstar as [s | s e s2 tau0 s3 Hstep Hstar IH];
        intros Hinp gs Hg.
      - exists [], gs. split; [constructor|]. split; [reflexivity|].
        split; [exact Hg|]. split; [reflexivity|].
        split; [exists []; rewrite app_nil_r; reflexivity|].
        split; [intros ? ? ? Hin; inversion Hin|].
        intros o' _ (outs & Hin & _); inversion Hin.
      - cbn in Hinp. destruct e as [m|outs]; [discriminate|]. cbn in Hinp.
        assert (Hg1 : map.get (map.put gs.(g_nodes) n s2) n = Some s2)
          by apply map.get_put_same.
        destruct (IH Hinp {| g_nodes := map.put gs.(g_nodes) n s2;
                             g_messages := gs.(g_messages) ++
                               flat_map (fun mm => map (fun n' => (n', mm)) (forward n mm)) outs |}
                    Hg1)
          as (T & gsf & HstarT & HinpT & Hgf & Hother & (extra & Hextra) & Hfwd & Hvis).
        cbn in Hother, Hextra.
        exists (O_event (filter (output_visible n) outs) :: T), gsf.
        split; [econstructor; [eapply gstep_run; eauto | exact HstarT]|].
        split; [cbn; exact HinpT|].
        split; [exact Hgf|].
        split.
        { intros n2 Hn2. rewrite (Hother n2 Hn2). rewrite map.get_put_diff by auto.
          reflexivity. }
        split.
        { exists (flat_map (fun mm => map (fun n' => (n', mm)) (forward n mm)) outs ++ extra).
          rewrite Hextra. rewrite app_assoc. reflexivity. }
        split.
        { intros outs0 mu n'' Hin0 Hinmu Hinn''.
          cbn in Hin0. destruct Hin0 as [Heq | Hin_rest].
          - injection Heq as Heq_outs. subst outs0.
            rewrite Hextra. apply in_or_app. left.
            apply in_or_app. right.
            apply in_flat_map. exists mu. split; [exact Hinmu|].
            apply in_map_iff. exists n''. split; [reflexivity | exact Hinn''].
          - apply Hfwd with (outs := outs0); assumption. }
        intros o' Hvis' (outs0 & Hin0 & Hino).
        cbn in Hin0. destruct Hin0 as [Heq | Hin_rest].
        + injection Heq as Heq_outs. subst outs0.
          exists (filter (output_visible n) outs). split; [left; reflexivity|].
          apply filter_In. split; [exact Hino | exact Hvis'].
        + specialize (Hvis o' Hvis' (ex_intro _ outs0 (conj Hin_rest Hino))).
          destruct Hvis as (outs1 & Hin1 & Hino1).
          exists outs1. split; [right; exact Hin1 | exact Hino1].
    Qed.

    (* Simulation used to replay an input-free witness from a dominating state.
       gsB dominates gsA: every node of gsB is reached with an input-set that
       includes gsA's (so it can do at least as much, via monotone'), and every
       message queued in gsA is either queued in gsB or already delivered to its
       destination in gsB. *)
    Definition core_dom (gsA gsB : @graph_state node_state node_states) : Prop :=
      (forall n np ns0 nsA,
         map.get p n = Some np -> map.get initial_ns n = Some ns0 ->
         map.get gsA.(g_nodes) n = Some nsA ->
         exists tauA tauB nsB,
           star (node_step np) ns0 tauA nsA /\
           map.get gsB.(g_nodes) n = Some nsB /\
           star (node_step np) ns0 tauB nsB /\
           incl (inputs_of tauA) (inputs_of tauB))
      /\
      (forall n m, In (n, m) gsA.(g_messages) ->
         In (n, m) gsB.(g_messages) \/
         (exists np ns0 tauB nsB,
            map.get p n = Some np /\ map.get initial_ns n = Some ns0 /\
            map.get gsB.(g_nodes) n = Some nsB /\
            star (node_step np) ns0 tauB nsB /\ In m (inputs_of tauB))).

    (* A single graph step establishes the simulation from gs to gs'. *)
    Lemma dom_of_step :
      Forall2_map (fun _ np ns => can_implies_will' (node_step np) A ns) p initial_ns ->
      forall T gs, star (graph_step p node_step) initial_graph_state T gs ->
      forall e gs', graph_step p node_step gs e gs' ->
      core_dom gs gs'.
    Proof.
      intros Hpernode T gs HT e gs' Hstep. split.
      - intros n np ns0 nsA Hp Hns0 HgA.
        destruct (project_node_gen _ _ _ HT n np ns0 Hp Hns0)
          as (tauA & nsA' & HtauA & HgA' & _).
        assert (nsA' = nsA) by congruence. subst nsA'.
        inversion Hstep as [ gs0 ni mi Hia
                           | gs0 ni npi nsi nsi' outsi Hpi Hgi Hsi
                           | gs0 ni npi nsi nsi' mi msa msb Hpi Hgi Hsi Hmsg ]; subst; cbn.
        + exists tauA, tauA, nsA. split; [exact HtauA|]. split; [exact HgA|].
          split; [exact HtauA|]. apply incl_refl.
        + destruct (Nat.eq_dec n ni) as [Heq|Hne].
          * subst ni. assert (nsi = nsA) by congruence. subst nsi.
            assert (npi = np) by congruence. subst npi.
            exists tauA, (tauA ++ [O_event outsi]), nsi'.
            split; [exact HtauA|]. split; [apply map.get_put_same|].
            split; [eapply star_app; [exact HtauA | econstructor; [exact Hsi | constructor]]|].
            rewrite inputs_of_app. cbn. rewrite app_nil_r. apply incl_refl.
          * exists tauA, tauA, nsA. split; [exact HtauA|].
            split; [rewrite map.get_put_diff by auto; exact HgA|].
            split; [exact HtauA|]. apply incl_refl.
        + destruct (Nat.eq_dec n ni) as [Heq|Hne].
          * subst ni. assert (nsi = nsA) by congruence. subst nsi.
            assert (npi = np) by congruence. subst npi.
            exists tauA, (tauA ++ [I_event mi]), nsi'.
            split; [exact HtauA|]. split; [apply map.get_put_same|].
            split; [eapply star_app; [exact HtauA | econstructor; [exact Hsi | constructor]]|].
            rewrite inputs_of_app. cbn. apply incl_appl. apply incl_refl.
          * exists tauA, tauA, nsA. split; [exact HtauA|].
            split; [rewrite map.get_put_diff by auto; exact HgA|].
            split; [exact HtauA|]. apply incl_refl.
      - intros n m Hin.
        inversion Hstep as [ gs0 ni mi Hia
                           | gs0 ni npi nsi nsi' outsi Hpi Hgi Hsi
                           | gs0 ni npi nsi nsi' mi msa msb Hpi Hgi Hsi Hmsg ]; subst; cbn.
        + left. right. exact Hin.
        + left. apply in_or_app. left. exact Hin.
        + rewrite Hmsg in Hin. apply in_app_or in Hin.
          destruct Hin as [Hin_a | Hin_mid].
          * left. apply in_or_app. left. exact Hin_a.
          * cbn in Hin_mid. destruct Hin_mid as [Heq | Hin_b].
            -- injection Heq as Hnieq Hmieq. subst.
               right.
               pose proof (Hpernode n) as Hpn. rewrite Hpi in Hpn.
               destruct (map.get initial_ns n) as [ns0|] eqn:Hns0; [|contradiction].
               destruct (project_node_gen _ _ _ HT n npi ns0 Hpi Hns0)
                 as (tauB0 & nsB0 & HtauB0 & HgB0 & _).
               assert (nsB0 = nsi) by congruence. subst nsB0.
               exists npi, ns0, (tauB0 ++ [I_event m]), nsi'.
               split; [exact Hpi|]. split; [reflexivity|].
               split; [apply map.get_put_same|].
               split; [eapply star_app; [exact HtauB0 | econstructor; [exact Hsi | constructor]]|].
               rewrite inputs_of_app. cbn. apply in_or_app. right. left. reflexivity.
            -- left. apply in_or_app. right. exact Hin_b.
    Qed.

    (* core_replay: the simulation transfers input-free reachability of an output.
       This is the heart of can_output preservation; proved by replaying the
       witness from the dominating state, re-deriving each node emission via
       cap_transfer + lift_node_outputs. *)
    Lemma core_replay :
      (forall t, A t) ->
      (forall n np, map.get p n = Some np -> input_total (node_step np)) ->
      Forall2_map (fun _ np ns => can_implies_will' (node_step np) A ns) p initial_ns ->
      forall TA gsA, star (graph_step p node_step) initial_graph_state TA gsA ->
      forall W gsfA, star (graph_step p node_step) gsA W gsfA ->
      inputs_of W = [] ->
      forall TB gsB, star (graph_step p node_step) initial_graph_state TB gsB ->
      core_dom gsA gsB ->
      forall o, output_in_trace o W ->
      exists WB gsfB,
        star (graph_step p node_step) gsB WB gsfB /\
        inputs_of WB = [] /\ output_in_trace o WB.
    Proof.
    Admitted.

    (* can_output is preserved by any single graph step (the demon move). *)
    Lemma can_output_step :
      (forall t, A t) ->
      (forall n np, map.get p n = Some np -> input_total (node_step np)) ->
      Forall2_map (fun _ np ns => can_implies_will' (node_step np) A ns) p initial_ns ->
      forall T gs, star (graph_step p node_step) initial_graph_state T gs ->
      forall e gs', graph_step p node_step gs e gs' ->
      forall t o, can_output (graph_step p node_step) gs t o ->
                  can_output (graph_step p node_step) gs' (e :: t) o.
    Proof.
      intros A_univ Hit Hpernode T gs HT e gs' Hstep t o (W & gsf & HW & HinpW & Hout).
      apply output_in_trace_app in Hout as [Hout_W | Hout_t].
      - destruct (core_replay A_univ Hit Hpernode T gs HT W gsf HW HinpW
                    (T ++ [e]) gs'
                    (star_app _ _ _ _ _ _ HT (star_step _ _ _ _ _ _ Hstep (star_refl _ _)))
                    (dom_of_step Hpernode T gs HT e gs' Hstep) o Hout_W)
          as (WB & gsfB & HWB & HinpWB & HoutWB).
        exists WB, gsfB. split; [exact HWB|]. split; [exact HinpWB|].
        apply output_in_trace_app. left. exact HoutWB.
      - exists [], gs'. split; [constructor|]. split; [reflexivity|].
        cbn. destruct Hout_t as (outs & Hin & Hino).
        exists outs. split; [right; exact Hin | exact Hino].
    Qed.

    (* ORCHESTRATION (crux liveness lemma).  If the angel can win after the graph
       performs an internal (input-free) path T_pre, then it can win from gs.
       Intuition: the angel forces the graph along T_pre.  The demon interferes,
       but (i) input_total guarantees the angel can always deliver any queued
       message, (ii) per-node ciw'/monotone' make "arming" permanent (a node that
       can produce o keeps that ability under any further step), and the per-node
       will-trees provide termination of each forced production. *)
    Lemma orchestrate :
      (forall t, A t) ->
      (forall n np, map.get p n = Some np -> input_total (node_step np)) ->
      Forall2_map (fun _ np ns => can_implies_will' (node_step np) A ns) p initial_ns ->
      forall gs t,
        star (graph_step p node_step) initial_graph_state t gs ->
        forall T_pre gs_pre,
          star (graph_step p node_step) gs T_pre gs_pre ->
          inputs_of T_pre = [] ->
          forall o,
            will_output (graph_step p node_step) A gs_pre (T_pre ++ t) o ->
            will_output (graph_step p node_step) A gs t o.
    Proof.
    Admitted.

    Lemma graph_can_implies_will :
      (forall t, A t) ->
      (forall n np, map.get p n = Some np -> input_total (node_step np)) ->
      Forall2_map (fun _ np ns => can_implies_will' (node_step np) A ns) p initial_ns ->
      can_implies_will (graph_step p node_step) A initial_graph_state.
    Proof.
      intros A_univ Hit Hpernode t gs o Hstar Hall Hcan.
      destruct Hcan as (T_a & s_f & Hstar_a & Hinp_a & Hout).
      apply output_in_trace_app in Hout as [Hout_T | Hout_t].
      2: { apply eventually_done. exact Hout_t. }
      (* Find the producing step in T_a (which has inputs_of = []). *)
      destruct (find_producing_step _ _ _ Hstar_a Hinp_a _ Hout_T)
        as (T_pre & T_post & n_o & np_o & ns_o & ns_o' & outs_o
            & gs_pre & gs_post & Heq_T & Hstar_pre_a & Hstep_prod
            & Hstar_post_a & Hinp_pre & Hp_o & Hg_o & Hns_o & Hino_o & Hvis_o).
      (* gs_pre is reachable from the initial state via t ++ T_pre. *)
      pose proof (star_app _ _ _ _ _ _ Hstar Hstar_pre_a) as Hstar_to_pre.
      (* At gs_pre, node n_o is "armed" for o: it can emit o in one step. *)
      assert (Harmed : can_output (node_step np_o) ns_o [] o).
      { exists [O_event outs_o], ns_o'. split; [|split].
        - econstructor; [exact Hns_o | constructor].
        - reflexivity.
        - apply output_in_trace_app. left.
          exists outs_o. split; [left; reflexivity | exact Hino_o]. }
      (* armed_node_drives: the angel wins from gs_pre (with past trace t ++ T_pre). *)
      pose proof (armed_node_drives A_univ Hpernode (t ++ T_pre) gs_pre Hstar_to_pre
                    n_o np_o ns_o o Hp_o Hg_o Hvis_o Harmed) as Hwill_pre.
      (* Reorder the past trace to T_pre ++ t (allowed since A is universal). *)
      assert (Hwill_pre' : will_output (graph_step p node_step) A gs_pre (T_pre ++ t) o).
      { unfold will_output in *.
        apply (eventually_swap o gs_pre (t ++ T_pre) (T_pre ++ t)).
        - rewrite !inputs_of_app, Hinp_pre, app_nil_r. reflexivity.
        - intros x. rewrite !output_in_trace_app. tauto.
        - exact Hwill_pre. }
      (* orchestrate: pull the win back from gs_pre to gs. *)
      apply (orchestrate A_univ Hit Hpernode gs t Hstar T_pre gs_pre
                         Hstar_pre_a Hinp_pre o Hwill_pre').
    Qed.
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
