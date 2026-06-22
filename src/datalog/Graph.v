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

    Lemma graph_can_implies_will :
      (forall t, A t) ->
      Forall2_map (fun _ np ns => can_implies_will (node_step np) A ns) p initial_ns ->
      can_implies_will (graph_step p node_step) A initial_graph_state.
    Proof.
      intros A_univ Hpernode t gs o Hstar Hall Hcan.
      destruct Hcan as (t' & gs' & Hstar' & Hinp' & Hout).
      apply output_in_trace_app in Hout as [Hout_t' | Hout_t].
      2: { apply eventually_done. exact Hout_t. }
      (* Induct on Hstar'. *)
      revert t Hall Hinp' Hout_t' Hstar.
      induction Hstar' as [gs | gs e gs_mid t'_rest gs' Hstep Hstar'_rest IH];
        intros t Hall Hinp' Hout_t' Hstar.
      - cbv [output_in_trace] in Hout_t'.
        destruct Hout_t' as (? & H & _). inversion H.
      - cbn in Hinp'. destruct e as [m | outs]; [discriminate|]. cbn in Hinp'.
        change (O_event outs :: t'_rest) with ([O_event outs] ++ t'_rest) in Hout_t'.
        apply output_in_trace_app in Hout_t' as [Hout_head | Hout_rest].
        + (* Head case: o is in the head O_event outs. *)
          destruct Hout_head as (outs0 & Hin_head & Hino).
          cbn in Hin_head. destruct Hin_head as [Heq|]; [|contradiction].
          injection Heq as Heq. subst outs0.
          inversion Hstep as [|gs0 n0 np0 ns0 ns0' outs_full Hp0 Hg0 Hns0|
                              gs0 n0 np0 ns0 ns0' m0 ms1 ms2 Hp0 Hg0 Hns0 Hmsg];
            subst.
          * (* gstep_run for n0 *)
            rewrite filter_In in Hino. destruct Hino as [Hino_full Hvis].
            pose proof (Hpernode n0) as Hp_n.
            rewrite Hp0 in Hp_n.
            destruct (map.get initial_ns n0) as [ns_init|] eqn:Hns_init; [|contradiction].
            destruct (project_node_gen _ _ _ Hstar n0 np0 ns_init Hp0 Hns_init)
              as (tau_outer & ns_at_gs & Htau_outer & Hg_at_gs & Hpres).
            rewrite Hg_at_gs in Hg0. inversion Hg0. subst ns_at_gs.
            assert (Hwill : eventually (can_step (node_step np0) A)
                              (fun '(_, t'') => output_in_trace o t'')
                              (ns0, tau_outer)).
            { apply Hp_n.
              - exact Htau_outer.
              - unfold allowed_trace; auto.
              - exists [O_event outs_full], ns0'. split.
                + econstructor; [exact Hns0 | constructor].
                + split; [reflexivity|].
                  exists outs_full. split; [left; reflexivity|exact Hino_full]. }
            apply (drive_node_must A_univ np0 n0 o Hp0 Hvis (ns0, tau_outer) Hwill gs t).
            -- cbn. exact Hg_at_gs.
            -- cbn. intros Hout_tau. apply Hpres; [exact Hvis | exact Hout_tau].
          * (* gstep_receive: outs = [] contradicts Hino *)
            cbn in Hino. contradiction.
        + (* Deeper case: o is in t'_rest.  Use eventually_step_cps to advance
             one event, then recurse via IH. *)
          apply eventually_step_cps.
          intros gs_demon t_demon Hstar_demon Hallow_d.
          (* For demon = empty: angel plays e, lands at (gs_mid, e :: t).
             For demon non-empty: similar but need state tracking. *)
          destruct t_demon as [|d t_demon_rest].
          * inversion Hstar_demon; subst.
            exists gs_mid, outs. split; [exact Hstep|].
            apply (eventually_swap o gs_mid (t ++ [O_event outs]) (O_event outs :: t)).
            -- rewrite inputs_of_app. cbn. rewrite app_nil_r. reflexivity.
            -- intros x.
               change (O_event outs :: t) with ([O_event outs] ++ t).
               rewrite !output_in_trace_app. tauto.
            -- apply (IH (t ++ [O_event outs]));
                 [unfold allowed_trace | exact Hinp' | exact Hout_rest |].
               ++ rewrite inputs_of_app. cbn. rewrite app_nil_r. exact Hall.
               ++ eapply star_app; [exact Hstar|].
                  econstructor; [exact Hstep | constructor].
          * (* Demon non-empty: find the producing step deep in t'_rest, then
               apply drive_node_must at gs_demon. *)
            (* Find the producing step in (Hstep + Hstar'_rest). *)
            assert (Hstar_full : star (graph_step p node_step) gs
                                     (O_event outs :: t'_rest) gs').
            { econstructor; [exact Hstep | exact Hstar'_rest]. }
            assert (Hinp_full : inputs_of (O_event outs :: t'_rest) = []) by exact Hinp'.
            assert (Hout_full : output_in_trace o (O_event outs :: t'_rest)).
            { change (O_event outs :: t'_rest) with ([O_event outs] ++ t'_rest).
              apply output_in_trace_app. right. exact Hout_rest. }
            destruct (find_producing_step _ _ _ Hstar_full Hinp_full _ Hout_full)
              as (T_pre & T_post & n_o & np_o & ns_o & ns_o' & outs_o
                  & gs_pre & gs_post & Heq_T & Hstar_pre & Hstep_prod
                  & Hstar_post & Hinp_pre & Hp_o & Hg_o & Hns_o
                  & Hino_o & Hvis_o).
            (* Build per-node will_output at (ns_o, _) trivially via Hpernode. *)
            pose proof (Hpernode n_o) as Hp_n.
            rewrite Hp_o in Hp_n.
            destruct (map.get initial_ns n_o) as [ns_init|] eqn:Hns_init;
              [|contradiction].
            (* Get per-node trace at n_o from initial to gs_demon, plus n_o's state at gs_demon. *)
            assert (Hstar_to_demon :
                      star (graph_step p node_step) initial_graph_state
                           (t ++ d :: t_demon_rest) gs_demon).
            { eapply star_app; [exact Hstar | exact Hstar_demon]. }
            destruct (project_node_gen _ _ _ Hstar_to_demon n_o np_o ns_init
                                       Hp_o Hns_init)
              as (tau_demon & ns_at_demon & Htau_demon & Hg_at_demon & Hpres_demon).
            (* Per-node will_output at (ns_at_demon, tau_demon, o):
               we want this so drive_node_must lifts to graph eventually at gs_demon.

               Strategy attempt: use per-node ciw at (ns_init, tau_demon, ns_at_demon, o)
               via Hp_n.  This requires per-node can_output at (ns_at_demon, tau_demon, o),
               i.e., a no-input per-node path from ns_at_demon producing o.

               That no-input path is the structural obstacle.  Conceptually it should
               exist: gs_demon is on the trajectory toward producing o (since gs is,
               and demon's t_demon is just a prefix of "history" not undoing progress);
               but constructing it formally from the available hypotheses is the
               substantive remaining work. *)
            assert (Hwill_demon :
                      eventually (can_step (node_step np_o) A)
                        (fun '(_, t'') => output_in_trace o t'')
                        (ns_at_demon, tau_demon)).
            { apply Hp_n.
              - exact Htau_demon.
              - unfold allowed_trace; auto.
              - (* per-node can_output at (ns_at_demon, tau_demon, o) *)
                admit. }
            (* Apply drive_node_must at gs_demon. *)
            assert (Hev_demon :
                      eventually (can_step (graph_step p node_step) A)
                                 (fun '(_, t') => output_in_trace o t')
                                 (gs_demon, d :: t_demon_rest ++ t)).
            { apply (drive_node_must A_univ np_o n_o o Hp_o Hvis_o
                       (ns_at_demon, tau_demon) Hwill_demon gs_demon).
              - cbn. exact Hg_at_demon.
              - cbn. intros Hout_tau.
                apply Hpres_demon in Hout_tau; [|exact Hvis_o].
                (* Hout_tau : output_in_trace o (t ++ d :: t_demon_rest).
                   Goal: output_in_trace o (d :: t_demon_rest ++ t). *)
                change (d :: t_demon_rest ++ t) with ([d] ++ t_demon_rest ++ t).
                apply output_in_trace_app.
                apply output_in_trace_app in Hout_tau as [Hout_t|Hout_d].
                + right. apply output_in_trace_app. right. exact Hout_t.
                + change (d :: t_demon_rest) with ([d] ++ t_demon_rest) in Hout_d.
                  apply output_in_trace_app in Hout_d as [Hout_d|Hout_d_rest].
                  * left. exact Hout_d.
                  * right. apply output_in_trace_app. left. exact Hout_d_rest. }
            (* Extract can_step from Hev_demon. *)
            inversion Hev_demon as [HP_done | midset Hcan_step Hmid]; clear Hev_demon.
            -- (* eventually_done: output already in (d :: t_demon_rest ++ t) *)
               cbn in HP_done.
               (* Then we'd need to construct an angel step + eventually.
                  Take any valid angel step (some O_event from gs_demon).
                  But we need to know SOMETHING is steppable.  Use admit. *)
               admit.
            -- (* can_step case: use it to give the response. *)
               cbv [can_step] in Hcan_step.
               specialize (Hcan_step gs_demon [] (star_refl _ _)).
               cbn in Hcan_step.
               specialize (Hcan_step Hallow_d).
               destruct Hcan_step as (s'' & outs' & Hstep' & Hmidset').
               exists s'', outs'. split; [exact Hstep'|].
               apply Hmid. exact Hmidset'.
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
