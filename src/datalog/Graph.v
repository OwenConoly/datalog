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
    (* Each node stores its state together with its own local IO trace (the events
       it has gone through, in forward order).  This makes a node's "projection"
       a pure function of the graph state: it is just [snd (g_nodes n)]. *)
    Context {node_state : Type}
            {node_states : map.map node_id (node_state * list IO_event)}.
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
    | gstep_run gs n np ns t ns' outs :
      map.get p n = Some np ->
      map.get gs.(g_nodes) n = Some (ns, t) ->
      node_step np ns (O_event outs) ns' ->
      graph_step gs (O_event (filter (output_visible n) outs))
                 {| g_nodes := map.put gs.(g_nodes) n (ns', t ++ [O_event outs]);
                   g_messages := gs.(g_messages) ++
                                      flat_map (fun m => map (fun n' => (n', m)) (forward n m))
                                      outs |}
    | gstep_receive gs n np ns t ns' m ms1 ms2 :
      map.get p n = Some np ->
      map.get gs.(g_nodes) n = Some (ns, t) ->
      node_step np ns (I_event m) ns' ->
      gs.(g_messages) = ms1 ++ (n, m) :: ms2 ->
      graph_step gs (O_event [])
                 {| g_nodes := map.put gs.(g_nodes) n (ns', t ++ [I_event m]);
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
    Context {node_state : Type}
            {node_states : map.map node_id (node_state * list IO_event)}.
    Context {node_states_ok : map.ok node_states}.
    Context (p : graph_prog) (initial_ns : node_states).
    (* The initial node states carry empty local traces. *)
    Context (initial_ns_empty :
               forall n x, map.get initial_ns n = Some x -> snd x = []).
    Context (node_step : node_prog -> node_state -> IO_event -> node_state -> Prop).

    Definition initial_graph_state : graph_state :=
      {| g_nodes := initial_ns; g_messages := [] |}.

    (* The state-stored projection: over any drive, node n's stored trace grows by
       a delta [td] that is a valid node run from n's state, whose visible outputs
       all appear in the graph trace.  Replaces the old project_node_gen. *)
    Lemma node_drive_delta :
      forall T gs0 gs,
        star (graph_step p node_step) gs0 T gs ->
        forall n np ns t,
          map.get p n = Some np ->
          map.get gs0.(g_nodes) n = Some (ns, t) ->
          exists ns' td,
            map.get gs.(g_nodes) n = Some (ns', t ++ td) /\
            star (node_step np) ns td ns' /\
            (forall o, output_visible n o = true ->
                       output_in_trace o td -> output_in_trace o T).
    Proof.
      intros T gs0 gs Hstar.
      induction Hstar as [s|s e s' t0 s'' Hstep Hstar IH];
        intros n np ns t Hp Hg0.
      - exists ns, []. rewrite app_nil_r. split; [exact Hg0|]. split; [constructor|].
        intros o _ (outs & Hin & _); inversion Hin.
      - inversion Hstep as [ gs1 ni mi Hia
                           | gs1 ni npi nsi ti nsi' outsi Hpi Hgi Hsi
                           | gs1 ni npi nsi ti nsi' mi msa msb Hpi Hgi Hsi Hmsg ]; subst.
        + destruct (IH n np ns t Hp Hg0) as (ns' & td & Hg & Hstd & Hpres).
          exists ns', td. split; [exact Hg|]. split; [exact Hstd|].
          intros o Hvis Hout. specialize (Hpres o Hvis Hout).
          destruct Hpres as (outs' & Hin & Hino). exists outs'. split; [right; exact Hin|exact Hino].
        + destruct (Nat.eq_dec n ni) as [Heq|Hne].
          * subst ni. assert (npi = np) by congruence. subst npi.
            assert (Heqp : (nsi, ti) = (ns, t)) by congruence.
            injection Heqp as Hns Ht; subst nsi ti.
            destruct (IH n np nsi' (t ++ [O_event outsi]) Hp) as (ns' & td & Hg & Hstd & Hpres).
            { cbn. apply map.get_put_same. }
            exists ns', (O_event outsi :: td).
            replace (t ++ O_event outsi :: td) with ((t ++ [O_event outsi]) ++ td)
              by (rewrite <- app_assoc; reflexivity).
            split; [exact Hg|]. split; [econstructor; [exact Hsi | exact Hstd]|].
            intros o Hvis (outs' & Hin & Hino). cbn in Hin. destruct Hin as [Heq|Hin_rest].
            -- injection Heq as Heq_outs. subst outs'.
               exists (filter (output_visible n) outsi). split; [left; reflexivity|].
               apply filter_In. split; [exact Hino|exact Hvis].
            -- specialize (Hpres o Hvis (ex_intro _ outs' (conj Hin_rest Hino))).
               destruct Hpres as (outs'' & Hin'' & Hino''). exists outs''.
               split; [right; exact Hin''|exact Hino''].
          * destruct (IH n np ns t Hp) as (ns' & td & Hg & Hstd & Hpres).
            { cbn. rewrite map.get_put_diff by auto. exact Hg0. }
            exists ns', td. split; [exact Hg|]. split; [exact Hstd|].
            intros o Hvis Hout. specialize (Hpres o Hvis Hout).
            destruct Hpres as (outs' & Hin & Hino). exists outs'. split; [right; exact Hin|exact Hino].
        + destruct (Nat.eq_dec n ni) as [Heq|Hne].
          * subst ni. assert (npi = np) by congruence. subst npi.
            assert (Heqp : (nsi, ti) = (ns, t)) by congruence.
            injection Heqp as Hns Ht; subst nsi ti.
            destruct (IH n np nsi' (t ++ [I_event mi]) Hp) as (ns' & td & Hg & Hstd & Hpres).
            { cbn. apply map.get_put_same. }
            exists ns', (I_event mi :: td).
            replace (t ++ I_event mi :: td) with ((t ++ [I_event mi]) ++ td)
              by (rewrite <- app_assoc; reflexivity).
            split; [exact Hg|]. split; [econstructor; [exact Hsi | exact Hstd]|].
            intros o Hvis (outs' & Hin & Hino). cbn in Hin. destruct Hin as [Heq|Hin_rest];
              [discriminate|].
            specialize (Hpres o Hvis (ex_intro _ outs' (conj Hin_rest Hino))).
            destruct Hpres as (outs'' & Hin'' & Hino''). exists outs''.
            split; [right; exact Hin''|exact Hino''].
          * destruct (IH n np ns t Hp) as (ns' & td & Hg & Hstd & Hpres).
            { cbn. rewrite map.get_put_diff by auto. exact Hg0. }
            exists ns', td. split; [exact Hg|]. split; [exact Hstd|].
            intros o Hvis Hout. specialize (Hpres o Hvis Hout).
            destruct Hpres as (outs' & Hin & Hino). exists outs'. split; [right; exact Hin|exact Hino].
    Qed.

    (* Specialization to runs from the initial graph state: a node's stored trace
       IS its projection — a valid node run from its bare initial state, whose
       visible outputs all appear in the graph trace. *)
    Lemma project_node_gen :
      forall T gs,
        star (graph_step p node_step) initial_graph_state T gs ->
        forall n np ns0,
          map.get p n = Some np ->
          map.get initial_ns n = Some ns0 ->
          exists tau ns_at,
            star (node_step np) (fst ns0) tau ns_at /\
            map.get gs.(g_nodes) n = Some (ns_at, tau) /\
            (forall o, output_visible n o = true ->
                       output_in_trace o tau -> output_in_trace o T).
    Proof.
      intros T gs Hstar n np ns0 Hp Hns0.
      pose proof (initial_ns_empty n ns0 Hns0) as Hempty.
      destruct ns0 as [ns0b t0b]. cbn in Hempty. subst t0b. cbn [fst].
      destruct (node_drive_delta _ _ _ Hstar n np ns0b [] Hp Hns0)
        as (ns' & td & Hg & Hstd & Hpres).
      rewrite app_nil_l in Hg.
      exists td, ns'. split; [exact Hstd|]. split; [exact Hg|]. exact Hpres.
    Qed.

    (* With traces stored in the state, "node n has received message mu" is simply:
       mu appears in the inputs of n's stored trace. *)
    Definition node_received (gs : @graph_state node_state node_states)
        (n : node_id) (mu : message) : Prop :=
      exists ns t, map.get gs.(g_nodes) n = Some (ns, t) /\ In mu (inputs_of t).

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
            (exists tr, map.get gs.(g_nodes) n = Some (fst s, tr)) ->
            (output_in_trace o (snd s) -> output_in_trace o t) ->
            eventually (can_step (graph_step p node_step) A)
                       (fun '(_, t') => output_in_trace o t') (gs, t).
    Proof.
      intros A_univ np n o Hp Hvis s Hwill.
      induction Hwill as [[ns_curr trace_curr] HP|
                          [ns_curr trace_curr] midset Hcan Hmid IH];
        intros gs t Hg Hout_proj.
      - apply eventually_done. cbn. apply Hout_proj. exact HP.
      - cbn in Hg. destruct Hg as (tr & Hg).
        apply eventually_step_cps.
        intros gs_demon t_demon Hstar_demon Hallow_g.
        destruct (node_drive_delta _ _ _ Hstar_demon n np ns_curr tr Hp Hg)
          as (ns_d & tau_d & Hg_d & Htau_d & Hpres_d).
        pose proof (Hcan ns_d tau_d Htau_d) as Hcan'.
        assert (Hallow_n : allowed_trace (tau_d ++ trace_curr))
          by (unfold allowed_trace; auto).
        specialize (Hcan' Hallow_n).
        destruct Hcan' as (s'' & outs & Hns_step & Hmidset_at).
        set (gs_next :=
               {| g_nodes := map.put gs_demon.(g_nodes) n (s'', (tr ++ tau_d) ++ [O_event outs]);
                  g_messages :=
                    gs_demon.(g_messages) ++
                    flat_map (fun m0 => map (fun n' => (n', m0))
                                            (forward n m0)) outs |}).
        exists gs_next, (filter (output_visible n) outs).
        split.
        { eapply gstep_run; [exact Hp | exact Hg_d | exact Hns_step]. }
        apply (IH (s'', O_event outs :: tau_d ++ trace_curr) Hmidset_at gs_next).
        + cbn. exists ((tr ++ tau_d) ++ [O_event outs]). apply map.get_put_same.
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
                 (ns_o ns_o' : node_state) (t_o : list IO_event)
                 (outs_o : list message)
                 (gs_pre gs_post : graph_state),
            T = T_pre ++ O_event (filter (output_visible n_o) outs_o) :: T_post /\
            star (graph_step p node_step) gs_start T_pre gs_pre /\
            graph_step p node_step gs_pre
                       (O_event (filter (output_visible n_o) outs_o)) gs_post /\
            star (graph_step p node_step) gs_post T_post s_f /\
            inputs_of T_pre = [] /\
            map.get p n_o = Some np_o /\
            map.get gs_pre.(g_nodes) n_o = Some (ns_o, t_o) /\
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
            | gs0 n0 np0 ns0 t0n ns0' outs_full Hp0 Hg0 Hns0
            | gs0 n0 np0 ns0 t0n ns0' m0 ms1 ms2 Hp0 Hg0 Hns0 Hmsg ]; subst.
          * (* gstep_run for n0 *)
            rewrite filter_In in Hino0. destruct Hino0 as [Hino_full Hvis].
            exists [], t0, n0, np0, ns0, ns0', t0n, outs_full, s,
              {| g_nodes := map.put s.(g_nodes) n0 (ns0', t0n ++ [O_event outs_full]);
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
          destruct IH as (T_pre & T_post & n_o & np_o & ns_o & ns_o' & t_o & outs_o
                          & gs_pre & gs_post & Heq_T & Hstar_pre & Hstep_prod
                          & Hstar_post & Hinp_pre & Hp_o & Hg_o & Hns_o
                          & Hino_o & Hvis_o).
          exists (O_event outs_e :: T_pre), T_post, n_o, np_o, ns_o, ns_o', t_o, outs_o,
                 gs_pre, gs_post.
          split; [cbn; rewrite Heq_T; reflexivity|].
          split; [econstructor; [exact Hstep|exact Hstar_pre]|].
          split; [exact Hstep_prod|]. split; [exact Hstar_post|].
          split; [cbn; exact Hinp_pre|].
          split; [exact Hp_o|]. split; [exact Hg_o|].
          split; [exact Hns_o|]. split; [exact Hino_o | exact Hvis_o].
    Qed.

    (* node_received is monotone under graph evolution: a node's stored trace only
       grows, so a delivered message stays recorded. *)
    Lemma node_received_mono :
      forall gs T gs', star (graph_step p node_step) gs T gs' ->
        forall n m, node_received gs n m -> node_received gs' n m.
    Proof.
      intros gs T gs' Hstar.
      induction Hstar as [s | s e s' T' s'' Hstep Hstar IH]; intros n m Hr.
      - exact Hr.
      - apply (IH n m). destruct Hr as (ns & t & Hg & Hin).
        inversion Hstep as [ gs0 ni mi Hia
                           | gs0 ni npi nsi ti nsi' outsi Hpi Hgi Hsi
                           | gs0 ni npi nsi ti nsi' mi msa msb Hpi Hgi Hsi Hmsg ]; subst.
        + exists ns, t. split; [exact Hg | exact Hin].
        + destruct (Nat.eq_dec n ni) as [->|Hne].
          * rewrite Hgi in Hg. injection Hg as Hns Ht; subst nsi ti.
            exists nsi', (t ++ [O_event outsi]).
            split; [cbn; apply map.get_put_same|].
            rewrite inputs_of_app. apply in_or_app. left. exact Hin.
          * exists ns, t.
            split; [cbn; rewrite map.get_put_diff by auto; exact Hg | exact Hin].
        + destruct (Nat.eq_dec n ni) as [->|Hne].
          * rewrite Hgi in Hg. injection Hg as Hns Ht; subst nsi ti.
            exists nsi', (t ++ [I_event mi]).
            split; [cbn; apply map.get_put_same|].
            rewrite inputs_of_app. apply in_or_app. left. exact Hin.
          * exists ns, t.
            split; [cbn; rewrite map.get_put_diff by auto; exact Hg | exact Hin].
    Qed.

    (* Message provenance: a message queued at gs is, after any graph evolution,
       either still queued, or has been delivered to its destination (recorded in
       that node's stored trace). *)
    Lemma queue_fate :
      forall gs T gs', star (graph_step p node_step) gs T gs' ->
        forall n m, In (n, m) gs.(g_messages) ->
          In (n, m) gs'.(g_messages) \/ node_received gs' n m.
    Proof.
      intros gs T gs' Hstar.
      induction Hstar as [s | s e s' T' s'' Hstep Hstar IH]; intros n m Hin.
      - left. exact Hin.
      - inversion Hstep as [ gs0 ni mi Hia
                           | gs0 ni npi nsi ti nsi' outsi Hpi Hgi Hsi
                           | gs0 ni npi nsi ti nsi' mi msa msb Hpi Hgi Hsi Hmsg ];
          subst; cbn [g_nodes g_messages] in IH |- *.
        + edestruct (IH n m) as [Hq | Hr];
            [right; exact Hin | left; exact Hq | right; exact Hr].
        + edestruct (IH n m) as [Hq | Hr];
            [apply in_or_app; left; exact Hin | left; exact Hq | right; exact Hr].
        + rewrite Hmsg in Hin. apply in_app_or in Hin.
          destruct Hin as [Hin_a | Hin_mid].
          * edestruct (IH n m) as [Hq | Hr];
              [apply in_or_app; left; exact Hin_a | left; exact Hq | right; exact Hr].
          * cbn in Hin_mid. destruct Hin_mid as [Heq2 | Hin_b].
            -- injection Heq2 as Hnieq Hmieq; subst ni mi.
               right. apply (node_received_mono _ _ _ Hstar).
               exists nsi', (ti ++ [I_event m]). split; [cbn; apply map.get_put_same|].
               rewrite inputs_of_app. apply in_or_app. right. left. reflexivity.
            -- edestruct (IH n m) as [Hq | Hr];
                 [apply in_or_app; right; exact Hin_b | left; exact Hq | right; exact Hr].
    Qed.

    (* A graph step preserves the node domain. *)
    Lemma graph_step_dom :
      forall gs e gs', graph_step p node_step gs e gs' ->
      forall k, map.get gs.(g_nodes) k = None <-> map.get gs'.(g_nodes) k = None.
    Proof.
      intros gs e gs' Hstep k.
      inversion Hstep as [ gs1 ni mi Hia
                         | gs1 ni npi nsi ti nsi' outsi Hpi Hgi Hsi
                         | gs1 ni npi nsi ti nsi' mi msa msb Hpi Hgi Hsi Hmsg ]; subst; cbn.
      - reflexivity.
      - destruct (Nat.eq_dec k ni) as [->|Hne].
        + rewrite map.get_put_same, Hgi. split; intro HH; discriminate.
        + rewrite map.get_put_diff by auto. reflexivity.
      - destruct (Nat.eq_dec k ni) as [->|Hne].
        + rewrite map.get_put_same, Hgi. split; intro HH; discriminate.
        + rewrite map.get_put_diff by auto. reflexivity.
    Qed.

    (* A graph state is "saturated" if every message any node has emitted (recorded
       in its stored trace) is still queued or already delivered to its target. *)
    Definition saturated (gs : @graph_state node_state node_states) : Prop :=
      forall n np ns t,
        map.get p n = Some np ->
        map.get gs.(g_nodes) n = Some (ns, t) ->
        forall mu n', output_in_trace mu t -> In n' (forward n mu) ->
          In (n', mu) gs.(g_messages) \/ node_received gs n' mu.

    Lemma sat_step :
      forall gs e gs', graph_step p node_step gs e gs' -> saturated gs -> saturated gs'.
    Proof.
      intros gs e gs' Hstep Hsat n np ns t Hp Hg mu n' Hout Hfwd.
      assert (Hmono1 : forall n0 m0, node_received gs n0 m0 -> node_received gs' n0 m0).
      { intros n0 m0 Hr.
        apply (node_received_mono _ _ _ (star_step _ _ _ _ _ _ Hstep (star_refl _ _))).
        exact Hr. }
      inversion Hstep as [ gs0 ni mi Hia
                         | gs0 ni npi nsi ti nsi' outsi Hpi Hgi Hsi
                         | gs0 ni npi nsi ti nsi' mi msa msb Hpi Hgi Hsi Hmsg ]; subst.
      - (* gstep_input *)
        cbn in Hg.
        destruct (Hsat n np ns t Hp Hg mu n' Hout Hfwd) as [Hq | Hr].
        + left. cbn. right. exact Hq.
        + right. apply Hmono1. exact Hr.
      - (* gstep_run ni *)
        destruct (Nat.eq_dec n ni) as [->|Hne].
        + cbn in Hg. rewrite map.get_put_same in Hg. inversion Hg; subst.
          apply output_in_trace_app in Hout as [Hout_old | Hout_new].
          * destruct (Hsat ni npi nsi ti Hpi Hgi mu n' Hout_old Hfwd) as [Hq | Hr].
            -- left. cbn. apply in_or_app. left. exact Hq.
            -- right. apply Hmono1. exact Hr.
          * destruct Hout_new as (outs0 & Hin0 & Hino0). cbn in Hin0.
            destruct Hin0 as [Heq0|[]]. injection Heq0 as Heq0; subst outs0.
            left. cbn. apply in_or_app. right.
            apply in_flat_map. exists mu. split; [exact Hino0|].
            apply in_map_iff. exists n'. split; [reflexivity | exact Hfwd].
        + cbn in Hg. rewrite map.get_put_diff in Hg by auto.
          destruct (Hsat n np ns t Hp Hg mu n' Hout Hfwd) as [Hq | Hr].
          * left. cbn. apply in_or_app. left. exact Hq.
          * right. apply Hmono1. exact Hr.
      - (* gstep_receive ni mi *)
        destruct (Nat.eq_dec n ni) as [->|Hne].
        + cbn in Hg. rewrite map.get_put_same in Hg. inversion Hg; subst.
          assert (Hout_ti : output_in_trace mu ti).
          { apply output_in_trace_app in Hout as [H|H]; [exact H|].
            destruct H as (outs0 & Hin0 & _). cbn in Hin0.
            destruct Hin0 as [Heq0|[]]. discriminate Heq0. }
          destruct (Hsat ni npi nsi ti Hpi Hgi mu n' Hout_ti Hfwd) as [Hq | Hr].
          * rewrite Hmsg in Hq. apply in_app_or in Hq. destruct Hq as [Hqa | Hqm].
            -- left. cbn. apply in_or_app. left. exact Hqa.
            -- cbn in Hqm. destruct Hqm as [Heqm | Hqb].
               ++ injection Heqm as Hn'eq Hmueq; subst n' mu.
                  right. exists ns, (ti ++ [I_event mi]).
                  split; [cbn; apply map.get_put_same|].
                  rewrite inputs_of_app. apply in_or_app. right. left. reflexivity.
               ++ left. cbn. apply in_or_app. right. exact Hqb.
          * right. apply Hmono1. exact Hr.
        + cbn in Hg. rewrite map.get_put_diff in Hg by auto.
          destruct (Hsat n np ns t Hp Hg mu n' Hout Hfwd) as [Hq | Hr].
          * rewrite Hmsg in Hq. apply in_app_or in Hq. destruct Hq as [Hqa | Hqm].
            -- left. cbn. apply in_or_app. left. exact Hqa.
            -- cbn in Hqm. destruct Hqm as [Heqm | Hqb].
               ++ injection Heqm as Hn'eq Hmueq; subst n' mu.
                  right. exists nsi', (ti ++ [I_event mi]).
                  split; [cbn; apply map.get_put_same|].
                  rewrite inputs_of_app. apply in_or_app. right. left. reflexivity.
               ++ left. cbn. apply in_or_app. right. exact Hqb.
          * right. apply Hmono1. exact Hr.
    Qed.

    Lemma saturated_star :
      forall gs0 T gs, star (graph_step p node_step) gs0 T gs ->
        saturated gs0 -> saturated gs.
    Proof.
      intros gs0 T gs Hstar. induction Hstar as [s | s e s' T' s'' Hstep Hstar IH];
        intro Hsat; [exact Hsat | apply IH; eapply sat_step; eauto].
    Qed.

    Lemma graph_saturated :
      forall T gs, star (graph_step p node_step) initial_graph_state T gs -> saturated gs.
    Proof.
      intros T gs Hstar. eapply saturated_star; [exact Hstar|].
      intros n np ns t Hp Hg mu n' Hout Hfwd.
      cbn in Hg. apply initial_ns_empty in Hg as Ht. cbn in Ht. subst t.
      destruct Hout as (outs & Hin & _); inversion Hin.
    Qed.

    (* Per-node ciw' gives per-node ciw. *)
    Lemma pernode_ciw :
      Forall2_map (fun _ np x => can_implies_will' (node_step np) A (fst x)) p initial_ns ->
      forall n_o np_o ns0,
        map.get p n_o = Some np_o ->
        map.get initial_ns n_o = Some ns0 ->
        can_implies_will (node_step np_o) A (fst ns0).
    Proof.
      intros Hpernode n_o np_o ns0 Hp_o Hns0.
      pose proof (Hpernode n_o) as Hp_n.
      rewrite Hp_o, Hns0 in Hp_n.
      apply (ciw'_iff_ciw_and_monotone' (node_step np_o) A (fst ns0)) in Hp_n.
      apply Hp_n.
    Qed.

    (* Per-node ciw' gives per-node monotone'. *)
    Lemma pernode_monotone' :
      Forall2_map (fun _ np x => can_implies_will' (node_step np) A (fst x)) p initial_ns ->
      forall n_o np_o ns0,
        map.get p n_o = Some np_o ->
        map.get initial_ns n_o = Some ns0 ->
        monotone' (node_step np_o) A (fst ns0).
    Proof.
      intros Hpernode n_o np_o ns0 Hp_o Hns0.
      pose proof (Hpernode n_o) as Hp_n.
      rewrite Hp_o, Hns0 in Hp_n.
      apply (ciw'_iff_ciw_and_monotone' (node_step np_o) A (fst ns0)) in Hp_n.
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
      Forall2_map (fun _ np x => can_implies_will' (node_step np) A (fst x)) p initial_ns ->
      forall n np ns0,
        map.get p n = Some np ->
        map.get initial_ns n = Some ns0 ->
        forall tau_W ns_W tau_act ns_act o',
          star (node_step np) (fst ns0) tau_W ns_W ->
          star (node_step np) (fst ns0) tau_act ns_act ->
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
      Forall2_map (fun _ np x => can_implies_will' (node_step np) A (fst x)) p initial_ns ->
      forall (t : list IO_event) (gs : graph_state),
        star (graph_step p node_step) initial_graph_state t gs ->
        forall (n_o : node_id) (np_o : node_prog) (ns_o : node_state)
               (t_o : list IO_event) (o : message),
          map.get p n_o = Some np_o ->
          map.get gs.(g_nodes) n_o = Some (ns_o, t_o) ->
          output_visible n_o o = true ->
          can_output (node_step np_o) ns_o [] o ->
          will_output (graph_step p node_step) A gs t o.
    Proof.
      intros A_univ Hpernode t gs Hstar n_o np_o ns_o t_o o Hp_o Hg_o Hvis Harmed.
      destruct (map.get initial_ns n_o) as [ns0|] eqn:Hns0.
      2:{ pose proof (Hpernode n_o) as Hp_n. rewrite Hp_o, Hns0 in Hp_n.
          contradiction. }
      pose proof (pernode_ciw Hpernode n_o np_o ns0 Hp_o Hns0) as Hciw_node.
      destruct (project_node_gen _ _ Hstar n_o np_o ns0 Hp_o Hns0)
        as (tau & ns_at_gs & Htau & Hg_at_gs & Hpres).
      assert (ns_at_gs = ns_o) by congruence.
      assert (tau = t_o) by congruence. subst ns_at_gs tau.
      assert (Hcan_tau : can_output (node_step np_o) ns_o t_o o).
      { destruct Harmed as (t' & s' & Hstar' & Hinp' & Hout').
        exists t', s'. split; [exact Hstar'|]. split; [exact Hinp'|].
        apply output_in_trace_app. left. rewrite app_nil_r in Hout'. exact Hout'. }
      pose proof (Hciw_node t_o ns_o o Htau (allowed_trace_universal A A_univ t_o) Hcan_tau)
        as Hwill_node.
      apply (drive_node_must A_univ np_o n_o o Hp_o Hvis (ns_o, t_o) Hwill_node gs t).
      - cbn. exists t_o. exact Hg_o.
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
          forall gs t_pre, map.get gs.(g_nodes) n = Some (ns, t_pre) ->
          exists (T : list IO_event) (gs' : graph_state),
            star (graph_step p node_step) gs T gs' /\
            inputs_of T = [] /\
            map.get gs'.(g_nodes) n = Some (ns', t_pre ++ tau) /\
            (forall n2, n2 <> n -> map.get gs'.(g_nodes) n2 = map.get gs.(g_nodes) n2) /\
            (exists extra, gs'.(g_messages) = gs.(g_messages) ++ extra) /\
            (forall outs mu n'', In (O_event outs) tau -> In mu outs ->
                In n'' (forward n mu) -> In (n'', mu) gs'.(g_messages)) /\
            (forall o', output_visible n o' = true -> output_in_trace o' tau ->
                output_in_trace o' T).
    Proof.
      intros n np Hp ns tau ns' Hstar.
      induction Hstar as [s | s e s2 tau0 s3 Hstep Hstar IH];
        intros Hinp gs t_pre Hg.
      - exists [], gs. split; [constructor|]. split; [reflexivity|].
        rewrite app_nil_r.
        split; [exact Hg|]. split; [reflexivity|].
        split; [exists []; rewrite app_nil_r; reflexivity|].
        split; [intros ? ? ? Hin; inversion Hin|].
        intros o' _ (outs & Hin & _); inversion Hin.
      - cbn in Hinp. destruct e as [m|outs]; [discriminate|]. cbn in Hinp.
        assert (Hg1 : map.get (map.put gs.(g_nodes) n (s2, t_pre ++ [O_event outs])) n
                      = Some (s2, t_pre ++ [O_event outs]))
          by apply map.get_put_same.
        destruct (IH Hinp {| g_nodes := map.put gs.(g_nodes) n (s2, t_pre ++ [O_event outs]);
                             g_messages := gs.(g_messages) ++
                               flat_map (fun mm => map (fun n' => (n', mm)) (forward n mm)) outs |}
                    (t_pre ++ [O_event outs])
                    Hg1)
          as (T & gsf & HstarT & HinpT & Hgf & Hother & (extra & Hextra) & Hfwd & Hvis).
        cbn in Hother, Hextra.
        exists (O_event (filter (output_visible n) outs) :: T), gsf.
        split; [econstructor; [eapply gstep_run; eauto | exact HstarT]|].
        split; [cbn; exact HinpT|].
        split.
        { rewrite <- app_assoc in Hgf. exact Hgf. }
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
      (forall n nsA tA,
         map.get gsA.(g_nodes) n = Some (nsA, tA) ->
         exists nsB tB,
           map.get gsB.(g_nodes) n = Some (nsB, tB) /\
           incl (inputs_of tA) (inputs_of tB))
      /\
      (forall n m, In (n, m) gsA.(g_messages) ->
         In (n, m) gsB.(g_messages) \/ node_received gsB n m).

    (* A single graph step establishes the simulation from gs to gs'. *)
    Lemma dom_of_step :
      forall gs e gs', graph_step p node_step gs e gs' ->
      core_dom gs gs'.
    Proof.
      intros gs e gs' Hstep. split.
      - intros n nsA tA HgA.
        inversion Hstep as [ gs0 ni mi Hia
                           | gs0 ni npi nsi ti nsi' outsi Hpi Hgi Hsi
                           | gs0 ni npi nsi ti nsi' mi msa msb Hpi Hgi Hsi Hmsg ]; subst; cbn.
        + exists nsA, tA. split; [exact HgA|]. apply incl_refl.
        + destruct (Nat.eq_dec n ni) as [Heq|Hne].
          * subst ni. cbn in HgA.
            assert (nsi = nsA) by congruence. assert (ti = tA) by congruence. subst nsi ti.
            exists nsi', (tA ++ [O_event outsi]). split; [apply map.get_put_same|].
            rewrite inputs_of_app. cbn. rewrite app_nil_r. apply incl_refl.
          * exists nsA, tA. split; [rewrite map.get_put_diff by auto; exact HgA|].
            apply incl_refl.
        + destruct (Nat.eq_dec n ni) as [Heq|Hne].
          * subst ni. cbn in HgA.
            assert (nsi = nsA) by congruence. assert (ti = tA) by congruence. subst nsi ti.
            exists nsi', (tA ++ [I_event mi]). split; [apply map.get_put_same|].
            rewrite inputs_of_app. cbn. apply incl_appl. apply incl_refl.
          * exists nsA, tA. split; [rewrite map.get_put_diff by auto; exact HgA|].
            apply incl_refl.
      - intros n m Hin.
        inversion Hstep as [ gs0 ni mi Hia
                           | gs0 ni npi nsi ti nsi' outsi Hpi Hgi Hsi
                           | gs0 ni npi nsi ti nsi' mi msa msb Hpi Hgi Hsi Hmsg ]; subst; cbn.
        + left. right. exact Hin.
        + left. apply in_or_app. left. exact Hin.
        + rewrite Hmsg in Hin. apply in_app_or in Hin.
          destruct Hin as [Hin_a | Hin_mid].
          * left. apply in_or_app. left. exact Hin_a.
          * cbn in Hin_mid. destruct Hin_mid as [Heq | Hin_b].
            -- injection Heq as Hnieq Hmieq. subst.
               right. exists nsi', (ti ++ [I_event m]).
               split; [cbn; apply map.get_put_same|].
               rewrite inputs_of_app. apply in_or_app. right. left. reflexivity.
            -- left. apply in_or_app. right. exact Hin_b.
    Qed.

    (* can_output depends on its past trace only through the past's output
       multiset, so a past trace with more outputs can only help. *)
    Lemma can_output_out_ext :
      forall (np : node_prog) ns tau tau' mu,
        (forall x, output_in_trace x tau -> output_in_trace x tau') ->
        can_output (node_step np) ns tau mu ->
        can_output (node_step np) ns tau' mu.
    Proof.
      intros np ns tau tau' mu Hsub (t' & s' & Hstar & Hinp & Hout).
      exists t', s'. split; [exact Hstar|]. split; [exact Hinp|].
      apply output_in_trace_app in Hout as [H|H].
      - apply output_in_trace_app. left. exact H.
      - apply output_in_trace_app. right. apply Hsub. exact H.
    Qed.

    (* Arming is permanent at the node level: if a node (reachable from its bare
       init via tau, hence ciw applies) can output mu, then after any further node
       run it can still output mu.  Iterates can_output_step_preserved. *)
    Lemma can_output_star_preserved :
      (forall t, A t) ->
      forall (np : node_prog) ns0,
        can_implies_will (node_step np) A ns0 ->
        forall td ns ns', star (node_step np) ns td ns' ->
        forall tau, star (node_step np) ns0 tau ns ->
        forall mu, can_output (node_step np) ns tau mu ->
          can_output (node_step np) ns' (tau ++ td) mu.
    Proof.
      intros A_univ np ns0 Hciw td ns ns' Hstar.
      induction Hstar as [s | s e s2 td0 s3 Hstep Hstar IH];
        intros tau Hreach mu Hcan.
      - rewrite app_nil_r. exact Hcan.
      - assert (Hcan2 : can_output (node_step np) s2 (e :: tau) mu)
          by (eapply can_output_step_preserved; eauto).
        assert (Hreach2 : star (node_step np) ns0 (tau ++ [e]) s2)
          by (eapply star_app; [exact Hreach | econstructor; [exact Hstep | constructor]]).
        assert (Hcan2' : can_output (node_step np) s2 (tau ++ [e]) mu).
        { eapply can_output_out_ext; [|exact Hcan2]. intros x.
          change (e :: tau) with ([e] ++ tau). rewrite !output_in_trace_app. tauto. }
        specialize (IH (tau ++ [e]) Hreach2 mu Hcan2').
        rewrite <- app_assoc in IH. cbn in IH. exact IH.
    Qed.

    (* Arming is permanent at the graph level: a node armed for mu at a reachable
       gs stays armed after any further graph evolution. *)
    Lemma node_armed_preserved :
      (forall t, A t) ->
      Forall2_map (fun _ np x => can_implies_will' (node_step np) A (fst x)) p initial_ns ->
      forall T gs, star (graph_step p node_step) initial_graph_state T gs ->
      forall n np ns t_n mu,
        map.get p n = Some np ->
        map.get gs.(g_nodes) n = Some (ns, t_n) ->
        can_output (node_step np) ns t_n mu ->
        forall T2 gs', star (graph_step p node_step) gs T2 gs' ->
        exists ns' t_n',
          map.get gs'.(g_nodes) n = Some (ns', t_n') /\
          can_output (node_step np) ns' t_n' mu.
    Proof.
      intros A_univ Hpernode T gs HT n np ns t_n mu Hp Hg Hcan T2 gs' Hstar2.
      destruct (map.get initial_ns n) as [ns0|] eqn:Hns0.
      2:{ pose proof (Hpernode n) as H. rewrite Hp, Hns0 in H. contradiction. }
      pose proof (pernode_ciw Hpernode n np ns0 Hp Hns0) as Hciw.
      destruct (project_node_gen _ _ HT n np ns0 Hp Hns0)
        as (tau & ns_at & Htau & Hg_at & _).
      assert (ns_at = ns) by congruence. assert (tau = t_n) by congruence.
      subst ns_at tau.
      destruct (node_drive_delta _ _ _ Hstar2 n np ns t_n Hp Hg)
        as (ns' & td & Hg' & Hstd & _).
      exists ns', (t_n ++ td). split; [exact Hg'|].
      eapply can_output_star_preserved;
        [exact A_univ | exact Hciw | exact Hstd | exact Htau | exact Hcan].
    Qed.

    (* "node n has emitted mu" — mu appears as an output in n's stored trace. *)
    Definition node_emitted (gs : @graph_state node_state node_states)
        (n : node_id) (mu : message) : Prop :=
      exists ns t, map.get gs.(g_nodes) n = Some (ns, t) /\ output_in_trace mu t.

    (* Lift a node-level will-to-emit-mu into a graph-level eventually that forces
       mu into n's stored trace.  Mirrors drive_node_must, but tracks emission via
       the node's stored trace (so mu need not be visible). *)
    Lemma drive_node_emit :
      (forall t, A t) ->
      forall (np : node_prog) (n : node_id) (mu : message),
        map.get p n = Some np ->
        forall (s : node_state * list IO_event),
          eventually (can_step (node_step np) A)
                     (fun '(_, t') => output_in_trace mu t') s ->
          forall gs t,
            (exists tr, map.get gs.(g_nodes) n = Some (fst s, tr) /\
                        (forall x, output_in_trace x (snd s) -> output_in_trace x tr)) ->
            eventually (can_step (graph_step p node_step) A)
                       (fun '(gs', _) => node_emitted gs' n mu) (gs, t).
    Proof.
      intros A_univ np n mu Hp s Hwill.
      induction Hwill as [[ns_curr trace_curr] HP|
                          [ns_curr trace_curr] midset Hcan Hmid IH];
        intros gs t (tr & Hg & Hsub).
      - apply eventually_done. cbn in HP |- *.
        exists ns_curr, tr. split; [exact Hg|]. apply Hsub. exact HP.
      - cbn in Hg, Hsub.
        apply eventually_step_cps.
        intros gs_demon t_demon Hstar_demon Hallow_g.
        destruct (node_drive_delta _ _ _ Hstar_demon n np ns_curr tr Hp Hg)
          as (ns_d & tau_d & Hg_d & Htau_d & Hpres_d).
        pose proof (Hcan ns_d tau_d Htau_d) as Hcan'.
        assert (Hallow_n : allowed_trace (tau_d ++ trace_curr))
          by (unfold allowed_trace; auto).
        specialize (Hcan' Hallow_n).
        destruct Hcan' as (s'' & outs & Hns_step & Hmidset_at).
        set (gs_next :=
               {| g_nodes := map.put gs_demon.(g_nodes) n (s'', (tr ++ tau_d) ++ [O_event outs]);
                  g_messages :=
                    gs_demon.(g_messages) ++
                    flat_map (fun m0 => map (fun n' => (n', m0))
                                            (forward n m0)) outs |}).
        exists gs_next, (filter (output_visible n) outs).
        split.
        { eapply gstep_run; [exact Hp | exact Hg_d | exact Hns_step]. }
        apply (IH (s'', O_event outs :: tau_d ++ trace_curr) Hmidset_at gs_next
                  (O_event (filter (output_visible n) outs) :: t_demon ++ t)).
        cbn. exists ((tr ++ tau_d) ++ [O_event outs]).
        split; [apply map.get_put_same|].
        intros x Hx.
        change (O_event outs :: tau_d ++ trace_curr)
          with ([O_event outs] ++ (tau_d ++ trace_curr)) in Hx.
        apply output_in_trace_app in Hx as [Hx|Hx].
        + apply output_in_trace_app. right.
          change [O_event outs] with ([] ++ [O_event outs]) in Hx.
          apply output_in_trace_app in Hx as [Hx|Hx]; [destruct Hx as (?&[]&_)|exact Hx].
        + apply output_in_trace_app in Hx as [Hx|Hx].
          * apply output_in_trace_app. left. apply output_in_trace_app. right. exact Hx.
          * apply output_in_trace_app. left. apply output_in_trace_app. left.
            apply Hsub. exact Hx.
    Qed.

    (* A graph invariant (preserved by any run) can be carried through an
       eventually: the angel reaches P-and-Inv whenever it can reach P. *)
    Lemma eventually_carry_inv :
      forall (Inv : graph_state -> Prop),
        (forall gs T gs', star (graph_step p node_step) gs T gs' -> Inv gs -> Inv gs') ->
        forall (P : graph_state * list IO_event -> Prop) gs t,
          Inv gs ->
          eventually (can_step (graph_step p node_step) A) P (gs, t) ->
          eventually (can_step (graph_step p node_step) A)
            (fun '(gs', t') => P (gs', t') /\ Inv gs') (gs, t).
    Proof.
      intros Inv Hinv P gs t HInv Hev.
      remember (gs, t) as st eqn:Est. revert gs t HInv Est.
      induction Hev as [[s' t'] HP | [s' t'] midset Hcan Hmid IH];
        intros gs t HInv [= -> ->].
      - apply eventually_done. split; [exact HP | exact HInv].
      - apply eventually_step_cps.
        intros gs_d t_d Hstar_d Hallow.
        specialize (Hcan gs_d t_d Hstar_d Hallow).
        destruct Hcan as (s'' & outs & Hstep & Hmidset).
        exists s'', outs. split; [exact Hstep|].
        apply (IH _ Hmidset s'' (O_event outs :: t_d ++ t)); [|reflexivity].
        eapply Hinv; [|exact HInv].
        eapply star_app; [exact Hstar_d | econstructor; [exact Hstep | constructor]].
    Qed.

    (* The node-state domain is invariant under runs: any node with a state in a
       later graph state already had one at the start. *)
    Lemma dom_preserved :
      forall gs0 T gs, star (graph_step p node_step) gs0 T gs ->
      forall n x, map.get gs.(g_nodes) n = Some x ->
      exists x0, map.get gs0.(g_nodes) n = Some x0.
    Proof.
      intros gs0 T gs Hstar.
      induction Hstar as [s | s e s' t0 s'' Hstep Hstar IH]; intros n x Hg.
      - eauto.
      - destruct (IH n x Hg) as (x1 & Hx1).
        inversion Hstep as [ gs1 ni mi Hia
                           | gs1 ni npi nsi ti nsi' outsi Hpi Hgi Hsi
                           | gs1 ni npi nsi ti nsi' mi msa msb Hpi Hgi Hsi Hmsg ]; subst; cbn in Hx1.
        + eauto.
        + destruct (Nat.eq_dec n ni) as [->|Hne]; [eauto|].
          rewrite map.get_put_diff in Hx1 by auto. eauto.
        + destruct (Nat.eq_dec n ni) as [->|Hne]; [eauto|].
          rewrite map.get_put_diff in Hx1 by auto. eauto.
    Qed.

    (* Node states only ever arise from the initial state map. *)
    Lemma reachable_state_initial :
      forall T gs, star (graph_step p node_step) initial_graph_state T gs ->
      forall n x, map.get gs.(g_nodes) n = Some x ->
      exists ns0, map.get initial_ns n = Some ns0.
    Proof.
      intros T gs Hstar n x Hg.
      destruct (dom_preserved _ _ _ Hstar n x Hg) as (x0 & Hx0).
      cbn in Hx0. eauto.
    Qed.

    (* Re-emit a whole list of messages from node n at a reachable gsB, given n is
       armed for each.  Each is either freshly emitted (lift_node_outputs forwards
       it) or already in n's trace (graph_saturated already forwarded it).  After
       the run, every target of every listed message is queued or has received it. *)
    Lemma advance_emit :
      (forall t, A t) ->
      Forall2_map (fun _ np x => can_implies_will' (node_step np) A (fst x)) p initial_ns ->
      forall (ms : list message) (n : node_id) (np : node_prog),
        map.get p n = Some np ->
        forall Tb gsB, star (graph_step p node_step) initial_graph_state Tb gsB ->
        forall nsB tB, map.get gsB.(g_nodes) n = Some (nsB, tB) ->
        (forall mu, In mu ms -> can_output (node_step np) nsB tB mu) ->
        exists WB gsfB nsB' tBe,
          star (graph_step p node_step) gsB WB gsfB /\
          inputs_of WB = [] /\
          map.get gsfB.(g_nodes) n = Some (nsB', tB ++ tBe) /\
          (forall n2, n2 <> n -> map.get gsfB.(g_nodes) n2 = map.get gsB.(g_nodes) n2) /\
          (exists extra, gsfB.(g_messages) = gsB.(g_messages) ++ extra) /\
          (forall mu n', In mu ms -> In n' (forward n mu) ->
             In (n', mu) gsfB.(g_messages) \/ node_received gsfB n' mu).
    Proof.
      intros A_univ Hpernode ms n np Hp.
      induction ms as [|mu ms IH]; intros Tb gsB HTb nsB tB Hg Hcan.
      - exists [], gsB, nsB, []. rewrite app_nil_r.
        split; [constructor|]. split; [reflexivity|]. split; [exact Hg|].
        split; [reflexivity|]. split; [exists []; rewrite app_nil_r; reflexivity|].
        intros mu n' [].
      - (* node n's bare initial state, for arming permanence *)
        destruct (reachable_state_initial _ _ HTb n _ Hg) as (ns0 & Hns0).
        pose proof (pernode_ciw Hpernode n np ns0 Hp Hns0) as Hciw.
        destruct (project_node_gen _ _ HTb n np ns0 Hp Hns0)
          as (tauP & nsP & HstarP & HgP & _).
        assert (nsP = nsB) by congruence. assert (tauP = tB) by congruence.
        subst nsP tauP.
        (* emit mu *)
        destruct (Hcan mu (or_introl eq_refl)) as (tau & s' & Hstar_run & Hinp_run & Hout_run).
        destruct (lift_node_outputs n np Hp nsB tau s' Hstar_run Hinp_run gsB tB Hg)
          as (WB1 & gsB1 & HstarB1 & HinpB1 & HgB1 & HotherB1 & (extra1 & Hextra1) & HfwdB1 & _).
        (* arming permanence for the rest of ms *)
        assert (Hcan' : forall mu', In mu' ms -> can_output (node_step np) s' (tB ++ tau) mu').
        { intros mu' Hin'.
          eapply can_output_star_preserved;
            [exact A_univ | exact Hciw | exact Hstar_run | exact HstarP
            | apply (Hcan mu' (or_intror Hin'))]. }
        destruct (IH (Tb ++ WB1) gsB1 (star_app _ _ _ _ _ _ HTb HstarB1) s' (tB ++ tau) HgB1 Hcan')
          as (WB2 & gsfB & nsB'' & tBe2 & HstarB2 & HinpB2 & HgfB & HotherB2
              & (extra2 & Hextra2) & HfwdB2).
        exists (WB1 ++ WB2), gsfB, nsB'', (tau ++ tBe2).
        split; [eapply star_app; eassumption|].
        split; [rewrite inputs_of_app, HinpB1, HinpB2; reflexivity|].
        split; [rewrite app_assoc; exact HgfB|].
        split.
        { intros n2 Hn2. rewrite (HotherB2 n2 Hn2). apply (HotherB1 n2 Hn2). }
        split.
        { exists (extra1 ++ extra2). rewrite Hextra2, Hextra1, app_assoc. reflexivity. }
        intros mu0 n' Hin0 Hfwd0.
        destruct Hin0 as [-> | Hin0'].
        + (* mu0 = mu *)
          apply output_in_trace_app in Hout_run as [Hmu_tau | Hmu_tB].
          * (* freshly emitted in tau *)
            destruct Hmu_tau as (outs0 & Hin_o0 & Hino0).
            left. rewrite Hextra2. apply in_or_app. left.
            apply (HfwdB1 outs0 mu0 n' Hin_o0 Hino0 Hfwd0).
          * (* already in n's trace tB: saturation forwarded it *)
            pose proof (graph_saturated _ _ HTb n np nsB tB Hp Hg mu0 n' Hmu_tB Hfwd0)
              as [Hq | Hr].
            -- left. rewrite Hextra2, Hextra1.
               apply in_or_app. left. apply in_or_app. left. exact Hq.
            -- right. apply (node_received_mono _ _ _
                              (star_app _ _ _ _ _ _ HstarB1 HstarB2) n' mu0 Hr).
        + (* mu0 in ms: from the recursive call *)
          apply (HfwdB2 mu0 n' Hin0' Hfwd0).
    Qed.

    (* Faithfully replay an input-free run of gsA from a dominating state gsB,
       maintaining domination: each gstep_run is re-emitted (advance_emit), each
       gstep_receive is matched by a delivery (queued at gsB) or skipped (already
       delivered). *)
    Lemma dom_advance :
      (forall t, A t) ->
      (forall n np, map.get p n = Some np -> input_total (node_step np)) ->
      Forall2_map (fun _ np x => can_implies_will' (node_step np) A (fst x)) p initial_ns ->
      forall W gsfA gsA, star (graph_step p node_step) gsA W gsfA ->
      inputs_of W = [] ->
      forall TA, star (graph_step p node_step) initial_graph_state TA gsA ->
      forall TB gsB, star (graph_step p node_step) initial_graph_state TB gsB ->
      core_dom gsA gsB ->
      exists WB gsfB,
        star (graph_step p node_step) gsB WB gsfB /\
        inputs_of WB = [] /\
        core_dom gsfA gsfB.
    Proof.
      intros A_univ Hit Hpernode W gsfA gsA Hstar.
      induction Hstar as [gA | gA e gA1 W' gfA Hstep Hstar' IH];
        intros HinpW TA HTA TB gsB HTB Hdom.
      - exists [], gsB. split; [constructor|]. split; [reflexivity|]. exact Hdom.
      - destruct Hdom as [Hdom_n Hdom_m].
        inversion Hstep as [ gs0 ni mi Hia
                           | gs0 ni npi nsi ti nsi' outsi Hpi Hgi Hsi
                           | gs0 ni npi nsi ti nsi' mi msa msb Hpi Hgi Hsi Hmsg ]; subst.
        + (* gstep_input: contradicts inputs_of W = [] *)
          cbn in HinpW. discriminate.
        + (* gstep_run ni: re-emit outsi from gsB's node ni *)
          cbn in HinpW.
          destruct (Hdom_n ni nsi ti Hgi) as (nsB & tB & HgB & Hincl).
          (* node ni's bare init, for the monotone' transfer *)
          destruct (reachable_state_initial _ _ HTA ni _ Hgi) as (ns0 & Hns0).
          pose proof (pernode_monotone' Hpernode ni npi ns0 Hpi Hns0) as Hmono.
          destruct (project_node_gen _ _ HTA ni npi ns0 Hpi Hns0)
            as (tauA & nsatA & HstarA & HgatA & _).
          assert (nsatA = nsi) by congruence. assert (tauA = ti) by congruence.
          subst nsatA tauA.
          destruct (project_node_gen _ _ HTB ni npi ns0 Hpi Hns0)
            as (tauB & nsatB & HstarB & HgatB & _).
          assert (nsatB = nsB) by congruence. assert (tauB = tB) by congruence.
          subst nsatB tauB.
          assert (Hcan : forall mu, In mu outsi -> can_output (node_step npi) nsB tB mu).
          { intros mu Hin.
            apply (Hmono ti tB nsi nsB mu HstarA HstarB
                     (allowed_trace_universal A A_univ ti)
                     (allowed_trace_universal A A_univ tB) Hincl).
            exists [O_event outsi], nsi'. split; [econstructor; [exact Hsi|constructor]|].
            split; [reflexivity|]. exists outsi. split; [left; reflexivity | exact Hin]. }
          destruct (advance_emit A_univ Hpernode outsi ni npi Hpi TB gsB HTB nsB tB HgB Hcan)
            as (WB1 & gsB1 & nsB1 & tBe & HstarB1 & HinpB1 & HgB1 & HotherB1
                & (extraB & HextraB) & HfwdB1).
          (* core_dom gsA1 gsB1, then recurse *)
          assert (Hdom1 : core_dom
                    {| g_nodes := map.put (g_nodes gA) ni (nsi', ti ++ [O_event outsi]);
                       g_messages := g_messages gA ++
                         flat_map (fun m => map (fun n' => (n', m)) (forward ni m)) outsi |}
                    gsB1).
          { split.
            - intros nn nsX tX HgX. cbn in HgX.
              destruct (Nat.eq_dec nn ni) as [->|Hne].
              + rewrite map.get_put_same in HgX. injection HgX as <- <-.
                exists nsB1, (tB ++ tBe). split; [exact HgB1|].
                rewrite inputs_of_app. cbn. rewrite app_nil_r.
                eapply incl_tran; [exact Hincl|]. rewrite inputs_of_app. apply incl_appl, incl_refl.
              + rewrite map.get_put_diff in HgX by auto.
                destruct (Hdom_n nn nsX tX HgX) as (nsBn & tBn & HgBn & Hincln).
                exists nsBn, tBn. split; [rewrite (HotherB1 nn Hne); exact HgBn | exact Hincln].
            - intros nn m Hin. cbn in Hin. apply in_app_or in Hin as [Hin | Hin].
              + destruct (Hdom_m nn m Hin) as [Hq | Hr].
                * left. rewrite HextraB. apply in_or_app. left. exact Hq.
                * right. apply (node_received_mono _ _ _ HstarB1 nn m Hr).
              + apply in_flat_map in Hin as (mm & Hmm & Hin).
                apply in_map_iff in Hin as (n'' & Heq & Hn'').
                injection Heq as <- <-.
                apply (HfwdB1 mm n'' Hmm Hn''). }
          destruct (IH HinpW (TA ++ [O_event (filter (output_visible ni) outsi)])
                      (star_app _ _ _ _ _ _ HTA
                        (star_step _ _ _ _ _ _ Hstep (star_refl _ _)))
                      (TB ++ WB1) gsB1
                      (star_app _ _ _ _ _ _ HTB HstarB1) Hdom1)
            as (WB2 & gsfB & HstarB2 & HinpB2 & Hdomf).
          exists (WB1 ++ WB2), gsfB. split; [eapply star_app; eassumption|].
          split; [rewrite inputs_of_app, HinpB1, HinpB2; reflexivity|]. exact Hdomf.
        + (* gstep_receive ni mi: match the delivery from gsB *)
          cbn in HinpW.
          destruct (Hdom_n ni nsi ti Hgi) as (nsB & tB & HgB & Hincl).
          assert (Hmrcv : In (ni, mi) (g_messages gsB) \/ node_received gsB ni mi).
          { apply Hdom_m. rewrite Hmsg. apply in_or_app. right. left. reflexivity. }
          destruct Hmrcv as [Hq | Hr].
          * (* (ni,mi) queued at gsB: deliver it *)
            apply in_split in Hq as (msaB & msbB & HqB).
            destruct (Hit ni npi Hpi nsB mi) as (nsB' & HstepB).
            set (gsB1 := {| g_nodes := map.put (g_nodes gsB) ni (nsB', tB ++ [I_event mi]);
                            g_messages := msaB ++ msbB |}).
            assert (HstepB1 : graph_step p node_step gsB (O_event []) gsB1)
              by (eapply gstep_receive; [exact Hpi | exact HgB | exact HstepB | exact HqB]).
            assert (Hdom1 : core_dom
                      {| g_nodes := map.put (g_nodes gA) ni (nsi', ti ++ [I_event mi]);
                         g_messages := msa ++ msb |} gsB1).
            { split.
              - intros nn nsX tX HgX. cbn in HgX.
                destruct (Nat.eq_dec nn ni) as [->|Hne].
                + rewrite map.get_put_same in HgX. injection HgX as <- <-.
                  exists nsB', (tB ++ [I_event mi]).
                  split; [cbn; apply map.get_put_same|].
                  rewrite !inputs_of_app. cbn. apply incl_app_app; [exact Hincl | apply incl_refl].
                + rewrite map.get_put_diff in HgX by auto.
                  destruct (Hdom_n nn nsX tX HgX) as (nsBn & tBn & HgBn & Hincln).
                  exists nsBn, tBn. split; [cbn; rewrite map.get_put_diff by auto; exact HgBn | exact Hincln].
              - intros nn m Hin. cbn in Hin.
                assert (HinA : In (nn, m) (g_messages gA)).
                { rewrite Hmsg. apply in_app_iff. apply in_app_or in Hin as [H|H];
                    [left; exact H | right; right; exact H]. }
                destruct (Hdom_m nn m HinA) as [Hqd | Hrd].
                + (* in gsB queue = msaB ++ (ni,mi)::msbB *)
                  rewrite HqB in Hqd. apply in_app_or in Hqd as [H | Hqd2].
                  * left. cbn. apply in_or_app. left. exact H.
                  * cbn in Hqd2. destruct Hqd2 as [Heq | H].
                    -- injection Heq as Hnieq Hmieq. subst nn m. right.
                       exists nsB', (tB ++ [I_event mi]).
                       split; [cbn; apply map.get_put_same|].
                       rewrite inputs_of_app. apply in_or_app. right. left. reflexivity.
                    -- left. cbn. apply in_or_app. right. exact H.
                + right. apply (node_received_mono _ _ _
                            (star_step _ _ _ _ _ _ HstepB1 (star_refl _ _)) nn m Hrd). }
            destruct (IH HinpW (TA ++ [O_event []])
                        (star_app _ _ _ _ _ _ HTA
                          (star_step _ _ _ _ _ _ Hstep (star_refl _ _)))
                        (TB ++ [O_event []]) gsB1
                        (star_app _ _ _ _ _ _ HTB
                          (star_step _ _ _ _ _ _ HstepB1 (star_refl _ _))) Hdom1)
              as (WB2 & gsfB & HstarB2 & HinpB2 & Hdomf).
            exists (O_event [] :: WB2), gsfB.
            split; [econstructor; [exact HstepB1 | exact HstarB2]|].
            split; [cbn; exact HinpB2|]. exact Hdomf.
          * (* (ni,mi) already received at gsB: skip, gsB unchanged *)
            assert (Hdom1 : core_dom
                      {| g_nodes := map.put (g_nodes gA) ni (nsi', ti ++ [I_event mi]);
                         g_messages := msa ++ msb |} gsB).
            { split.
              - intros nn nsX tX HgX. cbn in HgX.
                destruct (Nat.eq_dec nn ni) as [->|Hne].
                + rewrite map.get_put_same in HgX. injection HgX as <- <-.
                  exists nsB, tB. split; [exact HgB|].
                  destruct Hr as (nsr & tr & Hgr & Hinr).
                  assert (tr = tB) by congruence. subst tr.
                  rewrite inputs_of_app. cbn. apply incl_app; [exact Hincl|].
                  intros x [<-|[]]. exact Hinr.
                + rewrite map.get_put_diff in HgX by auto.
                  apply (Hdom_n nn nsX tX HgX).
              - intros nn m Hin. cbn in Hin. apply Hdom_m.
                rewrite Hmsg. apply in_app_iff. apply in_app_or in Hin as [H|H].
                + left. exact H.
                + right. right. exact H. }
            destruct (IH HinpW (TA ++ [O_event []])
                        (star_app _ _ _ _ _ _ HTA
                          (star_step _ _ _ _ _ _ Hstep (star_refl _ _)))
                        TB gsB HTB Hdom1)
              as (WB2 & gsfB & HstarB2 & HinpB2 & Hdomf).
            exists WB2, gsfB. split; [exact HstarB2|]. split; [exact HinpB2|]. exact Hdomf.
    Qed.

    (* core_replay: the simulation transfers input-free reachability of an output.
       This is the heart of can_output preservation; proved by replaying the
       witness from the dominating state, re-deriving each node emission via
       cap_transfer + lift_node_outputs. *)
    Lemma core_replay :
      (forall t, A t) ->
      (forall n np, map.get p n = Some np -> input_total (node_step np)) ->
      Forall2_map (fun _ np x => can_implies_will' (node_step np) A (fst x)) p initial_ns ->
      forall TA gsA, star (graph_step p node_step) initial_graph_state TA gsA ->
      forall W gsfA, star (graph_step p node_step) gsA W gsfA ->
      inputs_of W = [] ->
      forall TB gsB, star (graph_step p node_step) initial_graph_state TB gsB ->
      core_dom gsA gsB ->
      forall o, output_in_trace o W ->
      exists WB gsfB,
        star (graph_step p node_step) gsB WB gsfB /\
        inputs_of WB = [] /\ output_in_trace o (WB ++ TB).
    Proof.
      intros A_univ Hit Hpernode TA gsA HTA W gsfA Hstar HinpW TB gsB HTB Hdom o Hout.
      (* locate the step that emits o *)
      destruct (find_producing_step _ _ _ Hstar HinpW _ Hout)
        as (T_pre & T_post & n_o & np_o & ns_o & ns_o' & t_o & outs_o
            & gs_preA & gs_postA & HeqW & Hstar_preA & Hprod & Hstar_postA
            & Hinp_pre & Hp_o & Hg_o & Hns_o & Hino_o & Hvis_o).
      (* domination-preserving replay of T_pre from gsB *)
      destruct (dom_advance A_univ Hit Hpernode T_pre gs_preA gsA Hstar_preA Hinp_pre
                  TA HTA TB gsB HTB Hdom)
        as (WB1 & gs_preB & HstarB1 & HinpB1 & Hdom_pre).
      pose proof (star_app _ _ _ _ _ _ HTA Hstar_preA) as HTApre.
      pose proof (star_app _ _ _ _ _ _ HTB HstarB1) as HTBpre.
      destruct Hdom_pre as [Hdpre_n _].
      destruct (Hdpre_n n_o ns_o t_o Hg_o) as (nsBo & tBo & HgBo & Hinclo).
      (* n_o's bare init and reachability of its projections *)
      destruct (reachable_state_initial _ _ HTApre n_o _ Hg_o) as (ns0 & Hns0).
      destruct (project_node_gen _ _ HTApre n_o np_o ns0 Hp_o Hns0)
        as (tauPA & nsPA & HsPA & HgPA & _).
      assert (nsPA = ns_o) by congruence. assert (tauPA = t_o) by congruence. subst nsPA tauPA.
      destruct (project_node_gen _ _ HTBpre n_o np_o ns0 Hp_o Hns0)
        as (tauPB & nsPB & HsPB & HgPB & HvisPB).
      assert (nsPB = nsBo) by congruence. assert (tauPB = tBo) by congruence. subst nsPB tauPB.
      (* transfer n_o's capability to emit o, via monotone' *)
      pose proof (pernode_monotone' Hpernode n_o np_o ns0 Hp_o Hns0) as Hmono.
      assert (Hcano : can_output (node_step np_o) ns_o t_o o).
      { exists [O_event outs_o], ns_o'. split; [econstructor; [exact Hns_o|constructor]|].
        split; [reflexivity|]. exists outs_o. split; [left; reflexivity | exact Hino_o]. }
      pose proof (Hmono t_o tBo ns_o nsBo o HsPA HsPB
                    (allowed_trace_universal A A_univ t_o)
                    (allowed_trace_universal A A_univ tBo) Hinclo Hcano) as HcanBo.
      destruct HcanBo as (tau & sfin & Hstau & Hinptau & Houttau).
      apply output_in_trace_app in Houttau as [Ho_tau | Ho_tB].
      - (* emit o fresh from gs_preB *)
        destruct (lift_node_outputs n_o np_o Hp_o nsBo tau sfin Hstau Hinptau gs_preB tBo HgBo)
          as (WBE & gs_preB' & HsBE & HinpBE & _ & _ & _ & _ & HvBE).
        exists (WB1 ++ WBE), gs_preB'.
        split; [eapply star_app; eassumption|].
        split; [rewrite inputs_of_app, HinpB1, HinpBE; reflexivity|].
        apply output_in_trace_app. left. apply output_in_trace_app. right.
        apply (HvBE o Hvis_o Ho_tau).
      - (* o already in n_o's stored trace at gs_preB: it is in the graph history *)
        exists WB1, gs_preB. split; [exact HstarB1|]. split; [exact HinpB1|].
        pose proof (HvisPB o Hvis_o Ho_tB) as Ho_graph.
        apply output_in_trace_app in Ho_graph as [Ho | Ho]; apply output_in_trace_app.
        + right. exact Ho.
        + left. exact Ho.
    Qed.

    (* can_output is preserved by any single graph step (the demon move), where the
       past trace is the reaching trace. *)
    Lemma can_output_step :
      (forall t, A t) ->
      (forall n np, map.get p n = Some np -> input_total (node_step np)) ->
      Forall2_map (fun _ np x => can_implies_will' (node_step np) A (fst x)) p initial_ns ->
      forall T gs, star (graph_step p node_step) initial_graph_state T gs ->
      forall e gs', graph_step p node_step gs e gs' ->
      forall o, can_output (graph_step p node_step) gs T o ->
                can_output (graph_step p node_step) gs' (e :: T) o.
    Proof.
      intros A_univ Hit Hpernode T gs HT e gs' Hstep o (W & gsf & HW & HinpW & Hout).
      apply output_in_trace_app in Hout as [Hout_W | Hout_t].
      - destruct (core_replay A_univ Hit Hpernode T gs HT W gsf HW HinpW
                    (T ++ [e]) gs'
                    (star_app _ _ _ _ _ _ HT (star_step _ _ _ _ _ _ Hstep (star_refl _ _)))
                    (dom_of_step gs e gs' Hstep) o Hout_W)
          as (WB & gsfB & HWB & HinpWB & HoutWB).
        exists WB, gsfB. split; [exact HWB|]. split; [exact HinpWB|].
        (* output in WB ++ (T ++ [e]) -> output in WB ++ (e :: T) *)
        apply output_in_trace_app in HoutWB as [Ho|Ho]; apply output_in_trace_app.
        + left. exact Ho.
        + right. apply output_in_trace_app in Ho as [Ho|Ho].
          * change (e :: T) with ([e] ++ T). apply output_in_trace_app. right. exact Ho.
          * change (e :: T) with ([e] ++ T). apply output_in_trace_app. left. exact Ho.
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
      Forall2_map (fun _ np x => can_implies_will' (node_step np) A (fst x)) p initial_ns ->
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
      Forall2_map (fun _ np x => can_implies_will' (node_step np) A (fst x)) p initial_ns ->
      can_implies_will (graph_step p node_step) A initial_graph_state.
    Proof.
      intros A_univ Hit Hpernode t gs o Hstar Hall Hcan.
      destruct Hcan as (T_a & s_f & Hstar_a & Hinp_a & Hout).
      apply output_in_trace_app in Hout as [Hout_T | Hout_t].
      2: { apply eventually_done. exact Hout_t. }
      (* Find the producing step in T_a (which has inputs_of = []). *)
      destruct (find_producing_step _ _ _ Hstar_a Hinp_a _ Hout_T)
        as (T_pre & T_post & n_o & np_o & ns_o & ns_o' & t_o & outs_o
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
                    n_o np_o ns_o t_o o Hp_o Hg_o Hvis_o Harmed) as Hwill_pre.
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
