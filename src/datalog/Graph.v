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
  (* The graph's external alphabet tags each message with the node it is
     delivered to / produced by, so inputs to different nodes are distinguishable. *)
  Local Notation gevent := (Smallstep.IO_event (message * node_id)).

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

    Inductive graph_step : graph_state -> gevent -> graph_state -> Prop :=
    | gstep_input gs n m :
      input_allowed n m = true ->
      graph_step gs (I_event (m, n))
                 {| g_nodes := gs.(g_nodes);
                   g_messages := (n, m) :: gs.(g_messages) |}
    | gstep_run gs n np ns t ns' outs :
      map.get p n = Some np ->
      map.get gs.(g_nodes) n = Some (ns, t) ->
      node_step np ns (O_event outs) ns' ->
      graph_step gs (O_event (map (fun m => (m, n)) (filter (output_visible n) outs)))
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

  (* The graph's allowed predicate: a tagged trace is allowed iff its underlying
     (untagged) inputs are allowed by A. *)
  Local Notation Ag := (fun (inps : list (message * node_id)) => A (map fst inps)).

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

    (* Abbreviations to keep statements readable. *)
    Local Notation gstep := (graph_step p node_step).
    (* The graph's external inputs are all allowed. *)
    Local Notation A_total := (forall t, A t).
    (* Every node accepts every input in every state. *)
    Local Notation nodes_input_total :=
      (forall n np, map.get p n = Some np -> input_total (node_step np)).
    (* Every node satisfies the can-implies-will' contract from its initial state. *)
    Local Notation nodes_ciw' :=
      (Forall2_map (fun _ np x => can_implies_will' (node_step np) A (fst x)) p initial_ns).
    (* [gs] is reachable from the initial graph state. *)
    Local Notation reachable gs := (exists T, star gstep initial_graph_state T gs).

    (* Case-split a graph step into its three constructors with uniform hypothesis
       names: gstep_input (ni, mi), gstep_run (ni, npi, nsi, ti, nsi', outsi), and
       gstep_receive (ni, npi, nsi, ti, nsi', mi, msa, msb). *)
    Ltac inv_gstep H :=
      inversion H as [ gs0 ni mi Hia
                     | gs0 ni npi nsi ti nsi' outsi Hpi Hgi Hsi
                     | gs0 ni npi nsi ti nsi' mi msa msb Hpi Hgi Hsi Hmsg ].

    (* Roadmap for [graph_can_implies_will] (the goal of this section).  Each node
       stores its own IO trace, so a node's projection is just [snd (g_nodes n)];
       [node_drive_delta] / [project_node_gen] / [node_run] relate a graph run to
       the node run it induces.  Two ingredients drive the proof:

       - [saturated] (every message a node has emitted is queued or delivered) and
         [core_dom] (a state dominates another when its nodes have received at least
         as much and its messages are at least as available);
       - the "angel" forcing: [force_emit_list] / [force_deliver] make individual
         progress, [force_dominator] chains them to drive the graph from any state
         to one dominating a chosen checkpoint.

       Given a [can_output] witness, [find_producing_step] locates the step that
       emits it; [force_dominator] drives the graph to a state dominating that step's
       pre-state; there the responsible node is still armed ([node_cap_transfer]) and
       so will emit ([node_will], lifted to the graph by [drive_node_must]). *)

    (* Membership in a node's tagged output list: (o, n) is in node n's tagged
       outputs iff o is among the (untagged) outputs. *)
    Lemma In_tag (n : node_id) (l : list message) (o : message) :
      In (o, n) (map (fun m => (m, n)) l) <-> In o l.
    Proof.
      rewrite in_map_iff. split.
      - intros (x & Heq & Hin). injection Heq as ->. exact Hin.
      - intros Hin. exists o. split; [reflexivity | exact Hin].
    Qed.

    Lemma In_tag_inv (n0 nq : node_id) (l : list message) (o : message) :
      In (o, nq) (map (fun m => (m, n0)) l) -> nq = n0 /\ In o l.
    Proof.
      rewrite in_map_iff. intros (x & Heq & Hin).
      injection Heq as Hx Hn. subst. split; [reflexivity | exact Hin].
    Qed.

    (* The state-stored projection: over any drive, node n's stored trace grows by
       a delta [td] that is a valid node run from n's state, whose visible outputs
       all appear in the graph trace. *)
    Lemma node_drive_delta :
      forall T gs0 gs,
        star gstep gs0 T gs ->
        forall n np ns t,
          map.get p n = Some np ->
          map.get gs0.(g_nodes) n = Some (ns, t) ->
          exists ns' td,
            map.get gs.(g_nodes) n = Some (ns', t ++ td) /\
            star (node_step np) ns td ns' /\
            (forall o, output_visible n o = true ->
                       output_in_trace o td -> output_in_trace (o, n) T).
    Proof.
      intros T gs0 gs Hstar.
      induction Hstar as [s|s e s' t0 s'' Hstep Hstar IH];
        intros n np ns t Hp Hg0.
      - exists ns, []. rewrite app_nil_r. split; [exact Hg0|]. split; [constructor|].
        intros o _ (outs & Hin & _); inversion Hin.
      - inv_gstep Hstep; subst.
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
               exists (map (fun m => (m, n)) (filter (output_visible n) outsi)).
               split; [left; reflexivity|].
               apply In_tag. apply filter_In. split; [exact Hino|exact Hvis].
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
        star gstep initial_graph_state T gs ->
        forall n np ns0,
          map.get p n = Some np ->
          map.get initial_ns n = Some ns0 ->
          exists tau ns_at,
            star (node_step np) (fst ns0) tau ns_at /\
            map.get gs.(g_nodes) n = Some (ns_at, tau) /\
            (forall o, output_visible n o = true ->
                       output_in_trace o tau -> output_in_trace (o, n) T).
    Proof.
      intros T gs Hstar n np ns0 Hp Hns0.
      pose proof (initial_ns_empty n ns0 Hns0) as Hempty.
      destruct ns0 as [ns0b t0b]. cbn in Hempty. subst t0b. cbn [fst].
      destruct (node_drive_delta _ _ _ Hstar n np ns0b [] Hp Hns0)
        as (ns' & td & Hg & Hstd & Hpres).
      rewrite app_nil_l in Hg.
      exists td, ns'. split; [exact Hstd|]. split; [exact Hg|]. exact Hpres.
    Qed.

    (* The "backward" reading of project_node_gen: given a node's current stored
       state (ns, t) at a reachable graph state, recover its run from the bare
       initial state and the fact that its visible outputs reach the graph trace.
       Saves the caller the project + congruence dance. *)
    Lemma node_run :
      forall T gs, star gstep initial_graph_state T gs ->
      forall n np ns0 ns t,
        map.get p n = Some np ->
        map.get initial_ns n = Some ns0 ->
        map.get gs.(g_nodes) n = Some (ns, t) ->
        star (node_step np) (fst ns0) t ns /\
        (forall o, output_visible n o = true ->
                   output_in_trace o t -> output_in_trace (o, n) T).
    Proof.
      intros T gs Hstar n np ns0 ns t Hp Hns0 Hg.
      destruct (project_node_gen _ _ Hstar n np ns0 Hp Hns0)
        as (tau & ns_at & Hrun & Hgat & Hpres).
      assert (ns_at = ns) by congruence. assert (tau = t) by congruence. subst ns_at tau.
      split; [exact Hrun | exact Hpres].
    Qed.

    (* With traces stored in the state, "node n has received message mu" is simply:
       mu appears in the inputs of n's stored trace. *)
    Definition node_received (gs : @graph_state node_state node_states)
        (n : node_id) (mu : message) : Prop :=
      exists ns t, map.get gs.(g_nodes) n = Some (ns, t) /\ In mu (inputs_of t).

    (* Lift a node-level will_output for node n to a graph-level will_output,
       provided o is visible from n and the graph's node n is at the right state. *)
    Lemma drive_node_must :
      A_total ->
      forall (np : node_prog) (n : node_id) (o : message),
        map.get p n = Some np ->
        output_visible n o = true ->
        forall (s : node_state * list IO_event),
          eventually (can_step (node_step np) A)
                     (fun '(_, t') => output_in_trace o t') s ->
          forall gs t,
            (exists tr, map.get gs.(g_nodes) n = Some (fst s, tr)) ->
            (output_in_trace o (snd s) -> output_in_trace (o, n) t) ->
            eventually (can_step gstep Ag)
                       (fun '(_, t') => output_in_trace (o, n) t') (gs, t).
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
        destruct Hcan' as [Hmid_left | (s'' & outs & Hns_step & Hmidset_at)].
        { (* node already satisfies midset without emitting: no graph step needed *)
          left.
          apply (IH (ns_d, tau_d ++ trace_curr) Hmid_left gs_demon (t_demon ++ t)).
          - cbn. exists (tr ++ tau_d). exact Hg_d.
          - cbn. intros Hout_sd. apply output_in_trace_app in Hout_sd as [Ho_taud | Ho_curr].
            + apply output_in_trace_app. left. apply (Hpres_d o Hvis Ho_taud).
            + apply output_in_trace_app. right. apply Hout_proj. exact Ho_curr. }
        right.
        set (gs_next :=
               {| g_nodes := map.put gs_demon.(g_nodes) n (s'', (tr ++ tau_d) ++ [O_event outs]);
                  g_messages :=
                    gs_demon.(g_messages) ++
                    flat_map (fun m0 => map (fun n' => (n', m0))
                                            (forward n m0)) outs |}).
        exists gs_next, (map (fun m => (m, n)) (filter (output_visible n) outs)).
        split.
        { eapply gstep_run; [exact Hp | exact Hg_d | exact Hns_step]. }
        apply (IH (s'', O_event outs :: tau_d ++ trace_curr) Hmidset_at gs_next).
        + cbn. exists ((tr ++ tau_d) ++ [O_event outs]). apply map.get_put_same.
        + intros (outs' & Hin & Hino).
          cbn in Hin. destruct Hin as [Heq|Hin_rest].
          * injection Heq as Heq_outs. subst outs'.
            exists (map (fun m => (m, n)) (filter (output_visible n) outs)).
            split; [left; reflexivity|].
            apply In_tag. apply filter_In. split; [exact Hino|exact Hvis].
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

    (* Helper: find the producing step inside an angel's path. *)
    Lemma find_producing_step :
      forall (gs_start : graph_state) (T : list gevent) (s_f : graph_state),
        star gstep gs_start T s_f ->
        inputs_of T = [] ->
        forall (o : message) (n_o : node_id),
          output_in_trace (o, n_o) T ->
          exists (T_pre T_post : list gevent)
                 (np_o : node_prog)
                 (ns_o ns_o' : node_state) (t_o : list IO_event)
                 (outs_o : list message)
                 (gs_pre gs_post : graph_state),
            T = T_pre ++ O_event (map (fun m => (m, n_o)) (filter (output_visible n_o) outs_o)) :: T_post /\
            star gstep gs_start T_pre gs_pre /\
            gstep gs_pre
                       (O_event (map (fun m => (m, n_o)) (filter (output_visible n_o) outs_o))) gs_post /\
            star gstep gs_post T_post s_f /\
            inputs_of T_pre = [] /\
            map.get p n_o = Some np_o /\
            map.get gs_pre.(g_nodes) n_o = Some (ns_o, t_o) /\
            node_step np_o ns_o (O_event outs_o) ns_o' /\
            In o outs_o /\
            output_visible n_o o = true.
    Proof.
      intros gs_start T s_f Hstar Hinp o n_o.
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
            apply In_tag_inv in Hino0 as [Hn0eq Hino_filt]. subst n0.
            rewrite filter_In in Hino_filt. destruct Hino_filt as [Hino_full Hvis].
            exists [], t0, np0, ns0, ns0', t0n, outs_full, s,
              {| g_nodes := map.put s.(g_nodes) n_o (ns0', t0n ++ [O_event outs_full]);
                 g_messages := s.(g_messages) ++
                   flat_map (fun m => map (fun n' => (n', m)) (forward n_o m)) outs_full |}.
            split; [reflexivity|]. split; [constructor|].
            split; [eapply gstep_run; eassumption|].
            split; [exact Hstar|]. split; [reflexivity|].
            split; [exact Hp0|]. split; [exact Hg0|].
            split; [exact Hns0|]. split; [exact Hino_full | exact Hvis].
          * (* gstep_receive: outs = [] contradicts Hino0 *)
            cbn in Hino0. contradiction.
        + (* o is deeper *)
          specialize (IH Hinp Hout_rest).
          destruct IH as (T_pre & T_post & np_o & ns_o & ns_o' & t_o & outs_o
                          & gs_pre & gs_post & Heq_T & Hstar_pre & Hstep_prod
                          & Hstar_post & Hinp_pre & Hp_o & Hg_o & Hns_o
                          & Hino_o & Hvis_o).
          exists (O_event outs_e :: T_pre), T_post, np_o, ns_o, ns_o', t_o, outs_o,
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
      forall gs T gs', star gstep gs T gs' ->
        forall n m, node_received gs n m -> node_received gs' n m.
    Proof.
      intros gs T gs' Hstar.
      induction Hstar as [s | s e s' T' s'' Hstep Hstar IH]; intros n m Hr.
      - exact Hr.
      - apply (IH n m). destruct Hr as (ns & t & Hg & Hin).
        inv_gstep Hstep; subst.
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
      forall gs T gs', star gstep gs T gs' ->
        forall n m, In (n, m) gs.(g_messages) ->
          In (n, m) gs'.(g_messages) \/ node_received gs' n m.
    Proof.
      intros gs T gs' Hstar.
      induction Hstar as [s | s e s' T' s'' Hstep Hstar IH]; intros n m Hin.
      - left. exact Hin.
      - inv_gstep Hstep; subst; cbn [g_nodes g_messages] in IH |- *.
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

    (* A graph state is "saturated" if every message any node has emitted (recorded
       in its stored trace) is still queued or already delivered to its target. *)
    Definition saturated (gs : @graph_state node_state node_states) : Prop :=
      forall n np ns t,
        map.get p n = Some np ->
        map.get gs.(g_nodes) n = Some (ns, t) ->
        forall mu n', output_in_trace mu t -> In n' (forward n mu) ->
          In (n', mu) gs.(g_messages) \/ node_received gs n' mu.

    Lemma sat_step :
      forall gs e gs', gstep gs e gs' -> saturated gs -> saturated gs'.
    Proof.
      intros gs e gs' Hstep Hsat n np ns t Hp Hg mu n' Hout Hfwd.
      assert (Hmono1 : forall n0 m0, node_received gs n0 m0 -> node_received gs' n0 m0).
      { intros n0 m0 Hr.
        apply (node_received_mono _ _ _ (star_step _ _ _ _ _ _ Hstep (star_refl _ _))).
        exact Hr. }
      inv_gstep Hstep; subst.
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
      forall gs0 T gs, star gstep gs0 T gs ->
        saturated gs0 -> saturated gs.
    Proof.
      intros gs0 T gs Hstar. induction Hstar as [s | s e s' T' s'' Hstep Hstar IH];
        intro Hsat; [exact Hsat | apply IH; eapply sat_step; eauto].
    Qed.

    Lemma graph_saturated :
      forall T gs, star gstep initial_graph_state T gs -> saturated gs.
    Proof.
      intros T gs Hstar. eapply saturated_star; [exact Hstar|].
      intros n np ns t Hp Hg mu n' Hout Hfwd.
      cbn in Hg. apply initial_ns_empty in Hg as Ht. cbn in Ht. subst t.
      destruct Hout as (outs & Hin & _); inversion Hin.
    Qed.

    (* Each node, read off the per-node hypothesis, satisfies both the ciw and the
       monotone' contracts from its bare initial state. *)
    Lemma pernode_spec :
      nodes_ciw' ->
      forall n np ns0,
        map.get p n = Some np ->
        map.get initial_ns n = Some ns0 ->
        can_implies_will (node_step np) A (fst ns0) /\ monotone' (node_step np) A (fst ns0).
    Proof.
      intros Hpernode n np ns0 Hp Hns0.
      pose proof (Hpernode n) as Hn. rewrite Hp, Hns0 in Hn.
      apply (ciw'_iff_ciw_and_monotone' (node_step np) A (fst ns0)) in Hn. exact Hn.
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
      forall gs e gs', gstep gs e gs' ->
      core_dom gs gs'.
    Proof.
      intros gs e gs' Hstep. split.
      - intros n nsA tA HgA.
        inv_gstep Hstep; subst; cbn.
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
        inv_gstep Hstep; subst; cbn.
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

    (* "node n has emitted mu" — mu appears as an output in n's stored trace. *)
    Definition node_emitted (gs : @graph_state node_state node_states)
        (n : node_id) (mu : message) : Prop :=
      exists ns t, map.get gs.(g_nodes) n = Some (ns, t) /\ output_in_trace mu t.

    (* Lift a node-level will-to-emit-mu into a graph-level eventually that forces
       mu into n's stored trace.  Mirrors drive_node_must, but tracks emission via
       the node's stored trace (so mu need not be visible). *)
    Lemma drive_node_emit :
      A_total ->
      forall (np : node_prog) (n : node_id) (mu : message),
        map.get p n = Some np ->
        forall (s : node_state * list IO_event),
          eventually (can_step (node_step np) A)
                     (fun '(_, t') => output_in_trace mu t') s ->
          forall gs t,
            (exists tr, map.get gs.(g_nodes) n = Some (fst s, tr) /\
                        (forall x, output_in_trace x (snd s) -> output_in_trace x tr)) ->
            eventually (can_step gstep Ag)
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
        destruct Hcan' as [Hmid_left | (s'' & outs & Hns_step & Hmidset_at)].
        { left.
          apply (IH (ns_d, tau_d ++ trace_curr) Hmid_left gs_demon (t_demon ++ t)).
          cbn. exists (tr ++ tau_d). split; [exact Hg_d|].
          intros x Hx. apply output_in_trace_app in Hx as [Hx | Hx].
          - apply output_in_trace_app. right. exact Hx.
          - apply output_in_trace_app. left. apply Hsub. exact Hx. }
        right.
        set (gs_next :=
               {| g_nodes := map.put gs_demon.(g_nodes) n (s'', (tr ++ tau_d) ++ [O_event outs]);
                  g_messages :=
                    gs_demon.(g_messages) ++
                    flat_map (fun m0 => map (fun n' => (n', m0))
                                            (forward n m0)) outs |}).
        exists gs_next, (map (fun m => (m, n)) (filter (output_visible n) outs)).
        split.
        { eapply gstep_run; [exact Hp | exact Hg_d | exact Hns_step]. }
        apply (IH (s'', O_event outs :: tau_d ++ trace_curr) Hmidset_at gs_next
                  (O_event (map (fun m => (m, n)) (filter (output_visible n) outs)) :: t_demon ++ t)).
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
        (forall gs T gs', star gstep gs T gs' -> Inv gs -> Inv gs') ->
        forall (P : graph_state * list gevent -> Prop) gs t,
          Inv gs ->
          eventually (can_step gstep Ag) P (gs, t) ->
          eventually (can_step gstep Ag)
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
        destruct Hcan as [Hmid_left | (s'' & outs & Hstep & Hmidset)].
        + left. apply (IH (gs_d, t_d ++ t) Hmid_left gs_d (t_d ++ t)
                          (Hinv _ _ _ Hstar_d HInv) eq_refl).
        + right. exists s'', outs. split; [exact Hstep|].
          apply (IH _ Hmidset s'' (O_event outs :: t_d ++ t)); [|reflexivity].
          eapply Hinv; [|exact HInv].
          eapply star_app; [exact Hstar_d | econstructor; [exact Hstep | constructor]].
    Qed.

    (* Two-component version: carry a relation R between the state and the trace
       component (preserved by demon runs and by an output step) through an
       eventually.  Needed because the eventually's trace component is built by
       prepending, so it is not literally a reachability trace. *)
    Lemma eventually_carry_inv2 :
      forall (R : graph_state -> list gevent -> Prop),
        (forall gs tt t_d s_d, R gs tt ->
           star gstep gs t_d s_d -> R s_d (t_d ++ tt)) ->
        (forall gs tt outs gs', R gs tt ->
           gstep gs (O_event outs) gs' -> R gs' (O_event outs :: tt)) ->
        forall (P : graph_state * list gevent -> Prop) gs tt,
          R gs tt ->
          eventually (can_step gstep Ag) P (gs, tt) ->
          eventually (can_step gstep Ag)
            (fun '(gs', t') => P (gs', t') /\ R gs' t') (gs, tt).
    Proof.
      intros R Hstarp Hostep P gs tt HR Hev.
      remember (gs, tt) as st eqn:Est. revert gs tt HR Est.
      induction Hev as [[s' t'] HP | [s' t'] midset Hcan Hmid IH];
        intros gs tt HR [= -> ->].
      - apply eventually_done. split; [exact HP | exact HR].
      - apply eventually_step_cps.
        intros gs_d t_d Hstar_d Hallow.
        specialize (Hcan gs_d t_d Hstar_d Hallow).
        destruct Hcan as [Hmid_left | (s'' & outs & Hstep & Hmidset)].
        + left. apply (IH (gs_d, t_d ++ tt) Hmid_left gs_d (t_d ++ tt)
                          (Hstarp _ _ _ _ HR Hstar_d) eq_refl).
        + right. exists s'', outs. split; [exact Hstep|].
          apply (IH _ Hmidset s'' (O_event outs :: t_d ++ tt)); [|reflexivity].
          apply (Hostep _ _ _ _ (Hstarp _ _ _ _ HR Hstar_d) Hstep).
    Qed.

    (* The node-state domain is invariant under runs: any node with a state in a
       later graph state already had one at the start. *)
    Lemma dom_preserved :
      forall gs0 T gs, star gstep gs0 T gs ->
      forall n x, map.get gs.(g_nodes) n = Some x ->
      exists x0, map.get gs0.(g_nodes) n = Some x0.
    Proof.
      intros gs0 T gs Hstar.
      induction Hstar as [s | s e s' t0 s'' Hstep Hstar IH]; intros n x Hg.
      - eauto.
      - destruct (IH n x Hg) as (x1 & Hx1).
        inv_gstep Hstep; subst; cbn in Hx1.
        + eauto.
        + destruct (Nat.eq_dec n ni) as [->|Hne]; [eauto|].
          rewrite map.get_put_diff in Hx1 by auto. eauto.
        + destruct (Nat.eq_dec n ni) as [->|Hne]; [eauto|].
          rewrite map.get_put_diff in Hx1 by auto. eauto.
    Qed.

    (* Node states only ever arise from the initial state map. *)
    Lemma reachable_state_initial :
      forall T gs, star gstep initial_graph_state T gs ->
      forall n x, map.get gs.(g_nodes) n = Some x ->
      exists ns0, map.get initial_ns n = Some ns0.
    Proof.
      intros T gs Hstar n x Hg.
      destruct (dom_preserved _ _ _ Hstar n x Hg) as (x0 & Hx0).
      cbn in Hx0. eauto.
    Qed.

    (* Capability transfer between two reachable graph states of the SAME node:
       if node n is armed for o at gs1 (stored state ns1, trace t1) and the inputs
       it received there are included in those at gs2, then it is armed at gs2 too.
       This is the nodes' monotone' contract lifted to graph states. *)
    Lemma node_cap_transfer :
      A_total -> nodes_ciw' ->
      forall n np, map.get p n = Some np ->
      forall T1 gs1 ns1 t1, star gstep initial_graph_state T1 gs1 ->
        map.get gs1.(g_nodes) n = Some (ns1, t1) ->
      forall T2 gs2 ns2 t2, star gstep initial_graph_state T2 gs2 ->
        map.get gs2.(g_nodes) n = Some (ns2, t2) ->
        incl (inputs_of t1) (inputs_of t2) ->
      forall o, can_output (node_step np) ns1 t1 o ->
                can_output (node_step np) ns2 t2 o.
    Proof.
      intros A_univ Hpernode n np Hp T1 gs1 ns1 t1 HT1 Hg1 T2 gs2 ns2 t2 HT2 Hg2 Hincl o Hcan.
      destruct (reachable_state_initial _ _ HT1 n _ Hg1) as (ns0 & Hns0).
      destruct (node_run _ _ HT1 n np ns0 ns1 t1 Hp Hns0 Hg1) as (Hrun1 & _).
      destruct (node_run _ _ HT2 n np ns0 ns2 t2 Hp Hns0 Hg2) as (Hrun2 & _).
      destruct (pernode_spec Hpernode n np ns0 Hp Hns0) as (_ & Hmono).
      apply (Hmono t1 t2 ns1 ns2 o Hrun1 Hrun2
               (allowed_trace_universal A A_univ t1)
               (allowed_trace_universal A A_univ t2) Hincl Hcan).
    Qed.

    (* A capability at a reachable graph state is a node-level will_output: if node
       n can output o from its current stored state, then it will. *)
    Lemma node_will :
      A_total -> nodes_ciw' ->
      forall n np, map.get p n = Some np ->
      forall T gs ns t, star gstep initial_graph_state T gs ->
        map.get gs.(g_nodes) n = Some (ns, t) ->
      forall o, can_output (node_step np) ns t o ->
                will_output (node_step np) A ns t o.
    Proof.
      intros A_univ Hpernode n np Hp T gs ns t HT Hg o Hcan.
      destruct (reachable_state_initial _ _ HT n _ Hg) as (ns0 & Hns0).
      destruct (node_run _ _ HT n np ns0 ns t Hp Hns0 Hg) as (Hrun & _).
      destruct (pernode_spec Hpernode n np ns0 Hp Hns0) as (Hciw & _).
      apply (Hciw t ns o Hrun (allowed_trace_universal A A_univ t) Hcan).
    Qed.

    Lemma core_dom_refl : forall gs, core_dom gs gs.
    Proof.
      intros gs. split.
      - intros n ns t Hg. exists ns, t. split; [exact Hg | apply incl_refl].
      - intros n m Hin. left. exact Hin.
    Qed.

    Lemma core_dom_trans : forall a b c, core_dom a b -> core_dom b c -> core_dom a c.
    Proof.
      intros a b c [Hab_n Hab_m] [Hbc_n Hbc_m]. split.
      - intros n ns t Hg.
        destruct (Hab_n n ns t Hg) as (nsb & tb & Hgb & Hinclb).
        destruct (Hbc_n n nsb tb Hgb) as (nsc & tc & Hgc & Hinclc).
        exists nsc, tc. split; [exact Hgc | eapply incl_tran; eassumption].
      - intros n m Hin.
        destruct (Hab_m n m Hin) as [Hq | Hr].
        + apply (Hbc_m n m Hq).
        + right. destruct Hr as (ns & t & Hg & Hinm).
          destruct (Hbc_n n ns t Hg) as (nsc & tc & Hgc & Hinclc).
          exists nsc, tc. split; [exact Hgc | apply Hinclc; exact Hinm].
    Qed.

    (* core_dom in the second argument is preserved by any further run of it. *)
    Lemma core_dom_run : forall a b T c,
      core_dom a b -> star gstep b T c -> core_dom a c.
    Proof.
      intros a b T c Hab Hstar. revert a Hab.
      induction Hstar as [s | s e s' T0 s'' Hstep Hstar IH]; intros a Hab.
      - exact Hab.
      - apply IH. eapply core_dom_trans; [exact Hab | apply (dom_of_step s e s' Hstep)].
    Qed.

    (* Force a queued message to be delivered to its consumer: if the demon already
       delivered it the angel is simply done (the left disjunct of can_step);
       otherwise the angel delivers it (input_total supplies the receive step). *)
    Lemma force_deliver :
      nodes_input_total ->
      forall TX gsX, star gstep initial_graph_state TX gsX ->
      forall c m npc ns0c,
        map.get p c = Some npc ->
        map.get initial_ns c = Some ns0c ->
        (In (c, m) gsX.(g_messages) \/ node_received gsX c m) ->
      forall t,
        eventually (can_step gstep Ag)
          (fun '(gs', _) => node_received gs' c m) (gsX, t).
    Proof.
      intros Hit TX gsX HTX c m npc ns0c Hpc Hns0c Hcm t.
      destruct Hcm as [Hq | Hr].
      - apply eventually_step_cps.
        intros gs_d t_d Hstar_d Hallow.
        pose proof (star_app _ _ _ _ _ _ HTX Hstar_d) as HTd.
        destruct (queue_fate _ _ _ Hstar_d c m Hq) as [Hqd | Hrd].
        + right.
          destruct (project_node_gen _ _ HTd c npc ns0c Hpc Hns0c)
            as (tauc & nsc & _ & Hgc & _).
          apply in_split in Hqd as (ms1 & ms2 & Hsplit).
          destruct (Hit c npc Hpc nsc m) as (nsc' & Hstepc).
          exists {| g_nodes := map.put gs_d.(g_nodes) c (nsc', tauc ++ [I_event m]);
                    g_messages := ms1 ++ ms2 |}, [].
          split.
          * eapply gstep_receive; [exact Hpc | exact Hgc | exact Hstepc | exact Hsplit].
          * apply eventually_done. cbn. exists nsc', (tauc ++ [I_event m]).
            split; [apply map.get_put_same|].
            rewrite inputs_of_app. apply in_or_app. right. left. reflexivity.
        + left. apply eventually_done. exact Hrd.
      - apply eventually_done. exact Hr.
    Qed.

    (* Force a node f (armed for every message in [outs]) to emit all of them, so
       each forwarded (n', mu) is queued or already delivered.  Induction on the
       LIST [outs]; each element uses drive_node_emit (its own will-tree induction)
       — no nested induction. *)
    Lemma force_emit_list :
      A_total ->
      nodes_ciw' ->
      forall (outs : list message) (f : node_id) npf,
        map.get p f = Some npf ->
        forall TX gsX, star gstep initial_graph_state TX gsX ->
        forall nsf tf, map.get gsX.(g_nodes) f = Some (nsf, tf) ->
        (forall mu, In mu outs -> can_output (node_step npf) nsf tf mu) ->
        forall t,
        eventually (can_step gstep Ag)
          (fun '(gs', _) =>
             core_dom gsX gs' /\
             (forall mu n', In mu outs -> In n' (forward f mu) ->
                In (n', mu) gs'.(g_messages) \/ node_received gs' n' mu))
          (gsX, t).
    Proof.
      intros A_univ Hpernode outs.
      induction outs as [|mu outs IH];
        intros f npf Hpf TX gsX HTX nsf tf HgX Hcan t.
      - apply eventually_done. split; [apply core_dom_refl|]. intros mu n' [] _.
      - pose proof (node_will A_univ Hpernode f npf Hpf TX gsX nsf tf HTX HgX mu
                      (Hcan mu (or_introl eq_refl))) as Hwillmu.
        pose proof (drive_node_emit A_univ npf f mu Hpf (nsf, tf) Hwillmu gsX t
                      (ex_intro _ tf (conj HgX (fun x H => H)))) as Hemit.
        eapply eventually_trans.
        { apply (eventually_carry_inv
                   (fun gs => reachable gs /\ core_dom gsX gs)
                   ltac:(intros gs T gs' Hs [(T0 & HT0) Hdom]; split;
                         [exists (T0 ++ T); eapply star_app; eassumption
                         | eapply core_dom_run; eassumption])
                   _ gsX t (conj (ex_intro _ TX HTX) (core_dom_refl gsX)) Hemit). }
        intros [gsM tM] (Hemitted & (TM & HTM) & HdomM).
        destruct Hemitted as (nsM & tfM & HgfM & HoutM).
        assert (Hfwd_mu : forall n', In n' (forward f mu) ->
                  In (n', mu) gsM.(g_messages) \/ node_received gsM n' mu).
        { intros n' Hn'. apply (graph_saturated _ _ HTM f npf nsM tfM Hpf HgfM mu n' HoutM Hn'). }
        destruct HdomM as [HdomM_n HdomM_m].
        destruct (HdomM_n f nsf tf HgX) as (nsM' & tfM' & HgfM' & Hincl_f).
        assert (nsM' = nsM) by congruence. assert (tfM' = tfM) by congruence. subst nsM' tfM'.
        assert (Hcan' : forall mu', In mu' outs -> can_output (node_step npf) nsM tfM mu').
        { intros mu' Hin'.
          apply (node_cap_transfer A_univ Hpernode f npf Hpf
                   TX gsX nsf tf HTX HgX TM gsM nsM tfM HTM HgfM Hincl_f
                   mu' (Hcan mu' (or_intror Hin'))). }
        pose proof (IH f npf Hpf TM gsM HTM nsM tfM HgfM Hcan' tM) as Hrec.
        eapply eventually_trans.
        { apply (eventually_carry_inv
                   (fun gs => forall n', In n' (forward f mu) ->
                      In (n', mu) gs.(g_messages) \/ node_received gs n' mu)
                   ltac:(intros gs T gs' Hs Hinv n' Hn';
                         destruct (Hinv n' Hn') as [Hq | Hr];
                         [ apply (queue_fate _ _ _ Hs n' mu Hq)
                         | right; apply (node_received_mono _ _ _ Hs n' mu Hr) ])
                   _ gsM tM Hfwd_mu Hrec). }
        intros [gsF tF] ((HdomMF & Hfwds') & Hfwd_mu_F).
        apply eventually_done. split.
        + eapply core_dom_trans; [exact (conj HdomM_n HdomM_m) | exact HdomMF].
        + intros mu0 n' Hin0 Hn'. cbn in Hin0. destruct Hin0 as [-> | Hin0'].
          * apply Hfwd_mu_F. exact Hn'.
          * apply Hfwds'; assumption.
    Qed.

    (* The angel can force, from any reachable state dominating a checkpoint gsC,
       a state dominating gs_pre (where gsC reaches gs_pre by an input-free path).
       Induction on the PATH (list of steps); each step uses force_emit_list /
       force_deliver. *)
    Lemma force_dominator :
      A_total ->
      nodes_input_total ->
      nodes_ciw' ->
      forall TC gsC gs_pre, star gstep gsC TC gs_pre ->
      inputs_of TC = [] ->
      forall TC0, star gstep initial_graph_state TC0 gsC ->
      forall TX gsX, star gstep initial_graph_state TX gsX ->
      core_dom gsC gsX ->
      forall t,
      eventually (can_step gstep Ag)
        (fun '(gs', _) => core_dom gs_pre gs') (gsX, t).
    Proof.
      intros A_univ Hit Hpernode TC gsC gs_pre Hstar.
      induction Hstar as [gC | gC e gC1 TC' gpre Hstep Hstar' IH];
        intros HinpTC TC0 HC0 TX gsX HTX Hdom t.
      - apply eventually_done. exact Hdom.
      - cbn in HinpTC.
        inv_gstep Hstep; subst.
        + cbn in HinpTC. discriminate.
        + (* gstep_run ni: emit outsi from gsX's ni, reach a dominator of gC1 *)
          destruct Hdom as [Hdom_n Hdom_m].
          destruct (Hdom_n ni nsi ti Hgi) as (nsXi & tXi & HgXi & Hincli).
          (* node ni is armed for every message it emits at gC, hence (by monotone'
             across the domination) also at gsX. *)
          assert (Hcan : forall mu, In mu outsi -> can_output (node_step npi) nsXi tXi mu).
          { intros mu Hmu.
            apply (node_cap_transfer A_univ Hpernode ni npi Hpi
                     TC0 gC nsi ti HC0 Hgi TX gsX nsXi tXi HTX HgXi Hincli mu).
            exists [O_event outsi], nsi'. split; [econstructor; [exact Hsi|constructor]|].
            split; [reflexivity|]. exists outsi. split; [left; reflexivity | exact Hmu]. }
          eapply eventually_trans.
          { apply (eventually_carry_inv
                     (fun gs => reachable gs)
                     ltac:(intros gs T gs' Hs (T0 & HT0); exists (T0 ++ T);
                           eapply star_app; eassumption)
                     _ gsX t (ex_intro _ TX HTX)
                     (force_emit_list A_univ Hpernode outsi ni npi Hpi
                        TX gsX HTX nsXi tXi HgXi Hcan t)). }
          intros [gs' t'] ((HdomX' & Hfwds) & (TX' & HTX')).
          assert (HdomC1 : core_dom
                    {| g_nodes := map.put (g_nodes gC) ni (nsi', ti ++ [O_event outsi]);
                       g_messages := g_messages gC ++
                         flat_map (fun m => map (fun n' => (n', m)) (forward ni m)) outsi |}
                    gs').
          { pose proof (core_dom_trans _ _ _ (conj Hdom_n Hdom_m) HdomX') as [HdC_n HdC_m].
            split.
            - intros nn nsA tA HgA. cbn in HgA.
              destruct (Nat.eq_dec nn ni) as [->|Hne].
              + rewrite map.get_put_same in HgA. injection HgA as <- <-.
                destruct (HdC_n ni nsi ti Hgi) as (nsB & tB & HgB & HinclB).
                exists nsB, tB. split; [exact HgB|].
                rewrite inputs_of_app. cbn. rewrite app_nil_r. exact HinclB.
              + rewrite map.get_put_diff in HgA by auto. apply (HdC_n nn nsA tA HgA).
            - intros nn mm Hin. cbn in Hin. apply in_app_or in Hin as [Hin | Hin].
              + apply (HdC_m nn mm Hin).
              + apply in_flat_map in Hin as (mu & Hmu & Hin).
                apply in_map_iff in Hin as (n'' & Heq & Hn'').
                injection Heq as <- <-. apply (Hfwds mu n'' Hmu Hn''). }
          apply (IH HinpTC (TC0 ++ [O_event (map (fun m => (m, ni)) (filter (output_visible ni) outsi))])
                    (star_app _ _ _ _ _ _ HC0
                       (star_step _ _ _ _ _ _ Hstep (star_refl _ _)))
                    TX' gs' HTX' HdomC1 t').
        + (* gstep_receive ni mi: deliver (ni,mi) at gsX, reach a dominator of gC1 *)
          destruct Hdom as [Hdom_n Hdom_m].
          destruct (Hdom_n ni nsi ti Hgi) as (nsXi & tXi & HgXi & Hincli).
          destruct (reachable_state_initial _ _ HTX ni _ HgXi) as (ns0i & Hns0i).
          assert (Hcm : In (ni, mi) gsX.(g_messages) \/ node_received gsX ni mi).
          { apply Hdom_m. rewrite Hmsg. apply in_or_app. right. left. reflexivity. }
          eapply eventually_trans.
          { apply (eventually_carry_inv
                     (fun gs => reachable gs /\ core_dom gsX gs)
                     ltac:(intros gs T gs' Hs [(T0 & HT0) Hd]; split;
                           [exists (T0 ++ T); eapply star_app; eassumption
                           | eapply core_dom_run; eassumption])
                     _ gsX t (conj (ex_intro _ TX HTX) (core_dom_refl gsX))
                     (force_deliver Hit TX gsX HTX ni mi npi ns0i Hpi Hns0i Hcm t)). }
          intros [gs' t'] (Hrcv & (TX' & HTX') & HdomXg').
          assert (HdomC1 : core_dom
                    {| g_nodes := map.put (g_nodes gC) ni (nsi', ti ++ [I_event mi]);
                       g_messages := msa ++ msb |} gs').
          { assert (HdomCg' : core_dom gC gs')
              by (eapply core_dom_trans; [exact (conj Hdom_n Hdom_m) | exact HdomXg']).
            destruct HdomCg' as [HdC_n HdC_m].
            split.
            - intros nn nsA tA HgA. cbn in HgA.
              destruct (Nat.eq_dec nn ni) as [->|Hne].
              + rewrite map.get_put_same in HgA. injection HgA as <- <-.
                destruct (HdC_n ni nsi ti Hgi) as (nsB & tB & HgB & HinclB).
                destruct Hrcv as (nsr & tr & Hgr & Hinr).
                assert (tr = tB) by congruence. subst tr.
                exists nsB, tB. split; [exact HgB|].
                rewrite inputs_of_app. cbn. apply incl_app; [exact HinclB|].
                intros x [<-|[]]. exact Hinr.
              + rewrite map.get_put_diff in HgA by auto. apply (HdC_n nn nsA tA HgA).
            - intros nn mm Hin. cbn in Hin. apply (HdC_m nn mm).
              rewrite Hmsg. apply in_app_iff. apply in_app_or in Hin as [H|H];
                [left; exact H | right; right; exact H]. }
          apply (IH HinpTC (TC0 ++ [O_event []])
                    (star_app _ _ _ _ _ _ HC0
                       (star_step _ _ _ _ _ _ Hstep (star_refl _ _)))
                    TX' gs' HTX' HdomC1 t').
    Qed.

    Lemma graph_can_implies_will :
      A_total ->
      nodes_input_total ->
      nodes_ciw' ->
      can_implies_will gstep Ag initial_graph_state.
    Proof.
      intros A_univ Hit Hpernode t gs o Hstar Hall Hcan.
      destruct o as (omsg, on).
      destruct Hcan as (T_a & s_f & Hstar_a & Hinp_a & Hout).
      apply output_in_trace_app in Hout as [Hout_T | Hout_t].
      2: { apply eventually_done. exact Hout_t. }
      (* Find the producing step in T_a (which has inputs_of = []). *)
      destruct (find_producing_step _ _ _ Hstar_a Hinp_a omsg on Hout_T)
        as (T_pre & T_post & np_o & ns_o & ns_o' & t_o & outs_o
            & gs_pre & gs_post & Heq_T & Hstar_pre_a & Hstep_prod
            & Hstar_post_a & Hinp_pre & Hp_o & Hg_o & Hns_o & Hino_o & Hvis_o).
      (* gs_pre is reachable from the initial state via t ++ T_pre. *)
      pose proof (star_app _ _ _ _ _ _ Hstar Hstar_pre_a) as Hstar_to_pre.
      (* At gs_pre, node on is "armed" for omsg (it can emit omsg in one step). *)
      assert (Harmed : can_output (node_step np_o) ns_o t_o omsg).
      { exists [O_event outs_o], ns_o'. split; [econstructor; [exact Hns_o | constructor]|].
        split; [reflexivity|]. apply output_in_trace_app. left.
        exists outs_o. split; [left; reflexivity | exact Hino_o]. }
      (* on's bare initial state, needed for the forward projections in R below. *)
      destruct (reachable_state_initial _ _ Hstar_to_pre on _ Hg_o) as (ns0o & Hns0o).
      (* The carried relation R: reachability, plus "every emission of omsg in on's
         stored trace is reflected (tagged) in the eventually's trace component".
         The latter supplies drive_node_must's output-projection hypothesis at the
         mid state (the eventually trace is built by prepending, not a star trace). *)
      set (R := fun (g : graph_state) (tt : list gevent) =>
                  reachable g /\
                  (forall ns tn, map.get g.(g_nodes) on = Some (ns, tn) ->
                     output_in_trace omsg tn -> output_in_trace (omsg, on) tt)).
      assert (HR_init : R gs t).
      { split; [exists t; exact Hstar|].
        intros ns tn Hg Hotn.
        destruct (node_run _ _ Hstar on np_o ns0o ns tn Hp_o Hns0o Hg) as (_ & Hpres).
        apply (Hpres omsg Hvis_o Hotn). }
      assert (Hstarp : forall g tt t_d s_d, R g tt ->
                star gstep g t_d s_d -> R s_d (t_d ++ tt)).
      { intros g tt t_d s_d [(Tg & HTg) Href] Hs. split.
        - exists (Tg ++ t_d). eapply star_app; eassumption.
        - intros ns tn Hgsd Hotn.
          destruct (project_node_gen _ _ HTg on np_o ns0o Hp_o Hns0o)
            as (taug & nsg & _ & Hgg & _).
          destruct (node_drive_delta _ _ _ Hs on np_o nsg taug Hp_o Hgg)
            as (nsd & td & Hgd & _ & Hpresd).
          assert (tn = taug ++ td) by congruence. subst tn.
          apply output_in_trace_app in Hotn as [Ho | Ho].
          + apply output_in_trace_app. right. apply (Href nsg taug Hgg Ho).
          + apply output_in_trace_app. left. apply (Hpresd omsg Hvis_o Ho). }
      assert (Hostep : forall g tt outs g', R g tt ->
                gstep g (O_event outs) g' -> R g' (O_event outs :: tt)).
      { intros g tt outs g' [(Tg & HTg) Href] Hstep'. split.
        - exists (Tg ++ [O_event outs]).
          eapply star_app; [exact HTg | econstructor; [exact Hstep' | constructor]].
        - intros ns tn Hg' Hotn.
          inv_gstep Hstep'; subst.
          + (* gstep_run ni; the visible event equals O_event outs *)
            cbn in Hg'. destruct (Nat.eq_dec on ni) as [->|Hne].
            * rewrite map.get_put_same in Hg'. injection Hg' as <- <-.
              apply output_in_trace_app in Hotn as [Ho | Ho].
              -- change (O_event _ :: tt) with ([O_event (map (fun m => (m, ni)) (filter (output_visible ni) outsi))] ++ tt).
                 apply output_in_trace_app. right. apply (Href nsi ti Hgi Ho).
              -- destruct Ho as (os & [Heqo|[]] & Hino). injection Heqo as <-.
                 exists (map (fun m => (m, ni)) (filter (output_visible ni) outsi)).
                 split; [left; reflexivity|].
                 apply In_tag. apply filter_In. split; [exact Hino | exact Hvis_o].
            * rewrite map.get_put_diff in Hg' by auto.
              apply (Href ns tn Hg') in Hotn.
              change (O_event _ :: tt) with ([O_event (map (fun m => (m, ni)) (filter (output_visible ni) outsi))] ++ tt).
              apply output_in_trace_app. right. exact Hotn.
          + (* gstep_receive ni; the event is O_event [] *)
            cbn in Hg'. destruct (Nat.eq_dec on ni) as [->|Hne].
            * rewrite map.get_put_same in Hg'. injection Hg' as <- <-.
              apply output_in_trace_app in Hotn as [Ho | Ho].
              -- change (O_event [] :: tt) with ([O_event []] ++ tt).
                 apply output_in_trace_app. right. apply (Href nsi ti Hgi Ho).
              -- destruct Ho as (os & [Heqo|[]] & _). discriminate Heqo.
            * rewrite map.get_put_diff in Hg' by auto.
              apply (Href ns tn Hg') in Hotn.
              change (O_event [] :: tt) with ([O_event []] ++ tt).
              apply output_in_trace_app. right. exact Hotn. }
      (* Force the graph from gs to a state dominating gs_pre, carrying R. *)
      eapply eventually_trans.
      { apply (eventually_carry_inv2 R Hstarp Hostep _ gs t HR_init
                 (force_dominator A_univ Hit Hpernode T_pre gs gs_pre Hstar_pre_a Hinp_pre
                    t Hstar t gs Hstar (core_dom_refl gs) t)). }
      intros [gsStar tStar] (Hdomstar & (TStar & HTStar) & HRStar).
      (* on dominates its gs_pre state at gsStar, so it is still armed for omsg
         there (capability transfer), hence will emit it. *)
      destruct Hdomstar as [Hds_n _].
      destruct (Hds_n on ns_o t_o Hg_o) as (nsS & tS & HgS & HinclS).
      assert (HcanS : can_output (node_step np_o) nsS tS omsg).
      { apply (node_cap_transfer A_univ Hpernode on np_o Hp_o
                 _ gs_pre ns_o t_o Hstar_to_pre Hg_o
                 _ gsStar nsS tS HTStar HgS HinclS omsg Harmed). }
      pose proof (node_will A_univ Hpernode on np_o Hp_o TStar gsStar nsS tS HTStar HgS
                    omsg HcanS) as Hwillo.
      apply (drive_node_must A_univ np_o on omsg Hp_o Hvis_o (nsS, tS) Hwillo gsStar tStar
               (ex_intro _ tS HgS) (HRStar nsS tS HgS)).
    Qed.
  End graph.

  Section graphs.
    Context {node_prog1 : Type} {graph_prog1 : map.map node_id node_prog1}.
    Context {node_state1 : Type}
            {node_states1 : map.map node_id (node_state1 * list IO_event)}.
    Context {node_states1_ok : map.ok node_states1}.
    Context (p1 : graph_prog1) (initial_ns1 : node_states1).
    Context (initial_ns1_empty :
               forall n x, map.get initial_ns1 n = Some x -> snd x = []).
    Context (node_step1 : node_prog1 -> node_state1 -> IO_event -> node_state1 -> Prop).

    Context {node_prog2 : Type} {graph_prog2 : map.map node_id node_prog2}.
    Context {node_state2 : Type}
            {node_states2 : map.map node_id (node_state2 * list IO_event)}.
    Context {node_states2_ok : map.ok node_states2}.
    Context (p2 : graph_prog2) (initial_ns2 : node_states2).
    Context (initial_ns2_empty :
               forall n x, map.get initial_ns2 n = Some x -> snd x = []).
    Context (node_step2 : node_prog2 -> node_state2 -> IO_event -> node_state2 -> Prop).

    (* Extract the per-node correspondence at a node present in graph 2. *)
    Lemma corr_at :
      Forall4_map
        (fun _ np1 '(ns1, _) np2 '(ns2, _) =>
           steps_corresp_sound A (node_step1 np1) ns1 (node_step2 np2) ns2)
        p1 initial_ns1 p2 initial_ns2 ->
      forall n np2, map.get p2 n = Some np2 ->
      exists np1 i1 i2,
        map.get p1 n = Some np1 /\
        map.get initial_ns1 n = Some i1 /\
        map.get initial_ns2 n = Some i2 /\
        steps_corresp_sound A (node_step1 np1) (fst i1) (node_step2 np2) (fst i2).
    Proof.
      intros Hcorr n np2 Hp2. pose proof (Hcorr n) as H. rewrite Hp2 in H.
      destruct (map.get p1 n) as [np1|] eqn:E1;
        destruct (map.get initial_ns1 n) as [[a1 b1]|] eqn:E2;
        destruct (map.get initial_ns2 n) as [[a2 b2]|] eqn:E3;
        cbn in H; try contradiction.
      exists np1, (a1, b1), (a2, b2).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact H.
    Qed.

    (* Cross-graph domination: graph-1 state gs1 dominates graph-2 state gs2 — each
       node of gs1 has received a superset of gs2's node's inputs, and every message
       queued in gs2 is queued or already delivered in gs1. *)
    Definition xdom (gs2 : @graph_state node_state2 node_states2)
                    (gs1 : @graph_state node_state1 node_states1) : Prop :=
      (forall n ns2 t2, map.get gs2.(g_nodes) n = Some (ns2, t2) ->
         exists ns1 t1, map.get gs1.(g_nodes) n = Some (ns1, t1) /\
                        incl (inputs_of t2) (inputs_of t1))
      /\
      (forall n m, In (n, m) gs2.(g_messages) ->
         In (n, m) gs1.(g_messages) \/ node_received gs1 n m).

    (* Arming transfer: if node2-n produces mu (via a real node-2 run at inputs I),
       then node1-n can_output mu from any reachable graph-1 state of n whose inputs
       include I.  Uses steps_corresp_sound (per output) then monotone' (graph 1). *)
    Lemma xarm :
      (forall t, A t) ->
      Forall2_map (fun _ np x => can_implies_will' (node_step1 np) A (fst x)) p1 initial_ns1 ->
      Forall4_map
        (fun _ np1 '(ns1, _) np2 '(ns2, _) =>
           steps_corresp_sound A (node_step1 np1) ns1 (node_step2 np2) ns2)
        p1 initial_ns1 p2 initial_ns2 ->
      forall n np1 np2 i1 i2,
        map.get p1 n = Some np1 ->
        map.get p2 n = Some np2 ->
        map.get initial_ns1 n = Some i1 ->
        map.get initial_ns2 n = Some i2 ->
        forall t2 ns2', star (node_step2 np2) (fst i2) t2 ns2' ->
        forall mu, output_in_trace mu t2 ->
        forall ns1 t1, star (node_step1 np1) (fst i1) t1 ns1 ->
          incl (inputs_of t2) (inputs_of t1) ->
          can_output (node_step1 np1) ns1 t1 mu.
    Proof.
      intros A_univ Hciw1 Hcorr n np1 np2 i1 i2 Hp1 Hp2 Hi1 Hi2
             t2 ns2' Hstar2 mu Hmu ns1 t1 Hstar1 Hincl.
      destruct (corr_at Hcorr n np2 Hp2) as (np1' & i1' & i2' & Hp1' & Hi1' & Hi2' & Hsc).
      assert (np1' = np1) by congruence. assert (i1' = i1) by congruence.
      assert (i2' = i2) by congruence. subst np1' i1' i2'.
      pose proof (Hsc t2 ns2' mu Hstar2 (allowed_trace_universal A A_univ t2) Hmu) as Hprod.
      destruct Hprod as (tp & nsp & Hstarp & Hinpp & Houtp).
      assert (Hcanp : can_output (node_step1 np1) nsp tp mu).
      { exists [], nsp. split; [constructor|]. split; [reflexivity| exact Houtp]. }
      pose proof (proj2 (pernode_spec p1 initial_ns1 node_step1 Hciw1 n np1 i1 Hp1 Hi1)) as Hmono.
      apply (Hmono tp t1 nsp ns1 mu Hstarp Hstar1
               (allowed_trace_universal A A_univ tp) (allowed_trace_universal A A_univ t1)).
      - rewrite Hinpp. exact Hincl.
      - exact Hcanp.
    Qed.

    (* A pure-input graph run leaves all node states untouched and the message queue
       determined solely by the injected inputs — identical for any graph with the
       same routing. *)
    Lemma input_run_msgs :
      forall {NPr : Type} {GPr : map.map node_id NPr}
             {NS : Type} {NSM : map.map node_id (NS * list IO_event)}
             (pp : GPr) (nstep : NPr -> NS -> IO_event -> NS -> Prop)
             (ini : NSM) (m0 : list (node_id * message)) inps gs,
        star (graph_step pp nstep) {| g_nodes := ini; g_messages := m0 |}
             (map I_event inps) gs ->
        gs.(g_nodes) = ini /\
        gs.(g_messages) =
          fold_left (fun acc mn => (snd mn, fst mn) :: acc) inps m0.
    Proof.
      intros NPr GPr NS NSM pp nstep ini m0 inps. revert m0.
      induction inps as [|mn inps IH]; intros m0 gs Hstar; cbn in Hstar.
      - inversion Hstar; subst. split; reflexivity.
      - inversion Hstar as [|s0 e s1 t0 s2 Hstep Hrest]; subst.
        inversion Hstep as [ gs' n' m' Hia | gs' n' np' ns' t' ns'' outs' Hp' Hg' Hs'
                           | gs' n' np' ns' t' ns'' m' msa msb Hp' Hg' Hs' Hmsg ]; subst.
        destruct (IH ((n', m') :: m0) gs Hrest) as (Hn & Hm).
        split; [exact Hn|]. cbn. exact Hm.
    Qed.

    Lemma graphs_corresp_sound :
      (forall t, A t) ->
      (forall n np, map.get p1 n = Some np -> input_total (node_step1 np)) ->
      Forall2_map (fun _ np x => can_implies_will' (node_step1 np) A (fst x)) p1 initial_ns1 ->
      Forall4_map
        (fun _ np1 '(ns1, _) np2 '(ns2, _) =>
           steps_corresp_sound A (node_step1 np1) ns1 (node_step2 np2) ns2)
        p1 initial_ns1 p2 initial_ns2 ->
      steps_corresp_sound' Ag
        (graph_step p1 node_step1) (initial_graph_state initial_ns1)
        (graph_step p2 node_step2) (initial_graph_state initial_ns2).
    Proof.
    Admitted.
  End graphs.
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
