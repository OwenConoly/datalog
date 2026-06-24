From coqutil Require Import Map.Interface.
From coqutil Require Import Semantics.OmniSmallstepCombinators.
From Stdlib Require Import List PeanoNat.
From Datalog Require Import Smallstep Map.
Import ListNotations.

Definition node_id := nat.
Section __.
  Context {message : Type}.
  Context {label : Type}.
  Context (input_allowed : node_id -> message -> bool).
  Context (forward : node_id -> message -> list node_id).
  Context (output_visible : node_id -> message -> bool).

  Context (A : list message -> Prop).
  (*domain is multisets*)

  Local Notation IO_event := (Smallstep.IO_event label message).

  (* The graph's output events are labelled by the node responsible: [receive n]
     for a delivery to node n, [run n lbl] for node n firing its [lbl]-output. *)
  Variant graph_label :=
    | receive (_ : node_id) (_ : message)
    | run (_ : node_id) (_ : label).

  (* The graph's external alphabet tags each message with the node it is
     delivered to / produced by, so inputs to different nodes are distinguishable. *)
  Local Notation gevent := (Smallstep.IO_event graph_label (message * node_id)).

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
    | gstep_run gs n np ns t ns' lbl outs :
      map.get p n = Some np ->
      map.get gs.(g_nodes) n = Some (ns, t) ->
      node_step np ns (O_event lbl outs) ns' ->
      graph_step gs (O_event (run n lbl) (map (fun m => (m, n)) (filter (output_visible n) outs)))
                 {| g_nodes := map.put gs.(g_nodes) n (ns', t ++ [O_event lbl outs]);
                   g_messages := gs.(g_messages) ++
                                      flat_map (fun m => map (fun n' => (n', m)) (forward n m))
                                      outs |}
    | gstep_receive gs n np ns t ns' m ms1 ms2 :
      map.get p n = Some np ->
      map.get gs.(g_nodes) n = Some (ns, t) ->
      node_step np ns (I_event m) ns' ->
      gs.(g_messages) = ms1 ++ (n, m) :: ms2 ->
      graph_step gs (O_event (receive n m) [])
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
                     | gs0 ni npi nsi ti nsi' lbli outsi Hpi Hgi Hsi
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
        intros o _ (lbl0 & outs & Hin & _); inversion Hin.
      - inv_gstep Hstep; subst.
        + destruct (IH n np ns t Hp Hg0) as (ns' & td & Hg & Hstd & Hpres).
          exists ns', td. split; [exact Hg|]. split; [exact Hstd|].
          intros o Hvis Hout. specialize (Hpres o Hvis Hout).
          destruct Hpres as (lbl0 & outs' & Hin & Hino). exists lbl0, outs'. split; [right; exact Hin|exact Hino].
        + destruct (Nat.eq_dec n ni) as [Heq|Hne].
          * subst ni. assert (npi = np) by congruence. subst npi.
            assert (Heqp : (nsi, ti) = (ns, t)) by congruence.
            injection Heqp as Hns Ht; subst nsi ti.
            destruct (IH n np nsi' (t ++ [O_event lbli outsi]) Hp) as (ns' & td & Hg & Hstd & Hpres).
            { cbn. apply map.get_put_same. }
            exists ns', (O_event lbli outsi :: td).
            replace (t ++ O_event lbli outsi :: td) with ((t ++ [O_event lbli outsi]) ++ td)
              by (rewrite <- app_assoc; reflexivity).
            split; [exact Hg|]. split; [econstructor; [exact Hsi | exact Hstd]|].
            intros o Hvis (lbl0 & outs' & Hin & Hino). cbn in Hin. destruct Hin as [Heq|Hin_rest].
            -- injection Heq as Hlbl Houts; subst outs'.
               exists (run n lbli), (map (fun m => (m, n)) (filter (output_visible n) outsi)).
               split; [left; reflexivity|].
               apply In_tag. apply filter_In. split; [exact Hino|exact Hvis].
            -- specialize (Hpres o Hvis (ex_intro _ lbl0 (ex_intro _ outs' (conj Hin_rest Hino)))).
               destruct Hpres as (lbl'' & outs'' & Hin'' & Hino''). exists lbl'', outs''.
               split; [right; exact Hin''|exact Hino''].
          * destruct (IH n np ns t Hp) as (ns' & td & Hg & Hstd & Hpres).
            { cbn. rewrite map.get_put_diff by auto. exact Hg0. }
            exists ns', td. split; [exact Hg|]. split; [exact Hstd|].
            intros o Hvis Hout. specialize (Hpres o Hvis Hout).
            destruct Hpres as (lbl0 & outs' & Hin & Hino). exists lbl0, outs'. split; [right; exact Hin|exact Hino].
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
            intros o Hvis (lbl0 & outs' & Hin & Hino). cbn in Hin. destruct Hin as [Heq|Hin_rest];
              [discriminate|].
            specialize (Hpres o Hvis (ex_intro _ lbl0 (ex_intro _ outs' (conj Hin_rest Hino)))).
            destruct Hpres as (lbl'' & outs'' & Hin'' & Hino''). exists lbl'', outs''.
            split; [right; exact Hin''|exact Hino''].
          * destruct (IH n np ns t Hp) as (ns' & td & Hg & Hstd & Hpres).
            { cbn. rewrite map.get_put_diff by auto. exact Hg0. }
            exists ns', td. split; [exact Hg|]. split; [exact Hstd|].
            intros o Hvis Hout. specialize (Hpres o Hvis Hout).
            destruct Hpres as (lbl0 & outs' & Hin & Hino). exists lbl0, outs'. split; [right; exact Hin|exact Hino].
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
        destruct Hcan as [node_lbl Hcan].
        apply eventually_step_cps. exists (run n node_lbl).
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
               {| g_nodes := map.put gs_demon.(g_nodes) n (s'', (tr ++ tau_d) ++ [O_event node_lbl outs]);
                  g_messages :=
                    gs_demon.(g_messages) ++
                    flat_map (fun m0 => map (fun n' => (n', m0))
                                            (forward n m0)) outs |}).
        exists gs_next, (map (fun m => (m, n)) (filter (output_visible n) outs)).
        split.
        { eapply gstep_run; [exact Hp | exact Hg_d | exact Hns_step]. }
        apply (IH (s'', O_event node_lbl outs :: tau_d ++ trace_curr) Hmidset_at gs_next).
        + cbn. exists ((tr ++ tau_d) ++ [O_event node_lbl outs]). apply map.get_put_same.
        + intros (lbl0 & outs' & Hin & Hino).
          cbn in Hin. destruct Hin as [Heq|Hin_rest].
          * injection Heq as Hlbl Houts; subst outs'.
            exists (run n node_lbl), (map (fun m => (m, n)) (filter (output_visible n) outs)).
            split; [left; reflexivity|].
            apply In_tag. apply filter_In. split; [exact Hino|exact Hvis].
          * apply in_app_or in Hin_rest as [Hin_d|Hin_curr].
            -- specialize (Hpres_d o Hvis
                          (ex_intro _ lbl0 (ex_intro _ outs' (conj Hin_d Hino)))).
               destruct Hpres_d as (lbl'' & outs'' & Hin'' & Hino'').
               exists lbl'', outs''. split.
               { right. apply in_or_app. left. exact Hin''. }
               exact Hino''.
            -- assert (Hcurr : output_in_trace o trace_curr)
                 by (exists lbl0, outs'; split; [exact Hin_curr|exact Hino]).
               specialize (Hout_proj Hcurr).
               destruct Hout_proj as (lbl'' & outs'' & Hin'' & Hino'').
               exists lbl'', outs''. split; [right; apply in_or_app; right; exact Hin''|exact Hino''].
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
                 (outs_o : list message) (lbl_o : label)
                 (gs_pre gs_post : graph_state),
            T = T_pre ++ O_event (run n_o lbl_o) (map (fun m => (m, n_o)) (filter (output_visible n_o) outs_o)) :: T_post /\
            star gstep gs_start T_pre gs_pre /\
            gstep gs_pre
                       (O_event (run n_o lbl_o) (map (fun m => (m, n_o)) (filter (output_visible n_o) outs_o))) gs_post /\
            star gstep gs_post T_post s_f /\
            inputs_of T_pre = [] /\
            map.get p n_o = Some np_o /\
            map.get gs_pre.(g_nodes) n_o = Some (ns_o, t_o) /\
            node_step np_o ns_o (O_event lbl_o outs_o) ns_o' /\
            In o outs_o /\
            output_visible n_o o = true.
    Proof.
      intros gs_start T s_f Hstar Hinp o n_o.
      induction Hstar as [s|s e s' t0 s'' Hstep Hstar IH]; intros Hout.
      - cbv [output_in_trace] in Hout. destruct Hout as (? & ? & Hin & _). inversion Hin.
      - cbn in Hinp. destruct e as [m|lbl_e outs_e]; [discriminate|]. cbn in Hinp.
        change (O_event lbl_e outs_e :: t0) with ([O_event lbl_e outs_e] ++ t0) in Hout.
        apply output_in_trace_app in Hout as [Hout_head|Hout_rest].
        + (* o is in the head event *)
          destruct Hout_head as (lbl00 & outs0 & Hin0 & Hino0).
          cbn in Hin0. destruct Hin0 as [Heq|]; [|contradiction].
          injection Heq as Hlbl00 Houts0; subst outs0.
          inversion Hstep as [
            | gs0 n0 np0 ns0 t0n ns0' lbl0 outs_full Hp0 Hg0 Hns0
            | gs0 n0 np0 ns0 t0n ns0' m0 ms1 ms2 Hp0 Hg0 Hns0 Hmsg ]; subst.
          * (* gstep_run for n0 *)
            apply In_tag_inv in Hino0 as [Hn0eq Hino_filt]. subst n0.
            rewrite filter_In in Hino_filt. destruct Hino_filt as [Hino_full Hvis].
            exists [], t0, np0, ns0, ns0', t0n, outs_full, lbl0, s,
              {| g_nodes := map.put s.(g_nodes) n_o (ns0', t0n ++ [O_event lbl0 outs_full]);
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
          destruct IH as (T_pre & T_post & np_o & ns_o & ns_o' & t_o & outs_o & lbl_o
                          & gs_pre & gs_post & Heq_T & Hstar_pre & Hstep_prod
                          & Hstar_post & Hinp_pre & Hp_o & Hg_o & Hns_o
                          & Hino_o & Hvis_o).
          exists (O_event lbl_e outs_e :: T_pre), T_post, np_o, ns_o, ns_o', t_o, outs_o, lbl_o,
                 gs_pre, gs_post.
          split; [cbn; rewrite Heq_T; reflexivity|].
          split; [econstructor; [exact Hstep|exact Hstar_pre]|].
          split; [exact Hstep_prod|]. split; [exact Hstar_post|].
          split; [cbn; exact Hinp_pre|].
          split; [exact Hp_o|]. split; [exact Hg_o|].
          split; [exact Hns_o|]. split; [exact Hino_o | exact Hvis_o].
    Qed.

    (* General version of find_producing_step that does NOT require the run to be
       input-free: an input step in the path simply cannot carry the output, so we
       skip past it.  Used to locate the emission inside a producer run (which has
       its inputs interspersed).  The price is that T_pre may contain inputs. *)
    Lemma find_producing_step' :
      forall (gs_start : graph_state) (T : list gevent) (s_f : graph_state),
        star gstep gs_start T s_f ->
        forall (o : message) (n_o : node_id),
          output_in_trace (o, n_o) T ->
          exists (T_pre T_post : list gevent)
                 (np_o : node_prog)
                 (ns_o ns_o' : node_state) (t_o : list IO_event)
                 (outs_o : list message) (lbl_o : label)
                 (gs_pre gs_post : graph_state),
            T = T_pre ++ O_event (run n_o lbl_o) (map (fun m => (m, n_o)) (filter (output_visible n_o) outs_o)) :: T_post /\
            star gstep gs_start T_pre gs_pre /\
            gstep gs_pre
                       (O_event (run n_o lbl_o) (map (fun m => (m, n_o)) (filter (output_visible n_o) outs_o))) gs_post /\
            star gstep gs_post T_post s_f /\
            map.get p n_o = Some np_o /\
            map.get gs_pre.(g_nodes) n_o = Some (ns_o, t_o) /\
            node_step np_o ns_o (O_event lbl_o outs_o) ns_o' /\
            In o outs_o /\
            output_visible n_o o = true.
    Proof.
      intros gs_start T s_f Hstar o n_o.
      induction Hstar as [s|s e s' t0 s'' Hstep Hstar IH]; intros Hout.
      - cbv [output_in_trace] in Hout. destruct Hout as (? & ? & Hin & _). inversion Hin.
      - destruct e as [m | lbl_e outs_e].
        + (* I_event m: the output cannot live in an input event; recurse. *)
          assert (Hout' : output_in_trace (o, n_o) t0).
          { destruct Hout as (lbl0 & outs & Hin & Hino). destruct Hin as [Heq|Hin];
              [discriminate Heq | exists lbl0, outs; split; [exact Hin | exact Hino]]. }
          specialize (IH Hout').
          destruct IH as (T_pre & T_post & np_o & ns_o & ns_o' & t_o & outs_o & lbl_o
                          & gs_pre & gs_post & Heq_T & Hstar_pre & Hstep_prod
                          & Hstar_post & Hp_o & Hg_o & Hns_o & Hino_o & Hvis_o).
          exists (I_event m :: T_pre), T_post, np_o, ns_o, ns_o', t_o, outs_o, lbl_o,
                 gs_pre, gs_post.
          split; [cbn; rewrite Heq_T; reflexivity|].
          split; [econstructor; [exact Hstep|exact Hstar_pre]|].
          split; [exact Hstep_prod|]. split; [exact Hstar_post|].
          split; [exact Hp_o|]. split; [exact Hg_o|].
          split; [exact Hns_o|]. split; [exact Hino_o | exact Hvis_o].
        + change (O_event lbl_e outs_e :: t0) with ([O_event lbl_e outs_e] ++ t0) in Hout.
          apply output_in_trace_app in Hout as [Hout_head|Hout_rest].
          * destruct Hout_head as (lbl00 & outs0 & Hin0 & Hino0).
            cbn in Hin0. destruct Hin0 as [Heq|]; [|contradiction].
            injection Heq as Hlbl00 Houts0; subst outs0.
            inversion Hstep as [
              | gs0 n0 np0 ns0 t0n ns0' lbl0 outs_full Hp0 Hg0 Hns0
              | gs0 n0 np0 ns0 t0n ns0' m0 ms1 ms2 Hp0 Hg0 Hns0 Hmsg ]; subst.
            -- apply In_tag_inv in Hino0 as [Hn0eq Hino_filt]. subst n0.
               rewrite filter_In in Hino_filt. destruct Hino_filt as [Hino_full Hvis].
               exists [], t0, np0, ns0, ns0', t0n, outs_full, lbl0, s,
                 {| g_nodes := map.put s.(g_nodes) n_o (ns0', t0n ++ [O_event lbl0 outs_full]);
                    g_messages := s.(g_messages) ++
                      flat_map (fun m => map (fun n' => (n', m)) (forward n_o m)) outs_full |}.
               split; [reflexivity|]. split; [constructor|].
               split; [eapply gstep_run; eassumption|].
               split; [exact Hstar|].
               split; [exact Hp0|]. split; [exact Hg0|].
               split; [exact Hns0|]. split; [exact Hino_full | exact Hvis].
            -- cbn in Hino0. contradiction.
          * specialize (IH Hout_rest).
            destruct IH as (T_pre & T_post & np_o & ns_o & ns_o' & t_o & outs_o & lbl_o
                            & gs_pre & gs_post & Heq_T & Hstar_pre & Hstep_prod
                            & Hstar_post & Hp_o & Hg_o & Hns_o & Hino_o & Hvis_o).
            exists (O_event lbl_e outs_e :: T_pre), T_post, np_o, ns_o, ns_o', t_o, outs_o, lbl_o,
                   gs_pre, gs_post.
            split; [cbn; rewrite Heq_T; reflexivity|].
            split; [econstructor; [exact Hstep|exact Hstar_pre]|].
            split; [exact Hstep_prod|]. split; [exact Hstar_post|].
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
            exists nsi', (t ++ [O_event lbli outsi]).
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
          * destruct Hout_new as (lbl0 & outs0 & Hin0 & Hino0). cbn in Hin0.
            destruct Hin0 as [Heq0|[]]. injection Heq0 as Hlbl0 Heq0; subst outs0.
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
            destruct H as (lbl0 & outs0 & Hin0 & _). cbn in Hin0.
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
      destruct Hout as (lbl0 & outs & Hin & _); inversion Hin.
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
            exists nsi', (tA ++ [O_event lbli outsi]). split; [apply map.get_put_same|].
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
        destruct Hcan as [node_lbl Hcan].
        apply eventually_step_cps. exists (run n node_lbl).
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
               {| g_nodes := map.put gs_demon.(g_nodes) n (s'', (tr ++ tau_d) ++ [O_event node_lbl outs]);
                  g_messages :=
                    gs_demon.(g_messages) ++
                    flat_map (fun m0 => map (fun n' => (n', m0))
                                            (forward n m0)) outs |}).
        exists gs_next, (map (fun m => (m, n)) (filter (output_visible n) outs)).
        split.
        { eapply gstep_run; [exact Hp | exact Hg_d | exact Hns_step]. }
        apply (IH (s'', O_event node_lbl outs :: tau_d ++ trace_curr) Hmidset_at gs_next
                  (O_event (run n node_lbl) (map (fun m => (m, n)) (filter (output_visible n) outs)) :: t_demon ++ t)).
        cbn. exists ((tr ++ tau_d) ++ [O_event node_lbl outs]).
        split; [apply map.get_put_same|].
        intros x Hx.
        change (O_event node_lbl outs :: tau_d ++ trace_curr)
          with ([O_event node_lbl outs] ++ (tau_d ++ trace_curr)) in Hx.
        apply output_in_trace_app in Hx as [Hx|Hx].
        + apply output_in_trace_app. right.
          change [O_event node_lbl outs] with ([] ++ [O_event node_lbl outs]) in Hx.
          apply output_in_trace_app in Hx as [Hx|Hx]; [destruct Hx as (?&?&[]&_)|exact Hx].
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
      - destruct Hcan as [glbl Hcan].
        apply eventually_step_cps. exists glbl.
        intros gs_d t_d Hstar_d Hallow.
        specialize (Hcan gs_d t_d Hstar_d Hallow).
        destruct Hcan as [Hmid_left | (s'' & outs & Hstep & Hmidset)].
        + left. apply (IH (gs_d, t_d ++ t) Hmid_left gs_d (t_d ++ t)
                          (Hinv _ _ _ Hstar_d HInv) eq_refl).
        + right. exists s'', outs. split; [exact Hstep|].
          apply (IH _ Hmidset s'' (O_event glbl outs :: t_d ++ t)); [|reflexivity].
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
        (forall gs tt glbl outs gs', R gs tt ->
           gstep gs (O_event glbl outs) gs' -> R gs' (O_event glbl outs :: tt)) ->
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
      - destruct Hcan as [glbl Hcan].
        apply eventually_step_cps. exists glbl.
        intros gs_d t_d Hstar_d Hallow.
        specialize (Hcan gs_d t_d Hstar_d Hallow).
        destruct Hcan as [Hmid_left | (s'' & outs & Hstep & Hmidset)].
        + left. apply (IH (gs_d, t_d ++ tt) Hmid_left gs_d (t_d ++ tt)
                          (Hstarp _ _ _ _ HR Hstar_d) eq_refl).
        + right. exists s'', outs. split; [exact Hstep|].
          apply (IH _ Hmidset s'' (O_event glbl outs :: t_d ++ tt)); [|reflexivity].
          apply (Hostep _ _ _ _ _ (Hstarp _ _ _ _ HR Hstar_d) Hstep).
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
      - apply eventually_step_cps. exists (receive c m).
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
            exists [O_event lbli outsi], nsi'. split; [econstructor; [exact Hsi|constructor]|].
            split; [reflexivity|]. exists lbli, outsi. split; [left; reflexivity | exact Hmu]. }
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
                    {| g_nodes := map.put (g_nodes gC) ni (nsi', ti ++ [O_event lbli outsi]);
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
          apply (IH HinpTC (TC0 ++ [O_event (run ni lbli) (map (fun m => (m, ni)) (filter (output_visible ni) outsi))])
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
          apply (IH HinpTC (TC0 ++ [O_event (receive ni mi) []])
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
        as (T_pre & T_post & np_o & ns_o & ns_o' & t_o & outs_o & lbl_o
            & gs_pre & gs_post & Heq_T & Hstar_pre_a & Hstep_prod
            & Hstar_post_a & Hinp_pre & Hp_o & Hg_o & Hns_o & Hino_o & Hvis_o).
      (* gs_pre is reachable from the initial state via t ++ T_pre. *)
      pose proof (star_app _ _ _ _ _ _ Hstar Hstar_pre_a) as Hstar_to_pre.
      (* At gs_pre, node on is "armed" for omsg (it can emit omsg in one step). *)
      assert (Harmed : can_output (node_step np_o) ns_o t_o omsg).
      { exists [O_event lbl_o outs_o], ns_o'. split; [econstructor; [exact Hns_o | constructor]|].
        split; [reflexivity|]. apply output_in_trace_app. left.
        exists lbl_o, outs_o. split; [left; reflexivity | exact Hino_o]. }
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
      assert (Hostep : forall g tt glbl outs g', R g tt ->
                gstep g (O_event glbl outs) g' -> R g' (O_event glbl outs :: tt)).
      { intros g tt glbl outs g' [(Tg & HTg) Href] Hstep'. split.
        - exists (Tg ++ [O_event glbl outs]).
          eapply star_app; [exact HTg | econstructor; [exact Hstep' | constructor]].
        - intros ns tn Hg' Hotn.
          inv_gstep Hstep'; subst.
          + (* gstep_run ni; the visible event equals O_event (run ni lbli) ... *)
            cbn in Hg'. destruct (Nat.eq_dec on ni) as [->|Hne].
            * rewrite map.get_put_same in Hg'. injection Hg' as <- <-.
              apply output_in_trace_app in Hotn as [Ho | Ho].
              -- change (O_event (run ni lbli) (map (fun m => (m, ni)) (filter (output_visible ni) outsi)) :: tt)
                   with ([O_event (run ni lbli) (map (fun m => (m, ni)) (filter (output_visible ni) outsi))] ++ tt).
                 apply output_in_trace_app. right. apply (Href nsi ti Hgi Ho).
              -- destruct Ho as (lbo & os & [Heqo|[]] & Hino). injection Heqo as Hlbo Hos; subst os.
                 exists (run ni lbli), (map (fun m => (m, ni)) (filter (output_visible ni) outsi)).
                 split; [left; reflexivity|].
                 apply In_tag. apply filter_In. split; [exact Hino | exact Hvis_o].
            * rewrite map.get_put_diff in Hg' by auto.
              apply (Href ns tn Hg') in Hotn.
              change (O_event (run ni lbli) (map (fun m => (m, ni)) (filter (output_visible ni) outsi)) :: tt)
                with ([O_event (run ni lbli) (map (fun m => (m, ni)) (filter (output_visible ni) outsi))] ++ tt).
              apply output_in_trace_app. right. exact Hotn.
          + (* gstep_receive ni; the event is O_event (receive ni mi) [] *)
            cbn in Hg'. destruct (Nat.eq_dec on ni) as [->|Hne].
            * rewrite map.get_put_same in Hg'. injection Hg' as <- <-.
              apply output_in_trace_app in Hotn as [Ho | Ho].
              -- change (O_event (receive ni mi) [] :: tt) with ([O_event (receive ni mi) []] ++ tt).
                 apply output_in_trace_app. right. apply (Href nsi ti Hgi Ho).
              -- destruct Ho as (lbo & os & [Heqo|[]] & _). discriminate Heqo.
            * rewrite map.get_put_diff in Hg' by auto.
              apply (Href ns tn Hg') in Hotn.
              change (O_event (receive ni mi) [] :: tt) with ([O_event (receive ni mi) []] ++ tt).
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

    (* Arming transfer: if node2 produces mu (via a real node-2 run at inputs I),
       then the corresponding node1 (sound w.r.t. it and monotone') can_output mu
       from any of its runs whose inputs include I. *)
    Lemma xarm :
      (forall t, A t) ->
      forall (np1 : node_prog1) (init1 : node_state1),
        monotone' (node_step1 np1) A init1 ->
        forall (np2 : node_prog2) (init2 : node_state2),
          steps_corresp_sound A (node_step1 np1) init1 (node_step2 np2) init2 ->
          forall t2 ns2', star (node_step2 np2) init2 t2 ns2' ->
          forall mu, output_in_trace mu t2 ->
          forall ns1 t1, star (node_step1 np1) init1 t1 ns1 ->
            incl (inputs_of t2) (inputs_of t1) ->
            can_output (node_step1 np1) ns1 t1 mu.
    Proof.
      intros A_univ np1 init1 Hmono np2 init2 Hsc t2 ns2' Hstar2 mu Hmu ns1 t1 Hstar1 Hincl.
      destruct (Hsc t2 ns2' mu Hstar2 (allowed_trace_universal A A_univ t2) Hmu)
        as (tp & nsp & Hstarp & Hinpp & Houtp).
      apply (Hmono tp t1 nsp ns1 mu Hstarp Hstar1
               (allowed_trace_universal A A_univ tp) (allowed_trace_universal A A_univ t1)).
      - rewrite Hinpp. exact Hincl.
      - exists [], nsp. split; [constructor|]. split; [reflexivity| exact Houtp].
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
          fold_left (fun acc '(m, n) => (n, m) :: acc) inps m0 /\
        (forall m n, In (m, n) inps -> input_allowed n m = true).
    Proof.
      intros NPr GPr NS NSM pp nstep ini m0 inps. revert m0.
      induction inps as [|mn inps IH]; intros m0 gs Hstar; cbn in Hstar.
      - inversion Hstar; subst. split; [reflexivity|]. split; [reflexivity|]. intros ? ? [].
      - inversion Hstar as [|s0 e s1 t0 s2 Hstep Hrest]; subst.
        inversion Hstep as [ gs' n' m' Hia | gs' n' np' ns' t' ns'' lbl' outs' Hp' Hg' Hs'
                           | gs' n' np' ns' t' ns'' m' msa msb Hp' Hg' Hs' Hmsg ]; subst.
        destruct (IH ((n', m') :: m0) gs Hrest) as (Hn & Hm & Hal).
        split; [exact Hn|]. split; [cbn; exact Hm|].
        intros mm nn [Heq | Hin]; [injection Heq as -> ->; exact Hia | apply (Hal mm nn Hin)].
    Qed.

    (* Build a graph's pure-input run for any inputs all of whose destinations
       accept them — gives a concrete run with the determined queue. *)
    Lemma build_input_run :
      forall {NPr : Type} {GPr : map.map node_id NPr}
             {NS : Type} {NSM : map.map node_id (NS * list IO_event)}
             (pp : GPr) (nstep : NPr -> NS -> IO_event -> NS -> Prop)
             (ini : NSM) (m0 : list (node_id * message)) inps,
        (forall m n, In (m, n) inps -> input_allowed n m = true) ->
        star (graph_step pp nstep) {| g_nodes := ini; g_messages := m0 |}
             (map I_event inps)
             {| g_nodes := ini;
                g_messages := fold_left (fun acc '(m, n) => (n, m) :: acc) inps m0 |}.
    Proof.
      intros NPr GPr NS NSM pp nstep ini m0 inps. revert m0.
      induction inps as [|mn inps IH]; intros m0 Hal; cbn.
      - constructor.
      - destruct mn as [mm nn]. cbn.
        eapply star_step.
        + apply (gstep_input pp nstep {| g_nodes := ini; g_messages := m0 |} nn mm).
          apply (Hal mm nn); left; reflexivity.
        + cbn. apply IH. intros mm0 nn0 Hin. apply (Hal mm0 nn0). right. exact Hin.
    Qed.

    (* Injecting the same inputs into graph 1 reaches a state dominating the graph-2
       state reached by those inputs (same routing, same resulting queue). *)
    Lemma xdom_inputs :
      Forall4_map
        (fun _ np1 '(ns1, _) np2 '(ns2, _) =>
           steps_corresp_sound A (node_step1 np1) ns1 (node_step2 np2) ns2)
        p1 initial_ns1 p2 initial_ns2 ->
      forall inps GS2,
        star (graph_step p2 node_step2) (initial_graph_state initial_ns2) (map I_event inps) GS2 ->
        exists GS1,
          star (graph_step p1 node_step1) (initial_graph_state initial_ns1) (map I_event inps) GS1 /\
          xdom GS2 GS1.
    Proof.
      intros Hcorr inps GS2 Hstar2.
      destruct (input_run_msgs p2 node_step2 initial_ns2 [] inps GS2 Hstar2)
        as (HGS2n & HGS2m & Hallowed).
      eexists. split; [exact (build_input_run p1 node_step1 initial_ns1 [] inps Hallowed)|].
      split.
      - intros n ns2 t2 Hg. rewrite HGS2n in Hg.
        pose proof (initial_ns2_empty n (ns2, t2) Hg) as Ht2. cbn in Ht2. subst t2.
        pose proof (Hcorr n) as Hc. rewrite Hg in Hc.
        destruct (map.get p1 n) as [np1'|] eqn:E1;
          destruct (map.get initial_ns1 n) as [i1'|] eqn:E2;
          destruct (map.get p2 n) as [np2'|] eqn:E3; cbn in Hc; try contradiction.
        pose proof (initial_ns1_empty n i1' E2) as Ht1. destruct i1' as [ns1' t1'].
        cbn in Ht1. subst t1'.
        exists ns1', []. split; [exact E2 | apply incl_refl].
      - intros n m Hin. left. cbn. rewrite HGS2m in Hin. exact Hin.
    Qed.

    (* xdom composes with a graph-1 core_dom on the right. *)
    Lemma xdom_core_trans :
      forall (a : @graph_state node_state2 node_states2)
             (b c : @graph_state node_state1 node_states1),
        xdom a b -> core_dom b c -> xdom a c.
    Proof.
      intros a b c [Hab_n Hab_m] [Hbc_n Hbc_m]. split.
      - intros n ns2 t2 Hg. destruct (Hab_n n ns2 t2 Hg) as (nsb & tb & Hgb & Hinclb).
        destruct (Hbc_n n nsb tb Hgb) as (nsc & tc & Hgc & Hinclc).
        exists nsc, tc. split; [exact Hgc | eapply incl_tran; eassumption].
      - intros n m Hin. destruct (Hab_m n m Hin) as [Hq | Hr].
        + apply (Hbc_m n m Hq).
        + right. destruct Hr as (ns & t & Hg & Hinm).
          destruct (Hbc_n n ns t Hg) as (nsc & tc & Hgc & Hinclc).
          exists nsc, tc. split; [exact Hgc | apply Hinclc; exact Hinm].
    Qed.

    (* Cross-graph force_dominator: drive graph 1 (its own liveness) from a state
       dominating a graph-2 checkpoint gsC to one dominating gs_pre, where gsC
       reaches gs_pre by a graph-2 input-free path.  Mirrors force_dominator, but
       arms graph-1 nodes via xarm (from graph 2's emissions) and tracks xdom. *)
    Lemma xforce_dominator :
      (forall t, A t) ->
      (forall n np, map.get p1 n = Some np -> input_total (node_step1 np)) ->
      Forall2_map (fun _ np x => can_implies_will' (node_step1 np) A (fst x)) p1 initial_ns1 ->
      Forall4_map
        (fun _ np1 '(ns1, _) np2 '(ns2, _) =>
           steps_corresp_sound A (node_step1 np1) ns1 (node_step2 np2) ns2)
        p1 initial_ns1 p2 initial_ns2 ->
      forall TC gsC gs_pre, star (graph_step p2 node_step2) gsC TC gs_pre ->
      inputs_of TC = [] ->
      forall TC0, star (graph_step p2 node_step2) (initial_graph_state initial_ns2) TC0 gsC ->
      forall TX gsX, star (graph_step p1 node_step1) (initial_graph_state initial_ns1) TX gsX ->
      xdom gsC gsX ->
      forall t,
      eventually (can_step (graph_step p1 node_step1) Ag)
        (fun '(gs', _) => xdom gs_pre gs') (gsX, t).
    Proof.
      intros A_univ Hit Hciw1 Hcorr TC gsC gs_pre Hstar.
      induction Hstar as [gC | gC e gC1 TC' gpre Hstep Hstar' IH];
        intros HinpTC TC0 HC0 TX gsX HTX Hdom t.
      - apply eventually_done. exact Hdom.
      - cbn in HinpTC.
        inversion Hstep as [ gs0 ni mi Hia
                           | gs0 ni npi nsi ti nsi' lbli outsi Hpi Hgi Hsi
                           | gs0 ni npi nsi ti nsi' mi msa msb Hpi Hgi Hsi Hmsg ]; subst.
        + cbn in HinpTC. discriminate.
        + (* gstep_run ni in graph 2 *)
          destruct Hdom as [Hdom_n Hdom_m].
          destruct (Hdom_n ni nsi ti Hgi) as (nsXi & tXi & HgXi & Hincli).
          destruct (corr_at Hcorr ni npi Hpi) as (np1 & i1 & i2 & Hp1 & Hi1 & Hi2 & Hsc).
          destruct (node_run p2 initial_ns2 initial_ns2_empty node_step2 _ _ HC0
                      ni npi i2 nsi ti Hpi Hi2 Hgi) as (Hrun2 & _).
          destruct (node_run p1 initial_ns1 initial_ns1_empty node_step1 _ _ HTX
                      ni np1 i1 nsXi tXi Hp1 Hi1 HgXi) as (Hrun1 & _).
          pose proof (proj2 (pernode_spec p1 initial_ns1 node_step1 Hciw1 ni np1 i1 Hp1 Hi1)) as Hmono.
          assert (Hcan : forall mu, In mu outsi -> can_output (node_step1 np1) nsXi tXi mu).
          { intros mu Hmu.
            apply (xarm A_univ np1 (fst i1) Hmono npi (fst i2) Hsc
                     (ti ++ [O_event lbli outsi]) nsi'
                     (star_app _ _ _ _ _ _ Hrun2 (star_step _ _ _ _ _ _ Hsi (star_refl _ _)))
                     mu
                     ltac:(apply output_in_trace_app; right; exists lbli, outsi;
                           split; [left; reflexivity | exact Hmu])
                     nsXi tXi Hrun1
                     ltac:(rewrite inputs_of_app; cbn; rewrite app_nil_r; exact Hincli)). }
          eapply eventually_trans.
          { apply (eventually_carry_inv p1 node_step1
                     (fun gs => exists T, star (graph_step p1 node_step1)
                                  (initial_graph_state initial_ns1) T gs)
                     ltac:(intros gs T gs' Hs (T0 & HT0); exists (T0 ++ T);
                           eapply star_app; eassumption)
                     _ gsX t (ex_intro _ TX HTX)
                     (force_emit_list p1 initial_ns1 initial_ns1_empty node_step1
                        A_univ Hciw1 outsi ni np1 Hp1 TX gsX HTX nsXi tXi HgXi Hcan t)). }
          intros [gs' t'] ((HdomX' & Hfwds) & (TX' & HTX')).
          assert (HdomC1 : xdom
                    {| g_nodes := map.put (g_nodes gC) ni (nsi', ti ++ [O_event lbli outsi]);
                       g_messages := g_messages gC ++
                         flat_map (fun m => map (fun n' => (n', m)) (forward ni m)) outsi |}
                    gs').
          { pose proof (xdom_core_trans _ _ _ (conj Hdom_n Hdom_m) HdomX') as [HdC_n HdC_m].
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
          apply (IH HinpTC
                    (TC0 ++ [O_event (run ni lbli) (map (fun m => (m, ni)) (filter (output_visible ni) outsi))])
                    (star_app _ _ _ _ _ _ HC0
                       (star_step _ _ _ _ _ _ Hstep (star_refl _ _)))
                    TX' gs' HTX' HdomC1 t').
        + (* gstep_receive ni mi in graph 2 *)
          destruct Hdom as [Hdom_n Hdom_m].
          destruct (Hdom_n ni nsi ti Hgi) as (nsXi & tXi & HgXi & Hincli).
          destruct (corr_at Hcorr ni npi Hpi) as (np1 & i1 & _ & Hp1 & Hi1 & _ & _).
          assert (Hcm : In (ni, mi) gsX.(g_messages) \/ node_received gsX ni mi).
          { apply Hdom_m. rewrite Hmsg. apply in_or_app. right. left. reflexivity. }
          eapply eventually_trans.
          { apply (eventually_carry_inv p1 node_step1
                     (fun gs => (exists T, star (graph_step p1 node_step1)
                                   (initial_graph_state initial_ns1) T gs)
                                /\ core_dom gsX gs)
                     ltac:(intros gs T gs' Hs [(T0 & HT0) Hd]; split;
                           [exists (T0 ++ T); eapply star_app; eassumption
                           | eapply core_dom_run; eassumption])
                     _ gsX t (conj (ex_intro _ TX HTX) (core_dom_refl gsX))
                     (force_deliver p1 initial_ns1 initial_ns1_empty node_step1
                        Hit TX gsX HTX ni mi np1 i1 Hp1 Hi1 Hcm t)). }
          intros [gs' t'] (Hrcv & (TX' & HTX') & HdomXg').
          assert (HdomC1 : xdom
                    {| g_nodes := map.put (g_nodes gC) ni (nsi', ti ++ [I_event mi]);
                       g_messages := msa ++ msb |} gs').
          { assert (HdomCg' : xdom gC gs')
              by (eapply xdom_core_trans; [exact (conj Hdom_n Hdom_m) | exact HdomXg']).
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
          apply (IH HinpTC (TC0 ++ [O_event (receive ni mi) []])
                    (star_app _ _ _ _ _ _ HC0
                       (star_step _ _ _ _ _ _ Hstep (star_refl _ _)))
                    TX' gs' HTX' HdomC1 t').
    Qed.

    (* If the angel can drive graph 1 to a state where node [on] can_output the
       visible message [omsg], then graph 1 will_output (omsg, on).  Factors the
       "carry the output-reflection relation, then fire the node" pattern (cf. the
       tail of graph_can_implies_will). *)
    Lemma graph_emit_visible :
      (forall t, A t) ->
      Forall2_map (fun _ np x => can_implies_will' (node_step1 np) A (fst x)) p1 initial_ns1 ->
      forall (on : node_id) (np1 : node_prog1) (i1 : node_state1 * list IO_event) (omsg : message),
        map.get p1 on = Some np1 ->
        map.get initial_ns1 on = Some i1 ->
        output_visible on omsg = true ->
        forall gs t,
          star (graph_step p1 node_step1) (initial_graph_state initial_ns1) t gs ->
          eventually (can_step (graph_step p1 node_step1) Ag)
            (fun '(gs', _) => exists ns t',
               map.get gs'.(g_nodes) on = Some (ns, t') /\
               can_output (node_step1 np1) ns t' omsg)
            (gs, t) ->
          will_output (graph_step p1 node_step1) Ag gs t (omsg, on).
    Proof.
      intros A_univ Hciw1 on np1 i1 omsg Hp1 Hi1 Hvis_o gs t Hstar Hev.
      unfold will_output.
      set (R := fun (g : @graph_state node_state1 node_states1) (tt : list gevent) =>
                  (exists T, star (graph_step p1 node_step1) (initial_graph_state initial_ns1) T g) /\
                  (forall ns tn, map.get g.(g_nodes) on = Some (ns, tn) ->
                     output_in_trace omsg tn -> output_in_trace (omsg, on) tt)).
      assert (HR_init : R gs t).
      { split; [exists t; exact Hstar|].
        intros ns tn Hg Hotn.
        destruct (node_run p1 initial_ns1 initial_ns1_empty node_step1 _ _ Hstar
                    on np1 i1 ns tn Hp1 Hi1 Hg) as (_ & Hpres).
        apply (Hpres omsg Hvis_o Hotn). }
      assert (Hstarp : forall g tt t_d s_d, R g tt ->
                star (graph_step p1 node_step1) g t_d s_d -> R s_d (t_d ++ tt)).
      { intros g tt t_d s_d [(Tg & HTg) Href] Hs. split.
        - exists (Tg ++ t_d). eapply star_app; eassumption.
        - intros ns tn Hgsd Hotn.
          destruct (project_node_gen p1 initial_ns1 initial_ns1_empty node_step1 _ _ HTg
                      on np1 i1 Hp1 Hi1) as (taug & nsg & _ & Hgg & _).
          destruct (node_drive_delta p1 node_step1 _ _ _ Hs on np1 nsg taug Hp1 Hgg)
            as (nsd & td & Hgd & _ & Hpresd).
          assert (tn = taug ++ td) by congruence. subst tn.
          apply output_in_trace_app in Hotn as [Ho | Ho].
          + apply output_in_trace_app. right. apply (Href nsg taug Hgg Ho).
          + apply output_in_trace_app. left. apply (Hpresd omsg Hvis_o Ho). }
      assert (Hostep : forall g tt glbl outs g', R g tt ->
                graph_step p1 node_step1 g (O_event glbl outs) g' -> R g' (O_event glbl outs :: tt)).
      { intros g tt glbl outs g' [(Tg & HTg) Href] Hstep'. split.
        - exists (Tg ++ [O_event glbl outs]).
          eapply star_app; [exact HTg | econstructor; [exact Hstep' | constructor]].
        - intros ns tn Hg' Hotn.
          inversion Hstep' as [ gs0 ni mi Hia
                             | gs0 ni npi nsi ti nsi' lbli outsi Hpi Hgi Hsi
                             | gs0 ni npi nsi ti nsi' mi msa msb Hpi Hgi Hsi Hmsg ]; subst.
          + cbn in Hg'. destruct (Nat.eq_dec on ni) as [->|Hne].
            * rewrite map.get_put_same in Hg'. injection Hg' as <- <-.
              apply output_in_trace_app in Hotn as [Ho | Ho].
              -- change (O_event (run ni lbli) (map (fun m => (m, ni)) (filter (output_visible ni) outsi)) :: tt)
                   with ([O_event (run ni lbli) (map (fun m => (m, ni)) (filter (output_visible ni) outsi))] ++ tt).
                 apply output_in_trace_app. right. apply (Href nsi ti Hgi Ho).
              -- destruct Ho as (lbo & os & [Heqo|[]] & Hino). injection Heqo as Hlbo Hos; subst os.
                 exists (run ni lbli), (map (fun m => (m, ni)) (filter (output_visible ni) outsi)).
                 split; [left; reflexivity|].
                 apply In_tag. apply filter_In. split; [exact Hino | exact Hvis_o].
            * rewrite map.get_put_diff in Hg' by auto.
              apply (Href ns tn Hg') in Hotn.
              change (O_event (run ni lbli) (map (fun m => (m, ni)) (filter (output_visible ni) outsi)) :: tt)
                with ([O_event (run ni lbli) (map (fun m => (m, ni)) (filter (output_visible ni) outsi))] ++ tt).
              apply output_in_trace_app. right. exact Hotn.
          + cbn in Hg'. destruct (Nat.eq_dec on ni) as [->|Hne].
            * rewrite map.get_put_same in Hg'. injection Hg' as <- <-.
              apply output_in_trace_app in Hotn as [Ho | Ho].
              -- change (O_event (receive ni mi) [] :: tt) with ([O_event (receive ni mi) []] ++ tt).
                 apply output_in_trace_app. right. apply (Href nsi ti Hgi Ho).
              -- destruct Ho as (lbo & os & [Heqo|[]] & _). discriminate Heqo.
            * rewrite map.get_put_diff in Hg' by auto.
              apply (Href ns tn Hg') in Hotn.
              change (O_event (receive ni mi) [] :: tt) with ([O_event (receive ni mi) []] ++ tt).
              apply output_in_trace_app. right. exact Hotn. }
      eapply eventually_trans.
      { apply (eventually_carry_inv2 p1 node_step1 R Hstarp Hostep _ gs t HR_init Hev). }
      intros [gsStar tStar] ((nsS & tS & HgS & HcanS) & (TStar & HTStar) & HRStar).
      pose proof (node_will p1 initial_ns1 initial_ns1_empty node_step1 A_univ Hciw1 on np1 Hp1
                    TStar gsStar nsS tS HTStar HgS omsg HcanS) as Hwillo.
      apply (drive_node_must p1 node_step1 A_univ np1 on omsg Hp1 Hvis_o (nsS, tS) Hwillo
               gsStar tStar (ex_intro _ tS HgS) (HRStar nsS tS HgS)).
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
      intros A_univ Hit Hciw1 Hcorr GS2 inps o Hstar2 Hag Hwill.
      destruct o as (omsg, on).
      assert (Hallow2 : Smallstep.allowed_trace Ag (map I_event inps : list gevent)).
      { unfold Smallstep.allowed_trace. rewrite inputs_of_map_I_event. exact Hag. }
      (* graph 2 will_output -> can_output -> a concrete input-free run W producing o *)
      destruct (will_implies_can (graph_step p2 node_step2) Ag GS2 (map I_event inps)
                  (omsg, on) Hallow2 Hwill) as (W & GSf & HW & HinpW & Hout).
      assert (HoutW : output_in_trace (omsg, on) W).
      { apply output_in_trace_app in Hout as [HoutW | HoutI]; [exact HoutW|].
        exfalso. destruct HoutI as (lbl0 & outs & Hin & _).
        apply in_map_iff in Hin as (x & Heq & _). discriminate. }
      (* locate the producing step in W *)
      destruct (find_producing_step p2 node_step2 _ _ _ HW HinpW omsg on HoutW)
        as (T_pre & _ & np_o & ns_o & ns_o' & t_o & outs_o & lbl_o & gs_preA & _
            & _ & Hstar_preA & _ & _ & Hinp_pre & Hp_o & Hg_o & Hns_o
            & Hino_o & Hvis_o).
      pose proof (star_app _ _ _ _ _ _ Hstar2 Hstar_preA) as Hpre2reach.
      destruct (corr_at Hcorr on np_o Hp_o) as (np1 & i1 & i2 & Hp1 & Hi1 & Hi2 & Hsc).
      (* inject the same inputs into graph 1, reaching a state dominating GS2 *)
      destruct (xdom_inputs Hcorr inps GS2 Hstar2) as (GS1B & HinjB & HxdomB).
      (* graph 1 will_output o from GS1B: drive graph 1 (via xforce_dominator) to a
         state where node on can emit omsg, then graph_emit_visible fires it. *)
      assert (Hwill1 : will_output (graph_step p1 node_step1) Ag GS1B (map I_event inps) (omsg, on)).
      { apply (graph_emit_visible A_univ Hciw1 on np1 i1 omsg Hp1 Hi1 Hvis_o
                 GS1B (map I_event inps) HinjB).
        eapply eventually_trans.
        { apply (eventually_carry_inv p1 node_step1
                   (fun g => exists T, star (graph_step p1 node_step1)
                                (initial_graph_state initial_ns1) T g)
                   ltac:(intros g T g' Hs (T0 & HT0); exists (T0 ++ T);
                         eapply star_app; eassumption)
                   _ GS1B (map I_event inps) (ex_intro _ (map I_event inps) HinjB)
                   (xforce_dominator A_univ Hit Hciw1 Hcorr T_pre GS2 gs_preA Hstar_preA Hinp_pre
                      (map I_event inps) Hstar2 (map I_event inps) GS1B HinjB HxdomB
                      (map I_event inps))). }
        intros [gsStar tStar] (Hdomstar & (TStar & HTStar)).
        apply eventually_done.
        destruct Hdomstar as [Hds_n _].
        destruct (Hds_n on ns_o t_o Hg_o) as (nsS & tS & HgS & HinclS).
        exists nsS, tS. split; [exact HgS|].
        destruct (node_run p2 initial_ns2 initial_ns2_empty node_step2 _ _ Hpre2reach
                    on np_o i2 ns_o t_o Hp_o Hi2 Hg_o) as (Hrun2o & _).
        destruct (node_run p1 initial_ns1 initial_ns1_empty node_step1 _ _ HTStar
                    on np1 i1 nsS tS Hp1 Hi1 HgS) as (Hrun1o & _).
        apply (xarm A_univ np1 (fst i1)
                 (proj2 (pernode_spec p1 initial_ns1 node_step1 Hciw1 on np1 i1 Hp1 Hi1))
                 np_o (fst i2) Hsc
                 (t_o ++ [O_event lbl_o outs_o]) ns_o'
                 (star_app _ _ _ _ _ _ Hrun2o (star_step _ _ _ _ _ _ Hns_o (star_refl _ _)))
                 omsg
                 ltac:(apply output_in_trace_app; right; exists lbl_o, outs_o;
                       split; [left; reflexivity | exact Hino_o])
                 nsS tS Hrun1o
                 ltac:(rewrite inputs_of_app; cbn; rewrite app_nil_r; exact HinclS)). }
      (* will_output -> can_output -> produces, prepending the injection run *)
      destruct (will_implies_can (graph_step p1 node_step1) Ag GS1B (map I_event inps)
                  (omsg, on) Hallow2 Hwill1) as (W1 & GS1f & HW1 & HinpW1 & Hout1).
      unfold produces. exists (map I_event inps ++ W1), GS1f.
      split; [eapply star_app; [exact HinjB | exact HW1]|].
      split; [rewrite inputs_of_app, inputs_of_map_I_event, HinpW1, app_nil_r; reflexivity|].
      apply output_in_trace_app. apply output_in_trace_app in Hout1 as [H|H];
        [right; exact H | left; exact H].
    Qed.

    (* ===================== Cross-graph completeness ===================== *)

    (* Per-node completeness extraction, keyed on the graph-1 node (the checkpoint
       side in the completeness drive). *)
    Lemma corr_at_complete :
      Forall4_map
        (fun _ np1 '(ns1, _) np2 '(ns2, _) =>
           steps_corresp_complete A (node_step1 np1) ns1 (node_step2 np2) ns2)
        p1 initial_ns1 p2 initial_ns2 ->
      forall n np1, map.get p1 n = Some np1 ->
      exists np2 i1 i2,
        map.get p2 n = Some np2 /\
        map.get initial_ns1 n = Some i1 /\
        map.get initial_ns2 n = Some i2 /\
        steps_corresp_complete A (node_step1 np1) (fst i1) (node_step2 np2) (fst i2).
    Proof.
      intros Hcorr n np1 Hp1. pose proof (Hcorr n) as H. rewrite Hp1 in H.
      destruct (map.get initial_ns1 n) as [[a1 b1]|] eqn:E2;
        destruct (map.get p2 n) as [np2|] eqn:E3;
        destruct (map.get initial_ns2 n) as [[a2 b2]|] eqn:E4;
        cbn in H; try contradiction.
      exists np2, (a1, b1), (a2, b2).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact H.
    Qed.

    (* The mirror of xdom: graph-2 state gs2 dominates graph-1 state gs1.  Each node
       of gs2 has received a superset of gs1's inputs, and every message queued in
       gs1 is queued or already delivered in gs2. *)
    Definition xdom' (gs1 : @graph_state node_state1 node_states1)
                     (gs2 : @graph_state node_state2 node_states2) : Prop :=
      (forall n ns1 t1, map.get gs1.(g_nodes) n = Some (ns1, t1) ->
         exists ns2 t2, map.get gs2.(g_nodes) n = Some (ns2, t2) /\
                        incl (inputs_of t1) (inputs_of t2))
      /\
      (forall n m, In (n, m) gs1.(g_messages) ->
         In (n, m) gs2.(g_messages) \/ node_received gs2 n m).

    (* Arming transfer, completeness direction: if node1 emits mu along a real
       node-1 run at inputs I, then the corresponding node2 (complete w.r.t. it,
       input-total and monotone') can_output mu from any of its runs whose inputs
       include I.  Mirrors xarm, but manufactures the node-2 run that feeds per-node
       completeness via input_total, then lifts it with monotone'. *)
    Lemma xarm' :
      (forall t, A t) ->
      forall (np2 : node_prog2) (init2 : node_state2),
        input_total (node_step2 np2) ->
        monotone' (node_step2 np2) A init2 ->
        forall (np1 : node_prog1) (init1 : node_state1),
          steps_corresp_complete A (node_step1 np1) init1 (node_step2 np2) init2 ->
          forall t1 ns1', star (node_step1 np1) init1 t1 ns1' ->
          forall mu, output_in_trace mu t1 ->
          forall ns2 t2, star (node_step2 np2) init2 t2 ns2 ->
            incl (inputs_of t1) (inputs_of t2) ->
            can_output (node_step2 np2) ns2 t2 mu.
    Proof.
      intros A_univ np2 init2 Hit2 Hmono2 np1 init1 Hcc t1 ns1' Hstar1 mu Hmu ns2 t2 Hstar2 Hincl.
      destruct (star_recv (node_step2 np2) Hit2 (inputs_of t1) init2)
        as (treq & ns_req & Hreq & Hinpreq).
      assert (Hprod1 : produces (node_step1 np1) init1 (inputs_of treq) mu).
      { rewrite Hinpreq. exists t1, ns1'.
        split; [exact Hstar1|]. split; [reflexivity | exact Hmu]. }
      pose proof (Hcc treq ns_req mu Hreq (allowed_trace_universal A A_univ treq) Hprod1)
        as Hcan_req.
      apply (Hmono2 treq t2 ns_req ns2 mu Hreq Hstar2
               (allowed_trace_universal A A_univ treq)
               (allowed_trace_universal A A_univ t2)).
      - rewrite Hinpreq. exact Hincl.
      - exact Hcan_req.
    Qed.

    (* xdom' composes with a graph-2 core_dom on the right (mirror of xdom_core_trans). *)
    Lemma xdom'_core_trans :
      forall (a : @graph_state node_state1 node_states1)
             (b c : @graph_state node_state2 node_states2),
        xdom' a b -> core_dom b c -> xdom' a c.
    Proof.
      intros a b c [Hab_n Hab_m] [Hbc_n Hbc_m]. split.
      - intros n ns1 t1 Hg. destruct (Hab_n n ns1 t1 Hg) as (nsb & tb & Hgb & Hinclb).
        destruct (Hbc_n n nsb tb Hgb) as (nsc & tc & Hgc & Hinclc).
        exists nsc, tc. split; [exact Hgc | eapply incl_tran; eassumption].
      - intros n m Hin. destruct (Hab_m n m Hin) as [Hq | Hr].
        + apply (Hbc_m n m Hq).
        + right. destruct Hr as (ns & t & Hg & Hinm).
          destruct (Hbc_n n ns t Hg) as (nsc & tc & Hgc & Hinclc).
          exists nsc, tc. split; [exact Hgc | apply Hinclc; exact Hinm].
    Qed.

    (* "graph 2 has absorbed all of [inps]": every external input message is queued
       or already delivered.  Established by the pure-input injection and preserved
       under any further graph-2 evolution (core_dom). *)
    Definition absorbed (inps : list (message * node_id))
                        (gs : @graph_state node_state2 node_states2) : Prop :=
      forall m n, In (m, n) inps -> In (n, m) gs.(g_messages) \/ node_received gs n m.

    Lemma absorbed_core_dom :
      forall inps (gsA gsB : @graph_state node_state2 node_states2),
        core_dom gsA gsB -> absorbed inps gsA -> absorbed inps gsB.
    Proof.
      intros inps gsA gsB [Hn Hm] Habs m n Hmn.
      destruct (Habs m n Hmn) as [Hq | Hr].
      - destruct (Hm n m Hq) as [Hq' | Hr']; [left; exact Hq' | right; exact Hr'].
      - right. destruct Hr as (ns & t & Hg & Hin).
        destruct (Hn n ns t Hg) as (nsB & tB & HgB & Hincl).
        exists nsB, tB. split; [exact HgB | apply Hincl; exact Hin].
    Qed.

    (* Cross-graph force_dominator, completeness direction: drive graph 2 (its own
       liveness) from a state dominating a graph-1 checkpoint gsC to one dominating
       gs_pre, where gsC reaches gs_pre by a graph-1 path that MAY contain inputs.
       Mirrors xforce_dominator with the graph roles swapped (arming graph-2 nodes
       via xarm' from graph 1's emissions, tracking xdom'); the new gstep_input case
       requires no graph-2 step because graph 2 has already absorbed all of [inps]. *)
    Lemma xforce_dominator' :
      (forall t, A t) ->
      (forall n np, map.get p2 n = Some np -> input_total (node_step2 np)) ->
      Forall2_map (fun _ np x => can_implies_will' (node_step2 np) A (fst x)) p2 initial_ns2 ->
      Forall4_map
        (fun _ np1 '(ns1, _) np2 '(ns2, _) =>
           steps_corresp_complete A (node_step1 np1) ns1 (node_step2 np2) ns2)
        p1 initial_ns1 p2 initial_ns2 ->
      forall inps,
      forall TC gsC gs_pre, star (graph_step p1 node_step1) gsC TC gs_pre ->
      incl (inputs_of TC) inps ->
      forall TC0, star (graph_step p1 node_step1) (initial_graph_state initial_ns1) TC0 gsC ->
      forall TX gsX, star (graph_step p2 node_step2) (initial_graph_state initial_ns2) TX gsX ->
      absorbed inps gsX ->
      xdom' gsC gsX ->
      forall t,
      eventually (can_step (graph_step p2 node_step2) Ag)
        (fun '(gs', _) => xdom' gs_pre gs') (gsX, t).
    Proof.
      intros A_univ Hit2 Hciw2 Hcorr inps TC gsC gs_pre Hstar.
      induction Hstar as [gC | gC e gC1 TC' gpre Hstep Hstar' IH];
        intros Hincl TC0 HC0 TX gsX HTX Habs Hdom t.
      - apply eventually_done. exact Hdom.
      - inversion Hstep as [ gs0 ni mi Hia
                           | gs0 ni npi nsi ti nsi' lbli outsi Hpi Hgi Hsi
                           | gs0 ni npi nsi ti nsi' mi msa msb Hpi Hgi Hsi Hmsg ]; subst.
        + (* gstep_input ni mi in graph 1: graph 2 stays put (input already absorbed) *)
          assert (Hincl' : incl (inputs_of TC') inps)
            by (intros x Hx; apply Hincl; cbn; right; exact Hx).
          assert (Hin_mn : In (mi, ni) inps) by (apply Hincl; cbn; left; reflexivity).
          assert (Hdom1 : xdom'
                    {| g_nodes := g_nodes gC; g_messages := (ni, mi) :: g_messages gC |} gsX).
          { destruct Hdom as [Hdom_n Hdom_m]. split.
            - intros nn nsA tA HgA. cbn in HgA. apply (Hdom_n nn nsA tA HgA).
            - intros nn mm Hin. cbn in Hin. destruct Hin as [Heq | Hin].
              + injection Heq as Hnn Hmm. subst nn mm. apply (Habs mi ni Hin_mn).
              + apply (Hdom_m nn mm Hin). }
          apply (IH Hincl' (TC0 ++ [I_event (mi, ni)])
                    (star_app _ _ _ _ _ _ HC0
                       (star_step _ _ _ _ _ _ Hstep (star_refl _ _)))
                    TX gsX HTX Habs Hdom1 t).
        + (* gstep_run ni in graph 1: drive graph 2's ni to emit the same outputs *)
          assert (Hincl' : incl (inputs_of TC') inps)
            by (intros x Hx; apply Hincl; cbn; exact Hx).
          destruct Hdom as [Hdom_n Hdom_m].
          destruct (Hdom_n ni nsi ti Hgi) as (nsX2i & tX2i & HgX2i & Hincli).
          destruct (corr_at_complete Hcorr ni npi Hpi) as (np2 & i1 & i2 & Hp2 & Hi1 & Hi2 & Hcc).
          destruct (node_run p1 initial_ns1 initial_ns1_empty node_step1 _ _ HC0
                      ni npi i1 nsi ti Hpi Hi1 Hgi) as (Hrun1 & _).
          destruct (node_run p2 initial_ns2 initial_ns2_empty node_step2 _ _ HTX
                      ni np2 i2 nsX2i tX2i Hp2 Hi2 HgX2i) as (Hrun2 & _).
          pose proof (proj2 (pernode_spec p2 initial_ns2 node_step2 Hciw2 ni np2 i2 Hp2 Hi2)) as Hmono2.
          assert (Hcan : forall mu, In mu outsi -> can_output (node_step2 np2) nsX2i tX2i mu).
          { intros mu Hmu.
            apply (xarm' A_univ np2 (fst i2) (Hit2 ni np2 Hp2) Hmono2 npi (fst i1) Hcc
                     (ti ++ [O_event lbli outsi]) nsi'
                     (star_app _ _ _ _ _ _ Hrun1 (star_step _ _ _ _ _ _ Hsi (star_refl _ _)))
                     mu
                     ltac:(apply output_in_trace_app; right; exists lbli, outsi;
                           split; [left; reflexivity | exact Hmu])
                     nsX2i tX2i Hrun2
                     ltac:(rewrite inputs_of_app; cbn; rewrite app_nil_r; exact Hincli)). }
          eapply eventually_trans.
          { apply (eventually_carry_inv p2 node_step2
                     (fun gs => exists T, star (graph_step p2 node_step2)
                                  (initial_graph_state initial_ns2) T gs)
                     ltac:(intros gs T gs' Hs (T0 & HT0); exists (T0 ++ T);
                           eapply star_app; eassumption)
                     _ gsX t (ex_intro _ TX HTX)
                     (force_emit_list p2 initial_ns2 initial_ns2_empty node_step2
                        A_univ Hciw2 outsi ni np2 Hp2 TX gsX HTX nsX2i tX2i HgX2i Hcan t)). }
          intros [gs' t'] ((HdomX' & Hfwds) & (TX' & HTX')).
          assert (Habs' : absorbed inps gs')
            by (apply (absorbed_core_dom inps gsX gs' HdomX' Habs)).
          assert (Hdom1 : xdom'
                    {| g_nodes := map.put (g_nodes gC) ni (nsi', ti ++ [O_event lbli outsi]);
                       g_messages := g_messages gC ++
                         flat_map (fun m => map (fun n' => (n', m)) (forward ni m)) outsi |}
                    gs').
          { pose proof (xdom'_core_trans _ _ _ (conj Hdom_n Hdom_m) HdomX') as [HdC_n HdC_m].
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
          apply (IH Hincl'
                    (TC0 ++ [O_event (run ni lbli) (map (fun m => (m, ni)) (filter (output_visible ni) outsi))])
                    (star_app _ _ _ _ _ _ HC0
                       (star_step _ _ _ _ _ _ Hstep (star_refl _ _)))
                    TX' gs' HTX' Habs' Hdom1 t').
        + (* gstep_receive ni mi in graph 1: drive graph 2 to deliver (ni,mi) too *)
          assert (Hincl' : incl (inputs_of TC') inps)
            by (intros x Hx; apply Hincl; cbn; exact Hx).
          destruct Hdom as [Hdom_n Hdom_m].
          destruct (Hdom_n ni nsi ti Hgi) as (nsX2i & tX2i & HgX2i & Hincli).
          destruct (corr_at_complete Hcorr ni npi Hpi) as (np2 & i1 & i2 & Hp2 & Hi1 & Hi2 & _).
          assert (Hcm : In (ni, mi) gsX.(g_messages) \/ node_received gsX ni mi).
          { apply Hdom_m. rewrite Hmsg. apply in_or_app. right. left. reflexivity. }
          eapply eventually_trans.
          { apply (eventually_carry_inv p2 node_step2
                     (fun gs => (exists T, star (graph_step p2 node_step2)
                                   (initial_graph_state initial_ns2) T gs)
                                /\ core_dom gsX gs)
                     ltac:(intros gs T gs' Hs [(T0 & HT0) Hd]; split;
                           [exists (T0 ++ T); eapply star_app; eassumption
                           | eapply core_dom_run; eassumption])
                     _ gsX t (conj (ex_intro _ TX HTX) (core_dom_refl gsX))
                     (force_deliver p2 initial_ns2 initial_ns2_empty node_step2
                        Hit2 TX gsX HTX ni mi np2 i2 Hp2 Hi2 Hcm t)). }
          intros [gs' t'] (Hrcv & (TX' & HTX') & HdomXg').
          assert (Habs' : absorbed inps gs')
            by (apply (absorbed_core_dom inps gsX gs' HdomXg' Habs)).
          assert (Hdom1 : xdom'
                    {| g_nodes := map.put (g_nodes gC) ni (nsi', ti ++ [I_event mi]);
                       g_messages := msa ++ msb |} gs').
          { assert (HdomCg' : xdom' gC gs')
              by (eapply xdom'_core_trans; [exact (conj Hdom_n Hdom_m) | exact HdomXg']).
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
          apply (IH Hincl' (TC0 ++ [O_event (receive ni mi) []])
                    (star_app _ _ _ _ _ _ HC0
                       (star_step _ _ _ _ _ _ Hstep (star_refl _ _)))
                    TX' gs' HTX' Habs' Hdom1 t').
    Qed.

    (* graph_emit_visible, graph-2 copy: if the angel can drive graph 2 to a state
       where node [on] can_output the visible message [omsg], then graph 2 will emit
       (omsg, on). *)
    Lemma graph_emit_visible2 :
      (forall t, A t) ->
      Forall2_map (fun _ np x => can_implies_will' (node_step2 np) A (fst x)) p2 initial_ns2 ->
      forall (on : node_id) (np2 : node_prog2) (i2 : node_state2 * list IO_event) (omsg : message),
        map.get p2 on = Some np2 ->
        map.get initial_ns2 on = Some i2 ->
        output_visible on omsg = true ->
        forall gs t,
          star (graph_step p2 node_step2) (initial_graph_state initial_ns2) t gs ->
          eventually (can_step (graph_step p2 node_step2) Ag)
            (fun '(gs', _) => exists ns t',
               map.get gs'.(g_nodes) on = Some (ns, t') /\
               can_output (node_step2 np2) ns t' omsg)
            (gs, t) ->
          will_output (graph_step p2 node_step2) Ag gs t (omsg, on).
    Proof.
      intros A_univ Hciw2 on np2 i2 omsg Hp2 Hi2 Hvis_o gs t Hstar Hev.
      unfold will_output.
      set (R := fun (g : @graph_state node_state2 node_states2) (tt : list gevent) =>
                  (exists T, star (graph_step p2 node_step2) (initial_graph_state initial_ns2) T g) /\
                  (forall ns tn, map.get g.(g_nodes) on = Some (ns, tn) ->
                     output_in_trace omsg tn -> output_in_trace (omsg, on) tt)).
      assert (HR_init : R gs t).
      { split; [exists t; exact Hstar|].
        intros ns tn Hg Hotn.
        destruct (node_run p2 initial_ns2 initial_ns2_empty node_step2 _ _ Hstar
                    on np2 i2 ns tn Hp2 Hi2 Hg) as (_ & Hpres).
        apply (Hpres omsg Hvis_o Hotn). }
      assert (Hstarp : forall g tt t_d s_d, R g tt ->
                star (graph_step p2 node_step2) g t_d s_d -> R s_d (t_d ++ tt)).
      { intros g tt t_d s_d [(Tg & HTg) Href] Hs. split.
        - exists (Tg ++ t_d). eapply star_app; eassumption.
        - intros ns tn Hgsd Hotn.
          destruct (project_node_gen p2 initial_ns2 initial_ns2_empty node_step2 _ _ HTg
                      on np2 i2 Hp2 Hi2) as (taug & nsg & _ & Hgg & _).
          destruct (node_drive_delta p2 node_step2 _ _ _ Hs on np2 nsg taug Hp2 Hgg)
            as (nsd & td & Hgd & _ & Hpresd).
          assert (tn = taug ++ td) by congruence. subst tn.
          apply output_in_trace_app in Hotn as [Ho | Ho].
          + apply output_in_trace_app. right. apply (Href nsg taug Hgg Ho).
          + apply output_in_trace_app. left. apply (Hpresd omsg Hvis_o Ho). }
      assert (Hostep : forall g tt glbl outs g', R g tt ->
                graph_step p2 node_step2 g (O_event glbl outs) g' -> R g' (O_event glbl outs :: tt)).
      { intros g tt glbl outs g' [(Tg & HTg) Href] Hstep'. split.
        - exists (Tg ++ [O_event glbl outs]).
          eapply star_app; [exact HTg | econstructor; [exact Hstep' | constructor]].
        - intros ns tn Hg' Hotn.
          inversion Hstep' as [ gs0 ni mi Hia
                             | gs0 ni npi nsi ti nsi' lbli outsi Hpi Hgi Hsi
                             | gs0 ni npi nsi ti nsi' mi msa msb Hpi Hgi Hsi Hmsg ]; subst.
          + cbn in Hg'. destruct (Nat.eq_dec on ni) as [->|Hne].
            * rewrite map.get_put_same in Hg'. injection Hg' as <- <-.
              apply output_in_trace_app in Hotn as [Ho | Ho].
              -- change (O_event (run ni lbli) (map (fun m => (m, ni)) (filter (output_visible ni) outsi)) :: tt)
                   with ([O_event (run ni lbli) (map (fun m => (m, ni)) (filter (output_visible ni) outsi))] ++ tt).
                 apply output_in_trace_app. right. apply (Href nsi ti Hgi Ho).
              -- destruct Ho as (lbo & os & [Heqo|[]] & Hino). injection Heqo as Hlbo Hos; subst os.
                 exists (run ni lbli), (map (fun m => (m, ni)) (filter (output_visible ni) outsi)).
                 split; [left; reflexivity|].
                 apply In_tag. apply filter_In. split; [exact Hino | exact Hvis_o].
            * rewrite map.get_put_diff in Hg' by auto.
              apply (Href ns tn Hg') in Hotn.
              change (O_event (run ni lbli) (map (fun m => (m, ni)) (filter (output_visible ni) outsi)) :: tt)
                with ([O_event (run ni lbli) (map (fun m => (m, ni)) (filter (output_visible ni) outsi))] ++ tt).
              apply output_in_trace_app. right. exact Hotn.
          + cbn in Hg'. destruct (Nat.eq_dec on ni) as [->|Hne].
            * rewrite map.get_put_same in Hg'. injection Hg' as <- <-.
              apply output_in_trace_app in Hotn as [Ho | Ho].
              -- change (O_event (receive ni mi) [] :: tt) with ([O_event (receive ni mi) []] ++ tt).
                 apply output_in_trace_app. right. apply (Href nsi ti Hgi Ho).
              -- destruct Ho as (lbo & os & [Heqo|[]] & _). discriminate Heqo.
            * rewrite map.get_put_diff in Hg' by auto.
              apply (Href ns tn Hg') in Hotn.
              change (O_event (receive ni mi) [] :: tt) with ([O_event (receive ni mi) []] ++ tt).
              apply output_in_trace_app. right. exact Hotn. }
      eapply eventually_trans.
      { apply (eventually_carry_inv2 p2 node_step2 R Hstarp Hostep _ gs t HR_init Hev). }
      intros [gsStar tStar] ((nsS & tS & HgS & HcanS) & (TStar & HTStar) & HRStar).
      pose proof (node_will p2 initial_ns2 initial_ns2_empty node_step2 A_univ Hciw2 on np2 Hp2
                    TStar gsStar nsS tS HTStar HgS omsg HcanS) as Hwillo.
      apply (drive_node_must p2 node_step2 A_univ np2 on omsg Hp2 Hvis_o (nsS, tS) Hwillo
               gsStar tStar (ex_intro _ tS HgS) (HRStar nsS tS HgS)).
    Qed.

    (* Membership plumbing for the input-queue: the pure-input run leaves the queue
       as the reversal-map of [inps], so every injected input is present. *)
    Lemma fold_pair_mono :
      forall (l : list (message * node_id)) (acc : list (node_id * message)) x,
        In x acc -> In x (fold_left (fun a '(m0, n0) => (n0, m0) :: a) l acc).
    Proof.
      induction l as [|[m1 n1] l IH]; intros acc x Hin; cbn;
        [exact Hin | apply IH; right; exact Hin].
    Qed.

    Lemma In_fold_pair :
      forall (l : list (message * node_id)) (acc : list (node_id * message)) m n,
        In (m, n) l -> In (n, m) (fold_left (fun a '(m0, n0) => (n0, m0) :: a) l acc).
    Proof.
      induction l as [|[m1 n1] l IH]; intros acc m n Hin; cbn in Hin |- *;
        [contradiction|].
      destruct Hin as [Heq | Hin].
      - injection Heq as <- <-. apply fold_pair_mono. left. reflexivity.
      - apply IH. exact Hin.
    Qed.

    (* Injecting [inps] into graph 2 leaves it with every input absorbed. *)
    Lemma absorbed_of_input_run :
      forall inps GS2,
        star (graph_step p2 node_step2) (initial_graph_state initial_ns2) (map I_event inps) GS2 ->
        absorbed inps GS2.
    Proof.
      intros inps GS2 Hstar2 m n Hmn.
      destruct (input_run_msgs p2 node_step2 initial_ns2 [] inps GS2 Hstar2)
        as (_ & HGS2m & _).
      left. rewrite HGS2m. apply In_fold_pair. exact Hmn.
    Qed.

    (* ===== The cross-graph completeness theorem (dual of graphs_corresp_sound) ===== *)
    Lemma graphs_corresp_complete' :
      (forall t, A t) ->
      (forall n np, map.get p2 n = Some np -> input_total (node_step2 np)) ->
      Forall2_map (fun _ np x => can_implies_will' (node_step2 np) A (fst x)) p2 initial_ns2 ->
      Forall4_map
        (fun _ np1 '(ns1, _) np2 '(ns2, _) =>
           steps_corresp_complete A (node_step1 np1) ns1 (node_step2 np2) ns2)
        p1 initial_ns1 p2 initial_ns2 ->
      steps_corresp_complete' Ag
        (graph_step p1 node_step1) (initial_graph_state initial_ns1)
        (graph_step p2 node_step2) (initial_graph_state initial_ns2).
    Proof.
      intros A_univ Hit2 Hciw2 Hcorr GS2 inps o Hstar2 Hag Hprod1.
      destruct o as (omsg, on).
      assert (Hallow2 : Smallstep.allowed_trace Ag (map I_event inps : list gevent)).
      { unfold Smallstep.allowed_trace. rewrite inputs_of_map_I_event. exact Hag. }
      (* the concrete graph-1 producer run, and the step inside it that emits o *)
      destruct Hprod1 as (W1 & GS1f & HW1 & HinpW1 & HoutW1).
      destruct (find_producing_step' p1 node_step1 _ _ _ HW1 omsg on HoutW1)
        as (T_pre & T_post & np_o & ns_o & ns_o' & t_o & outs_o & lbl_o & gs_pre1 & gs_post1
            & Heq_W1 & Hstar_pre1 & Hstep_prod & Hstar_post1 & Hp_o & Hg_o & Hns_o
            & Hino_o & Hvis_o).
      assert (HinclTpre : incl (inputs_of T_pre) inps).
      { intros x Hx. rewrite <- HinpW1, Heq_W1, inputs_of_app.
        apply in_or_app. left. exact Hx. }
      destruct (corr_at_complete Hcorr on np_o Hp_o) as (np2 & i1 & i2 & Hp2 & Hi1 & Hi2 & Hcc).
      (* graph 2 has absorbed all inputs, and trivially dominates the empty graph-1 init *)
      pose proof (absorbed_of_input_run inps GS2 Hstar2) as Habs.
      assert (Hxdom0 : xdom' (initial_graph_state initial_ns1) GS2).
      { destruct (input_run_msgs p2 node_step2 initial_ns2 [] inps GS2 Hstar2)
          as (HGS2n & _ & _).
        split.
        - intros n ns1 t1 Hg. cbn in Hg.
          pose proof (initial_ns1_empty n (ns1, t1) Hg) as Ht1. cbn in Ht1. subst t1.
          pose proof (Hcorr n) as Hc. rewrite Hg in Hc.
          destruct (map.get p1 n) as [np1'|] eqn:E1;
            destruct (map.get p2 n) as [np2'|] eqn:E3;
            destruct (map.get initial_ns2 n) as [i2'|] eqn:E4; cbn in Hc; try contradiction.
          pose proof (initial_ns2_empty n i2' E4) as Ht2. destruct i2' as [ns2' t2'].
          cbn in Ht2. subst t2'.
          exists ns2', []. rewrite HGS2n. split; [exact E4 | apply incl_refl].
        - intros n m Hin. cbn in Hin. contradiction. }
      (* drive graph 2 to dominate gs_pre1, then fire node on; gives will_output *)
      assert (Hwill2 : will_output (graph_step p2 node_step2) Ag GS2 (map I_event inps) (omsg, on)).
      { apply (graph_emit_visible2 A_univ Hciw2 on np2 i2 omsg Hp2 Hi2 Hvis_o
                 GS2 (map I_event inps) Hstar2).
        eapply eventually_trans.
        { apply (eventually_carry_inv p2 node_step2
                   (fun gs => exists T, star (graph_step p2 node_step2)
                                (initial_graph_state initial_ns2) T gs)
                   ltac:(intros gs T gs' Hs (T0 & HT0); exists (T0 ++ T);
                         eapply star_app; eassumption)
                   _ GS2 (map I_event inps) (ex_intro _ (map I_event inps) Hstar2)
                   (xforce_dominator' A_univ Hit2 Hciw2 Hcorr inps
                      T_pre (initial_graph_state initial_ns1) gs_pre1 Hstar_pre1 HinclTpre
                      [] (star_refl _ _)
                      (map I_event inps) GS2 Hstar2 Habs Hxdom0
                      (map I_event inps))). }
        intros [gsStar tStar] (Hdomstar & (TStar & HTStar)).
        apply eventually_done.
        destruct Hdomstar as [Hds_n _].
        destruct (Hds_n on ns_o t_o Hg_o) as (nsS & tS & HgS & HinclS).
        exists nsS, tS. split; [exact HgS|].
        destruct (node_run p1 initial_ns1 initial_ns1_empty node_step1 _ _ Hstar_pre1
                    on np_o i1 ns_o t_o Hp_o Hi1 Hg_o) as (Hrun1on & _).
        destruct (node_run p2 initial_ns2 initial_ns2_empty node_step2 _ _ HTStar
                    on np2 i2 nsS tS Hp2 Hi2 HgS) as (Hrun2on & _).
        apply (xarm' A_univ np2 (fst i2) (Hit2 on np2 Hp2)
                 (proj2 (pernode_spec p2 initial_ns2 node_step2 Hciw2 on np2 i2 Hp2 Hi2))
                 np_o (fst i1) Hcc
                 (t_o ++ [O_event lbl_o outs_o]) ns_o'
                 (star_app _ _ _ _ _ _ Hrun1on (star_step _ _ _ _ _ _ Hns_o (star_refl _ _)))
                 omsg
                 ltac:(apply output_in_trace_app; right; exists lbl_o, outs_o;
                       split; [left; reflexivity | exact Hino_o])
                 nsS tS Hrun2on
                 ltac:(rewrite inputs_of_app; cbn; rewrite app_nil_r; exact HinclS)). }
      apply (will_implies_can (graph_step p2 node_step2) Ag GS2 (map I_event inps)
               (omsg, on) Hallow2 Hwill2).
    Qed.
  End graphs.
End __.

Definition translate_event {L M M'} (t : M' -> M) (ev : IO_event L M') : IO_event L M :=
  match ev with
  | I_event m' => I_event (t m')
  | O_event l ms' => O_event l (map t ms')
  end.

Definition translate_step {NS L M M'} (t : M' -> M)
  (step : NS -> IO_event L M -> NS -> Prop)
  : NS -> IO_event L M' -> NS -> Prop :=
  fun ns ev ns' => step ns (translate_event t ev) ns'.
