From coqutil Require Import Map.Interface.
From coqutil Require Import Semantics.OmniSmallstepCombinators.
From Stdlib Require Import List PeanoNat Permutation.
From Stdlib Require Import RelationClasses.
From Datalog Require Import Smallstep Map.
Import ListNotations.

Definition node_id := nat.
Section __.
  Context {message : Type}.
  Context {label : Type}.
  Context (input_allowed : node_id -> message -> bool).
  Context (forward : node_id -> message -> list node_id).
  (* A message is forwarded to a given node at most once per emission. *)
  Context (forward_nodup : forall n m, NoDup (forward n m)).
  Context (output_visible : node_id -> message -> bool).

  Context (equiv : message -> message -> Prop).
  Context (equiv_equiv : Equivalence equiv).
  Context (output_visible_equiv :
             forall n a b, equiv a b -> output_visible n a = output_visible n b).
  (* Forwarding cannot distinguish [equiv]-related messages: a forced re-emission
     produces [mu' ~ mu] and must reach the same consumers as [mu]. *)
  Context (forward_equiv :
             forall n a b, equiv a b -> forward n a = forward n b).
  Context (well_formed_output : node_id -> list message -> Prop).
  Context {constraint} (well_formed : constraint -> list message -> Prop).
  Context (well_formed_inputs : constraint -> list message -> Prop).

  Local Notation IO_event := (Smallstep.IO_event label message).

  Variant graph_label :=
    | receive (_ : node_id) (_ : message)
    | run (_ : node_id) (_ : label).

  Definition well_formed_graph_inputs (c : constraint) (inps : list (message * node_id)) :=
    forall n, well_formed_inputs c (map fst (filter (fun '(_, n') => Nat.eqb n n') inps)).

  Local Notation gevent := (Smallstep.IO_event graph_label (message * node_id)).

  Definition equiv_g : message * node_id -> message * node_id -> Prop :=
    fun '(m1, n1) '(m2, n2) => n1 = n2 /\ equiv m1 m2.

  Definition well_formed_good :=
    forall nodes fss,
      NoDup nodes ->
      Forall2 well_formed_output nodes fss ->
      forall c inps,
        well_formed c (concat fss ++ inps) <-> well_formed_inputs c inps.

  Context (Hwfg : well_formed_good).

  Context (well_formed_monotone :
    forall c l1 l2, allowed well_formed l1 -> allowed well_formed l2 ->
                    submultiset l1 l2 -> well_formed c l1 -> well_formed c l2).

  Section graph.
    Context {node_prog : Type} {graph_prog : map.map node_id node_prog}.
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

  Section graph.
    Context {node_prog : Type} {graph_prog : map.map node_id node_prog}.
    Context {node_state : Type}
            {node_states : map.map node_id (node_state * list IO_event)}.
    Context {node_states_ok : map.ok node_states}.
    Context (p : graph_prog) (initial_ns : node_states).
    Context (initial_ns_empty :
               forall n x, map.get initial_ns n = Some x -> snd x = []).
    Context (node_step : node_prog -> node_state -> IO_event -> node_state -> Prop).
    Context (p_initial_dom :
               forall n np, map.get p n = Some np -> exists x, map.get initial_ns n = Some x).
    Context (nodes_input_total :
               forall n np, map.get p n = Some np -> input_total (node_step np)).

    Definition initial_graph_state : graph_state :=
      {| g_nodes := initial_ns; g_messages := [] |}.

    Local Notation gstep := (graph_step p node_step).

    Definition node_good (n : node_id) (np : node_prog) : node_state * list IO_event -> Prop :=
      fun '(ns, _) =>
        outputs_well_formed    (node_step np)       (fun (_ : unit) => well_formed_output n) ns /\
        monotone_mod_equiv     (node_step np) equiv well_formed ns /\
        can_implies_will_equiv (node_step np) equiv well_formed ns.
    Ltac inv_gstep H :=
      inversion H as [ gs0 ni mi Hia
                     | gs0 ni npi nsi ti nsi' lbli outsi Hpi Hgi Hsi
                     | gs0 ni npi nsi ti nsi' mi msa msb Hpi Hgi Hsi Hmsg ].

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
                       In o (outputs_of td) -> In (o, n) (outputs_of T)).
    Proof.
      intros T gs0 gs Hstar.
      induction Hstar as [s|s e s' t0 s'' Hstep Hstar IH];
        intros n np ns t Hp Hg0.
      - exists ns, []. rewrite app_nil_r. split; [exact Hg0|]. split; [constructor|].
        intros o _ Hout. cbn in Hout. contradiction.
      - inv_gstep Hstep; subst.
        + destruct (IH n np ns t Hp Hg0) as (ns' & td & Hg & Hstd & Hpres).
          exists ns', td. split; [exact Hg|]. split; [exact Hstd|].
          intros o Hvis Hout. exact (Hpres o Hvis Hout).
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
            intros o Hvis Hout.
            apply in_app_or in Hout as [Hhead | Hrest].
            -- apply in_or_app. left.
               apply In_tag. apply filter_In. split; [exact Hhead|exact Hvis].
            -- apply in_or_app. right. exact (Hpres o Hvis Hrest).
          * destruct (IH n np ns t Hp) as (ns' & td & Hg & Hstd & Hpres).
            { cbn. rewrite map.get_put_diff by auto. exact Hg0. }
            exists ns', td. split; [exact Hg|]. split; [exact Hstd|].
            intros o Hvis Hout. specialize (Hpres o Hvis Hout).
            apply in_or_app. right. exact Hpres.
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
            intros o Hvis Hout.
            exact (Hpres o Hvis Hout).
          * destruct (IH n np ns t Hp) as (ns' & td & Hg & Hstd & Hpres).
            { cbn. rewrite map.get_put_diff by auto. exact Hg0. }
            exists ns', td. split; [exact Hg|]. split; [exact Hstd|].
            intros o Hvis Hout. exact (Hpres o Hvis Hout).
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
                       In o (outputs_of tau) -> In (o, n) (outputs_of T)).
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
                   In o (outputs_of t) -> In (o, n) (outputs_of T)).
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

    (* Helper: find the producing step inside an angel's path. *)
    Lemma find_producing_step :
      forall (gs_start : graph_state) (T : list gevent) (s_f : graph_state),
        star gstep gs_start T s_f ->
        inputs_of T = [] ->
        forall (o : message) (n_o : node_id),
          In (o, n_o) (outputs_of T) ->
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
      - cbn in Hout. contradiction.
      - cbn in Hinp. destruct e as [m|lbl_e outs_e]; [discriminate|]. cbn in Hinp.
        
        apply in_app_or in Hout as [Hino0|Hout_rest].
        + (* o is in the head event *)
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
          In (o, n_o) (outputs_of T) ->
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
      - cbn in Hout. contradiction.
      - destruct e as [m | lbl_e outs_e].
        + (* I_event m: the output cannot live in an input event; recurse. *)
          assert (Hout' : In (o, n_o) (outputs_of t0))
            by (exact Hout).
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
        + 
          apply in_app_or in Hout as [Hino0|Hout_rest].
          * inversion Hstep as [
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
        forall mu n', In mu (outputs_of t) -> In n' (forward n mu) ->
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
          apply outputs_of_in_app in Hout as [Hout_old | Hout_new].
          * destruct (Hsat ni npi nsi ti Hpi Hgi mu n' Hout_old Hfwd) as [Hq | Hr].
            -- left. cbn. apply in_or_app. left. exact Hq.
            -- right. apply Hmono1. exact Hr.
          * 
            apply in_app_or in Hout_new as [Hino0 | Hcontra];
              [|cbn in Hcontra; contradiction].
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
          assert (Hout_ti : In mu (outputs_of ti)).
          { apply outputs_of_in_app in Hout as [H|H]; [exact H|].
            cbn in H. contradiction. }
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
      cbn in Hout. contradiction.
    Qed.

    (* Read the three [node_good] obligations off the per-node hypothesis at a
       node's bare initial state. *)
    Lemma pernode_spec_good :
      Forall2_map node_good p initial_ns ->
      forall n np ns0,
        map.get p n = Some np ->
        map.get initial_ns n = Some ns0 ->
        outputs_well_formed    (node_step np) (fun (_ : unit) => well_formed_output n) (fst ns0) /\
        monotone_mod_equiv     (node_step np) equiv well_formed (fst ns0) /\
        can_implies_will_equiv (node_step np) equiv well_formed (fst ns0).
    Proof.
      intros Hgood n np ns0 Hp Hns0.
      pose proof (Hgood n) as Hn. rewrite Hp, Hns0 in Hn.
      destruct ns0 as [ns tr]. exact Hn.
    Qed.
    Lemma sub_nil (l : list message) : submultiset [] l.
    Proof. exists l. reflexivity. Qed.

    Lemma sub_cons (x : message) (a b : list message) :
      submultiset a b -> submultiset (x :: a) (x :: b).
    Proof. intros (rest & Hp). exists rest. cbn. apply perm_skip. exact Hp. Qed.

    Lemma sub_app_r (a b c : list message) :
      submultiset a b -> submultiset a (b ++ c).
    Proof.
      intros (rest & Hp). exists (rest ++ c).
      rewrite app_assoc. apply Permutation_app_tail. exact Hp.
    Qed.

    Lemma sub_app_mono (a1 b1 a2 b2 : list message) :
      submultiset a1 b1 -> submultiset a2 b2 -> submultiset (a1 ++ a2) (b1 ++ b2).
    Proof.
      intros (r1 & H1) (r2 & H2). exists (r1 ++ r2).
      eapply perm_trans; [apply Permutation_app; eassumption|].
      rewrite <- !app_assoc. apply Permutation_app_head.
      rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
    Qed.

    Lemma sub_trans (a b c : list message) :
      submultiset a b -> submultiset b c -> submultiset a c.
    Proof.
      intros (r1 & H1) (r2 & H2). exists (r1 ++ r2).
      eapply perm_trans; [exact H2|].
      eapply perm_trans; [apply Permutation_app_tail; exact H1|].
      rewrite <- app_assoc. reflexivity.
    Qed.

    Lemma sub_perm_r (a b b' : list message) :
      Permutation b b' -> submultiset a b -> submultiset a b'.
    Proof. intros Hp (rest & H). exists rest. eapply perm_trans; [symmetry; exact Hp | exact H]. Qed.

    Lemma sub_perm_l (a a' b : list message) :
      Permutation a a' -> submultiset a b -> submultiset a' b.
    Proof. intros Hp (rest & H). exists rest. eapply perm_trans; [exact H | apply Permutation_app_tail; exact Hp]. Qed.

    Lemma sub_perm_both (a a' b b' : list message) :
      Permutation a a' -> Permutation b b' -> submultiset a b -> submultiset a' b'.
    Proof.
      intros Ha Hb H. apply (sub_perm_r a' b b' Hb). apply (sub_perm_l a a' b Ha). exact H.
    Qed.

    Lemma perm_mid_move (X Y Z : list message) (b : message) :
      Permutation (X ++ (Y ++ b :: Z)) ((X ++ [b]) ++ (Y ++ Z)).
    Proof.
      rewrite <- (app_assoc X [b] (Y ++ Z)). apply Permutation_app_head.
      symmetry. apply Permutation_cons_app. apply Permutation_refl.
    Qed.

    Lemma sub_map_fst {B} (a b : list (message * B)) :
      submultiset a b -> submultiset (map fst a) (map fst b).
    Proof.
      intros (rest & H). exists (map fst rest).
      rewrite <- map_app. apply Permutation_map. exact H.
    Qed.

    Lemma flat_map_sub (g : message -> list message) (l : list message) :
      (forall a, submultiset (g a) [a]) -> submultiset (flat_map g l) l.
    Proof.
      intro Hg. induction l as [|a l IH]; [apply sub_nil|].
      cbn. change (a :: l) with ([a] ++ l). apply sub_app_mono; [apply Hg | exact IH].
    Qed.

    Lemma filter_flat_map {X Y} (q : Y -> bool) (ff : X -> list Y) (l : list X) :
      filter q (flat_map ff l) = flat_map (fun x => filter q (ff x)) l.
    Proof.
      induction l as [|a l IH]; [reflexivity|]. cbn. rewrite filter_app, IH. reflexivity.
    Qed.

    Lemma map_flat_map {X Y Z} (g : Y -> Z) (ff : X -> list Y) (l : list X) :
      map g (flat_map ff l) = flat_map (fun x => map g (ff x)) l.
    Proof.
      induction l as [|a l IH]; [reflexivity|]. cbn. rewrite map_app, IH. reflexivity.
    Qed.

    Lemma filter_tag_nil (nn : node_id) (m0 : message) (L : list node_id) :
      ~ In nn L ->
      filter (fun de => Nat.eqb (fst de) nn) (map (fun n' => (n', m0)) L) = [].
    Proof.
      induction L as [|a L IH]; [reflexivity|]. cbn. intro Hni.
      destruct (Nat.eqb a nn) eqn:E.
      - apply Nat.eqb_eq in E; subst a. exfalso. apply Hni. left. reflexivity.
      - apply IH. intro; apply Hni; right; assumption.
    Qed.

    Lemma forwarded_one_sub (ni nn : node_id) (m0 : message) :
      submultiset (map snd (filter (fun de => Nat.eqb (fst de) nn)
                                   (map (fun n' => (n', m0)) (forward ni m0)))) [m0].
    Proof.
      pose proof (forward_nodup ni m0) as Hnd. induction (forward ni m0) as [|a L IH].
      - apply sub_nil.
      - cbn. destruct (Nat.eqb a nn) eqn:E.
        + apply Nat.eqb_eq in E; subst a. inversion Hnd; subst.
          rewrite filter_tag_nil by assumption. cbn. apply submultiset_refl.
        + apply IH. inversion Hnd; subst; assumption.
    Qed.

    Lemma forwarded_sub (ni nn : node_id) (outsi : list message) :
      submultiset
        (map snd (filter (fun de => Nat.eqb (fst de) nn)
           (flat_map (fun m0 => map (fun n' => (n', m0)) (forward ni m0)) outsi)))
        outsi.
    Proof.
      rewrite filter_flat_map, map_flat_map. apply flat_map_sub.
      intro a. apply forwarded_one_sub.
    Qed.

    Lemma graph_can_implies_will_equiv :
      Forall2_map node_good p initial_ns ->
      can_implies_will_equiv (graph_step p node_step) equiv_g well_formed_graph_inputs
                             initial_graph_state.
    Admitted.
  End graph.

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
