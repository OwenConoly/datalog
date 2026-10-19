From coqutil Require Import Semantics.OmniSmallstepCombinators.
From Stdlib Require Import List Permutation.
From Datalog Require Import Smallstep Fin Function List.
From Datalog Require Import MessagelessSmallstep.
Import ListNotations.

Section __.
  Context (message label : Type) (num_nodes : nat) (node := fin num_nodes).
  Context (forward : node -> node -> message -> bool) (node_state : Type).
  Context (node_step : node -> node_state -> IO_event label message -> node_state -> Prop).
  Abbreviation nevent := (IO_event label message).
  Context (nodes_input_total : forall n, input_total (node_step n)).

  Context (npred_transf : node -> list message -> (list message -> Prop) -> Prop).
  Context (init : node -> node_state).
  Context (safe : node -> list message -> Prop).
  Context (safe_mono : forall n, multiset_monotone_dec (safe n)).
  Context (safe_nothing : forall n, safe n []).

  Definition inputs_of_outputs (outputs : node -> list message) destn :=
    flat_map (fun n => filter (forward n destn) (outputs n)) (fin.all _).

  Definition safe_inputs (n : node) (inps : list message) :=
    exists ojs,
      (forall n', safe n' (ojs n')) /\
        Permutation inps (inputs_of_outputs ojs n).

  Context (safe_preserved :
            forall n t st,
              star (node_step n) (init n) t st ->
              safe_inputs n (flat_map inputs_of t) ->
              safe n (flat_map outputs_of t)).

  Context (npred_transf_sound :
            forall n t P st,
              npred_transf n (flat_map inputs_of t) P ->
              star (node_step n) (init n) t st ->
              eventually (Smallstep.will_step (node_step n) (safe_inputs n)) (fun '(_, t') => P (flat_map outputs_of t')) (st, t)).

  Context (relevant : node -> (list message -> Prop) -> Prop).

  Context (npred_transf_complete :
            forall n t st P,
            star (node_step n) (init n) t st ->
            relevant n P ->
            P (flat_map outputs_of t) ->
            npred_transf n (flat_map inputs_of t) P).

  Definition suffices loc (Pjs : node -> list message -> Prop) P :=
    forall ojs,
      (forall n', Pjs n' (ojs n') /\ safe n' (ojs n')) ->
      npred_transf loc (inputs_of_outputs ojs loc) P.

  Context (relevant_preserved :
            forall n ojs P,
              relevant n P ->
              (forall n', safe n' (ojs n')) ->
              npred_transf n (inputs_of_outputs ojs n) P ->
              exists (Pjs : node -> (list message -> Prop)),
                (forall n', relevant n' (Pjs n') /\ Pjs n' (ojs n')) /\
                  suffices n Pjs P).

  Record graph_node_state :=
    { gns_node_state : node_state;
      gns_trace : list nevent;
      gns_queue : list message }.

  Definition enqueue inps gns :=
    {| gns_node_state := gns.(gns_node_state);
      gns_trace := gns.(gns_trace);
      gns_queue := inps ++ gns.(gns_queue) |}.

  Variant graph_label :=
    | receive (_ : node) (_ : message)
    | run (_ : node) (_ : label).

  Definition graph_state := node -> graph_node_state.

  Definition forward_to (keep : node -> message -> bool) (msgs : list message) (gs : graph_state) : graph_state :=
    fun n => enqueue (filter (keep n) msgs) (gs n).

  Definition gns_run n (ns : graph_node_state) (e : nevent) (ns' : graph_node_state) :=
    exists st',
      node_step n ns.(gns_node_state) e st' /\
        ns' = {| gns_node_state := st';
                gns_trace := e :: ns.(gns_trace);
                gns_queue := ns.(gns_queue) |}.

  Definition gns_receive n (ns : graph_node_state) m ns' :=
    exists ms1 ms2,
      ns.(gns_queue) = ms1 ++ m :: ms2 /\
        gns_run n {| gns_node_state := ns.(gns_node_state);
                    gns_trace := ns.(gns_trace);
                    gns_queue := ms1 ++ ms2 |} (I_event m) ns'.

  Variant graph_step : graph_state -> graph_label -> graph_state -> Prop :=
    | gstep_run n gs ns' lbl outs :
      gns_run n (gs n) (O_event lbl outs) ns' ->
      graph_step gs (run n lbl) (forward_to (forward n) outs (fun_put gs n ns'))
    | gstep_receive gs n m ns' :
      gns_receive n (gs n) m ns' ->
      graph_step gs (receive n m) (fun_put gs n ns').

  Definition outputs_at (gs : graph_state) n := flat_map outputs_of (gs n).(gns_trace).

  Definition inputs_at (gs : graph_state) n := flat_map inputs_of (gs n).(gns_trace).

  Inductive graph_sat : node -> (list message -> Prop) -> Prop :=
  | step_sat loc P Pjs :
    (forall n', graph_sat n' (Pjs n')) ->
    suffices loc Pjs P ->
    graph_sat loc P
  | top_sat loc :
    graph_sat loc (fun _ => True).

  Definition init_graph := fun n =>
    {| gns_node_state := init n;
      gns_trace := [];
      gns_queue := [] |}.

  Lemma outputs_are_inputs gs dst :
    inputs_of_outputs (outputs_at gs) dst = inputs_at gs dst.
  Proof. Admitted.

  Lemma step_sat_sound Pjs gs dst P :
    (forall src, Pjs src (outputs_at gs src)) ->
    npred_transf dst (inputs_of_outputs (outputs_at gs) dst) P ->
    eventually (will_step graph_step) (fun gs' => P (outputs_at gs' dst)) gs.
  Proof.
    intros HPjs Htrans.
    rewrite outputs_are_inputs in Htrans.
    eapply npred_transf_correct in Htrans. 2: admit.
    admit.
  Admitted.

  Lemma graph_sat_sound loc P :
    graph_sat loc P ->
    eventually (will_step graph_step) (fun gs => P (outputs_at gs loc)) init_graph.
  Proof. Admitted.

  Lemma graph_sat_complete P dst t gs :
    relevant dst P ->
    star (graph_step) init_graph t gs ->
    P (outputs_at gs dst) ->
    graph_sat dst P.
  Proof. Admitted.
End __.
