From coqutil Require Import Map.Interface.
From coqutil Require Import Map.Properties.
From coqutil Require Import Map.MapKeys.
From coqutil Require Import Semantics.OmniSmallstepCombinators.
From coqutil Require Import Eqb.
From Stdlib Require Import List PeanoNat Permutation Lia.
From Stdlib Require Import RelationClasses Morphisms Classical_Prop.
From Datalog Require Import OmniSmallstep Smallstep Map List Eqb Monadish Default.
From Datalog Require Import Tactics Fin Function.
From Datalog Require Import MessagelessSmallstep.
From coqutil Require Import Tactics Tactics.fwd.
Import ListNotations.

Open Scope option_monad_scope.

Section __.
  Context (message label : Type) (num_nodes : nat) (node := fin num_nodes).
  Context (forward : node -> node -> message -> bool) (node_state : Type).
  Context (node_step : node -> node_state -> IO_event label message -> node_state -> Prop).
  Abbreviation nevent := (IO_event label message).

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
    | run (_ : node) (_ : label)
    | emit (_ : message).

  Definition graph_state := node -> graph_node_state.

  Definition forward_to (keep : node -> message -> bool) (msgs : list message) (gs : graph_state) : graph_state :=
    fun n => enqueue (filter (keep n) msgs) (gs n).

  Definition gns_run n (ns : graph_node_state) (e : nevent) (ns' : graph_node_state) :=
    exists st',
      node_step n ns.(gns_node_state) e st' /\
        ns' = {| gns_node_state := st';
                gns_trace := e :: ns.(gns_trace);
                gns_queue := ns.(gns_queue) |}.

  Definition gns_receive (n : node) (ns : graph_node_state) (m : message) (ns' : graph_node_state) :=
    exists st' ms1 ms2,
      node_step n ns.(gns_node_state) (I_event m) st' /\
        ns.(gns_queue) = ms1 ++ m :: ms2 /\
        ns' = {| gns_node_state := st';
                gns_trace := I_event m :: ns.(gns_trace);
                gns_queue := ms1 ++ ms2 |}.

  Variant graph_step : graph_state -> graph_label -> graph_state -> Prop :=
    | gstep_run n gs ns' lbl outs :
      gns_run n (gs n) (O_event lbl outs) ns' ->
      graph_step gs (run n lbl) (forward_to (forward n) outs (fun_put gs n ns'))
    | gstep_receive gs n ns m ns' :
      gns_receive n ns m ns' ->
      graph_step gs (receive n m) (fun_put gs n ns').

  Context (npred_transf : node -> list message -> (list message -> Prop) -> Prop).
  (*TODO does this return False when input is non-monotone?  or what?*)
  Context (init : node -> node_state).
  Context (safe : node -> list message -> Prop).
  (*Axiom safe_valid : safe inputs to node -> safe outputs from node.  can be stated in terms of npred_transf?*)
  Context (npred_transf_correct :
            forall n t P st,
              npred_transf n (flat_map inputs_of t) P ->
              star (node_step n) (init n) t st ->
              eventually (Smallstep.will_step (node_step n) (safe n)) (fun '(_, t') => P (flat_map outputs_of t')) (st, t)).

  Context (relevant : node -> (list message -> Prop) -> Prop).
  Context (npred_transf_complete1 :
            forall n t st P,
            star (node_step n) (init n) t st ->
            relevant n P ->
            P (flat_map outputs_of t) ->
            npred_transf n (flat_map inputs_of t) P).

  Definition outputs_at (gs : graph_state) n := flat_map outputs_of (gs n).(gns_trace).

  Definition inputs_at (gs : graph_state) n := flat_map inputs_of (gs n).(gns_trace).

  Scheme All for Forall.
  Definition inputs_of_outputs (outputs : node -> list message) destn :=
    flat_map (fun n => filter (forward n destn) (outputs n)) (fin.all _).

  Context (npred_transf_complete2 :
            forall n P,
              relevant n P ->
              exists (Pjs : node -> (list message -> Prop)),
                (forall n', relevant n (Pjs n')) /\
                  forall ojs,
                    (forall n', safe n' (ojs n')) ->
                    npred_transf n (inputs_of_outputs ojs n) P ->
                    (forall n', Pjs n' (ojs n'))).

  Inductive graph_sat : node -> (list message -> Prop) -> Prop :=
  | step_sat loc P Pjs :
    (forall n', graph_sat n' (Pjs n')) ->
    (forall ojs,
        (forall n', Pjs n' (ojs n') /\ safe n' (ojs n'))  ->
        npred_transf loc (inputs_of_outputs ojs loc) P) ->
    graph_sat loc P
  | base_sat loc P :
    (forall inps, safe loc inps -> npred_transf loc inps P) ->
    graph_sat loc P.

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
