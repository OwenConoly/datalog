From coqutil Require Import Map.Interface.
From coqutil Require Import Map.Properties.
From coqutil Require Import Map.MapKeys.
From coqutil Require Import Semantics.OmniSmallstepCombinators.
From coqutil Require Import Eqb.
From Stdlib Require Import List PeanoNat Permutation Lia.
From Stdlib Require Import RelationClasses Morphisms Classical_Prop.
From Datalog Require Import OmniSmallstep Smallstep Map List Eqb Monadish Default.
From Datalog Require Import Tactics.
From coqutil Require Import Tactics Tactics.fwd.
Import ListNotations.
From Datalog Require Import Graph.

Open Scope option_monad_scope.

Section __.
  Context (message label : Type) (forward : source -> destn -> message -> bool) (node_state : Type).
  Context (node_step : node_id -> node_state -> IO_event label message -> node_state -> Prop).
  Context {blah : map.map nat (graph_node_state message label node_state)}.

  Abbreviation graph_step := (graph_step forward node_step).

  Context (npred_transf : node_id -> list message -> (list message -> Prop) -> Prop).
  (*TODO does this return False when input is non-monotone?  or what?*)
  Context (init : node_id -> node_state).
  Context (safe : node_id -> list message -> Prop).
  (*Axiom safe_valid : safe inputs to node -> safe outputs from node.  can be stated in terms of npred_transf?*)
  Context (npred_transf_correct :
            forall n t P st,
              npred_transf n (flat_map inputs_of t) P ->
              star (node_step n) (init n) t st ->
              eventually (will_step (node_step n) (safe n)) (fun '(_, t') => P (flat_map outputs_of t')) (st, t)).

  Context (relevant : location -> (list message -> Prop) -> Prop).
  Context (npred_transf_complete1 :
            forall n t st P,
            star (node_step n) (init n) t st ->
            relevant (node_loc n) P ->
            P (flat_map outputs_of t) ->
            npred_transf n (flat_map inputs_of t) P).

  Context (safe_input : list message -> Prop).

  Definition lpred_transf (inputs : list message) : location -> list message -> (list message -> Prop) -> Prop :=
    fun loc inps P =>
      match loc with
      | node_loc n => npred_transf n inps P
      | input_loc => P inputs
      | output_loc => P inps
      end.

  Definition lsafe : location -> list message -> Prop. Admitted.

  Axiom all_nodes : list node_id.

  Definition outputs_at (gs : graph_state message label node_state) (t : list (IO_event (graph_label message label) message)) loc :=
    match loc with
    | node_loc n =>
        '(Some ns) <- map.get gs.(graph_nodes) n ;;
        flat_map outputs_of ns.(gns_trace)
    | input_loc => flat_map inputs_of t
    | output_loc => flat_map outputs_of t
    end.

  (*assuming empty queues...*)
  Definition inputs_at (gs : graph_state message label node_state) (t : list (IO_event (graph_label message label) message)) dst :=
    match dst with
    | node_destn n =>
        '(Some ns) <- map.get gs.(graph_nodes) n ;;
        flat_map inputs_of ns.(gns_trace)
    | output_destn => flat_map outputs_of t
    end.

  Definition forward' (x y : location) :=
    match source_of_loc x, dest_of_loc y with
    | Some src, Some destn => forward src destn
    | _, _ => fun _ => false
    end.
  Definition all_locations := output_loc :: input_loc :: map node_loc all_nodes.

  Scheme All for Forall.
  Definition inputs_of_outputs (outputs : location -> list message) destn :=
    flat_map (fun loc => filter (forward' loc destn) (outputs loc)) all_locations.

  Context (npred_transf_complete2 :
            forall loc inps P,
              safe_input inps ->
              relevant loc P ->
              exists Pjs,
                Forall (fun src => relevant loc (Pjs src)) all_locations /\
                  forall ojs,
                    Forall (fun src => lsafe loc (ojs src)) all_locations ->
                    lpred_transf inps loc (inputs_of_outputs ojs loc) P ->
                    Forall (fun loc => Pjs loc (ojs loc)) all_locations).

  Inductive graph_sat (inputs : list message) : location -> (list message -> Prop) -> Prop :=
  | step_sat loc P Pjs :
    Forall (fun src => graph_sat _ src (Pjs src)) all_locations ->
    (forall ojs,
        Forall (fun src => Pjs src (ojs src) /\ lsafe loc (ojs src)) all_locations ->
        lpred_transf inputs loc (inputs_of_outputs ojs loc) P) ->
    graph_sat _ loc P
  | base_sat loc P :
    (forall inps, lsafe loc inps -> lpred_transf inputs loc inps P) ->
    graph_sat _ loc P.

  Lemma Forall_all_spec X Y (xs : list X) (ys : list Y) R R' idk :
    Forall_all _ R (fun x _ => R' x) xs idk ->
    Forall R' xs.
  Proof. induction 1; auto. Qed.

  Axiom init_graph : graph_state message label node_state.

  Lemma outputs_are_inputs gs t dst :
    inputs_of_outputs (outputs_at gs t) (loc_of_dest dst) = inputs_at gs t dst.
  Proof. Admitted.

  Lemma step_sat_sound Pjs gs t dst P :
    Forall (fun src => Pjs src (outputs_at gs t src)) all_locations ->
    lpred_transf (flat_map inputs_of t) dst (inputs_of_outputs (outputs_at gs t) dst) P ->
    eventually (will_step graph_step safe_input) (fun '(gs', t') => P (outputs_at gs' t' dst)) (gs, t).
  Proof.
    intros HPjs Htrans. destruct dst as [n| |]; cycle 1.
    - cbn -[will_step]. simpl in Htrans. cbv [will_step]. apply eventually_done. assumption.
    - simpl in Htrans. cbn -[will_step]. rewrite outputs_are_inputs with (dst := output_destn) in Htrans.
      simpl in Htrans. apply eventually_done. assumption.
    - rewrite outputs_are_inputs with (dst := node_destn n) in Htrans. simpl in Htrans.
      assert (exists ns, map.get gs.(graph_nodes) n = Some ns) as [foot Hfoot]. { admit. }
      rewrite Hfoot in Htrans. eapply npred_transf_correct in Htrans. 2: admit.
      admit.
  Admitted.

  Lemma graph_sat_sound t loc P :
    graph_sat (flat_map inputs_of t) loc P ->
    eventually (will_step graph_step safe_input) (fun '(gs, t') => P (outputs_at gs t' loc)) (init_graph, t).
  Proof. Admitted.

  Lemma graph_sat_complete P dst t gs :
    relevant dst P ->
    star (graph_step) init_graph t gs ->
    P (outputs_at gs t dst) ->
    graph_sat (flat_map inputs_of t) dst P.
  Proof. Admitted.
End __.
