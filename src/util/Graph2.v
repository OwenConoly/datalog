From coqutil Require Import Map.Interface.
From coqutil Require Import Map.Properties.
From coqutil Require Import Map.MapKeys.
From coqutil Require Import Semantics.OmniSmallstepCombinators.
From coqutil Require Import Eqb.
From Stdlib Require Import List PeanoNat Permutation Lia.
From Stdlib Require Import RelationClasses Morphisms Classical_Prop.
From Datalog Require Import OmniSmallstep Smallstep Map List Eqb.
From Datalog Require Import Tactics.
From coqutil Require Import Tactics Tactics.fwd.
Import ListNotations.
From Datalog Require Import Graph.

Print graph_step.

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
            forall n inputs P,
              npred_transf n inputs P ->
              forall (t : list (IO_event label message)) st,
                submultiset inputs (flat_map inputs_of t) ->
                star (node_step n) (init n) t st ->
                will_step (node_step n) (safe n) (st, t) (fun '(_, t') =>
                                                            P (flat_map outputs_of t'))).
  Context (input_guarantee : (list message -> Prop) -> Prop).
  Context (safe_input : list message -> Prop).

  Definition lpred_transf : location -> list message -> (list message -> Prop) -> Prop :=
    fun loc inps P =>
      match loc with
      | node_loc n => npred_transf n inps P
      | input_loc => input_guarantee P
      | output_loc => P inps
      end.

  Definition lsafe : location -> list message -> Prop. Admitted.

  Axiom all_locs : list location.

  Inductive graph_sat : location -> (list message -> Prop) -> Prop :=
  | step_sat loc P Pjs :
    (forall ojs,
        Forall2 (fun Pj oj => Pj oj) Pjs ojs ->
        lpred_transf loc (concat ojs) P) ->
    Forall2 graph_sat all_locs Pjs ->
    graph_sat loc P
  | base_sat loc P :
    (forall inps, lsafe loc inps -> lpred_transf loc inps P) ->
    graph_sat loc P
  | base_sat' loc P :
    P [] ->
    graph_sat loc P.

  Axiom init_graph : graph_state message label node_state.
  Lemma graph_sat_sound loc P :
    graph_sat loc P ->
    exists Pinp,
      input_guarantee Pinp /\
        forall inputs,
          Pinp inputs ->
          will_step graph_step safe_input (init_graph, []) (fun '(_, t) => P (flat_map outputs_of t)).
  Proof. Abort.

  Succeed Lemma true : True.
  Check graph_sat_ind.
  Check graph_step.
End __.
