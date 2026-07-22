From Stdlib Require Import List PeanoNat.
From Datalog Require Import Datalog Node Operational Smallstep.
From coqutil Require Import Map.Interface Datatypes.List.
Import ListNotations.

Section __.
  Context {rel : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map exprvar T}.
  Context (is_input : rel -> bool).
  Context (R_senders : rel -> list nat).
  Context (p : prog).

  Local Notation IO_event := (Smallstep.IO_event unit dfact).

  Inductive step : state -> IO_event -> state -> Prop :=
  | step_comp s1 s2 :
    comp_step is_input p s1 s2 ->
    step s1 (O_event tt []) s2
  | step_input s f :
    step s (I_event f) (map (add_waiting_fact f) s)
  | step_output s f :
    knows_dfact s f ->
    step s (O_event tt [f]) s.

  Definition empty_rule_state : Operational.node_state :=
    {| known_facts := []; waiting_facts := []; sent_facts := [] |}.

  Definition initial : state := repeat empty_rule_state (length p.(non_meta_rules)).
End __.
