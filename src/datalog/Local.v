From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import Classical_Prop.
From Stdlib Require Import Relations.Relation_Operators Relations.Operators_Properties.

From Datalog Require Import Map Tactics Fp List Dag Datalog Operational Interpreter.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List Datatypes.Option.

Import ListNotations.

Section __.
  Context {rel lrel var fn aggregator T : Type}.
  Context `{sig : signature fn aggregator T}.
  Context {T_eqb : T -> T -> bool}.
  Context {context : map.map var T} {context_ok : map.ok context}.
  Context {lrel_to_rel : map.map lrel rel} {lrel_to_rel_ok : map.ok lrel_to_rel}.
  Context {rel_to_lrel : map.map rel lrel} {rel_to_lrel_ok : map.ok rel_to_lrel}.

  Local Notation clause := (clause rel var fn).
  Local Notation meta_clause := (meta_clause rel var fn).
  Local Notation fact := (fact rel T).
  Local Notation expr := (expr var fn).
  Local Notation rule := (rule rel var fn aggregator).
  Local Notation non_meta_rule := (non_meta_rule rel var fn aggregator).
  Local Notation dfact := (dfact rel T).
  Local Notation prog := (prog rel var fn aggregator).

  Implicit Types known_facts sent_facts waiting_facts input_facts inputs : list dfact.
  Implicit Types nf result : dfact.
  Implicit Types p : prog.
  Implicit Types r : non_meta_rule.
  Implicit Types mf_rel : rel.
  Implicit Types mf_args : list (option T).
  Implicit Types nf_args : list T.

  Record spec_node_state :=
    { known_facts : list dfact;
      sent_facts : list dfact }.

  Definition spec_node_prog :=
    list rule.

  Definition spec_node_step (p : list rule) : spec_node_state -> spec_node_state -> Prop. Admitted.

  Record local_rel_info :=
    { num_inputs : nat;
      num_outputs : nat;
      track_sent : bool;
      track_received : bool;
      agg_ops : list aggregator; }.

  Context {local_rels_info : map.map lrel local_rel_info} {local_rels_info_ok : map.ok local_rels_info}.

  Inductive local_hyp_clause :=
  | outputs_hyp  (name : lrel) (inputs : list expr) (outputs : list expr)
  | agg_hyp      (name : lrel) (inputs : list expr) (agg : aggregator) (num : var)
  | received_hyp (name : lrel) (inputs : list expr) (num : var)
  | sent_hyp     (name : lrel) (inputs : list expr) (num : var).

  Inductive local_fact :=
  | outputs_fact (name : lrel) (inputs : list T) (outputs : list T)
  | agg_fact (name : lrel) (inputs : list T) (agg : aggregator) (num : T)
  | received_fact (name : lrel) (inputs : list T) (num : nat)
  | sent_fact (name : lrel) (inputs : list T) (num : nat).

  Record local_concl :=
    { local_concl_name : lrel;
      local_concl_inputs : list expr;
      local_concl_outputs : list expr }.

  Record local_rule :=
    { local_rule_concls : list local_concl;
      local_rule_hyps : list local_hyp_clause }.

  Record node_prog :=
    { output_corresp : lrel_to_rel;
      input_corresp : rel_to_lrel;
      local_rels : local_rels_info;
      rules : list local_rule }.

  Context {outputs_set : map.map (list T) unit}.
  Context {agg_to_T : map.map aggregator T}.

  Record inputs_data :=
    { msgs_received : nat;
      msgs_sent : nat;
      aggs : agg_to_T;
      outputs : outputs_set }.

  Context {inputs_to_data : map.map (list T) inputs_data}.
  Context {lrel_to_all_inputs_data : map.map lrel inputs_to_data}.

  Definition node_state :=
    lrel_to_all_inputs_data.

  Definition inputs_of (f : local_fact) : lrel * list T :=
    match f with
    | outputs_fact name inputs _
    | agg_fact name inputs _ _
    | received_fact name inputs _
    | sent_fact name inputs _ => (name, inputs)
    end.

  Definition inputs_data_of (s : node_state) (name_inputs : lrel * list T) : option inputs_data :=
    let (name, inputs) := name_inputs in
    match map.get s name with
    | Some inp_datas => map.get inp_datas inputs
    | None => None
    end.

  Definition knows_local_fact (s : node_state) (f : local_fact) :=
    match inputs_data_of s (inputs_of f) with
    | Some inp_data =>
        match f with
        | outputs_fact _ _ output =>
            set_contains inp_data.(outputs) output
        | agg_fact _ _ agg val =>
            map_contains (value_eqb := T_eqb) inp_data.(aggs) agg val
        | received_fact _ _ val =>
            Nat.eqb inp_data.(msgs_received) val
        | sent_fact _ _ val =>
            Nat.eqb inp_data.(msgs_sent) val
        end
    | None => false
    end.

  Definition eval_local_hyp_clause (c : context) (h : local_hyp_clause) :=
    match h with
    | outputs_hyp name inputs outputs =>
        match option_all (map (subst_in_expr c) inputs), option_all (map (subst_in_expr c) outputs) with
        |
        outputs_fact name (map

  Definition local_hyps_match (hs : list local_hyp)

  Definition node_step_rule (p : node_prog) (r : rule) (s : node_state) : node_state :=
    match

  Definition node_comp_step (p : node_prog) (s : node_state) : node_state :=
