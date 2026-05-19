From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import Classical_Prop.
From Stdlib Require Import Relations.Relation_Operators Relations.Operators_Properties.

From Datalog Require Import Map Tactics Fp List Dag Datalog Operational.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List Datatypes.Option.

Import ListNotations.

Section __.
  Context {rel lrel var fn aggregator T : Type}.
  Context `{sig : signature fn aggregator T}.
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

  Inductive spec_node_step : spec_node_state -> spec_node_state -> Prop :=
  (*TODO*).

  Record local_rel_info :=
    { num_inputs : nat;
      num_outputs : nat;
      track_sent : bool;
      track_received : bool;
      agg_ops : list aggregator; }.

  Context {local_rels_info : map.map lrel local_rel_info} {local_rels_info_ok : map.ok local_rels_info}.

  Inductive local_clause :=
  |

  Record node_prog :=
    { output_corresp : lrel_to_rel;
      input_corresp : rel_to_lrel;
      local_rels : local_rels_info;
    }.


  Inductive lrule :=
  |
