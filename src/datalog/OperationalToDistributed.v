From Stdlib Require Import List Permutation.
From Datalog Require Import Datalog Node Operational Smallstep Graph List Distributed Map.
From coqutil Require Import Map.Interface Eqb.
From coqutil Require Import Semantics.OmniSmallstepCombinators.
Import ListNotations.

Section __.
  Context {rel : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context {rel_eqb : Eqb rel} {rel_eqb_ok : Eqb_ok rel_eqb}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.
  Context (is_input : rel -> bool).
  Context (p : prog).
  Context (Hp_input : Forall (good_non_meta_rule is_input) p.(non_meta_rules)).
  Context (Hmeta_rules : meta_rules_valid (rules_of p)).
  Context (Hp_meta_input : Forall (good_meta_rule_inputs is_input) p.(meta_rules)).

  Context {gns_map : map.map node_id (graph_node_state dfact dfact_mod_count Node.node_state)}.
  Context {gns_map_ok : map.ok gns_map}.

  Context (rel_forward : source -> destn -> rel -> bool).
  Context {prog_map : map.map node_id (list rule)} {prog_map_ok : map.ok prog_map}.
  Context (graph_prog : prog_map).

  Local Notation R_senders := (Operational.R_senders is_input p).
  Local Notation ok_to_deduce_fact := (Node.ok_to_deduce_fact R_senders).
  Local Notation new_facts := (Node.new_facts R_senders).
  Local Notation fire_at_rule := (Operational.fire_at_rule is_input p).

  Context (graph_senders : rel -> list source).

  Local Notation distributed_step := (distributed_step graph_senders rel_forward graph_prog).
  Local Notation start := (Operational.start p).
  Local Notation comp_step := (Operational.comp_step is_input p).
  Local Notation has_derived_datalog_fact := (Operational.has_derived_datalog_fact is_input p).

  Definition graph_prog_distributes_normal_rules (rules : list rule) :=
    forall concls hyps,
      In (normal_rule concls hyps) rules <->
        In (normal_rule concls hyps) (concat (values graph_prog)).

  Axiom is_normal : rule -> bool.

  Definition graph_prog_distributes_meta_rules (rules : list rule) :=
    forall concls hyps,
      In (meta_rule concls hyps) rules ->
      Forall_map (fun _ rules =>
                    forall R,
                      In R (map meta_clause_rel concls) ->
                      In R (flat_map concl_rels (filter is_normal rules)) ->
                      In (meta_rule concls hyps) rules)
        graph_prog.

  Definition node_senders_ok :=
    forall R n np,
      map.get graph_prog n = Some np ->
      In R (flat_map concl_rels np) ->
      In (node_source n) (graph_senders R).

  Definition input_senders_ok :=
    forall R,
      is_input R = true ->
      In input_source (graph_senders R).

  Context (Hlayout_normal : graph_prog_distributes_normal_rules (rules_of p)).
  Context (Hlayout_meta : graph_prog_distributes_meta_rules (rules_of p)).
  Context (Hsenders_node : node_senders_ok).
  Context (Hsenders_input : input_senders_ok).

  Print meta_dfact.
  Definition graph_facts_of (ofact : dfact) :=
    match ofact with
    | normal_dfact R args => [normal_dfact R args]
    | meta_dfact R args n =>
        map (fun '(f

                 filter (fun '(_, rules) => inb R (flat_map concl_rels (filter is_normal rules))) (map.tuples graph_prog)

  Definition distribute_R (os : state) (gs : graph_state dfact dfact_mod_count Node.node_state) :=
    Forall2_map (fun n np (ns : graph_node_state dfact dfact_mod_count Node.node_state) =>
                   ns.(gns_node_state).(Node.known_facts) =
                     (filter (fun f => inb (dfact_rel f) (flat_map hyp_rels np)) os.(known_facts)) /\
                     nth_error os.(sents) n = Some ns.(gns_node_state).(Node.sent_facts) /\
                     ns.(gns_queue) = [])
      graph_prog gs.(graph_nodes).

  Lemma sim1 os gs os' :
    distribute_R os gs ->
    comp_step os os' ->
    exists gs' t,
      star distributed_step gs t gs' /\
        distribute_R os' gs'.
  Proof.

  Admitted.

  (*we add two pieces of complexity here.
    first, we have a graph (wow)
    second, we do not broadcast facts; we route them according to relation names, in the obvious way.
   *)

  Print distributed_step.



  Check distributed_step.

End __.
