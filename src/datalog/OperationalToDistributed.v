From Stdlib Require Import List Permutation.
From Datalog Require Import Datalog Node Operational Smallstep Graph List Distributed Map Default Tactics.
From coqutil Require Import Map.Interface Eqb.
From coqutil Require Import Semantics.OmniSmallstepCombinators.
Import ListNotations.

Open Scope bool_scope.

#[local] Instance mf_label : mf_labelT := source.
Section __.
  Context {rel : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context {rel_eqb : Eqb rel} {rel_eqb_ok : Eqb_ok rel_eqb}.
  Context {rule_eqb : Eqb rule} {rule_eqb_ok : Eqb_ok rule_eqb}.
  Context {sig : signature fn aggregator T}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.
  Context (is_input : rel -> bool).
  Context (p : list rule).
  Context (Hmeta_rules : meta_rules_valid p).
  Context (Hp_rule_inputs : Forall (good_rule_inputs is_input) p).

  Context {gns_map : map.map node_id (graph_node_state dfact dfact_mod_count Node.node_state)}.
  Context {gns_map_ok : map.ok gns_map}.

  Context (rel_forward : source -> destn -> rel -> bool).
  Context {prog_map : map.map node_id (list rule)} {prog_map_ok : map.ok prog_map}.
  Context {sent_map : map.map rule (list (dfact (mf_label := op_source)))}.
  Context (graph_prog : prog_map).

  Local Notation R_senders := (Operational.R_senders is_input p).
  Local Notation ok_to_deduce_fact := (Node.ok_to_deduce_fact R_senders).
  Local Notation new_facts := (Node.new_facts R_senders).
  Local Notation fire_at_rule := (Operational.fire_at_rule is_input p).

  Context (graph_senders : rel -> list source).

  Local Notation distributed_step := (distributed_step graph_senders rel_forward graph_prog).
  Local Notation start := (initial p).
  Local Notation comp_step := (Operational.comp_step is_input p).
  Local Notation has_derived_datalog_fact := (Operational.has_derived_datalog_fact is_input p).

  Definition graph_prog_distributes_normal_rules (rules : list rule) :=
    forall concls hyps,
      In (normal_rule concls hyps) rules <->
        In (normal_rule concls hyps) (concat (values graph_prog)).

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

  Context (Hlayout_normal : graph_prog_distributes_normal_rules p).
  Context (Hlayout_meta : graph_prog_distributes_meta_rules p).
  Context (Hsenders_node : node_senders_ok).
  Context (Hsenders_input : input_senders_ok).

  Definition distribute_R (os : state) (gs : graph_state dfact dfact_mod_count node_state) :=
    Forall2_map (fun n np ns =>
                   Permutation (flat_map normal_facts_of (flat_map (get_or_default os.(sents)) (dedup np)))
                     (flat_map normal_facts_of ns.(gns_node_state).(Node.sent_facts)) /\
                     (forall R args num,
                         In (meta_dfact R args (node_source n) num) ns.(gns_node_state).(Node.sent_facts) <->
                           (exists nums,
                               Forall2 (fun nr num0 => In (meta_dfact R args (from_rule nr) num0) (get_or_default os.(sents) nr))
                                 (dedup (filter is_normal np)) nums /\
                                 num = list_sum nums)) /\
                     ns.(gns_queue) = [])
      graph_prog gs.(graph_nodes).

  Lemma sim1 os gs os' :
    distribute_R os gs ->
    comp_step os os' ->
    exists gs' t,
      star distributed_step gs t gs' /\
        distribute_R os' gs'.
  Proof.
    intros H. invert 1. cbv [fire_at_rule] in H2.
  Admitted.

  (*we add two pieces of complexity here.
    first, we have a graph (wow)
    second, we do not broadcast facts; we route them according to relation names, in the obvious way.
   *)

  Print distributed_step.



  Check distributed_step.

End __.
