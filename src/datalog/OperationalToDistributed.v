From Stdlib Require Import List Permutation.
From Datalog Require Import Datalog Node Operational Smallstep Graph List Distributed Map Default Tactics.
From coqutil Require Import Map.Interface Eqb Tactics.fwd Tactics.
From coqutil Require Import Semantics.OmniSmallstepCombinators.
Import ListNotations.
Import node.

Open Scope bool_scope.

#[local] Instance sender_label : sender_labelT := source.
Section __.
  Context `{params : datalog_params}.
  Context {rel_eqb : Eqb rel} {rel_eqb_ok : Eqb_ok rel_eqb}.
  Context {rule_eqb : Eqb rule} {rule_eqb_ok : Eqb_ok rule_eqb}.
  Context (is_input : rel -> bool).
  Context (p : program).
  Context (Hmeta_rules : program.meta_rules_valid p).

  (* Context (Hp_rule_inputs : program.good_input_set p). *)

  Context {gns_map : map.map node_id (graph_node_state node.message node.action_label node.state)}.
  Context {gns_map_ok : map.ok gns_map}.

  Context (rel_forward : source -> destn -> rel -> bool).
  Context {prog_map : map.map node_id program} {prog_map_ok : map.ok prog_map}.
  Context {sent_map : map.map rule (list (message (sender_label := op_source)))}.
  Context (graph_prog : prog_map).

  Local Abbreviation R_senders := (Operational.R_senders is_input p).
  (* Local Notation ok_to_deduce_fact := (Node.ok_to_deduce_fact R_senders). *)
  (* Local Notation new_facts := (Node.new_facts R_senders). *)
  (* Local Notation fire_at_rule := (Operational.fire_at_rule is_input p). *)

  Context (graph_senders : rel -> list source).

  Local Notation distributed_step := (distributed_step graph_senders rel_forward graph_prog).
  Local Notation start := (initial p).
  Local Notation comp_step := (Operational.comp_step is_input p).
  Local Notation has_derived_datalog_fact := (Operational.has_derived_datalog_fact is_input p).

  Definition normal_rules_of :=
    concat (map program.rules (values graph_prog)).

  Definition enough_meta_rules (p : program) :=
    forall mr,
      In mr p.(program.meta_rules) ->
      Forall_map (fun _ np =>
                    forall R,
                      In R (map clause_pattern.rel mr.(meta_rule.concls)) ->
                      In R (flat_map rule.concl_rels p.(program.rules)) ->
                      In mr np.(program.meta_rules))
        graph_prog.

  Definition meta_rules_of :=
    concat (map program.meta_rules (values graph_prog)).

  Definition node_senders_ok :=
    forall R n np,
      map.get graph_prog n = Some np ->
      In R (program.concl_rels np) ->
      In (node_source n) (graph_senders R).

  Definition input_senders_ok :=
    forall R,
      is_input R = true ->
      In input_source (graph_senders R).

  Context (Hlayout_normal : same_set p.(program.rules) normal_rules_of).
  Context (Hlayout_meta : same_set p.(program.meta_rules) meta_rules_of).
  Context (Hsenders_node : node_senders_ok).
  Context (Hsenders_input : input_senders_ok).

  Definition distribute_R (os : Operational.state) (gs : graph_state message action_label state) :=
    Forall2_map (fun n np ns =>
                   Permutation
                     (flat_map message.normal_facts (flat_map (get_or_default os.(sents)) (dedup np.(program.rules))))
                     (flat_map message.normal_facts ns.(gns_node_state).(state.sent)) /\
                     (forall pat num,
                         In (message.done_with pat (node_source n) num) ns.(gns_node_state).(state.sent) <->
                           (exists nums,
                               Forall2 (fun nr num0 => In (message.done_with pat (from_rule nr) num0) (get_or_default os.(sents) nr))
                                 (dedup np.(program.rules)) nums /\
                                 num = list_sum nums)) /\
                     ns.(gns_queue) = [])
      graph_prog gs.(graph_nodes).

  Lemma can_deduce_iff os gs n ns np f r :
    distribute_R os gs ->
    map.get gs.(graph_nodes) n = Some ns ->
    map.get graph_prog n = Some np ->
    can_deduce graph_senders np (node_source n) ns.(gns_node_state) (message.normal f) <->
      fire_at_rule is_input p r os.(known_facts) (get_or_default os.(sents) r) (message.normal f).
  Proof. Admitted.

  Lemma sim1 os gs os' :
    distribute_R os gs ->
    comp_step os os' ->
    exists gs' t,
      star distributed_step gs t gs' /\
        distribute_R os' gs'.
  Proof.
    intros H. invert 1. rename H1 into Hp, H2 into Hr.
    cbv [fire_at_rule] in Hr. cbv [can_deduce] in Hr.
    destruct new_fact as [nf|pat src num]; fwd; simpl in *.
    - destruct Hrp0p0; contradiction || subst.
      apply Hlayout_normal in Hp. cbv [normal_rules_of] in Hp.
      apply in_concat in Hp. fwd. apply in_map_iff in Hpp0. fwd.
      apply In_values in Hpp0p1. fwd.
      epose proof Forall2_map_get_l as Hk. especialize Hk; try eassumption. fwd.
      cbv [distribute_R] in H. do 2 eexists. split.
      + eapply star_step.
        -- apply star_one. apply gstep_run.
           ++ eassumption.
           ++ cbv [prog_at]. erewrite get_or_default_Some by eassumption.
              eapply node.deduce_step with (output := message.normal _).
              simpl. split.
              --- apply Exists_exists. eexists. split; [eassumption|].
                  Print can_deduce.
                  move Hrp0p1 at bottom. cbv [can_deduce_normal_fact] in Hrp0p1.
                  fwd. cbv [can_deduce_normal_fact]. eexists. split; [eassumption|].
                  About R_senders.
                  Print can_deduce_normal_fact.
                  Search @graph_senders.
              cbv [Node.new_facts]. Print can_deduce_fact.
              Print node_step.
        destruct r; simpl in *; try discriminate; fwd. 2: { simpl in *.
      fwd. admit.
    - fwd. cbv [can_deduce_fact] in Hrp1. Tactics.destruct_one_match_hyp.
      { fwd. cbv [can_deduce_normal_fact] in Hrp1p0. fwd. invert Hrp1p0p0. }
      fwd.
      fwd.
  Admitted.

  (*we add two pieces of complexity here.
    first, we have a graph (wow)
    second, we do not broadcast facts; we route them according to relation names, in the obvious way.
   *)

  Print distributed_step.



  Check distributed_step.

End __.
