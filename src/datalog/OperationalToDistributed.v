From Stdlib Require Import List Permutation.
From Datalog Require Import Datalog Node Operational Smallstep Graph List Distributed Map Default Tactics.
From coqutil Require Import Map.Interface Eqb Tactics.fwd Tactics.
From coqutil Require Import Semantics.OmniSmallstepCombinators.
Import ListNotations.

Open Scope bool_scope.

Section __.
  Context `{params : datalog_params}.
  Context {rel_eqb : Eqb rel} {rel_eqb_ok : Eqb_ok rel_eqb}.
  Context {rule_eqb : Eqb rule} {rule_eqb_ok : Eqb_ok rule_eqb}.
  Context (is_input : rel -> bool).
  Context (p : program).
  Context (Hmeta_rules : program.meta_rules_valid p).
  Context (Hp_good : Forall (fun R => is_input R = false) (program.concl_rels p)).

  #[local] Instance sender_label : sender_labelT := source.

  Context {sent_map : map.map rule (list (node.message (sender_label := op_source)))}
    {sent_map_ok : map.ok sent_map}.
  Context {prog_map : map.map node_id program} {prog_map_ok : map.ok prog_map}.
  Context {gns_map : map.map node_id (graph_node_state node.message node.action_label node.state)}
    {gns_map_ok : map.ok gns_map}.

  Context (rel_forward : source -> destn -> rel -> bool).
  Context (graph_prog : prog_map).
  Context (graph_senders : rel -> list source).

  Local Abbreviation R_senders := (Operational.R_senders is_input p).
  Local Abbreviation can_deduce := (node.can_deduce R_senders).
  Local Abbreviation fire_at_rule := (Operational.fire_at_rule is_input p).
  Local Abbreviation comp_step := (Operational.comp_step is_input p).
  Local Abbreviation has_derived_datalog_fact := (Operational.has_derived_datalog_fact is_input p).
  Local Abbreviation distributed_step := (Distributed.distributed_step graph_senders rel_forward graph_prog).

  Definition graph_prog_distributes_normal_rules (prog : program) :=
    forall r, In r prog.(program.rules) <-> In r (flat_map program.rules (values graph_prog)).

  Definition graph_prog_distributes_meta_rules (prog : program) :=
    forall mr,
      In mr prog.(program.meta_rules) ->
      Forall_map (fun _ np =>
                    forall R,
                      In R (meta_rule.concl_rels mr) ->
                      In R (flat_map rule.concl_rels np.(program.rules)) ->
                      In mr np.(program.meta_rules))
        graph_prog.

  Definition node_senders_ok :=
    Forall_map (fun n np => node.sends_concl_rels graph_senders (node_source n) np) graph_prog.

  Definition input_senders_ok :=
    forall R,
      is_input R = true ->
      In input_source (graph_senders R).

  Context (Hlayout_normal : graph_prog_distributes_normal_rules p).
  Context (Hlayout_meta : graph_prog_distributes_meta_rules p).
  Context (Hsenders_node : node_senders_ok).
  Context (Hsenders_input : input_senders_ok).

  (*operational state os is consistent with node-program np being done with fp after having sent n messages*)
  Definition operational_done_with os np fp num :=
    exists nums,
      Forall2 (fun nr num0 => In (node.message.done_with fp (from_rule nr) num0) (get_or_default os.(op_state.sents) nr))
        (dedup np.(program.rules)) nums /\
        num = list_sum nums.

  Definition normal_facts_sent_by_rules os rules :=
    flat_map node.message.normal_facts (flat_map (get_or_default os.(op_state.sents)) (dedup rules)).

  Definition normal_facts_sent_by_node (ns : graph_node_state node.message node.action_label node.state) :=
    flat_map node.message.normal_facts ns.(gns_node_state).(node.state.sent).

  Definition normal_facts_known_by_node (ns : graph_node_state node.message node.action_label node.state) :=
    flat_map node.message.normal_facts ns.(gns_node_state).(node.state.known).

  Definition normal_facts_wanted_by_rules os rules :=
    filter (fun f => true) (flat_map node.message.normal_facts os.(op_state.known)).

  Definition distribute_R (os : op_state) (gs : graph_state node.message node.action_label node.state) :=
    Forall2_map (fun n np ns =>
                   Permutation
                     (normal_facts_sent_by_rules os np.(program.rules))
                     (normal_facts_sent_by_node ns) /\
                     Permutation
                       (normal_facts_wanted_by_rules os np.(program.rules))
                       (normal_facts_known_by_node ns) /\
                     (forall fp num,
                         In (node.message.done_with fp (node_source n) num) ns.(gns_node_state).(node.state.sent) <->
                           operational_done_with os np fp num) /\
                     ns.(gns_queue) = [])
      graph_prog gs.(graph_nodes).

  Lemma same_known_facts :


  Lemma sim1 os gs os' :
    distribute_R os gs ->
    comp_step os os' ->
    exists gs' t,
      star distributed_step gs t gs' /\
        distribute_R os' gs'.
  Proof.
    intros H. invert 1. rename H1 into Hp, H2 into Hr.
    cbv [fire_at_rule node.can_deduce] in Hr. simpl in Hr. destruct new_fact; fwd.
    - invert_stuff. subst.
      cbv [graph_prog_distributes_normal_rules] in Hlayout_normal.
      apply Hlayout_normal in Hp; auto. apply in_flat_map in Hp. fwd.
      apply In_values in Hpp0. fwd.
      cbv [distribute_R] in H.
      epose proof Forall2_map_get_l as Hk. especialize Hk; try eassumption. fwd.
      do 2 eexists. split.
      + eapply star_step.
        -- apply star_one. apply gstep_run.
           ++ eassumption.
           ++ cbv [prog_at]. erewrite get_or_default_Some by eassumption.
              eapply node.deduce_step with (output := node.message.normal _).
              simpl. split.
              --- apply Exists_exists. eexists. split; [eassumption|].

              ; [|eassumption].
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
