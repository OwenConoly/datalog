From Stdlib Require Import List Permutation.
From coqutil Require Import Map.Interface Eqb Tactics.fwd Tactics Datatypes.List.
From Datalog Require Import Datalog Node Operational Smallstep Graph List Distributed Map Default Tactics.
From coqutil Require Import Semantics.OmniSmallstepCombinators.

Import ListNotations.
Import node.

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

  Context {sent_map : map.map rule (list (message (sender_label := op_source)))} {sent_map_ok : map.ok sent_map}.
  Context {prog_map : map.map node_id program} {prog_map_ok : map.ok prog_map}.
  Context {gns_map : map.map node_id (graph_node_state message action_label state)} {gns_map_ok : map.ok gns_map}.

  Context (graph_prog : prog_map).
  Context (Hgraph_good : Forall_map (fun _ np => Forall (fun R => is_input R = false) (program.concl_rels np)) graph_prog).

  Local Abbreviation graph_senders := (Distributed.R_senders graph_prog is_input).
  Local Abbreviation R_senders := (Operational.R_senders is_input p).
  Local Abbreviation can_deduce := (can_deduce R_senders).
  Local Abbreviation fire_at_rule := (Operational.fire_at_rule is_input p).
  Local Abbreviation comp_step := (Operational.comp_step is_input p).
  Local Abbreviation has_derived_datalog_fact := (Operational.has_derived_datalog_fact is_input p).
  Local Abbreviation distributed_step := (Distributed.distributed_step graph_prog is_input).

  Definition all_rules :=
    flat_map program.rules (values graph_prog).

  Context (NoDup_all_rules : NoDup all_rules).

  Definition graph_prog_distributes_normal_rules (prog : program) :=
    forall r, In r prog.(program.rules) <-> In r all_rules.

  Definition graph_prog_distributes_meta_rules (prog : program) :=
    forall mr,
      In mr prog.(program.meta_rules) ->
      Forall_map (fun _ np =>
                    forall R,
                      In R (meta_rule.concl_rels mr) ->
                      In R (flat_map rule.concl_rels np.(program.rules)) ->
                      In mr np.(program.meta_rules))
        graph_prog.

  Context (Hlayout_normal : graph_prog_distributes_normal_rules p).
  Context (Hlayout_meta : graph_prog_distributes_meta_rules p).

  (*operational state os is consistent with node-program np being done with fp after having sent n messages*)
  Definition normal_facts_sent_by_rules os rules :=
    flat_map message.normal_facts (flat_map (get_or_default os.(op_state.sents)) rules).

  Definition normal_facts_sent_by_node (ns : graph_node_state message action_label state) :=
    flat_map message.normal_facts ns.(gns_node_state).(state.sent).

  Definition normal_facts_known_by_node (ns : graph_node_state message action_label state) :=
    flat_map message.normal_facts ns.(gns_node_state).(state.known).

  Definition normal_facts_wanted_by_rules os (rules : list rule) :=
    filter (fun f => inb (normal_fact.rel f) (flat_map rule.hyp_rels rules)) (flat_map message.normal_facts os.(op_state.known)).

  Definition op_sources_of (src : source) : list op_source :=
    match src with
    | node_source n => map from_rule (get_or_default graph_prog n).(program.rules)
    | input_source => [from_input]
    end.

  Definition operational_done_with os (src : source) fp num :=
    exists nums,
      Forall2 (fun src num0 => In (message.done_with fp src num0) os.(op_state.known))
        (op_sources_of src) nums /\
        num = list_sum nums.

  Definition done_msgs_corresp (os : op_state) (ns : graph_node_state message action_label state) :=
    forall fp num src,
      In (message.done_with fp src num) ns.(gns_node_state).(state.known) <->
        In src (graph_senders (fact_pattern.rel fp)) /\
          operational_done_with os src fp num.

  Definition distribute_R (os : op_state) (gs : graph_state message action_label state) :=
    Forall2_map (fun n np ns =>
                   Permutation
                     (normal_facts_sent_by_rules os np.(program.rules))
                     (normal_facts_sent_by_node ns) /\
                     Permutation
                       (normal_facts_wanted_by_rules os np.(program.rules))
                       (normal_facts_known_by_node ns) /\
                     done_msgs_corresp os ns /\
                     (forall fp num,
                         In (message.done_with fp (node_source n) num) ns.(gns_node_state).(state.sent) <->
                           operational_done_with os (node_source n) fp num) /\
                     ns.(gns_queue) = [])
      graph_prog gs.(graph_nodes).

  Lemma R_senders_to_graph_senders R :
    Permutation (R_senders R) (flat_map op_sources_of (graph_senders R)).
  Proof.
    cbv [R_senders graph_senders]. destr (is_input R).
    - simpl. reflexivity.
    - apply NoDup_Permutation.
      + apply Finite.Injective_map_NoDup.
        -- cbv [Finite.Injective]. congruence.
        -- cbv [sender_rules]. apply NoDup_dedup.
      + rewrite flat_map_filter_map. apply NoDup_flat_map.
        -- apply Properties.map.tuples_NoDup.
        -- intros [? ?] ?. destr (inb R (program.concl_rels p0)).
           ++



  Lemma sth' r rules os ns f :
    In r rules ->
    In (fact.rel f) (rule.hyp_rels r) ->
    Permutation (normal_facts_wanted_by_rules os rules) (normal_facts_known_by_node ns) ->
    done_msgs_corresp os ns ->
    knows_fact R_senders (op_state.known os) f ->
    knows_fact graph_senders (state.known (gns_node_state ns)) f.
  Proof.
    intros Hr Hf Hperm Hcorresp H. cbv [knows_fact] in H |- *. destruct f as [nf | mf].
    - cbv [knows_normal_fact] in H |- *. simpl in Hf.
      apply Permutation_incl in Hperm.
      cbv [normal_facts_wanted_by_rules incl] in Hperm. especialize Hperm.
      { rewrite filter_In. rewrite message.in_flat_map_normal_facts.
        split; [eassumption|]. apply inb_true_iff. apply in_flat_map. eauto. }
      cbv [normal_facts_known_by_node] in Hperm.
      rewrite message.in_flat_map_normal_facts in Hperm. assumption.
    - cbv [knows_meta_fact] in H |- *. fwd. eexists. split.
      + clear Hp1 Hp2. cbv [expects_num_facts] in Hp0 |- *. fwd.
        cbv [done_msgs_corresp] in Hcorresp.
        Print Distributed.R_senders. graph_senders.
        Print op_source.
        (forall pat n num,
            In (message.done_with pat n num) (op_state.known os) ->
            ~In n (graph_senders (fact_pattern.rel pat))
        In (message.done_with (meta_fact.pattern mf) n expected_msgs)
        forall
         Print Operational.R_senders.
  Admitted.

  Lemma sth r rules os ns nf :
    In r rules ->
    Permutation (normal_facts_wanted_by_rules os rules) (normal_facts_known_by_node ns) ->
    can_deduce_normal_fact R_senders r (op_state.known os) nf ->
    can_deduce_normal_fact graph_senders r (state.known (gns_node_state ns)) nf.
  Proof.
    intros Hr Hperm H. cbv [can_deduce_normal_fact] in *.
    fwd. eexists. split; [eassumption|].
    apply rule.interp_hyp_relname_in in Hp0.
    eapply Forall_impl.
    { apply Forall_and; [exact Hp0|exact Hp1]. }
    simpl. intros. fwd. eapply sth'; eassumption.
  Qed.

  Lemma sim1 os gs os' :
    distribute_R os gs ->
    comp_step os os' ->
    exists gs' t,
      star distributed_step gs t gs' /\
        distribute_R os' gs'.
  Proof.
    intros H. invert 1. rename H1 into Hp, H2 into Hr.
    cbv [fire_at_rule can_deduce] in Hr. simpl in Hr. destruct new_fact; fwd.
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
              eapply deduce_step with (output := message.normal _).
              simpl. split.
              --- apply Exists_exists. eexists. split; [eassumption|].
                  Search x.
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
