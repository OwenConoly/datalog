From Stdlib Require Import List Permutation.
From coqutil Require Import Map.Interface Map.Properties Eqb Tactics.fwd Tactics Datatypes.List.
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

  Lemma NoDup_node_rules n : NoDup (get_or_default graph_prog n).(program.rules).
  Proof.
    destruct (map.get graph_prog n) eqn:E.
    - erewrite get_or_default_Some by eassumption.
      eapply NoDup_flat_map_in; [exact NoDup_all_rules|]. apply In_values. eauto.
    - erewrite get_or_default_None by eassumption. constructor.
  Qed.

  Lemma NoDup_op_sources_of src : NoDup (op_sources_of src).
  Proof.
    destruct src; simpl; [| constructor; [intros [] | constructor]].
    apply Finite.Injective_map_NoDup; [| apply NoDup_node_rules]. cbv [Finite.Injective]. congruence.
  Qed.

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

  Lemma R_senders_to_graph_senders' R :
     incl (flat_map op_sources_of (graph_senders R)) (R_senders R).
  Proof.
    cbv [R_senders graph_senders]. destr (is_input R).
    - simpl. auto with incl.
    - rewrite flat_map_filter_map. intros x Hx. rewrite in_flat_map in Hx.
      fwd. Fail progress simp.
      repeat (Tactics.destruct_one_match_hyp; try (contradiction || discriminate); []).
      fwd. cbv [sender_rules]. apply in_map_iff. cbv [op_sources_of] in Hxp1.
      apply in_map_iff in Hxp1. fwd. apply Properties.map.tuples_spec in Hxp0.
      cbv [get_or_default get_or] in Hxp1p1. rewrite Hxp0 in Hxp1p1.
      eexists. split; [reflexivity|]. Search Datatypes.List.dedup.
      rewrite <- dedup_preserves_In. apply Hlayout_normal. cbv [all_rules].
      apply in_flat_map. eexists. split; [|eassumption]. Search values.
      apply In_values. eauto.
  Qed.

  Lemma op_sources_all_nodes :
    flat_map op_sources_of (map node_source (map.keys graph_prog)) = map from_rule all_rules.
  Proof.
    cbv [all_rules].
    rewrite values_eq_map_keys, !flat_map_concat_map, concat_map, !map_map.
    reflexivity.
  Qed.

  Lemma NoDup_flat_map_op_sources R :
    NoDup (flat_map op_sources_of (graph_senders R)).
  Proof.
    destr (is_input R).
    - cbv [Distributed.R_senders]. rewrite E. cbn. constructor; [intros [] | constructor].
    - eapply NoDup_sublist with (l := flat_map op_sources_of (map node_source (map.keys graph_prog))).
      + apply sublist_flat_map. cbv [Distributed.R_senders]. rewrite E. cbn iota.
        rewrite keys_eq_tuples, map_map. apply sublist_filter_map.
        intros [n np] s Hs. simpl in *. destruct (inb R (program.concl_rels np)); congruence.
      + rewrite op_sources_all_nodes.
        apply Finite.Injective_map_NoDup; [intros ? ? ?; congruence | exact NoDup_all_rules].
  Qed.

  Lemma R_senders_to_graph_senders R :
    exists rest,
      Permutation (R_senders R) (flat_map op_sources_of (graph_senders R) ++ rest) /\
        disjoint_lists rest (flat_map op_sources_of (graph_senders R)).
  Proof.
    pose proof (R_senders_to_graph_senders' R) as Hincl.
    apply NoDup_incl_Permutation in Hincl; [| apply NoDup_flat_map_op_sources].
    destruct Hincl as (rest & Hperm). exists rest. split; [exact Hperm|].
    apply disjoint_lists_comm, NoDup_app_disjoint_lists.
    eapply Permutation_NoDup; [exact Hperm | apply Operational.R_senders_NoDup].
  Qed.

  Definition op_actual_R_senders R :=
    if is_input R then [from_input] else
      map from_rule
        (filter (fun r => inb R (rule.concl_rels r)) (sender_rules p)).

  Definition op_state_reasonable os :=
    forall pat src num,
      In (message.done_with pat src num) (op_state.known os) ->
      In src (op_actual_R_senders (fact_pattern.rel pat)) \/
        num = 0.

  Lemma sth'' R :
    incl (op_actual_R_senders R) (flat_map op_sources_of (graph_senders R)).
  Proof.
    cbv [op_actual_R_senders graph_senders op_sources_of]. destruct (is_input R).
    - simpl. auto with incl.
    - rewrite flat_map_filter_map. intros x Hx.
      rewrite in_map_iff in Hx. fwd. rewrite filter_In in Hxp1. fwd.
      apply in_flat_map. cbv [sender_rules] in Hxp1p0.
      apply dedup_preserves_In in Hxp1p0. apply Hlayout_normal in Hxp1p0.
      cbv [all_rules] in Hxp1p0. apply in_flat_map in Hxp1p0. fwd.
      apply In_values in Hxp1p0p0. fwd.
      eexists (_, _). split.
      { apply map.tuples_spec. eassumption. }
      rewrite (proj2 (inb_true_iff _ _)).
      2: { cbv [program.concl_rels]. apply in_app_iff. left. apply in_flat_map.
           eauto. }
      apply in_map. erewrite get_or_default_Some by eassumption. assumption.
  Qed.

  Lemma op_knows_normal_fact_iff nf rules ns os :
    In nf.(normal_fact.rel) (flat_map rule.hyp_rels rules) ->
    Permutation (normal_facts_wanted_by_rules os rules) (normal_facts_known_by_node ns) ->
    knows_normal_fact (op_state.known os) nf <->
      knows_normal_fact (state.known (gns_node_state ns)) nf.
  Proof.
    intros HR Hperm. cbv [knows_normal_fact].
    transitivity (In nf (normal_facts_wanted_by_rules os rules)).
    - cbv [normal_facts_wanted_by_rules]. rewrite filter_In, message.in_flat_map_normal_facts.
      split; [intros H; split; [exact H | apply inb_true_iff; exact HR] | tauto].
    - rewrite Hperm. cbv [normal_facts_known_by_node]. apply message.in_flat_map_normal_facts.
  Qed.

  Lemma sth' r rules os ns f :
    In r rules ->
    In (fact.rel f) (rule.hyp_rels r) ->
    op_state_reasonable os ->
    Permutation (normal_facts_wanted_by_rules os rules) (normal_facts_known_by_node ns) ->
    done_msgs_corresp os ns ->
    knows_fact R_senders (op_state.known os) f ->
    knows_fact graph_senders (state.known (gns_node_state ns)) f.
  Proof.
    intros Hr Hf Hos Hperm Hcorresp H. cbv [knows_fact] in H |- *. destruct f as [nf | mf].
    - cbv [knows_normal_fact] in H |- *. simpl in Hf.
      apply Permutation_incl in Hperm.
      cbv [normal_facts_wanted_by_rules incl] in Hperm. especialize Hperm.
      { rewrite filter_In. rewrite message.in_flat_map_normal_facts.
        split; [eassumption|]. apply inb_true_iff. apply in_flat_map. eauto. }
      cbv [normal_facts_known_by_node] in Hperm.
      rewrite message.in_flat_map_normal_facts in Hperm. assumption.
    - cbv [knows_meta_fact] in H |- *. fwd.

      cbv [expects_num_facts] in Hp0 |- *. fwd.
      cbv [done_msgs_corresp] in Hcorresp.
      epose proof (R_senders_to_graph_senders _) as H. fwd.
      eapply Permutation_Forall2 in Hp0p0; [|eassumption]. fwd.
      apply Forall2_app_inv_l in Hp0p0p1. fwd.
      apply Forall2_flat_map_inv_l in Hp0p0p1p0. fwd.

      eexists. ssplit.
      + clear Hp1 Hp2. eexists (map list_sum _). split.
        { apply Forall2_map_r. eapply Forall2_impl_strong; [eassumption|].
          simpl. intros node_src msgss HR Hsrc _. apply Hcorresp.
          split; [assumption|]. cbv [operational_done_with]. eauto. }
        reflexivity.
      + rewrite <- list_sum_concat.
        assert (list_sum l2'0 = 0).
        { apply Forall2_forget_l in Hp0p0p1p1.
          apply list_sum_zero. eapply Forall_impl; [eassumption|].
          simpl. intros. fwd. cbv [disjoint_lists] in Hp3.
          specialize (Hp3 _ Hp4). apply Hos in Hp5.
          destruct Hp5 as [Hp5|Hp5]; [|auto].
          exfalso. apply Hp3. apply sth''. assumption. }
        move Hp1 at bottom. rewrite Hp0p0p0 in Hp1.
        rewrite list_sum_app in Hp1. rewrite H in Hp1. rewrite <- plus_n_O in Hp1.
        admit.
      + move Hp2 at bottom. eapply meta_fact.consistent_with_ext; [eassumption|].
        intros nf Hnf. move Hperm at bottom.

        Print normal_facts_wanted_by_rules.
        Search meta_fact.consistent_with.

          Print op_sources_of.
          Search graph_senders

            cbv [graph_senders op_sources_of] in Hp3.
          simpl in Hp3. apply sth'' in Hp5.
          simp
          Print graph_senders. Print Distributed.R_senders.





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
