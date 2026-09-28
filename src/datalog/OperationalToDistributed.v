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
  Local Abbreviation can_deduce_message := (Operational.can_deduce_message is_input p).
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
    filter_map message.as_normal (flat_map (get_or_default os.(op_state.sents)) rules).

  Definition normal_facts_sent_by_node (ns : graph_node_state message action_label state) :=
    filter_map message.as_normal ns.(gns_node_state).(state.sent).

  Definition normal_facts_known_by_node (ns : graph_node_state message action_label state) :=
    filter_map message.as_normal ns.(gns_node_state).(state.known).

  Definition normal_facts_wanted_by_rules os (np : program) :=
    filter (fun f => inb (normal_fact.rel f) (program.hyp_rels np)) (filter_map message.as_normal os.(op_state.known)).

  Definition op_sources_of (src : source) : list op_source :=
    match src with
    | node_source n => map op_source.rule (get_or_default graph_prog n).(program.rules)
    | input_source => [op_source.input]
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

  Definition done_msgs_corresp (op_known : list (message (sender_label := op_source))) (ns : graph_node_state message action_label state) :=
    forall fp num src,
      In (message.done_with fp src num) ns.(gns_node_state).(state.known) <->
        In src (graph_senders (fact_pattern.rel fp)) /\
          expects_num_facts (op_sources_of src) fp op_known num.

  (*TODO consider how to merge this with done_msgs_corresp*)
  Definition sent_done_msgs_corresp (op_known : list (message (sender_label := op_source))) n (ns : graph_node_state message action_label state) :=
    forall fp num,
      In (message.done_with fp (node_source n) num) ns.(gns_node_state).(state.sent) <->
        In (node_source n) (graph_senders (fact_pattern.rel fp)) /\
          expects_num_facts (op_sources_of (node_source n)) fp op_known num.

  Definition node_corresp (os : op_state) n np (ns : graph_node_state message action_label state) :=
    Permutation (normal_facts_sent_by_rules os np.(program.rules)) (normal_facts_sent_by_node ns) /\
      Permutation (normal_facts_wanted_by_rules os np) (normal_facts_known_by_node ns) /\
      done_msgs_corresp os.(op_state.known) ns /\
      sent_done_msgs_corresp os.(op_state.known) n ns /\
      ns.(gns_queue) = [].

  Definition distribute_R (os : op_state) (gs : graph_state message action_label state) :=
    Forall2_map (node_corresp os) graph_prog gs.(graph_nodes).

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
    flat_map op_sources_of (map node_source (map.keys graph_prog)) = map op_source.rule all_rules.
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
    if is_input R then [op_source.input] else
      map op_source.rule
        (filter (fun r => inb R (rule.concl_rels r)) (sender_rules p)).

  Definition op_state_reasonable os :=
    forall pat src num,
      In (message.done_with pat src num) (op_state.known os) ->
      In src (op_actual_R_senders (fact_pattern.rel pat)) \/
        num = 0.

  Definition op_state_sents_ok os :=
    forall pat r num,
      In (message.done_with pat (op_source.rule r) num) (op_state.known os) <->
        In (message.done_with pat (op_source.rule r) num) (get_or_default os.(op_state.sents) r).

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

  Lemma op_knows_normal_fact_iff nf np ns os :
    In nf.(normal_fact.rel) (program.hyp_rels np) ->
    Permutation (normal_facts_wanted_by_rules os np) (normal_facts_known_by_node ns) ->
    knows_normal_fact (op_state.known os) nf <->
      knows_normal_fact (state.known (gns_node_state ns)) nf.
  Proof.
    intros HR Hperm. cbv [knows_normal_fact].
    transitivity (In nf (normal_facts_wanted_by_rules os np)).
    - cbv [normal_facts_wanted_by_rules].
      rewrite filter_In, message.in_filter_map_as_normal.
      split; intros; fwd; eauto. split; auto. apply inb_true_iff. auto.
    - rewrite Hperm. cbv [normal_facts_known_by_node]. apply message.in_filter_map_as_normal.
  Qed.

  Lemma op_existsn_iff pat np ns os n :
    In (fact_pattern.rel pat) (program.hyp_rels np) ->
    Existsn (message.matches pat) n (op_state.known os) ->
    Permutation (normal_facts_wanted_by_rules os np) (normal_facts_known_by_node ns) ->
    Existsn (message.matches pat) n (state.known (gns_node_state ns)).
  Proof.
    intros HR H Hperm. cbv [normal_facts_wanted_by_rules] in Hperm.
    cbv [normal_facts_known_by_node] in Hperm. Search Existsn filter_map.
    eapply Existsn_filter_map with (P := fact_pattern.matches pat). 2: rewrite <- Hperm.
    { intros x. destruct x; simpl; intros; split; intros; fwd; (eauto || contradiction || discriminate). }
    apply Existsn_filter.
    { intros nf Hnf. apply inb_true_iff. cbv [fact_pattern.matches] in Hnf.
      fwd. rewrite <- Hnfp0. assumption. }
    rewrite <- Existsn_filter_map; [eassumption|].
    { intros x. destruct x; simpl; intros; split; intros; fwd; (eauto || contradiction || discriminate). }
  Qed.

  Lemma sth' (np : program) os ns f :
    In (fact.rel f) (program.hyp_rels np) ->
    op_state_reasonable os ->
    Permutation (normal_facts_wanted_by_rules os np) (normal_facts_known_by_node ns) ->
    done_msgs_corresp os.(op_state.known) ns ->
    knows_fact R_senders (op_state.known os) f ->
    knows_fact graph_senders (state.known (gns_node_state ns)) f.
  Proof.
    intros Hf Hos Hperm Hcorresp H. cbv [knows_fact] in H |- *. destruct f as [nf | mf].
    - cbv [knows_normal_fact] in H |- *. simpl in Hf.
      apply Permutation_incl in Hperm.
      cbv [normal_facts_wanted_by_rules incl] in Hperm. especialize Hperm.
      { rewrite filter_In. rewrite message.in_filter_map_as_normal.
        split; [eassumption|]. apply inb_true_iff. assumption. }
      cbv [normal_facts_known_by_node] in Hperm.
      rewrite message.in_filter_map_as_normal in Hperm. assumption.
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
          split; [assumption|]. cbv [expects_num_facts]. eauto. }
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

        move Hperm at bottom.
        Check op_existsn_iff.
        eapply op_existsn_iff; eassumption.
      + move Hp2 at bottom. eapply meta_fact.consistent_with_ext; [eassumption|].
        intros nf Hnf. move Hperm at bottom.
        eapply op_knows_normal_fact_iff; try eassumption. rewrite Hnf. exact Hf.
  Qed.

  Lemma sth r (np : program) os ns nf :
    In r np.(program.rules) ->
    op_state_reasonable os ->
    done_msgs_corresp os.(op_state.known) ns ->
    Permutation (normal_facts_wanted_by_rules os np) (normal_facts_known_by_node ns) ->
    can_deduce_normal_fact R_senders r (op_state.known os) nf ->
    can_deduce_normal_fact graph_senders r (state.known (gns_node_state ns)) nf.
  Proof.
    intros Hr Hos Hcorresp Hperm H. cbv [can_deduce_normal_fact] in *.
    fwd. eexists. split; [eassumption|].
    apply rule.interp_hyp_relname_in in Hp0.
    eapply Forall_impl.
    { apply Forall_and; [exact Hp0|exact Hp1]. }
    simpl. intros. fwd. eapply sth'; try eassumption. eapply program.rule_hyp_rel_in; eauto.
  Qed.

  Lemma sth_meta mr (np : program) os ns pat :
    In mr np.(program.meta_rules) ->
    op_state_reasonable os ->
    done_msgs_corresp os.(op_state.known) ns ->
    Permutation (normal_facts_wanted_by_rules os np) (normal_facts_known_by_node ns) ->
    can_deduce_pattern R_senders mr (op_state.known os) pat ->
    can_deduce_pattern graph_senders mr (state.known (gns_node_state ns)) pat.
  Proof.
    intros Hmr Hos Hcorresp Hperm H. cbv [can_deduce_pattern] in *.
    fwd. eexists. split; [eassumption|].
    apply meta_rule.pattern_interp_hyp_relname_in in Hp0. rewrite Lists.List.Forall_map in Hp0.
    eapply Forall_impl.
    { apply Forall_and; [exact Hp0|exact Hp1]. }
    simpl. intros. fwd. eapply sth' with (f := fact.meta _); try eassumption.
    eapply program.meta_rule_hyp_rel_in; eauto.
  Qed.

  Lemma blah os x nf :
    op_state_sents_ok os ->
    counted (op_source.rule x) (get_or_default (op_state.sents os) x) nf <->
      counted (op_source.rule x) os.(op_state.known) nf.
  Proof. intros Hok. cbv [counted op_state_sents_ok] in *. setoid_rewrite Hok. reflexivity. Qed.

  (*TODO want some converse to this?*)
  Lemma blah' op_known k ns nf :
    sent_done_msgs_corresp op_known k ns ->
    counted (node_source k) (state.sent ns.(gns_node_state)) nf ->
    Forall (fun src => counted src op_known nf) (op_sources_of (node_source k)).
  Proof.
    intros H1 H2. cbv [sent_done_msgs_corresp] in H1. cbv [counted] in H2.
    fwd. apply H1 in H2p0. fwd. cbv [expects_num_facts] in H2p0p1. fwd.
    apply Forall2_forget_r in H2p0p1p0. eapply Forall_impl; [eassumption|].
    simpl. intros. cbv [counted]. fwd. eauto.
  Qed.

  Definition eat inps (gns : graph_node_state message action_label state) :=
    {| gns_node_state := state.add_to_known inps gns.(gns_node_state);
      gns_trace := map I_event inps ++ gns.(gns_trace);
      gns_queue := gns.(gns_queue);
    |}.

  Definition directly_send_to keep msgs gs :=
    {| graph_nodes := map_values' (fun dst => eat (filter (keep (node_destn dst)) msgs)) gs.(graph_nodes);
      graph_output_queue := filter (keep output_destn) msgs ++ gs.(graph_output_queue); |}.

  Local Abbreviation nstep := (fun n => node.step graph_senders (Distributed.prog_at graph_prog n) (node_source n)).

  Lemma eat_app inps1 inps2 gns : eat (inps1 ++ inps2) gns = eat inps1 (eat inps2 gns).
  Proof. cbv [eat state.add_to_known]. rewrite map_app, <- !app_assoc. reflexivity. Qed.

  Lemma drain_node n inps gns :
    star (receive_step nstep n) (enqueue inps gns) inps (eat inps gns).
  Proof.
    revert gns. induction inps as [| m inps IH] using rev_ind; intros gns.
    - destruct gns as [[known sent] trace queue]. apply star_refl.
    - rewrite eat_app. eapply star_app; [apply star_one | apply IH].
      destruct gns as [node trace queue]. cbv [enqueue eat state.add_to_known]. simpl.
      rewrite <- app_assoc. apply receive_step_intro; [apply node.input_step | reflexivity].
  Qed.

  Lemma eat_forwarded_msgs nids msgs st :
    exists t,
      star distributed_step (forward_to nids msgs st) t (directly_send_to nids msgs st).
  Proof.
    apply star_per_node; [exact gns_map_ok | reflexivity |].
    cbv [forward_to directly_send_to]. cbn [graph_nodes].
    apply Forall2_map_map_values'_l, Forall2_map_map_values'_r, Forall2_map_dup.
    intros n gns _. eexists. apply drain_node.
  Qed.

  Lemma done_msgs_corresp_cons_normal (known : list (message (sender_label := op_source))) nf (b : bool) ns :
    done_msgs_corresp known ns ->
    done_msgs_corresp (message.normal nf :: known) (eat (if b then [message.normal nf] else []) ns).
  Proof.
    cbv [done_msgs_corresp]. intros H fp num src.
    rewrite expects_num_facts_cons_normal, <- (H fp num src). cbv [eat state.add_to_known]. simpl.
    destruct b; simpl; intuition congruence.
  Qed.

  Lemma sent_done_msgs_corresp_cons_normal (known : list (message (sender_label := op_source))) nf n ns ns' :
    (forall fp num,
        In (message.done_with fp (node_source n) num) ns'.(gns_node_state).(state.sent) <->
          In (message.done_with fp (node_source n) num) ns.(gns_node_state).(state.sent)) ->
    sent_done_msgs_corresp known n ns ->
    sent_done_msgs_corresp (message.normal nf :: known) n ns'.
  Proof.
    cbv [sent_done_msgs_corresp]. intros Hsent H fp num.
    rewrite expects_num_facts_cons_normal, Hsent. apply H.
  Qed.

  Lemma flat_map_sents_deduce_off os r nf rules :
    ~ In r rules ->
    flat_map (get_or_default (deduce_message os r (message.normal nf)).(op_state.sents)) rules =
      flat_map (get_or_default os.(op_state.sents)) rules.
  Proof.
    intros Hr. rewrite !flat_map_concat_map. f_equal. apply map_ext_in. intros r' Hr'.
    rewrite get_or_default_deduce_message_sents. destr (eqb r r'); [subst; contradiction | reflexivity].
  Qed.

  Lemma normal_facts_sent_by_rules_deduce_other os r nf rules :
    ~ In r rules ->
    normal_facts_sent_by_rules (deduce_message os r (message.normal nf)) rules = normal_facts_sent_by_rules os rules.
  Proof. intros. cbv [normal_facts_sent_by_rules]. f_equal. apply flat_map_sents_deduce_off. assumption. Qed.

  Lemma normal_facts_sent_by_rules_deduce_self os r nf rules :
    In r rules -> NoDup rules ->
    Permutation (normal_facts_sent_by_rules (deduce_message os r (message.normal nf)) rules)
      (nf :: normal_facts_sent_by_rules os rules).
  Proof.
    intros Hr Hnd. apply in_split in Hr. destruct Hr as (l1 & l2 & ->). apply NoDup_remove_2 in Hnd.
    cbv [normal_facts_sent_by_rules]. rewrite <- (Permutation_middle l1 l2 r).
    cbn [flat_map]. rewrite flat_map_sents_deduce_off by assumption.
    rewrite get_or_default_deduce_message_sents, eqb_refl_true by assumption. reflexivity.
  Qed.

  Lemma normal_facts_wanted_deduce os r nf np :
    normal_facts_wanted_by_rules (deduce_message os r (message.normal nf)) np =
      (if inb nf.(normal_fact.rel) (program.hyp_rels np) then [nf] else []) ++
        normal_facts_wanted_by_rules os np.
  Proof. cbv [normal_facts_wanted_by_rules deduce_message]. simpl. destruct (inb _ _); reflexivity. Qed.

  Lemma normal_facts_known_eat (b : bool) nf ns :
    normal_facts_known_by_node (eat (if b then [message.normal nf] else []) ns) =
      (if b then [nf] else []) ++ normal_facts_known_by_node ns.
  Proof. cbv [normal_facts_known_by_node eat state.add_to_known]. simpl. destruct b; reflexivity. Qed.

  Lemma rule_at_unique n n' np np' r :
    map.get graph_prog n = Some np -> map.get graph_prog n' = Some np' ->
    In r np.(program.rules) -> In r np'.(program.rules) -> n = n'.
  Proof.
    intros Hn Hn' Hr Hr'. pose proof NoDup_all_rules as Hnd. cbv [all_rules] in Hnd.
    rewrite values_eq_map_keys, flat_map_concat_map, map_map, <- flat_map_concat_map in Hnd.
    eapply NoDup_flat_map_inj; [exact Hnd | eapply map.in_keys; eassumption | eapply map.in_keys; eassumption | |].
    - cbv beta. erewrite get_or_default_Some by eassumption. exact Hr.
    - cbv beta. erewrite get_or_default_Some by eassumption. exact Hr'.
  Qed.

  Lemma node_corresp_deduce_other os r nf n np ns :
    map.get graph_prog n = Some np ->
    ~ In r np.(program.rules) ->
    node_corresp os n np ns ->
    node_corresp (deduce_message os r (message.normal nf)) n np
      (eat (if inb nf.(normal_fact.rel) (program.hyp_rels (prog_at graph_prog n)) then [message.normal nf] else []) ns).
  Proof.
    intros Hget Hr (Hsent & Hknown & Hdone & Hsdone & Hq). erewrite prog_at_get by eassumption.
    cbv [node_corresp]. ssplit.
    - rewrite normal_facts_sent_by_rules_deduce_other by assumption. exact Hsent.
    - rewrite normal_facts_wanted_deduce, normal_facts_known_eat.
      destruct (inb _ _); simpl; [apply perm_skip |]; exact Hknown.
    - cbn [deduce_message op_state.known]. apply done_msgs_corresp_cons_normal. exact Hdone.
    - cbn [deduce_message op_state.known]. eapply sent_done_msgs_corresp_cons_normal; [| exact Hsdone].
      intros. reflexivity.
    - exact Hq.
  Qed.

  Lemma node_corresp_deduce_self os r nf n np ns tr :
    map.get graph_prog n = Some np ->
    In r np.(program.rules) ->
    node_corresp os n np ns ->
    node_corresp (deduce_message os r (message.normal nf)) n np
      (eat (if inb nf.(normal_fact.rel) (program.hyp_rels (prog_at graph_prog n)) then [message.normal nf] else [])
         {| gns_node_state := {| state.known := ns.(gns_node_state).(state.known);
                                 state.sent := message.normal nf :: ns.(gns_node_state).(state.sent) |};
            gns_trace := tr; gns_queue := ns.(gns_queue) |}).
  Proof.
    intros Hget Hr (Hsent & Hknown & Hdone & Hsdone & Hq). erewrite prog_at_get by eassumption.
    pose proof (NoDup_node_rules n) as Hnd. erewrite get_or_default_Some in Hnd by eassumption.
    cbv [node_corresp]. ssplit.
    - rewrite normal_facts_sent_by_rules_deduce_self by assumption. apply perm_skip. exact Hsent.
    - rewrite normal_facts_wanted_deduce, normal_facts_known_eat.
      destruct (inb _ _); simpl; [apply perm_skip |]; exact Hknown.
    - cbn [deduce_message op_state.known]. apply done_msgs_corresp_cons_normal. exact Hdone.
    - cbn [deduce_message op_state.known]. eapply sent_done_msgs_corresp_cons_normal; [| exact Hsdone].
      intros. simpl. intuition congruence.
    - exact Hq.
  Qed.

  Lemma sim1 os gs os' :
    op_state_reasonable os ->
    op_state_sents_ok os ->
    distribute_R os gs ->
    comp_step os os' ->
    exists gs' t,
      star distributed_step gs t gs' /\ distribute_R os' gs'.
  Proof.
    intros Hos1 Hos2 H. invert 1. rename H1 into Hp, H2 into Hr.
    cbv [can_deduce_message can_deduce] in Hr. simpl in Hr. destruct new_fact; fwd.
    - invert_stuff. subst.
      cbv [graph_prog_distributes_normal_rules] in Hlayout_normal.
      apply Hlayout_normal in Hp; auto. apply in_flat_map in Hp. fwd.
      apply In_values in Hpp0. fwd.
      cbv [distribute_R] in H.
      epose proof Forall2_map_get_l as Hk. especialize Hk; try eassumption. fwd.
      pose proof Hkp1 as Hcorr. cbv [node_corresp] in Hkp1. fwd.
      edestruct eat_forwarded_msgs as [t Ht].
      do 2 eexists. split.
      + eapply star_app.
        -- apply star_one. apply gstep_run.
           ++ eassumption.
           ++ cbv [prog_at]. erewrite get_or_default_Some by eassumption.
              eapply deduce_step with (output := message.normal _).
              simpl. split.
              --- apply Exists_exists. eexists. split; [eassumption|].
                  eapply sth; try eassumption.
              --- rewrite blah in Hrp1 by assumption.
                  intro Hcnt. apply Hrp1.
                  pose proof blah' as H'. especialize H'; eauto.
                  rewrite Forall_forall in H'. apply H'.
                  simpl. apply in_map. erewrite get_or_default_Some by eassumption.
                  assumption.
        -- apply Ht.
      + clear Ht. cbv [distribute_R directly_send_to]. simpl.
        apply Forall2_map_map_values'_r.
        eapply Forall2_map_put_r; [| exact Hpp0 |].
        * eapply Forall2_map_impl_strong; [exact H|]. intros k0 np ns Hk0 _ Hnc Hne.
          apply node_corresp_deduce_other; [exact Hk0 | | exact Hnc].
          intros Hr. apply Hne. eapply rule_at_unique; eassumption.
        * apply node_corresp_deduce_self; assumption.
    - cbv [graph_prog_distributes_meta_rules] in Hlayout_meta.
      apply Hlayout_meta in Hrp1p0. clear Hlayout_meta.
      cbv [graph_prog_distributes_normal_rules] in Hlayout_normal.
      apply Hlayout_normal in Hp. clear Hlayout_normal.
      cbv [all_rules] in Hp. apply in_flat_map in Hp. fwd.
      apply In_values in Hpp0. fwd. specialize (Hrp1p0 _ _ Hpp0). simpl in Hrp1p0.
      epose proof Forall2_map_get_l as Hk. especialize Hk; try eassumption. fwd.
      pose proof Classical_Prop.classic (In (fact_pattern.rel pattern) (flat_map rule.concl_rels (program.rules x0)) /\ exists num, expects_num_facts (removeb eqb (op_source.rule r) (op_sources_of (node_source k))) pattern os.(op_state.known) num) as [[Hin [num Hdone]]|Hnot_done].
      + cbv [can_deduce_pattern] in Hrp1p1. fwd.
        do 2 eexists. split.
        -- eapply star_app.
           ++ apply star_one. apply gstep_run. 1: eassumption.
              eapply deduce_step with (output := message.done_with _ _ _).
              simpl. split; [reflexivity|]. split.
              --- apply Exists_exists. eexists. split.
                  +++ erewrite prog_at_get by eassumption. eapply Hrp1p0. 2: exact Hin.
                      eapply meta_rule.pattern_interp_concl_relname_in. eassumption.
                  +++ cbv [can_deduce_pattern]. eexists. split; [eassumption|].
                      done.
                      Search knows_meta_fact.
                      Print can_deduce_pattern.
              Print step.
        Print distribute_R. Print node_corresp. invert_stuff. subst.
  Admitted.

  (*we add two pieces of complexity here.
    first, we have a graph (wow)
    second, we do not broadcast facts; we route them according to relation names, in the obvious way.
   *)

  Print distributed_step.



  Check distributed_step.

End __.
