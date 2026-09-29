From Stdlib Require Import List Permutation.
From coqutil Require Import Map.Interface Map.Properties Eqb Tactics.fwd Tactics Datatypes.List.
From Datalog Require Import Datalog Node Operational Smallstep Graph List Distributed Map Default Tactics Decidable.
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

  Definition normal_facts_wanted_by_prog known (np : program) :=
    filter (fun f => inb (normal_fact.rel f) (program.hyp_rels np)) (filter_map message.as_normal known).

  Definition normal_facts_known_by_node (ns : graph_node_state message action_label state) :=
    filter_map message.as_normal ns.(gns_node_state).(state.known).

  Print message.

  Definition op_sources_of (src : source) : list op_source :=
    match src with
    | node_source n => map op_source.rule (get_or_default graph_prog n).(program.rules)
    | input_source => [op_source.input]
    end.

  Definition R_senders : rel -> list op_source :=
    fun R => if is_input R then [op_source.input] else map op_source.rule (dedup p.(program.rules)).

  Lemma R_senders_NoDup R : NoDup (R_senders R).
  Proof.
    cbv [R_senders]. destruct (is_input R).
    - constructor; [intros [] | constructor].
    - apply Finite.Injective_map_NoDup; [intros ? ? ?; congruence | apply NoDup_dedup].
  Qed.

  Lemma R_senders_to_graph_senders' R :
     incl (flat_map op_sources_of (graph_senders R)) (R_senders R).
  Proof.
    cbv [R_senders graph_senders]. destr (is_input R).
    - simpl. auto with incl.
    - rewrite flat_map_filter_map. intros x Hx. rewrite in_flat_map in Hx.
      fwd. Fail progress simp.
      repeat (Tactics.destruct_one_match_hyp; try (contradiction || discriminate); []).
      fwd. apply in_map_iff. cbv [op_sources_of] in Hxp1.
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
    eapply Permutation_NoDup; [exact Hperm | apply R_senders_NoDup].
  Qed.

  Definition op_actual_R_senders R :=
    if is_input R then [op_source.input] else
      map op_source.rule
        (filter (fun r => inb R (rule.concl_rels r)) (dedup p.(program.rules))).

  Lemma sth'' R :
    incl (op_actual_R_senders R) (flat_map op_sources_of (graph_senders R)).
  Proof.
    cbv [op_actual_R_senders graph_senders op_sources_of]. destruct (is_input R).
    - simpl. auto with incl.
    - rewrite flat_map_filter_map. intros x Hx.
      rewrite in_map_iff in Hx. fwd. rewrite filter_In in Hxp1. fwd.
      apply in_flat_map.
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

  Definition op_ish_inputs_to (known : list message) :=
    forall pat,
      Forall (fun src => exists num, In (message.done_with pat src num) known) (graph_senders pat.(fact_pattern.rel)) ->
      exists mf,
        mf.(meta_fact.pattern) = pat /\ knows_meta_fact graph_senders known mf.

  (* [Distributed.allowed_output] with exact counts. *)
  Definition outputs_ok_from (src : source) (outs : list message) :=
    (forall pat src' num,
        In (message.done_with pat src' num) outs ->
        src' = src /\ Existsn (message.matches pat) num outs) /\
      (forall f, In f outs -> In src (graph_senders (message.rel f))).

  Context {msg_map : map.map nat (list message)}.

  Definition all_outputs (gs : graph_state message action_label state) :=
    flat_map (fun ns => ns.(gns_node_state).(state.sent)) (values gs.(graph_nodes)).

  Definition inputs_eq_outputs (gs : graph_state message action_label state) (gt : list (IO_event (graph_label message action_label) message)) :=
    Forall_map
      (fun (nn : nat) (ns : graph_node_state message action_label state) =>
         Permutation (ns.(gns_node_state).(state.known) ++ gns_queue ns)
           (filter
              (fun m => rel_forward graph_prog (node_destn nn) (message.rel m))
              (all_outputs gs ++ flat_map inputs_of gt)))
      (graph_nodes gs).

  Definition outputs_ok (gs : graph_state message action_label state) (gt : list (IO_event (graph_label message action_label) message)) :=
    Forall_map (fun n ns => outputs_ok_from (node_source n) ns.(gns_node_state).(state.sent)) gs.(graph_nodes) /\
      outputs_ok_from input_source (flat_map inputs_of gt).

  Definition op_ish_inputs (gs : graph_state message action_label state) :=
    Forall_map (fun _ ns => op_ish_inputs_to ns.(gns_node_state).(state.known)) gs.(graph_nodes).

  Definition queues_empty (gs : graph_state message action_label state) :=
    Forall_map (fun _ ns => ns.(gns_queue) = []) gs.(graph_nodes).

  Definition node_sent (gs : graph_state message action_label state) n :=
    match map.get gs.(graph_nodes) n with
    | Some ns => ns.(gns_node_state).(state.sent)
    | None => []
    end.

  Definition outs_of gs (inputs : list message) (src : source) :=
    match src with
    | node_source n => node_sent gs n
    | input_source => inputs
    end.

  Definition all_sources (gs : graph_state message action_label state) :=
    input_source :: map node_source (map.keys gs.(graph_nodes)).

  Lemma NoDup_all_sources gs : NoDup (all_sources gs).
  Proof.
    constructor.
    - intros Hin. apply in_map_iff in Hin. fwd. discriminate.
    - apply Finite.Injective_map_NoDup; [intros ? ? ?; congruence | apply Properties.map.keys_NoDup].
  Qed.

  Lemma all_outputs_eq gs :
    all_outputs gs = flat_map (node_sent gs) (map.keys gs.(graph_nodes)).
  Proof.
    cbv [all_outputs].
    rewrite values_eq_tuples, keys_eq_tuples, !flat_map_concat_map, map_map, map_map.
    f_equal. apply map_ext_in. intros [k v] Hin. cbv [node_sent]. simpl.
    rewrite (proj1 (Properties.map.tuples_spec _ _ _) Hin). reflexivity.
  Qed.

  Lemma all_outputs_flat_map gs inputs :
    Permutation (all_outputs gs ++ inputs) (flat_map (outs_of gs inputs) (all_sources gs)).
  Proof.
    cbv [all_sources outs_of]. cbn [flat_map].
    rewrite all_outputs_eq, (flat_map_concat_map _ (map _ _)), map_map, <- flat_map_concat_map.
    apply Permutation_app_comm.
  Qed.

  Lemma outputs_ok_outs_of gs gt src :
    outputs_ok gs gt ->
    In src (all_sources gs) ->
    outputs_ok_from src (outs_of gs (flat_map inputs_of gt) src).
  Proof.
    intros (Hnodes & Hinp) [<- | Hin]; [exact Hinp|].
    apply in_map_iff in Hin. destruct Hin as (n & <- & _). cbv [outs_of node_sent].
    destruct (map.get gs.(graph_nodes) n) eqn:E; [eapply Hnodes; exact E|].
    split; [intros ? ? ? [] | intros ? []].
  Qed.

  Lemma done_source gs gt pat src c :
    outputs_ok gs gt ->
    In (message.done_with pat src c) (all_outputs gs ++ flat_map inputs_of gt) ->
    In src (all_sources gs) /\ Existsn (message.matches pat) c (outs_of gs (flat_map inputs_of gt) src).
  Proof.
    intros (Hnodes & Hinp) Hin. apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
    - cbv [all_outputs] in Hin. apply in_flat_map in Hin. destruct Hin as (ns & Hns & Hin).
      apply In_values in Hns. destruct Hns as (n & Hget).
      destruct (proj1 (Hnodes _ _ Hget) _ _ _ Hin) as (-> & Hcnt).
      split; [right; apply in_map; eapply Properties.map.in_keys; exact Hget|].
      cbv [outs_of node_sent]. rewrite Hget. exact Hcnt.
    - destruct (proj1 Hinp _ _ _ Hin) as (-> & Hcnt). split; [left; reflexivity | exact Hcnt].
  Qed.

  Definition all_matching (known : list message) pat :=
    meta_fact.mk pat
      (map normal_fact.args (filter (fact_pattern.matchesb pat) (filter_map message.as_normal known))).

  Lemma all_matching_consistent known pat :
    meta_fact.consistent_with (all_matching known pat) (knows_normal_fact known).
  Proof.
    intros nf Hm. cbv [all_matching knows_normal_fact].
    rewrite meta_fact.contains_mk, in_map_iff. split.
    - intros (_ & nf' & Hargs & Hin). apply filter_In in Hin. destruct Hin as (Hin & Hm').
      rewrite (Reflects_true_iff (fact_pattern.matches pat nf')) in Hm' by typeclasses eauto.
      apply message.in_filter_map_as_normal in Hin.
      destruct nf, nf', Hm, Hm'. simpl in *. congruence.
    - intros Hin. split; [exact (proj2 Hm)|]. eexists. split; [reflexivity|].
      apply filter_In. split; [apply message.in_filter_map_as_normal; exact Hin|].
      rewrite (Reflects_true_iff (fact_pattern.matches pat nf)) by typeclasses eauto. exact Hm.
  Qed.

  Lemma get_op_ish_inputs gs gt :
    queues_empty gs ->
    outputs_ok gs gt ->
    inputs_eq_outputs gs gt ->
    op_ish_inputs gs.
  Proof.
    intros Hq Hok Hio. cbv [op_ish_inputs Forall_map op_ish_inputs_to]. intros nn ns Hget pat Hdone.
    specialize (Hq _ _ Hget). specialize (Hio _ _ Hget). cbv beta in Hq, Hio.
    rewrite Hq, app_nil_r in Hio.
    set (inputs := flat_map inputs_of gt) in *.
    set (q := fun m => rel_forward graph_prog (node_destn nn) (message.rel m)) in *.
    assert (Hknown : forall m, In m ns.(gns_node_state).(state.known) ->
                               In m (all_outputs gs ++ inputs) /\ q m = true).
    { intros m Hm. eapply Permutation_in in Hm; [| exact Hio]. apply filter_In. exact Hm. }
    pose proof Hdone as Hcs. apply Forall_exists_r_Forall2 in Hcs. destruct Hcs as (cs & Hcs).
    exists (all_matching ns.(gns_node_state).(state.known) pat). split; [reflexivity|].
    exists (list_sum cs).
    ssplit; [exists cs; split; [exact Hcs | reflexivity] | | apply all_matching_consistent].
    eapply Existsn_perm; [| symmetry; exact Hio].
    destruct (rel_forward graph_prog (node_destn nn) pat.(fact_pattern.rel)) eqn:E.
    - apply Existsn_filter.
      { intros [nf | ? ? ?] Hm; [| destruct Hm]. subst q. cbn [message.rel].
        rewrite <- (proj1 Hm). exact E. }
      eapply Existsn_perm; [| symmetry; apply all_outputs_flat_map].
      eapply Existsn_flat_map_incl.
      + apply Distributed.R_senders_NoDup.
      + apply NoDup_all_sources.
      + intros src Hsrc. rewrite Forall_forall in Hdone. destruct (Hdone _ Hsrc) as (c & Hin).
        exact (proj1 (done_source _ _ _ _ _ Hok (proj1 (Hknown _ Hin)))).
      + eapply Forall2_impl; [exact Hcs|]. intros src c Hin.
        exact (proj2 (done_source _ _ _ _ _ Hok (proj1 (Hknown _ Hin)))).
      + intros src Hsrc Hnot. apply Forall_not_Existsn_0, Forall_forall. intros m Hm Hmatch.
        apply Hnot.
        destruct (outputs_ok_outs_of _ _ _ Hok Hsrc) as (_ & Hrel). specialize (Hrel _ Hm).
        destruct m as [nf | ? ? ?]; [| destruct Hmatch].
        cbn [message.rel] in Hrel. rewrite <- (proj1 Hmatch) in Hrel. exact Hrel.
    - assert (Hnone : forall m, message.rel m = pat.(fact_pattern.rel) ->
                                ~ In m (filter q (all_outputs gs ++ inputs))).
      { intros m Hm Hin. apply filter_In in Hin. destruct Hin as (_ & Hq'). subst q.
        cbv beta in Hq'. rewrite Hm, E in Hq'. discriminate. }
      invert Hcs.
      + apply Forall_not_Existsn_0, Forall_forall. intros [nf | ? ? ?] Hin Hmatch; [| destruct Hmatch].
        eapply Hnone; [| exact Hin]. exact (eq_sym (proj1 Hmatch)).
      + exfalso. eapply Hnone; [| eapply Permutation_in; [exact Hio | eassumption]]. reflexivity.
  Qed.

  Definition outs_corresp (known : list op_message) (gs : graph_state message action_label state) (gt : list (IO_event (graph_label message action_label) message)) :=
    let outs := all_outputs gs ++ flat_map inputs_of gt in
    (forall nf, In (op_message.normal nf) known <-> In (message.normal nf) outs) /\
      (forall pat src,
          In src (graph_senders pat.(fact_pattern.rel)) ->
          Forall (fun osrc => In (op_message.done_with pat osrc) known) (op_sources_of src) <->
            exists num, In (message.done_with pat src num) outs).

  Definition inps_corresp (known : list op_message) np (ns : graph_node_state message action_label state) :=
    (forall nf,
        In (message.normal nf) ns.(gns_node_state).(state.known) <-> In (normal_fact.rel nf) (program.hyp_rels np) /\ In (op_message.normal nf) known) /\
      (forall pat src,
          (exists num, In (message.done_with pat src num) ns.(gns_node_state).(state.known)) <->
            In pat.(fact_pattern.rel) (program.hyp_rels np) /\
              In src (graph_senders pat.(fact_pattern.rel)) /\
              Forall (fun osrc => In (op_message.done_with pat osrc) known) (op_sources_of src)).

  Lemma idkkk known f np ns :
    In (fact.rel f) (program.hyp_rels np) ->
    op_ish_inputs_to ns.(gns_node_state).(state.known) ->
    op_knows_fact is_input p known f ->
    inps_corresp known np ns ->
    knows_fact graph_senders ns.(gns_node_state).(state.known) f.
  Proof.
    intros Hrel Hinps H (Hnormal & Hdone). destruct f as [nf | mf]; cbv [knows_fact fact.rel] in *.
    - cbv [knows_normal_fact]. apply Hnormal. auto.
    - destruct H as (Hall & Hcons).
      destruct (Hinps mf.(meta_fact.pattern)) as (mf' & Hpat & num & Hexp & Hexn & _).
      { apply Forall_forall. intros src Hsrc. apply Hdone. ssplit; [exact Hrel | exact Hsrc |].
        cbv [all_done_with meta_fact.rel] in Hall. cbv [Distributed.R_senders] in Hsrc.
        destruct (is_input _).
        - destruct Hsrc as [<- | []]. cbn [op_sources_of]. auto.
        - apply in_filter_map in Hsrc. destruct Hsrc as ([m prog] & Htup & Hsrc).
          destruct (inb _ _) eqn:E in Hsrc; [invert Hsrc | discriminate].
          apply Properties.map.tuples_spec in Htup.
          cbn [op_sources_of]. erewrite get_or_default_Some by eassumption.
          rewrite Lists.List.Forall_map. apply Forall_forall. intros r Hr.
          rewrite Forall_forall in Hall. apply Hall, Hlayout_normal. cbv [all_rules].
          apply in_flat_map. eexists. split; [apply In_values; eauto | exact Hr]. }
      exists num. cbv [meta_fact.rel] in Hexp |- *. rewrite Hpat in Hexp, Hexn.
      ssplit; [exact Hexp | exact Hexn |].
      cbv [meta_fact.consistent_with knows_normal_fact] in Hcons |- *. intros nf Hm.
      rewrite Hcons, Hnormal by assumption. rewrite <- (proj1 Hm). tauto.
  Qed.

  Lemma sim1 os gs os' :
    distribute_R os gs ->
    comp_step os os' ->
    exists gs' t,
      star distributed_step gs t gs' /\ distribute_R os' gs'.
  Proof.
    intros HR Hstep. cbv [comp_step] in Hstep. fwd. cbv [can_deduce_message] in Hstepp1.
    destruct new_fact as [nf|pat src].
    - cbv [op_can_deduce_normal_fact] in Hstepp1. fwd.
      cbv [distribute_R] in HR.
      cbv [graph_prog_distributes_normal_rules] in Hlayout_normal.
      apply Hlayout_normal in Hstepp0.
      cbv [all_rules] in Hstepp0. apply in_flat_map in Hstepp0. fwd.
      apply In_values in Hstepp0p0. fwd.
      epose proof Forall2_map_get_l as Hk. especialize Hk; try eassumption. fwd.
      do 2 eexists. split.
      + eapply star_app.
        -- apply star_one. apply gstep_run. 1: eassumption.
           eapply deduce_step with (output := message.normal _).
           simpl. split.
           ++ apply Exists_exists. eexists. erewrite prog_at_get by eassumption.
              split; [eassumption|]. cbv [can_deduce_normal_fact].
              eexists. split; [eassumption|]. eapply Forall_impl; [eassumption|].
              intros. eapply idkkk. 2: eassumption. 2: eassumption. admit.
           ++


  Print consistent_with.
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
    intros HR H Hperm. cbv [normal_facts_wanted_by_rules normal_facts_known_by_node] in Hperm.
    rewrite message.Existsn_matches_filter_map_as_normal in H.
    rewrite message.Existsn_matches_filter_map_as_normal, <- Hperm.
    apply Existsn_filter; [| assumption].
    intros nf Hnf. apply inb_true_iff. cbv [fact_pattern.matches] in Hnf.
    fwd. rewrite <- Hnfp0. assumption.
  Qed.

  Lemma op_existsn_sent_iff pat (np : program) ns os n :
    Permutation (normal_facts_sent_by_rules os np.(program.rules)) (normal_facts_sent_by_node ns) ->
    Existsn (message.matches pat) n (flat_map (get_or_default os.(op_state.sents)) np.(program.rules)) <->
      Existsn (message.matches pat) n (state.sent (gns_node_state ns)).
  Proof.
    intros Hperm. cbv [normal_facts_sent_by_rules normal_facts_sent_by_node] in Hperm.
    rewrite !message.Existsn_matches_filter_map_as_normal, Hperm. reflexivity.
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
      apply Hlayout_meta in Hrp1p0.
      cbv [graph_prog_distributes_normal_rules] in Hlayout_normal.
      apply Hlayout_normal in Hp.
      cbv [all_rules] in Hp. apply in_flat_map in Hp. fwd.
      apply In_values in Hpp0. fwd. specialize (Hrp1p0 _ _ Hpp0). simpl in Hrp1p0.
      epose proof Forall2_map_get_l as Hk. especialize Hk; try eassumption. fwd.
      pose proof Classical_Prop.classic (In (fact_pattern.rel pattern) (flat_map rule.concl_rels (program.rules x0)) /\ exists num, expects_num_facts (removeb eqb (op_source.rule r) (op_sources_of (node_source k))) pattern os.(op_state.known) num) as [[Hin [num Hdone]]|Hnot_done].
      + do 2 eexists. split.
        -- eapply star_app.
           ++ apply star_one. apply gstep_run. 1: eassumption.
              eapply deduce_step with (output := message.done_with _ _ _).
              simpl. split; [reflexivity|]. ssplit.
              --- apply Exists_exists. eexists. split.
                  +++ cbv [can_deduce_pattern] in Hrp1p1. fwd.
                      erewrite prog_at_get by eassumption. eapply Hrp1p0. 2: exact Hin.
                      eapply meta_rule.pattern_interp_concl_relname_in. eassumption.
                  +++ cbv [node_corresp] in Hkp1. fwd. eapply sth_meta; try eassumption.
                      eapply Hrp1p0; try eassumption.
                      cbv [can_deduce_pattern] in Hrp1p1. fwd.
                      eapply meta_rule.pattern_interp_concl_relname_in. eassumption.
              --- admit. (*Existsn_total or something*)
              --- erewrite prog_at_get by eassumption. cbv [saturated].
                  split.
                  { eapply op_existsn_sent_iff.
                    rewrite <- op_existsn_sent_iff in Hrp2.
                    eapply op_existsn_sent_iff. 2: eassumption. Search Existsn. eapply
                  rewrite


                        e
                       cbv [
                            Search x. eassumption. cbv [can_deduce_pattern]. eexists. split; [eassumption|].

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
