From Stdlib Require Import List Permutation Morphisms.
From coqutil Require Import Map.Interface Map.Properties Eqb Tactics.fwd Tactics Datatypes.List.
From Datalog Require Import Datalog Node Smallstep Graph List Distributed Map Default Tactics Decidable Pftree Relations.
From coqutil Require Import Semantics.OmniSmallstepCombinators.

Import ListNotations.
Import node.

Open Scope bool_scope.

Section __.
  Context `{params : datalog_params}.
  Context (is_input : rel -> bool).
  Context (p : program).
  Context (Hmeta_rules : program.meta_rules_valid p).
  Context (Hp_good : Forall (fun R => is_input R = false) (program.concl_rels p)).

  #[local] Instance sender_label : sender_labelT := source.

  Context {prog_map : map.map node_id program} {prog_map_ok : map.ok prog_map}.
  Context {gns_map : map.map node_id (graph_node_state message action_label state)} {gns_map_ok : map.ok gns_map}.
  Context {msg_map : map.map node_id (list message)} {msg_map_ok : map.ok msg_map}.

  Context (graph_prog : prog_map).
  Context (Hgraph_good : Forall_map (fun _ np => Forall (fun R => is_input R = false) (program.concl_rels np)) graph_prog).

  Local Abbreviation graph_senders := (Distributed.R_senders graph_prog is_input).
  Local Abbreviation distributed_step := (Distributed.distributed_step graph_prog is_input).
  Local Abbreviation initial_graph_state := (Distributed.initial_graph_state graph_prog).
  Local Abbreviation initial_graph_state_with := (Distributed.initial_graph_state_with graph_prog).

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
                      In R (program.normal_concl_rels np) ->
                      In mr np.(program.meta_rules))
        graph_prog.

  Context (Hlayout_normal : graph_prog_distributes_normal_rules p).
  Context (Hlayout_meta : graph_prog_distributes_meta_rules p).

  Definition node_all_done_with (pat : fact_pattern) (known : list message) :=
    Forall (fun src => exists num, In (message.done_with pat src num) known) (graph_senders pat.(fact_pattern.rel)).

  Definition op_ish_inputs_to (known : list message) :=
    forall pat,
      node_all_done_with pat known ->
      exists mf,
        mf.(meta_fact.pattern) = pat /\ knows_meta_fact graph_senders known mf.

  (* [Distributed.allowed_output] with exact counts. *)
  Definition outputs_ok_from (src : source) (outs : list message) :=
    (forall pat src' num,
        In (message.done_with pat src' num) outs ->
        src' = src /\ Existsn (message.matches pat) num outs) /\
      (forall nf, In (message.normal nf) outs -> In src (graph_senders nf.(normal_fact.rel))).

  Context (inputs : list message) (Hinputs : outputs_ok_from input_source inputs).

  Definition all_outputs (gs : graph_state message action_label state) :=
    flat_map (fun ns => ns.(gns_node_state).(state.sent)) (values gs.(graph_nodes)).

  Definition inputs_eq_outputs (gs : graph_state message action_label state) :=
    Forall_map
      (fun (nn : nat) (ns : graph_node_state message action_label state) =>
         Permutation (ns.(gns_node_state).(state.known) ++ gns_queue ns)
           (filter
              (fun m => rel_forward graph_prog (node_destn nn) (message.rel m))
              (all_outputs gs ++ inputs)))
      (graph_nodes gs).

  Definition outputs_ok (gs : graph_state message action_label state) :=
    Forall_map (fun n ns => outputs_ok_from (node_source n) ns.(gns_node_state).(state.sent)) gs.(graph_nodes).

  Definition op_ish_inputs (gs : graph_state message action_label state) :=
    Forall_map (fun _ ns => op_ish_inputs_to ns.(gns_node_state).(state.known)) gs.(graph_nodes).

  Definition queues_empty (gs : graph_state message action_label state) :=
    Forall_map (fun _ ns => ns.(gns_queue) = []) gs.(graph_nodes).

  Definition node_sent (gs : graph_state message action_label state) n :=
    match map.get gs.(graph_nodes) n with
    | Some ns => ns.(gns_node_state).(state.sent)
    | None => []
    end.

  Definition outs_of gs (src : source) :=
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

  Lemma all_outputs_flat_map gs :
    Permutation (all_outputs gs ++ inputs) (flat_map (outs_of gs) (all_sources gs)).
  Proof.
    cbv [all_sources outs_of]. cbn [flat_map].
    rewrite all_outputs_eq, (flat_map_concat_map _ (map _ _)), map_map, <- flat_map_concat_map.
    apply Permutation_app_comm.
  Qed.

  Lemma in_all_outputs gs k ns m :
    map.get gs.(graph_nodes) k = Some ns ->
    In m ns.(gns_node_state).(state.sent) ->
    In m (all_outputs gs).
  Proof.
    intros Hget Hin. cbv [all_outputs]. apply in_flat_map.
    eexists. split; [apply In_values; eauto | exact Hin].
  Qed.

  Lemma all_outputs_forward_to keep msgs gs :
    Permutation (all_outputs (forward_to keep msgs gs)) (all_outputs gs).
  Proof.
    cbv [all_outputs forward_to]. cbn [graph_nodes].
    rewrite values_eq_tuples, tuples_map_values', values_eq_tuples.
    rewrite flat_map_concat_map, map_map, map_map, (flat_map_concat_map _ (map snd _)), map_map.
    apply Permutation_of_eq. f_equal. apply map_ext. intros [k v]. reflexivity.
  Qed.

  Lemma all_outputs_put gs gs' k ns ns' new :
    map.get gs.(graph_nodes) k = Some ns ->
    gs'.(graph_nodes) = map.put gs.(graph_nodes) k ns' ->
    ns'.(gns_node_state).(state.sent) = new ++ ns.(gns_node_state).(state.sent) ->
    Permutation (all_outputs gs') (new ++ all_outputs gs).
  Proof.
    intros Hget Hnodes Hsent. cbv [all_outputs].
    rewrite Hnodes, values_put, (values_remove _ _ _ Hget). cbn [flat_map].
    rewrite Hsent, <- app_assoc. reflexivity.
  Qed.

  Lemma outputs_ok_outs_of gs src :
    outputs_ok gs ->
    In src (all_sources gs) ->
    outputs_ok_from src (outs_of gs src).
  Proof.
    intros Hnodes [<- | Hin]; [exact Hinputs|].
    apply in_map_iff in Hin. destruct Hin as (n & <- & _). cbv [outs_of node_sent].
    destruct (map.get gs.(graph_nodes) n) eqn:E; [eapply Hnodes; exact E|].
    split; [intros ? ? ? [] | intros ? []].
  Qed.

  Lemma done_source gs pat src c :
    outputs_ok gs ->
    In (message.done_with pat src c) (all_outputs gs ++ inputs) ->
    In src (all_sources gs) /\ Existsn (message.matches pat) c (outs_of gs src).
  Proof.
    intros Hnodes Hin. apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
    - cbv [all_outputs] in Hin. apply in_flat_map in Hin. destruct Hin as (ns & Hns & Hin).
      apply In_values in Hns. destruct Hns as (n & Hget).
      destruct (proj1 (Hnodes _ _ Hget) _ _ _ Hin) as (-> & Hcnt).
      split; [right; apply in_map; eapply Properties.map.in_keys; exact Hget|].
      cbv [outs_of node_sent]. rewrite Hget. exact Hcnt.
    - destruct (proj1 Hinputs _ _ _ Hin) as (-> & Hcnt). split; [left; reflexivity | exact Hcnt].
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

  Lemma outputs_all_done_knows gs known (qr : rel -> bool) pat :
    outputs_ok gs ->
    Permutation known (filter (fun m => qr (message.rel m)) (all_outputs gs ++ inputs)) ->
    node_all_done_with pat known ->
    knows_meta_fact graph_senders known (all_matching known pat).
  Proof.
    intros Hok Hio Hdone. cbv [node_all_done_with] in Hdone.
    set (q := fun m => qr (message.rel m)) in *.
    assert (Hknown : forall m, In m known -> In m (all_outputs gs ++ inputs) /\ q m = true).
    { intros m Hm. eapply Permutation_in in Hm; [| exact Hio]. apply filter_In. exact Hm. }
    pose proof Hdone as Hcs. apply Forall_exists_r_Forall2 in Hcs. destruct Hcs as (cs & Hcs).
    exists (list_sum cs).
    ssplit; [exists cs; split; [exact Hcs | reflexivity] | | apply all_matching_consistent].
    eapply Existsn_perm; [| symmetry; exact Hio].
    destruct (qr pat.(fact_pattern.rel)) eqn:E.
    - apply Existsn_filter.
      { intros [nf | ? ? ?] Hm; [| destruct Hm]. subst q. cbn [message.rel].
        rewrite <- (proj1 Hm). exact E. }
      eapply Existsn_perm; [| symmetry; apply all_outputs_flat_map].
      eapply Existsn_flat_map_incl.
      + apply Distributed.R_senders_NoDup.
      + apply NoDup_all_sources.
      + intros src Hsrc. rewrite Forall_forall in Hdone. destruct (Hdone _ Hsrc) as (c & Hin).
        exact (proj1 (done_source _ _ _ _ Hok (proj1 (Hknown _ Hin)))).
      + eapply Forall2_impl; [exact Hcs|]. intros src c Hin.
        exact (proj2 (done_source _ _ _ _ Hok (proj1 (Hknown _ Hin)))).
      + intros src Hsrc Hnot. apply Forall_not_Existsn_0, Forall_forall. intros m Hm Hmatch.
        apply Hnot.
        destruct m as [nf | ? ? ?]; [| destruct Hmatch].
        destruct (outputs_ok_outs_of _ _ Hok Hsrc) as (_ & Hrel). specialize (Hrel _ Hm).
        rewrite <- (proj1 Hmatch) in Hrel. exact Hrel.
    - assert (Hnone : forall m, message.rel m = pat.(fact_pattern.rel) ->
                                ~ In m (filter q (all_outputs gs ++ inputs))).
      { intros m Hm Hin. apply filter_In in Hin. destruct Hin as (_ & Hq'). subst q.
        cbv beta in Hq'. rewrite Hm, E in Hq'. discriminate. }
      invert Hcs.
      + apply Forall_not_Existsn_0, Forall_forall. intros [nf | ? ? ?] Hin Hmatch; [| destruct Hmatch].
        eapply Hnone; [| exact Hin]. exact (eq_sym (proj1 Hmatch)).
      + exfalso. eapply Hnone; [| eapply Permutation_in; [exact Hio | eassumption]]. reflexivity.
  Qed.

  Lemma get_op_ish_inputs gs :
    queues_empty gs ->
    outputs_ok gs ->
    inputs_eq_outputs gs ->
    op_ish_inputs gs.
  Proof.
    intros Hq Hok Hio. cbv [op_ish_inputs Forall_map op_ish_inputs_to]. intros nn ns Hget pat Hdone.
    specialize (Hq _ _ Hget). specialize (Hio _ _ Hget). cbv beta in Hq, Hio.
    rewrite Hq, app_nil_r in Hio.
    exists (all_matching ns.(gns_node_state).(state.known) pat). split; [reflexivity|].
    eapply outputs_all_done_knows; eassumption.
  Qed.

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

  Lemma outs_of_forward_to keep msgs gs src :
    outs_of (forward_to keep msgs gs) src = outs_of gs src.
  Proof.
    destruct src as [n |]; [| reflexivity]. cbv [outs_of node_sent forward_to]. cbn [graph_nodes].
    rewrite get_map_values'. destruct (map.get _ n); reflexivity.
  Qed.

  Lemma outs_of_put_cons gs gs' k ns ns' m src :
    map.get gs.(graph_nodes) k = Some ns ->
    gs'.(graph_nodes) = map.put gs.(graph_nodes) k ns' ->
    ns'.(gns_node_state).(state.sent) = m :: ns.(gns_node_state).(state.sent) ->
    outs_of gs' src =
      if eqb src (node_source k) then m :: outs_of gs src else outs_of gs src.
  Proof.
    intros Hget Hnodes Hsent. destruct src as [n |]; [| reflexivity].
    cbn [outs_of]. cbv [node_sent]. rewrite Hnodes.
    destr (eqb (node_source n) (node_source k)).
    - rewrite map.get_put_same, Hget, Hsent. reflexivity.
    - rewrite map.get_put_diff by congruence. reflexivity.
  Qed.

  Lemma outs_of_forward_to_pointwise keep msgs gs :
    pointwise_relation source same_set
      (outs_of (forward_to keep msgs gs)) (outs_of gs).
  Proof. intros src. rewrite outs_of_forward_to. reflexivity. Qed.

  Lemma outs_of_put_cons_pointwise gs gs' k ns ns' m :
    map.get gs.(graph_nodes) k = Some ns ->
    gs'.(graph_nodes) = map.put gs.(graph_nodes) k ns' ->
    ns'.(gns_node_state).(state.sent) = m :: ns.(gns_node_state).(state.sent) ->
    pointwise_relation source same_set (outs_of gs')
      (fun src => if eqb src (node_source k) then m :: outs_of gs src else outs_of gs src).
  Proof. intros Hget Hnodes Hsent src. erewrite outs_of_put_cons by eassumption. reflexivity. Qed.

  Definition eat inps (gns : graph_node_state message action_label state) :=
    {| gns_node_state := state.add_to_known inps gns.(gns_node_state);
      gns_trace := map I_event inps ++ gns.(gns_trace);
      gns_queue := gns.(gns_queue);
    |}.

  Definition drain_gns (gns : graph_node_state message action_label state) :=
    {| gns_node_state := state.add_to_known gns.(gns_queue) gns.(gns_node_state);
      gns_trace := map I_event gns.(gns_queue) ++ gns.(gns_trace);
      gns_queue := [] |}.

  Definition drain (gs : graph_state message action_label state) :=
    {| graph_nodes := map_values' (fun _ => drain_gns) gs.(graph_nodes);
      graph_output_queue := gs.(graph_output_queue) |}.

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

  Lemma star_drain_gns n gns :
    star (receive_step nstep n) gns gns.(gns_queue) (drain_gns gns).
  Proof.
    destruct gns as [node trace queue]. cbn [gns_queue].
    rewrite <- (app_nil_r queue) at 1.
    apply (drain_node n queue {| gns_node_state := node; gns_trace := trace; gns_queue := [] |}).
  Qed.

  Lemma star_drain gs : exists t, star distributed_step gs t (drain gs) /\ flat_map inputs_of t = [].
  Proof.
    apply star_per_node; [exact gns_map_ok | reflexivity |].
    apply Forall2_map_map_values'_r, Forall2_map_dup.
    intros n gns _. eexists. apply star_drain_gns.
  Qed.

  Lemma outs_drain gs src : outs_of (drain gs) src = outs_of gs src.
  Proof.
    cbv [outs_of drain]. destruct src; try reflexivity.
    cbv [node_sent]. simpl. rewrite get_map_values'.
    destruct (map.get _ _); reflexivity.
  Qed.

  Lemma queues_empty_drain gs : queues_empty (drain gs).
  Proof. apply Forall_map_map_values'. intros k v _. reflexivity. Qed.

  Lemma outs_drain_pointwise gs :
    pointwise_relation source same_set (outs_of (drain gs)) (outs_of gs).
  Proof. intros src. rewrite outs_drain. reflexivity. Qed.

  Definition reachable gs :=
    exists t, star distributed_step (initial_graph_state_with inputs) t gs /\ flat_map inputs_of t = [].

  Lemma reachable_step gs t gs' :
    reachable gs ->
    star distributed_step gs t gs' ->
    flat_map inputs_of t = [] ->
    reachable gs'.
  Proof.
    intros (t0 & Hstar & Ht0) Hstar' Ht. exists (t ++ t0).
    split; [eapply star_app; eassumption|]. rewrite flat_map_app, Ht, Ht0. reflexivity.
  Qed.

  Lemma run_from_initial gs t :
    star distributed_step (initial_graph_state_with inputs) t gs ->
    star distributed_step initial_graph_state (t ++ map I_event inputs) gs.
  Proof. intros Hstar. eapply star_app; [apply star_gstep_input; exact gns_map_ok | exact Hstar]. Qed.

  Lemma reachable_from_initial gs :
    reachable gs ->
    exists gt, star distributed_step initial_graph_state gt gs /\ flat_map inputs_of gt = inputs.
  Proof.
    intros (t & Hstar & Ht). exists (t ++ map I_event inputs). split; [apply run_from_initial; exact Hstar|].
    rewrite flat_map_app, Ht, inputs_of_map_I_event. reflexivity.
  Qed.

  Lemma reachable_node_runs gs :
    reachable gs ->
    Forall2_map (fun n _ gns => star (nstep n) node.init gns.(gns_trace) gns.(gns_node_state))
      graph_prog gs.(graph_nodes).
  Proof.
    intros Hreach k. destruct (reachable_from_initial _ Hreach) as (gt & Hstar & _).
    pose proof (graph_step_to_node_step_from_beginning _ _ _ (initial_graph_state_empty _) _ _ Hstar k) as H.
    cbv [Distributed.initial_graph_state Distributed.initial_graph_nodes] in H. cbn [graph_nodes] in H.
    rewrite get_map_values' in H.
    destruct (map.get graph_prog k); destruct (map.get gs.(graph_nodes) k); cbn in *; auto.
  Qed.

  Lemma output_map_all_outputs gs d :
    reachable gs ->
    Permutation
      (output_map (mp' := msg_map)
         (fun k outs => filter (Distributed.forward graph_prog (node_source k) d) outs) gs.(graph_nodes))
      (filter (fun m => rel_forward graph_prog d (message.rel m)) (all_outputs gs)).
  Proof.
    intros Hreach. pose proof (reachable_node_runs _ Hreach) as Hruns.
    cbv [output_map outputs_partition all_outputs].
    rewrite map_values'_map_values', values_eq_tuples, <- flat_map_concat_map, tuples_map_values'.
    rewrite filter_flat_map, values_eq_tuples, !flat_map_concat_map, !map_map.
    apply Permutation_of_eq, f_equal, map_ext_in. intros [k ns] Hin. cbn.
    apply Properties.map.tuples_spec in Hin.
    destruct (Forall2_map_get_r _ _ _ _ _ Hruns Hin) as (np & _ & Hrun).
    erewrite <- node.sent_eq_outputs by exact Hrun. reflexivity.
  Qed.

  Lemma inputs_eq_outputs_of_reachable gs :
    reachable gs ->
    inputs_eq_outputs gs.
  Proof.
    intros Hreach. destruct (reachable_from_initial _ Hreach) as (gt' & Hstar & Hinp).
    pose proof (reachable_node_runs _ Hreach) as Hruns.
    intros k ns Hget.
    pose proof (inputs_are_outputs _ _ _ (initial_graph_state_empty _) _ _ Hstar k ns Hget) as H.
    rewrite Hinp in H.
    destruct (Forall2_map_get_r _ _ _ _ _ Hruns Hget) as (np & _ & Hrun).
    erewrite <- node.known_eq_inputs in H by exact Hrun.
    rewrite H, filter_app. cbv [fwd_total].
    apply Permutation_app; [apply output_map_all_outputs; assumption | reflexivity].
  Qed.

  Lemma outputs_ok_of_reachable gs :
    reachable gs ->
    outputs_ok gs.
  Proof.
    intros Hreach.
    pose proof (reachable_node_runs _ Hreach) as Hruns.
    intros k ns Hget.
    destruct (Forall2_map_get_r _ _ _ _ _ Hruns Hget) as (np & Hnp & Hrun).
    cbv beta in Hrun. erewrite prog_at_get in Hrun by exact Hnp.
    split.
    - intros pat src num Hin.
      pose proof (node.sent_source_correct _ _ _ _ _ Hrun _ _ _ Hin). subst src.
      split; [reflexivity|]. eapply node.sent_counts_correct; eassumption.
    - intros nf Hin. eapply node.sent_rel_sender; [| exact Hrun | exact Hin].
      intros ? ? Hcd. apply node.can_deduce_normal_concl_rel in Hcd.
      eauto using node_sends_concl_rels.
  Qed.

  Lemma emitted_eq_outputs gs t :
    star distributed_step (initial_graph_state_with inputs) t gs ->
    flat_map inputs_of t = [] ->
    Permutation (flat_map outputs_of t ++ gs.(graph_output_queue)) (all_outputs gs ++ inputs).
  Proof.
    intros Hstar Ht.
    pose proof (outputs_are_node_outputs _ _ _ (initial_graph_state_empty _) eq_refl _ _ (run_from_initial _ _ Hstar)) as H.
    rewrite !flat_map_app, outputs_of_map_I_event, inputs_of_map_I_event, Ht, app_nil_r in H.
    cbn [app] in H. rewrite H. cbv [output_total]. apply Permutation_app.
    - etransitivity; [apply output_map_all_outputs; eexists; split; eassumption|].
      cbv [Distributed.rel_forward]. rewrite filter_true. reflexivity.
    - cbv [Distributed.forward Distributed.rel_forward]. rewrite filter_true. reflexivity.
  Qed.

  Lemma sender_prog n R :
    In (node_source n) (graph_senders R) ->
    exists np, map.get graph_prog n = Some np /\ In R (program.normal_concl_rels np).
  Proof.
    intros Hin. cbv [Distributed.R_senders] in Hin. destruct (is_input R).
    - destruct Hin as [Heq | []]. discriminate.
    - apply in_filter_map in Hin. destruct Hin as ([k np] & Htup & Hsrc).
      destruct (inb _ _) eqn:E; [invert Hsrc | discriminate].
      exists np. split; [apply Properties.map.tuples_spec; exact Htup | apply inb_true_iff; exact E].
  Qed.

  Lemma node_sent_initial n : node_sent initial_graph_state n = [].
  Proof.
    cbv [node_sent]. destruct (map.get _ n) eqn:E; [| reflexivity].
    apply initial_graph_state_get in E; [| exact gns_map_ok]. fwd. reflexivity.
  Qed.

  Lemma node_in_all_sources gs k np :
    same_domain graph_prog gs.(graph_nodes) ->
    map.get graph_prog k = Some np ->
    In (node_source k) (all_sources gs).
  Proof.
    intros Hdom Hnp. right. apply in_map. specialize (Hdom k). rewrite Hnp in Hdom.
    destruct (map.get gs.(graph_nodes) k) eqn:E; [| contradiction].
    eapply Properties.map.in_keys. exact E.
  Qed.

  Lemma senders_in_all_sources gs R src :
    same_domain graph_prog gs.(graph_nodes) ->
    In src (graph_senders R) ->
    In src (all_sources gs).
  Proof.
    intros Hdom Hin. cbv [Distributed.R_senders] in Hin. destruct (is_input R).
    - destruct Hin as [<- | []]. left. reflexivity.
    - apply in_filter_map in Hin. destruct Hin as ([k np] & Htup & Hsrc).
      destruct (inb _ _); [invert Hsrc | discriminate].
      apply Properties.map.tuples_spec in Htup. eauto using node_in_all_sources.
  Qed.

  Lemma in_all_outputs_iff gs m :
    In m (all_outputs gs ++ inputs) <->
    exists src, In src (all_sources gs) /\ In m (outs_of gs src).
  Proof. rewrite (all_outputs_flat_map gs). apply in_flat_map. Qed.

  Lemma in_known_iff gs k np ns m :
    queues_empty gs ->
    inputs_eq_outputs gs ->
    map.get graph_prog k = Some np ->
    map.get gs.(graph_nodes) k = Some ns ->
    In m ns.(gns_node_state).(state.known) <->
      In (message.rel m) (program.hyp_rels np) /\ In m (all_outputs gs ++ inputs).
  Proof.
    intros Hqe Hieo Hnp Hns.
    specialize (Hieo _ _ Hns). specialize (Hqe _ _ Hns). cbv beta in Hieo, Hqe.
    rewrite Hqe, app_nil_r in Hieo.
    rewrite Hieo, filter_In. cbv [Distributed.rel_forward]. erewrite prog_at_get by eassumption.
    rewrite inb_true_iff. tauto.
  Qed.

  Lemma in_outs_done gs pat src num :
    outputs_ok gs ->
    In (message.done_with pat src num) (all_outputs gs ++ inputs) <->
      In src (all_sources gs) /\
        In (message.done_with pat src num) (outs_of gs src).
  Proof.
    intros Hok. rewrite in_all_outputs_iff. split.
    - intros (src' & Hsrc' & Hin).
      destruct (proj1 (outputs_ok_outs_of _ _ Hok Hsrc') _ _ _ Hin) as (<- & _). auto.
    - intros (Hsrc & Hin). eauto.
  Qed.

End __.
