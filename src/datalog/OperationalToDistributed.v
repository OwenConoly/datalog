From Stdlib Require Import List Permutation Morphisms.
From coqutil Require Import Map.Interface Map.Properties Eqb Tactics.fwd Tactics Datatypes.List.
From Datalog Require Import Datalog Node Operational Smallstep Graph List Distributed Map Default Tactics Decidable.
From coqutil Require Import Semantics.OmniSmallstepCombinators.

Import ListNotations.
Import node.

Open Scope bool_scope.

Section __.
  Context `{params : datalog_params}.
  Context {rel_eqb : Eqb rel} {rel_eqb_ok : Eqb_ok rel_eqb}.
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
  Local Abbreviation can_deduce_message := (Operational.can_deduce_message is_input p).
  Local Abbreviation comp_step := (Operational.comp_step is_input p).
  Local Abbreviation distributed_step := (Distributed.distributed_step graph_prog is_input).
  Local Abbreviation initial_graph_state := (Distributed.initial_graph_state graph_prog).

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

  Definition op_sources_of (src : source) : list op_source :=
    match src with
    | node_source n => map op_source.rule (get_or_default graph_prog n).(program.rules)
    | input_source => [op_source.input]
    end.

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
    apply Permutation_refl'. f_equal. apply map_ext. intros [k v]. reflexivity.
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
    intros Hq Hok Hio. cbv [op_ish_inputs Forall_map op_ish_inputs_to node_all_done_with].
    intros nn ns Hget pat Hdone.
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
        destruct m as [nf | ? ? ?]; [| destruct Hmatch].
        destruct (outputs_ok_outs_of _ _ _ Hok Hsrc) as (_ & Hrel). specialize (Hrel _ Hm).
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

  Lemma op_sources_of_rule src k np r :
    map.get graph_prog k = Some np ->
    In r np.(program.rules) ->
    In (op_source.rule r) (op_sources_of src) ->
    src = node_source k.
  Proof.
    intros Hget Hr Hin. destruct src as [n |]; cbn [op_sources_of] in Hin.
    - apply in_map_iff in Hin. destruct Hin as (r' & Heq & Hr'). invert Heq.
      destruct (map.get graph_prog n) eqn:En.
      + erewrite get_or_default_Some in Hr' by eassumption.
        f_equal. eapply rule_at_unique; eassumption.
      + erewrite get_or_default_None in Hr' by eassumption. destruct Hr'.
    - destruct Hin as [Heq | []]. discriminate.
  Qed.

  Definition outs_corresp (known : list op_message) (outs : source -> list message) :=
    (forall nf src,
        In (message.normal nf) (outs src) <->
          Exists (fun osrc => In (op_message.normal nf osrc) known) (op_sources_of src)) /\
      (forall pat src,
          In src (graph_senders pat.(fact_pattern.rel)) ->
          (exists num, In (message.done_with pat src num) (outs src)) <->
            Forall (fun osrc => In (op_message.done_with pat osrc) known) (op_sources_of src)).

  Lemma outs_corresp_ext k1 k2 o1 o2 :
    outs_corresp k1 o1 ->
    same_set k1 k2 ->
    (forall src, same_set (o1 src) (o2 src)) ->
    outs_corresp k2 o2.
  Proof.
    cbv [outs_corresp same_set]. intros (Hn & Hd) Hk Ho. split.
    - intros nf src. rewrite <- Ho, Hn, !Exists_exists. setoid_rewrite Hk. reflexivity.
    - intros pat src Hsrc. setoid_rewrite <- Ho. rewrite (Hd pat src Hsrc), !Forall_forall.
      setoid_rewrite Hk. reflexivity.
  Qed.

  #[global] Instance outs_corresp_same_set_Proper :
    Proper (same_set ==> pointwise_relation source same_set ==> iff) outs_corresp.
  Proof.
    intros k1 k2 Hk o1 o2 Ho. split; intros H.
    - eapply outs_corresp_ext; [exact H | exact Hk | exact Ho].
    - eapply outs_corresp_ext; [exact H | symmetry; exact Hk | intros src; symmetry; apply Ho].
  Qed.

  Lemma outs_of_forward_to keep msgs gs inputs src :
    outs_of (forward_to keep msgs gs) inputs src = outs_of gs inputs src.
  Proof.
    destruct src as [n |]; [| reflexivity]. cbv [outs_of node_sent forward_to]. cbn [graph_nodes].
    rewrite get_map_values'. destruct (map.get _ n); reflexivity.
  Qed.

  Lemma outs_of_put_cons gs gs' k ns ns' m inputs src :
    map.get gs.(graph_nodes) k = Some ns ->
    gs'.(graph_nodes) = map.put gs.(graph_nodes) k ns' ->
    ns'.(gns_node_state).(state.sent) = m :: ns.(gns_node_state).(state.sent) ->
    outs_of gs' inputs src =
      if eqb src (node_source k) then m :: outs_of gs inputs src else outs_of gs inputs src.
  Proof.
    intros Hget Hnodes Hsent. destruct src as [n |]; [| reflexivity].
    cbn [outs_of]. cbv [node_sent]. rewrite Hnodes.
    destr (eqb (node_source n) (node_source k)).
    - rewrite map.get_put_same, Hget, Hsent. reflexivity.
    - rewrite map.get_put_diff by congruence. reflexivity.
  Qed.

  Lemma outs_of_forward_to_pointwise keep msgs gs inputs :
    pointwise_relation source same_set
      (outs_of (forward_to keep msgs gs) inputs) (outs_of gs inputs).
  Proof. intros src. rewrite outs_of_forward_to. reflexivity. Qed.

  Lemma outs_of_put_cons_pointwise gs gs' k ns ns' m inputs :
    map.get gs.(graph_nodes) k = Some ns ->
    gs'.(graph_nodes) = map.put gs.(graph_nodes) k ns' ->
    ns'.(gns_node_state).(state.sent) = m :: ns.(gns_node_state).(state.sent) ->
    pointwise_relation source same_set (outs_of gs' inputs)
      (fun src => if eqb src (node_source k) then m :: outs_of gs inputs src else outs_of gs inputs src).
  Proof. intros Hget Hnodes Hsent src. erewrite outs_of_put_cons by eassumption. reflexivity. Qed.

  Lemma outs_corresp_cons_normal known outs k np r nf :
    outs_corresp known outs ->
    map.get graph_prog k = Some np ->
    In r np.(program.rules) ->
    outs_corresp (op_message.normal nf (op_source.rule r) :: known)
      (fun src => if eqb src (node_source k) then message.normal nf :: outs src else outs src).
  Proof.
    intros (Hn & Hd) Hget Hr. split.
    - intros nf0 src. destr (eqb src (node_source k)).
      + cbn [In op_sources_of]. rewrite Hn, !Exists_exists. cbn [op_sources_of].
        erewrite get_or_default_Some by eassumption. split.
        * intros [Heq | (osrc & Hosrc & Hin)].
          -- invert Heq. exists (op_source.rule r). split; [apply in_map; assumption | left; reflexivity].
          -- exists osrc. split; [assumption | right; assumption].
        * intros (osrc & Hosrc & [Heq | Hin]); [invert Heq; left; reflexivity | right; eauto].
      + rewrite Hn, !Exists_exists. split.
        * intros (osrc & Hosrc & Hin). exists osrc. split; [assumption | right; assumption].
        * intros (osrc & Hosrc & [Heq | Hin]); [exfalso | eauto]. invert Heq.
          destruct src as [n |]; cbn [op_sources_of] in Hosrc.
          -- apply in_map_iff in Hosrc. destruct Hosrc as (r' & Heq & Hr'). invert Heq.
             destruct (map.get graph_prog n) eqn:En.
             ++ erewrite get_or_default_Some in Hr' by eassumption.
                apply E. f_equal. eapply rule_at_unique; eassumption.
             ++ erewrite get_or_default_None in Hr' by eassumption. destruct Hr'.
          -- destruct Hosrc as [Heq | []]. discriminate.
    - intros pat src Hsrc. specialize (Hd pat src Hsrc).
      transitivity (exists num, In (message.done_with pat src num) (outs src)).
      + destr (eqb src (node_source k)); [| reflexivity]. cbn [In].
        split; intros (num & H); exists num; [destruct H as [Heq | H]; [discriminate | exact H] | right; exact H].
      + rewrite Hd, !Forall_forall. cbn [In].
        split; intros H osrc Hosrc; [right; auto |].
        destruct (H osrc Hosrc) as [Heq | ?]; [discriminate | assumption].
  Qed.

  Lemma outs_corresp_cons_done known outs k np r pat num :
    outs_corresp known outs ->
    map.get graph_prog k = Some np ->
    In r np.(program.rules) ->
    (forall osrc, In osrc (op_sources_of (node_source k)) ->
                  osrc = op_source.rule r \/ In (op_message.done_with pat osrc) known) ->
    outs_corresp (op_message.done_with pat (op_source.rule r) :: known)
      (fun src => if eqb src (node_source k)
                  then message.done_with pat (node_source k) num :: outs src else outs src).
  Proof.
    intros (Hn & Hd) Hget Hr Hothers. split.
    - intros nf src. transitivity (In (message.normal nf) (outs src)).
      + destr (eqb src (node_source k)); [| reflexivity]. cbn [In].
        split; [intros [Heq | H]; [discriminate | exact H] | auto].
      + rewrite Hn, !Exists_exists. cbn [In].
        split; intros (osrc & Hosrc & H); exists osrc; (split; [exact Hosrc|]); [auto |].
        destruct H as [Heq | H]; [discriminate | exact H].
    - intros pat0 src Hsrc. specialize (Hd pat0 src Hsrc). rewrite !Forall_forall in *. cbn [In].
      destr (eqb src (node_source k)).
      + split.
        * intros (num0 & [Heq | H]) osrc Hosrc.
          -- invert Heq. destruct (Hothers _ Hosrc) as [-> | H]; auto.
          -- right. apply Hd; eauto.
        * intros H. destr (eqb pat0 pat); [exists num; left; reflexivity|].
          destruct (proj2 Hd) as (num0 & Hin).
          { intros osrc Hosrc.
            destruct (H _ Hosrc) as [Heq | ?]; [invert Heq; congruence | assumption]. }
          exists num0. right. exact Hin.
      + rewrite Hd. split; [auto|]. intros H osrc Hosrc.
        destruct (H _ Hosrc) as [Heq | ?]; [exfalso | assumption]. invert Heq.
        destruct src as [n |]; cbn [op_sources_of] in Hosrc.
        * apply in_map_iff in Hosrc. destruct Hosrc as (r' & Heq & Hr'). invert Heq.
          destruct (map.get graph_prog n) eqn:En.
          -- erewrite get_or_default_Some in Hr' by eassumption.
             apply E. f_equal. eapply rule_at_unique; eassumption.
          -- erewrite get_or_default_None in Hr' by eassumption. destruct Hr'.
        * destruct Hosrc as [Heq | []]. discriminate.
  Qed.

  Lemma outs_corresp_cons_done_stutter known outs k np r pat :
    outs_corresp known outs ->
    map.get graph_prog k = Some np ->
    In r np.(program.rules) ->
    ~ (In (node_source k) (graph_senders pat.(fact_pattern.rel)) /\
       forall osrc, In osrc (op_sources_of (node_source k)) ->
                    osrc = op_source.rule r \/ In (op_message.done_with pat osrc) known) ->
    outs_corresp (op_message.done_with pat (op_source.rule r) :: known) outs.
  Proof.
    intros (Hn & Hd) Hget Hr Hno. split.
    - intros nf src. rewrite Hn, !Exists_exists. cbn [In].
      split; intros (osrc & Hosrc & H); exists osrc; (split; [exact Hosrc|]); [auto |].
      destruct H as [Heq | H]; [discriminate | exact H].
    - intros pat0 src Hsrc. rewrite (Hd pat0 src Hsrc), !Forall_forall. cbn [In]. split.
      + intros H osrc Hosrc. right. auto.
      + intros H osrc Hosrc. destruct (H _ Hosrc) as [Heq | Hin]; [| exact Hin].
        invert Heq. exfalso. apply Hno.
        pose proof (op_sources_of_rule _ _ _ _ Hget Hr Hosrc) as ->.
        split; [exact Hsrc|]. intros osrc Hosrc'.
        destruct (H _ Hosrc') as [Heq | Hin]; [left; congruence | right; exact Hin].
  Qed.

  Definition inps_corresp (known : list op_message) np (ns : graph_node_state message action_label state) :=
    (forall nf,
        In (message.normal nf) ns.(gns_node_state).(state.known) <-> In (normal_fact.rel nf) (program.hyp_rels np) /\ op_knows_normal_fact known nf) /\
      (forall pat src,
          In src (graph_senders pat.(fact_pattern.rel)) ->
          (exists num, In (message.done_with pat src num) ns.(gns_node_state).(state.known)) <->
            In pat.(fact_pattern.rel) (program.hyp_rels np) /\
              Forall (fun osrc => In (op_message.done_with pat osrc) known) (op_sources_of src)).

  Lemma op_all_done_node_all_done os np ns pat :
    In pat.(fact_pattern.rel) (program.hyp_rels np) ->
    inps_corresp os np ns ->
    all_done_with is_input p os pat ->
    node_all_done_with pat ns.(gns_node_state).(state.known).
  Proof.
    intros Hrel (_ & Hdone) Hall. cbv [node_all_done_with]. apply Forall_forall.
    intros src Hsrc. apply (Hdone _ _ Hsrc). split; [exact Hrel |].
    cbv [all_done_with] in Hall. cbv [Distributed.R_senders] in Hsrc.
    destruct (is_input _).
    - destruct Hsrc as [<- | []]. cbn [op_sources_of]. auto.
    - apply in_filter_map in Hsrc. destruct Hsrc as ([m prog] & Htup & Hsrc).
      destruct (inb _ _) eqn:E in Hsrc; [invert Hsrc | discriminate].
      apply Properties.map.tuples_spec in Htup.
      cbn [op_sources_of]. erewrite get_or_default_Some by eassumption.
      rewrite Lists.List.Forall_map. apply Forall_forall. intros r Hr.
      rewrite Forall_forall in Hall. apply Hall, Hlayout_normal. cbv [all_rules].
      apply in_flat_map. eexists. split; [apply In_values; eauto | exact Hr].
  Qed.

  Lemma idkkk known f np ns :
    In (fact.rel f) (program.hyp_rels np) ->
    op_ish_inputs_to ns.(gns_node_state).(state.known) ->
    op_knows_fact is_input p known f ->
    inps_corresp known np ns ->
    knows_fact graph_senders ns.(gns_node_state).(state.known) f.
  Proof.
    intros Hrel Hinps H Hcorr. pose proof Hcorr as (Hnormal & _).
    destruct f as [nf | mf]; cbv [knows_fact fact.rel] in *.
    - cbv [knows_normal_fact]. apply Hnormal. auto.
    - destruct H as (Hall & Hcons).
      destruct (Hinps mf.(meta_fact.pattern)) as (mf' & Hpat & num & Hexp & Hexn & _).
      { eapply op_all_done_node_all_done; [exact Hrel | exact Hcorr | exact Hall]. }
      exists num. cbv [meta_fact.rel] in Hexp |- *. rewrite Hpat in Hexp, Hexn.
      ssplit; [exact Hexp | exact Hexn |].
      cbv [meta_fact.consistent_with knows_normal_fact] in Hcons |- *. intros nf Hm.
      rewrite Hcons, Hnormal by assumption. rewrite <- (proj1 Hm). tauto.
  Qed.

  Lemma node_knows_op_knows os np ns pats f :
    In (fact.rel f) (program.hyp_rels np) ->
    inps_corresp os np ns ->
    Forall (all_done_with is_input p os) pats ->
    fact.covered_by_pats pats f ->
    knows_fact graph_senders ns.(gns_node_state).(state.known) f ->
    op_knows_fact is_input p os f.
  Proof.
    intros Hrel (Hnormal & _) Hdone Hcov H.
    destruct f as [nf | mf]; cbv [knows_fact op_knows_fact fact.rel] in *.
    - apply Hnormal in H. apply H.
    - destruct H as (num & _ & _ & Hcons). split.
      + apply Exists_exists in Hcov. destruct Hcov as (q & Hq & Hcov).
        cbv [fact.covered_by] in Hcov. subst q. rewrite Forall_forall in Hdone. auto.
      + cbv [meta_fact.consistent_with knows_normal_fact meta_fact.rel] in *. intros nf Hm.
        rewrite Hcons, Hnormal by assumption. rewrite <- (proj1 Hm). tauto.
  Qed.

  Lemma saturated_of_ok_to_deduce os gs (gt : list (IO_event (graph_label message action_label) message))
    k np ns pat :
    map.get graph_prog k = Some np ->
    map.get gs.(graph_nodes) k = Some ns ->
    inps_corresp os np ns ->
    outs_corresp os (outs_of gs (flat_map inputs_of gt)) ->
    op_can_deduce_pattern is_input p os pat ->
    Forall (fun r => ok_to_deduce is_input p r os pat) np.(program.rules) ->
    saturated graph_senders np ns.(gns_node_state) pat.
  Proof.
    intros Hk Hget Hinps (Houts & _) (mr & pats & Hmr & Hpi & Hdone) Hok.
    cbv [saturated can_deduce_normal_fact]. intros r nf Hr (hyps & Hri & Hhyps) Hm.
    assert (Hp : In r p.(program.rules)).
    { apply Hlayout_normal. cbv [all_rules]. apply in_flat_map.
      eexists. split; [apply In_values; eauto | exact Hr]. }
    specialize (Houts nf (node_source k)). cbn [outs_of] in Houts. cbv [node_sent] in Houts.
    rewrite Hget in Houts. apply Houts. apply Exists_exists. exists (op_source.rule r). split.
    - cbn [op_sources_of]. erewrite get_or_default_Some by eassumption. apply in_map. exact Hr.
    - rewrite Forall_forall in Hok. apply (Hok _ Hr); [| exact Hm].
      exists hyps. split; [exact Hri|].
      pose proof (Hmeta_rules _ _ Hmr Hp _ _ _ _ Hpi Hri Hm) as Hcov.
      pose proof (rule.interp_hyp_relname_in _ _ _ Hri) as Hrels.
      eapply Forall_impl;
        [apply Forall_and; [apply Forall_and; [exact Hcov | exact Hrels] | exact Hhyps] |].
      cbv beta. intros h ((Hcov_h & Hrel_h) & Hh).
      eapply node_knows_op_knows with (np := np); eauto using program.rule_hyp_rel_in.
  Qed.

  Lemma sim1 os gs os' (gt : list (IO_event (graph_label message action_label) message))  :
    op_ish_inputs gs ->
    Forall2_map (fun _ => inps_corresp os) graph_prog gs.(graph_nodes) ->
    outs_corresp os (outs_of gs (flat_map inputs_of gt)) ->
    meta_facts_ok is_input p os ->
    comp_step os os' ->
    exists gs' t,
      star distributed_step gs t gs' /\
        flat_map inputs_of t = [] /\
        outs_corresp os' (outs_of gs' (flat_map inputs_of gt)).
  Proof.
    intros Hopish Hinps Houts Hmfs Hstep. cbv [comp_step] in Hstep. fwd.
    pose proof Hstepp0 as Hp.
    cbv [can_deduce_message] in Hstepp1. destruct new_fact as [nf src|pat src].
    - cbv [op_can_deduce_normal_fact] in Hstepp1. fwd.
      cbv [graph_prog_distributes_normal_rules] in Hlayout_normal.
      apply Hlayout_normal in Hstepp0.
      cbv [all_rules] in Hstepp0. apply in_flat_map in Hstepp0. fwd.
      apply In_values in Hstepp0p0. fwd.
      epose proof Forall2_map_get_l as Hk. especialize Hk; try eassumption. fwd.
      pose proof (Classical_Prop.classic (In (op_message.normal nf (op_source.rule r)) os))
        as [Hin|Hnin].
      { do 2 eexists. split; [apply star_refl|]. split; [reflexivity|].
        rewrite same_set_cons_in by assumption.
        assumption. }
      do 2 eexists. split.
      + apply star_one. apply gstep_run. 1: eassumption.
        eapply deduce_step with (output := message.normal _).
        simpl. split.
        ++ apply Exists_exists. eexists. erewrite prog_at_get by eassumption.
           split; [exact Hstepp0p1|]. cbv [can_deduce_normal_fact].
           eexists. split; [eassumption|]. rewrite Forall_forall in Hstepp1p1p1 |- *.
           intros f Hf. eapply idkkk.
           --- eapply program.rule_hyp_rel_in. 1: exact Hstepp0p1.
               apply rule.interp_hyp_relname_in in Hstepp1p1p0.
               rewrite Forall_forall in Hstepp1p1p0. auto.
           --- cbv [op_ish_inputs] in Hopish. eapply Hopish. eassumption.
           --- eauto.
           --- assumption.
        ++ intro Hcnt. apply Hnin. cbv [meta_facts_ok_at_rule] in Hmfs.
           cbv [counted] in Hcnt. fwd. cbv [outs_corresp] in Houts.
           destruct Houts as [_ Houts]. especialize Houts.
           { rewrite (proj1 Hcntp1). eapply node_sends_concl_rels;
               eauto using program.rule_normal_concl_rel_in, rule.interp_concl_relname_in. }
           destruct Houts as [Houts _]. especialize Houts.
           { exists num. cbv [outs_of node_sent]. rewrite Hkp0. exact Hcntp0. }
           cbn [op_sources_of] in Houts. erewrite get_or_default_Some in Houts by eassumption.
           rewrite Lists.List.Forall_map, Forall_forall in Houts.
           cbv [meta_facts_ok] in Hmfs. rewrite Forall_forall in Hmfs.
           eapply Hmfs; eauto. eexists. eauto.
      + split; [reflexivity|]. rewrite outs_of_forward_to_pointwise.
        erewrite outs_of_put_cons_pointwise by (eassumption || reflexivity).
        eapply outs_corresp_cons_normal; eassumption.
    - fwd. pose proof Hstepp1p2 as Hcdp. cbv [op_can_deduce_pattern] in Hstepp1p2. fwd.
      apply Hlayout_normal in Hstepp0.
      apply Hlayout_meta in Hstepp1p2p0.
      cbv [all_rules] in Hstepp0. apply in_flat_map in Hstepp0. fwd.
      apply In_values in Hstepp0p0. fwd.
      epose proof Forall2_map_get_l as Hk. especialize Hk; try eassumption. fwd.
      specialize (Hstepp1p2p0 _ _ ltac:(eassumption)). simpl in Hstepp1p2p0.
      pose proof Classical_Prop.classic (In (fact_pattern.rel pat) (program.normal_concl_rels x) /\ forall src, In src (op_sources_of (node_source k)) -> src = op_source.rule r \/ In (op_message.done_with pat src) os) as [Hyes|Hno].
      + fwd. do 2 eexists. split.
        -- apply star_one. apply gstep_run. 1: eassumption.
           eapply deduce_step with (output := message.done_with _ _ _).
           erewrite prog_at_get by eassumption.
           simpl. split; [reflexivity|]. ssplit.
           ++ apply Exists_exists. eexists. split.
              --- eapply Hstepp1p2p0. 2: eassumption.
                  eapply meta_rule.pattern_interp_concl_relname_in. eassumption.
              --- cbv [can_deduce_pattern].
                  eapply Forall_and in Hstepp1p2p2;
                    [| eapply meta_rule.pattern_interp_hyp_relname_in; eassumption].
                  eapply Forall_impl in Hstepp1p2p2.
                  1: eapply Forall_exists_r_Forall2 in Hstepp1p2p2.
                  2: { intros pat' (Hrel' & Hpat'). simpl.
                       cbv [op_ish_inputs] in Hopish.
                       specialize (Hopish _ _ ltac:(eassumption)). simpl in Hopish.
                       cbv [op_ish_inputs_to] in Hopish.
                       apply Hopish with (pat := pat').
                       eapply op_all_done_node_all_done; [| eassumption | exact Hpat'].
                       eapply program.meta_rule_hyp_rel_in; [| exact Hrel'].
                       eapply Hstepp1p2p0; [| eassumption].
                       eapply meta_rule.pattern_interp_concl_relname_in. eassumption. }
                  destruct Hstepp1p2p2 as [mhyps Hmhyps]. exists mhyps.
                  apply Forall2_flip in Hmhyps.
                  eassert (map _ mhyps = pats) as ->.
                  { symmetry. eapply Forall2_eq_map. eapply Forall2_impl; [eassumption|].
                    simpl. intros. fwd. reflexivity. }
                  split; [eassumption|].
                  eapply Forall2_forget_r in Hmhyps. eapply Forall_impl; [eassumption|].
                  simpl. intros. fwd. auto.
           ++ apply Existsn_length_filter with (f := message.matchesb pat). intros m. exact _.
           ++ eapply saturated_of_ok_to_deduce; try eassumption.
              apply Forall_forall. intros r' Hr'.
              destruct (Hyesp1 (op_source.rule r')) as [Heq | Hdone'].
              { cbn [op_sources_of]. erewrite get_or_default_Some by eassumption.
                apply in_map. exact Hr'. }
              { invert Heq. assumption. }
              cbv [meta_facts_ok] in Hmfs. rewrite Forall_forall in Hmfs.
              apply Hmfs; [| exact Hdone'].
              apply Hlayout_normal. cbv [all_rules]. apply in_flat_map.
              eexists. split; [apply In_values; eauto | exact Hr'].
        -- split; [reflexivity|]. rewrite outs_of_forward_to_pointwise.
           erewrite outs_of_put_cons_pointwise by (eassumption || reflexivity).
           eapply outs_corresp_cons_done; eassumption.
      + exists gs, []. split; [apply star_refl|]. split; [reflexivity|].
        eapply outs_corresp_cons_done_stutter; [exact Houts | eassumption | eassumption |].
        intros (Hsender & Hothers). apply Hno. split; [| exact Hothers].
        eapply node_sends_concl_rels_inv; eassumption.
  Qed.

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

  Lemma outs_drain gs inps src : outs_of (drain gs) inps src = outs_of gs inps src.
  Proof.
    cbv [outs_of drain]. destruct src; try reflexivity.
    cbv [node_sent]. simpl. rewrite get_map_values'.
    destruct (map.get _ _); reflexivity.
  Qed.

  Lemma queues_empty_drain gs : queues_empty (drain gs).
  Proof. apply Forall_map_map_values'. intros k v _. reflexivity. Qed.

  Lemma outs_drain_pointwise gs inputs :
    pointwise_relation source same_set (outs_of (drain gs) inputs) (outs_of gs inputs).
  Proof. intros src. rewrite outs_drain. reflexivity. Qed.

  Definition reachable gs (inputs : list message) :=
    exists gt, star distributed_step initial_graph_state gt gs /\ flat_map inputs_of gt = inputs.

  Lemma reachable_step gs t gs' inputs :
    reachable gs inputs ->
    star distributed_step gs t gs' ->
    flat_map inputs_of t = [] ->
    reachable gs' inputs.
  Proof.
    intros (gt & Hstar & Hinp) Hstar' Ht. exists (t ++ gt).
    split; [eapply star_app; eassumption|]. rewrite flat_map_app, Ht, Hinp. reflexivity.
  Qed.

  Lemma reachable_node_runs gs inputs :
    reachable gs inputs ->
    Forall2_map (fun n _ gns => star (nstep n) node.init gns.(gns_trace) gns.(gns_node_state))
      graph_prog gs.(graph_nodes).
  Proof.
    intros (gt & Hstar & _) k.
    pose proof (graph_step_to_node_step_from_beginning _ _ _ (initial_graph_state_empty _) _ _ Hstar k) as H.
    cbv [Distributed.initial_graph_state Distributed.initial_graph_nodes] in H. cbn [graph_nodes] in H.
    rewrite get_map_values' in H.
    destruct (map.get graph_prog k); destruct (map.get gs.(graph_nodes) k); cbn in *; auto.
  Qed.

  Lemma fwd_total_all_outputs gs inputs nn :
    reachable gs inputs ->
    Permutation (fwd_total (Distributed.forward graph_prog) nn gs.(graph_nodes))
      (filter (fun m => rel_forward graph_prog (node_destn nn) (message.rel m)) (all_outputs gs)).
  Proof.
    intros Hreach. pose proof (reachable_node_runs _ _ Hreach) as Hruns.
    cbv [fwd_total output_map outputs_partition all_outputs].
    rewrite map_values'_map_values', values_eq_tuples, <- flat_map_concat_map, tuples_map_values'.
    rewrite filter_flat_map, values_eq_tuples, !flat_map_concat_map, !map_map.
    apply Permutation_refl', f_equal, map_ext_in. intros [k ns] Hin. cbn.
    apply Properties.map.tuples_spec in Hin.
    destruct (Forall2_map_get_r _ _ _ _ _ Hruns Hin) as (np & _ & Hrun).
    erewrite <- node.sent_eq_outputs by exact Hrun. reflexivity.
  Qed.

  Lemma inputs_eq_outputs_of_reachable gs gt :
    reachable gs (flat_map inputs_of gt) ->
    inputs_eq_outputs gs gt.
  Proof.
    intros Hreach. pose proof Hreach as (gt' & Hstar & Hinp).
    pose proof (reachable_node_runs _ _ Hreach) as Hruns.
    intros k ns Hget.
    pose proof (inputs_are_outputs _ _ _ (initial_graph_state_empty _) _ _ Hstar k ns Hget) as H.
    rewrite Hinp in H.
    destruct (Forall2_map_get_r _ _ _ _ _ Hruns Hget) as (np & _ & Hrun).
    erewrite <- node.known_eq_inputs in H by exact Hrun.
    rewrite H, filter_app. apply Permutation_app; [eapply fwd_total_all_outputs; eassumption | reflexivity].
  Qed.

  Lemma outputs_ok_of_reachable gs gt :
    reachable gs (flat_map inputs_of gt) ->
    outputs_ok_from input_source (flat_map inputs_of gt) ->
    outputs_ok gs gt.
  Proof.
    intros Hreach Hinp. split; [| exact Hinp].
    pose proof (reachable_node_runs _ _ Hreach) as Hruns.
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

  Lemma in_all_outputs_iff gs inputs m :
    In m (all_outputs gs ++ inputs) <->
    exists src, In src (all_sources gs) /\ In m (outs_of gs inputs src).
  Proof. rewrite (all_outputs_flat_map gs inputs). apply in_flat_map. Qed.

  Lemma in_known_iff gs gt k np ns m :
    queues_empty gs ->
    inputs_eq_outputs gs gt ->
    map.get graph_prog k = Some np ->
    map.get gs.(graph_nodes) k = Some ns ->
    In m ns.(gns_node_state).(state.known) <->
      In (message.rel m) (program.hyp_rels np) /\ In m (all_outputs gs ++ flat_map inputs_of gt).
  Proof.
    intros Hqe Hieo Hnp Hns.
    specialize (Hieo _ _ Hns). specialize (Hqe _ _ Hns). cbv beta in Hieo, Hqe.
    rewrite Hqe, app_nil_r in Hieo.
    rewrite Hieo, filter_In. cbv [Distributed.rel_forward]. erewrite prog_at_get by eassumption.
    rewrite inb_true_iff. tauto.
  Qed.

  Lemma op_knows_normal_fact_sources os gs nf :
    tags_ok p os ->
    same_domain graph_prog gs.(graph_nodes) ->
    op_knows_normal_fact os nf <->
      exists src, In src (all_sources gs) /\
        Exists (fun osrc => In (op_message.normal nf osrc) os) (op_sources_of src).
  Proof.
    intros Htags Hdom. split.
    - intros ([r|] & Hin).
      + pose proof (Htags _ _ Hin) as Hr. apply Hlayout_normal in Hr. cbv [all_rules] in Hr.
        apply in_flat_map in Hr. destruct Hr as (np & Hnp & Hr).
        apply In_values in Hnp. destruct Hnp as (k & Hnp).
        exists (node_source k). split; [eauto using node_in_all_sources|].
        cbn [op_sources_of]. erewrite get_or_default_Some by eassumption.
        apply Exists_exists. eexists. split; [apply in_map; exact Hr | exact Hin].
      + exists input_source. split; [left; reflexivity|]. left. exact Hin.
    - intros (src & _ & Hex). apply Exists_exists in Hex. destruct Hex as (osrc & _ & Hin).
      eexists. exact Hin.
  Qed.

  Lemma in_outs_done gs gt pat src num :
    outputs_ok gs gt ->
    In (message.done_with pat src num) (all_outputs gs ++ flat_map inputs_of gt) <->
      In src (all_sources gs) /\
        In (message.done_with pat src num) (outs_of gs (flat_map inputs_of gt) src).
  Proof.
    intros Hok. rewrite in_all_outputs_iff. split.
    - intros (src' & Hsrc' & Hin).
      destruct (proj1 (outputs_ok_outs_of _ _ _ Hok Hsrc') _ _ _ Hin) as (<- & _). auto.
    - intros (Hsrc & Hin). eauto.
  Qed.

  Lemma get_inps_corresp os gs gt :
    tags_ok p os ->
    same_domain graph_prog gs.(graph_nodes) ->
    queues_empty gs ->
    outputs_ok gs gt ->
    inputs_eq_outputs gs gt ->
    outs_corresp os (outs_of gs (flat_map inputs_of gt)) ->
    Forall2_map (fun _ => inps_corresp os) graph_prog gs.(graph_nodes).
  Proof.
    intros Htags Hdom Hqe Hok Hieo (Houts_n & Houts_d) k.
    pose proof (Hdom k) as Hk.
    destruct (map.get graph_prog k) as [np|] eqn:Hnp;
      destruct (map.get gs.(graph_nodes) k) as [ns|] eqn:Hns; try exact Hk.
    split.
    - intros nf. erewrite in_known_iff by eassumption. cbn [message.rel].
      rewrite in_all_outputs_iff, (op_knows_normal_fact_sources _ gs) by assumption.
      setoid_rewrite Houts_n. reflexivity.
    - intros pat src Hsrc. rewrite <- (Houts_d pat src Hsrc).
      pose proof (senders_in_all_sources _ _ _ Hdom Hsrc) as Hsrc'.
      split.
      + intros (num & Hin). erewrite in_known_iff in Hin by eassumption.
        cbn [message.rel] in Hin. destruct Hin as (Hrel & Hin).
        rewrite in_outs_done in Hin by assumption. destruct Hin as (_ & Hin).
        split; [exact Hrel | eexists; exact Hin].
      + intros (Hrel & num & Hin). exists num. erewrite in_known_iff by eassumption.
        cbn [message.rel]. split; [exact Hrel|]. rewrite in_outs_done by assumption. auto.
  Qed.

  Definition distribute_R os gs (gt : list (IO_event (graph_label message action_label) message)) :=
    reachable gs (flat_map inputs_of gt) /\
      outputs_ok_from input_source (flat_map inputs_of gt) /\
      op_ish_inputs gs /\

      meta_facts_correct is_input p os /\
      meta_facts_ok is_input p os /\
      tags_ok p os /\

      Forall2_map (fun _ => inps_corresp os) graph_prog gs.(graph_nodes) /\
      outs_corresp os (outs_of gs (flat_map inputs_of gt)).

  Lemma sim1' os os' gs (gt : list (IO_event (graph_label message action_label) message))  :
    distribute_R os gs gt ->
    comp_step os os' ->
    exists gs' t,
      star distributed_step gs t gs' /\
        flat_map inputs_of t = [] /\
        distribute_R os' gs' gt.
  Proof.
    intros (Hreach & Hinp_ok & Hopish & Hmfc & Hmfo & Htags & Hinps & Houts) Hstep.
    destruct (sim1 _ _ _ gt Hopish Hinps Houts Hmfo Hstep) as (gs1 & t1 & Hstar1 & Ht1 & Houts1).
    destruct (star_drain gs1) as (t2 & Hstar2 & Ht2).
    assert (Hreach' : reachable (drain gs1) (flat_map inputs_of gt)) by eauto using reachable_step.
    pose proof (Forall2_map_same_domain _ _ _ (reachable_node_runs _ _ Hreach')) as Hdom.
    pose proof (inputs_eq_outputs_of_reachable _ _ Hreach') as Hieo.
    pose proof (outputs_ok_of_reachable _ _ Hreach' Hinp_ok) as Hok.
    pose proof (queues_empty_drain gs1) as Hqe.
    rewrite <- outs_drain_pointwise in Houts1.
    exists (drain gs1), (t2 ++ t1). split; [eauto using star_app|].
    split; [rewrite flat_map_app, Ht1, Ht2; reflexivity|].
    cbv [distribute_R]. ssplit.
    - exact Hreach'.
    - exact Hinp_ok.
    - eauto using get_op_ish_inputs.
    - eauto using step_preserves_meta_facts_correct.
    - eauto using step_preserves_meta_facts_ok.
    - eauto using step_preserves_tags_ok.
    - eapply get_inps_corresp; eauto using step_preserves_tags_ok.
    - exact Houts1.
  Qed.
End __.
