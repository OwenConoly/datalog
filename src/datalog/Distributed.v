From Stdlib Require Import List Lia.
From coqutil Require Import Datatypes.List.
From Datalog Require Import Datalog Node Graph Smallstep List Map Default Eqb Tactics.
From coqutil Require Import Map.Interface Map.Properties Tactics Tactics.fwd Eqb Decidable.
Import ListNotations.
Import node.

Section Distributed.
  Context `{params : datalog_params}.
  Context {rel_eqb : Eqb rel} {rel_eqb_ok : Eqb_ok rel_eqb}.
  Context {prog_map : map.map node_id program} {prog_map_ok : map.ok prog_map}.

  Context (graph_prog : prog_map).
  Context (Hmrv : Forall_map (fun _ p => program.meta_rules_valid p) graph_prog).
  Context (is_input : rel -> bool).
  Context (Hp_good : Forall_map (fun _ p => Forall (fun R => is_input R = false) (program.concl_rels p)) graph_prog).

  #[local] Instance sender_label : sender_labelT := source.

  #[local] Instance program_default : WithDefault program :=
    {| program.rules := []; program.meta_rules := [] |}.

  Ltac map_func := cbv [sender_label] in *; Datalog.Util.Tactics.map_func.

  Definition prog_at (n : node_id) : program := get_or_default graph_prog n.

  Lemma prog_at_get n p : map.get graph_prog n = Some p -> prog_at n = p.
  Proof. apply get_or_default_Some. Qed.

  Definition rel_forward (s : source) (d : destn) (R : rel) : bool :=
    match d with
    | output_destn => true (*TODO: don't output everything*)
    | node_destn nd => inb R (program.hyp_rels (prog_at nd))
    end.

  Definition forward (s : source) (d : destn) (f : message) := rel_forward s d (message.rel f).

  Lemma forward_equiv s d a b :
    message.equiv a b ->
    forward s d a = forward s d b.
  Proof.
    intros Heq. unfold forward. f_equal.
    destruct a, b; simpl in Heq; fwd; congruence || reflexivity.
  Qed.

  Lemma forward_rel_level s d f g :
    message.rel f = message.rel g -> forward s d f = forward s d g.
  Proof. intros. cbv [forward]. congruence. Qed.

  Definition R_senders (R : rel) : list source :=
    if is_input R then [input_source] else
      filter_map
        (fun '(n, p) => if inb R (program.concl_rels p) then Some (node_source n) else None)
        (map.tuples graph_prog).

  Lemma R_senders_NoDup R : NoDup (R_senders R).
  Proof.
    cbv [R_senders]. destruct (is_input R); [constructor; [intros [] | constructor]|].
    apply NoDup_filter_map; [apply map.tuples_NoDup|].
    intros [n p] [n' p'] s Hin Hin' Hf Hf'. simpl in Hf, Hf'.
    apply map.tuples_spec in Hin, Hin'.
    destruct (inb R (program.concl_rels p)), (inb R (program.concl_rels p')); congruence.
  Qed.

  Lemma node_sends_concl_rels k p R :
    map.get graph_prog k = Some p -> In R (program.concl_rels p) -> In (node_source k) (R_senders R).
  Proof.
    intros Hget HR. cbv [R_senders].
    pose proof (Hp_good _ _ Hget) as HF. rewrite Forall_forall in HF. rewrite HF by assumption.
    apply in_filter_map. exists (k, p). split; [apply map.tuples_spec; assumption|].
    simpl. destr (inb R (program.concl_rels p)); [reflexivity | contradiction].
  Qed.

  Abbreviation claim := (node.claim R_senders).
  Abbreviation consistent := (node.consistent R_senders).
  Local Abbreviation nstep := (fun n => node.step R_senders (prog_at n) (node_source n)).
  Local Abbreviation nallowed := (node.allowed_inputs R_senders).

  Hint Immediate message.equiv_Equivalence : core.
  Hint Resolve node.expects_num_facts_incl Existsn_ge_submultiset Existsn_le_submultiset submultiset_incl incl_def : core.

  Definition claim_output (pat : fact_pattern) (n : source) (fs : list message) : Prop :=
    In n (R_senders pat.(fact_pattern.rel)) ->
    exists cnt, In (message.done_with pat n cnt) fs.

  Definition consistent_output (pat : fact_pattern) (n : source) (fs : list message) : Prop :=
    In n (R_senders pat.(fact_pattern.rel)) ->
    exists cnt, In (message.done_with pat n cnt) fs /\
      Existsn_ge (message.matches pat) cnt fs.

  Definition allowed_output (n : source) (fs : list message) : Prop :=
    (forall pat src cnt,
       In (message.done_with pat src cnt) fs ->
       n = src /\ Existsn_le (message.matches pat) cnt fs) /\
    (forall f, In f fs -> In n (R_senders (message.rel f))).

  Lemma claim_output_mono pat n ms1 ms2 :
    claim_output pat n ms1 -> incl_mod message.equiv ms1 ms2 -> claim_output pat n ms2.
  Proof.
    cbv [claim_output]. intros H1 Hincl Hn. especialize H1; eauto. fwd.
    destruct (Hincl _ H1) as ([|] & Hin2 & Heq); simpl in Heq; fwd; try congruence. eauto.
  Qed.

  Lemma consistent_output_mono pat n ms1 ms2 :
    consistent_output pat n ms1 -> submultiset ms1 ms2 -> consistent_output pat n ms2.
  Proof.
    cbv [consistent_output]. intros H1 H2. fwd.
    intros. especialize H1; eauto. fwd. eauto 6.
  Qed.

  Lemma allowed_output_submultiset n : multiset_monotone_dec (allowed_output n).
  Proof.
    cbv [multiset_monotone_dec allowed_output]. intros ? ? H1 H2. fwd.
    split; eauto. intros. especialize H1p0; eauto. fwd. eauto.
  Qed.

  Context {node_map : map.map source (list message)} {node_map_ok : map.ok node_map}.

  Lemma meta_locate pat (partition : node_map) n cnt :
    Forall_map allowed_output partition ->
    In (message.done_with pat n cnt) (concat (values partition)) ->
    exists ms, map.get partition n = Some ms /\ In (message.done_with pat n cnt) ms /\
                 Existsn_le (message.matches pat) cnt ms.
  Proof.
    intros HF Hin. apply In_concat_values in Hin. destruct Hin as (k & ms & Hget & Hin).
    destruct (HF _ _ Hget) as (Hall & _). specialize (Hall _ _ _ Hin). fwd. eauto.
  Qed.

  Lemma no_R_matches_off_senders pat (partition : node_map) n ms :
    Forall_map allowed_output partition ->
    map.get partition n = Some ms -> ~ In n (R_senders pat.(fact_pattern.rel)) ->
    Forall (fun f => ~ message.matches pat f) ms.
  Proof.
    intros HF Hget Hnin. apply Forall_forall. intros f Hf Hmatch. apply Hnin.
    destruct (HF _ _ Hget) as (_ & Hsend). specialize (Hsend _ Hf).
    destruct f as [nf |]; [| destruct Hmatch]. destruct Hmatch as (Hrel & _). rewrite Hrel. exact Hsend.
  Qed.

  (* the claim's per-sender expected counts (absent senders count 0) *)
  Local Abbreviation count_at pat ems := (fun_of_lists 0 (R_senders pat.(fact_pattern.rel)) ems).

  Lemma sum_count_at pat ems (partition : node_map) :
    length (R_senders pat.(fact_pattern.rel)) = length ems ->
    incl (R_senders pat.(fact_pattern.rel)) (map.keys partition) ->
    list_sum (List.map (count_at pat ems) (map.keys partition)) = list_sum ems.
  Proof.
    intros Hlen Hsub.
    erewrite list_sum_map_over_subset; try eassumption.
    - f_equal. apply map_fun_of_lists; [|eassumption]. apply R_senders_NoDup.
    - apply R_senders_NoDup.
    - apply map.keys_NoDup.
    - intros. apply fun_of_lists_off. assumption.
  Qed.

  Lemma senders_in_keys pat ems (partition : node_map) :
    Forall_map allowed_output partition ->
    Forall2 (fun k e => In (message.done_with pat k e) (concat (values partition)))
            (R_senders pat.(fact_pattern.rel)) ems ->
    incl (R_senders pat.(fact_pattern.rel)) (map.keys partition).
  Proof.
    intros HF Hems k Hk. destruct (Forall2_In_l _ _ _ _ Hems Hk) as (em & _ & Hmeta).
    eapply meta_locate in Hmeta; eauto. fwd. eapply map.in_keys; eassumption.
  Qed.

  (*each node's sent multiset stays within the count the claim assigns it*)
  Lemma counts_bound pat ems (partition : node_map) k ms :
    Forall_map allowed_output partition ->
    Forall2 (fun k e => In (message.done_with pat k e) (concat (values partition)))
            (R_senders pat.(fact_pattern.rel)) ems ->
    map.get partition k = Some ms ->
    Existsn_le (message.matches pat) (count_at pat ems k) ms.
  Proof.
    intros HF Hems Hget. destr (inb k (R_senders pat.(fact_pattern.rel))).
    - destruct (Forall2_In_l _ _ _ _ Hems E) as (em & Hcomb & Hmeta).
      erewrite fun_of_lists_In by eauto using R_senders_NoDup, Forall2_length.
      eapply meta_locate in Hmeta; eauto. fwd. map_func. assumption.
    - rewrite fun_of_lists_off by assumption. apply Existsn_le_0_Forall_not.
      eapply no_R_matches_off_senders; eassumption.
  Qed.

  Lemma allowed_of_outputs (partition : node_map) :
    Forall_map allowed_output partition -> nallowed (concat (values partition)).
  Proof.
    intros HF pat ems Hems.
    erewrite <- sum_count_at by eauto using Forall2_length, senders_in_keys.
    apply Existsn_le_concat_map. intros k ms Hget. eapply counts_bound; eassumption.
  Qed.

  Lemma consistent_good_holds :
    consistent_good claim claim_output consistent_output allowed_output consistent.
  Proof.
    intros pat partition Hallow Hclaim. cbv [node.claim] in Hclaim. split.
    - intros n ms Hget Hn. specialize (Hclaim _ Hn). fwd.
      eapply meta_locate in Hclaim; eauto. fwd. map_func. eauto.
    - cbv [node.consistent node.expects_num_facts]. split.
      + intros (num & (ems & Hexpect & ->) & Hge).
        erewrite <- sum_count_at in Hge by eauto using Forall2_length, senders_in_keys.
        intros n ms Hget Hn. destruct (Forall2_In_l _ _ _ _ Hexpect Hn) as (em & Hcomb & Hmeta).
        exists (count_at pat ems n). split.
        * erewrite fun_of_lists_In by eauto using R_senders_NoDup, Forall2_length.
          eapply meta_locate in Hmeta; eauto. fwd. map_func. assumption.
        * eapply Existsn_squeeze_map; [exact Hge | intros ? ? ?; eapply counts_bound; eassumption | exact Hget].
      + intros HcoF.
        assert (Hbuild : Forall (fun k => exists cnt ms, map.get partition k = Some ms /\
                    In (message.done_with pat k cnt) ms /\ Existsn_ge (message.matches pat) cnt ms)
                    (R_senders pat.(fact_pattern.rel))).
        { apply Forall_forall. intros k Hk. specialize (Hclaim _ Hk). fwd.
          eapply meta_locate in Hclaim; eauto. fwd.
          cbv [Forall_map consistent_output] in HcoF. especialize HcoF; eauto. fwd. eauto 6. }
        apply Forall_exists_r_Forall2 in Hbuild. destruct Hbuild as (ems & Hbuild).
        assert (Hin : Forall2 (fun k e => In (message.done_with pat k e) (concat (values partition)))
                        (R_senders pat.(fact_pattern.rel)) ems).
        { eapply Forall2_impl; [exact Hbuild|]. intros ? ? H. cbv beta in H. fwd.
          apply In_concat_values. eauto. }
        exists (list_sum ems). split; [eauto|].
        erewrite <- sum_count_at by eauto using Forall2_length, senders_in_keys.
        apply Existsn_ge_concat_map. intros k ms Hget.
        destr (inb k (R_senders pat.(fact_pattern.rel))).
        -- destruct (Forall2_In_l _ _ _ _ Hbuild E) as (cnt & Hcomb & Hk). fwd.
           erewrite fun_of_lists_In by eauto using R_senders_NoDup, Forall2_length.
           map_func. assumption.
        -- rewrite fun_of_lists_off by assumption. apply Eg_zero.
  Qed.

  Context {gmap : map.map node_id (@graph_node_state message action_label state)}.
  Context {gmap_ok : map.ok gmap}.
  Context {msg_map : map.map node_id (list message)} {msg_map_ok : map.ok msg_map}.

  Definition graph_node_init : @graph_node_state message action_label state :=
    {| gns_node_state := node.init; gns_trace := []; gns_queue := [] |}.

  Definition initial_graph_nodes : gmap :=
    map_values' (fun _ _ => graph_node_init) graph_prog.

  Definition initial_graph_state :=
    {| graph_nodes := initial_graph_nodes; graph_output_queue := @nil message |}.

  Lemma initial_graph_state_get n gns :
    map.get initial_graph_state.(graph_nodes) n = Some gns ->
    exists np, map.get graph_prog n = Some np /\ gns = graph_node_init.
  Proof.
    cbv [initial_graph_state initial_graph_nodes]. cbn [graph_nodes]. rewrite get_map_values'.
    destruct (map.get graph_prog n); simpl; intros; fwd; try discriminate; eauto.
  Qed.

  Lemma initial_graph_state_empty n gns :
    map.get initial_graph_state.(graph_nodes) n = Some gns ->
    gns.(gns_trace) = [] /\ gns.(gns_queue) = [].
  Proof. intros H. apply initial_graph_state_get in H. fwd. auto. Qed.

  Lemma nallowed_multiset_monotone : multiset_monotone_dec nallowed.
  Proof. intros l1 l2 Hl2 Hsub. eapply node.allowed_inputs_submultiset; eauto. Qed.

  Lemma nstep_input_total n : input_total (nstep n).
  Proof. intros s m. eexists. apply node.input_step. Qed.

  Lemma node_outputs_well_formed k p :
    map.get graph_prog k = Some p ->
    outputs_well_formed (node.step R_senders p (node_source k))
      (good_node_output forward claim_output consistent_output allowed_output k) node.init.
  Proof.
    intros Hget t s Hstar dest. set (name := node_source k) in *.
    pose proof (node.sent_eq_outputs _ _ _ _ _ Hstar) as Hso.
    pose proof (node.sent_source_correct _ _ _ _ _ Hstar) as Hsrc.
    pose proof (node.sent_counts_correct _ _ _ _ _ Hstar) as Hcnt.
    rewrite <- Hso. split.
    - cbv [allowed_output]. split.
      + intros pat src cnt Hin. apply filter_In in Hin. destruct Hin as (Hin_sent & _).
        specialize (Hsrc _ _ _ Hin_sent). subst. split; [reflexivity|].
        apply Existsn_le_filter. eapply Existsn_le_of_Existsn; [eauto | lia].
      + intros f Hin. apply filter_In in Hin. destruct Hin as (Hin_sent & _).
        eapply node.sent_rel_sender; [| exact Hstar | exact Hin_sent].
        intros ? ? Hcd. apply node.can_deduce_concl_rel in Hcd. eauto using node_sends_concl_rels.
    - intros pat Hclaim Hn. cbv [claim_output consistent_output] in *. specialize (Hclaim Hn). fwd.
      exists cnt. split; [assumption|]. apply filter_In in Hclaim. destruct Hclaim as (Hsent & Hfwd).
      apply Existsn_ge_filter.
      + intros f Hf. rewrite (forward_rel_level _ _ f (message.done_with pat name cnt)); [exact Hfwd|].
        destruct f as [nf |]; [| destruct Hf]. destruct Hf as (Hrel & _). cbn [message.rel]. congruence.
      + eapply Existsn_ge_of_Existsn; [eauto | lia].
  Qed.

  Lemma nodes_good_holds :
    Forall_map (node_good forward message.equiv claim claim_output consistent_output allowed_output
                  consistent nallowed nstep) initial_graph_state.(graph_nodes).
  Proof.
    intros k v Hkv. apply initial_graph_state_get in Hkv. fwd.
    pose proof node.might_implies_will' as H. especialize H; eauto.
    apply miw'_iff_miw_and_monotone' in H; auto. fwd.
    cbv [node_good graph_node_init gns_node_state]. erewrite prog_at_get by eassumption.
    ssplit; try eassumption. apply node_outputs_well_formed; eassumption.
  Qed.

  Definition distributed_step := graph_step forward nstep.

  Theorem distributed_might_implies_will :
    might_implies_will_equiv distributed_step message.equiv
      (graph_inputs_allowed forward allowed_output) initial_graph_state.
  Proof.
    intros.
    pose proof initial_graph_state_empty as Hemp.
    assert (Hoq : initial_graph_state.(graph_output_queue) = []) by reflexivity.
    eapply graph_might_implies_will; try eassumption.
    - exact message.equiv_Equivalence.
    - exact forward_equiv.
    - exact (node.claim_mono R_senders).
    - exact claim_output_mono.
    - exact (node.consistent_mono R_senders).
    - exact consistent_output_mono.
    - exact consistent_good_holds.
    - exact nallowed_multiset_monotone.
    - exact allowed_output_submultiset.
    - exact allowed_of_outputs.
    - exact nstep_input_total.
    - exact nodes_good_holds.
  Qed.

End Distributed.
