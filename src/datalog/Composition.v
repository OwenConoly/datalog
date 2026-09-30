From Stdlib Require Import List.
From coqutil Require Import Map.Interface Eqb.
From Datalog Require Import Datalog Node Operational Smallstep Graph List Distributed Map Relations OperationalToDistributed.

Import ListNotations.
Import node.

Section __.
  Context `{params : datalog_params}.
  Context {rel_eqb : Eqb rel} {rel_eqb_ok : Eqb_ok rel_eqb}.
  Context (is_input : rel -> bool).
  Context (p : program).
  Context (Hmeta_rules : program.meta_rules_valid p).
  Context (Hp_good : Forall (fun R => is_input R = false) (program.concl_rels p)).
  Context (Hrules : 0 < length p.(program.rules)).

  #[local] Instance sender_label : sender_labelT := source.

  Context {prog_map : map.map node_id program} {prog_map_ok : map.ok prog_map}.
  Context {gns_map : map.map node_id (graph_node_state message action_label state)} {gns_map_ok : map.ok gns_map}.
  Context {msg_map : map.map node_id (list message)} {msg_map_ok : map.ok msg_map}.

  Context (graph_prog : prog_map).
  Context (Hgraph_good : Forall_map (fun _ np => Forall (fun R => is_input R = false) (program.concl_rels np)) graph_prog).
  Context (NoDup_all_rules : NoDup (all_rules graph_prog)).
  Context (Hlayout_normal : graph_prog_distributes_normal_rules graph_prog p).
  Context (Hlayout_meta : graph_prog_distributes_meta_rules graph_prog p).

  Context (inputs : list message).
  Context (Hinputs : outputs_ok_from is_input graph_prog input_source inputs).
  Context (Hinputs_rel : Forall (fun m => is_input (message.rel m) = true) inputs).

  Local Abbreviation graph_senders := (Distributed.R_senders graph_prog is_input).
  Local Abbreviation comp_step := (Operational.comp_step is_input p).
  Local Abbreviation distributed_step := (Distributed.distributed_step graph_prog is_input).
  Local Abbreviation initial_graph_state_with := (Distributed.initial_graph_state_with graph_prog).

  Lemma op_inputs_good : good_input_facts is_input (map op_input_of_input inputs).
  Proof.
    cbv [good_input_facts]. rewrite Lists.List.Forall_map.
    eapply Forall_impl; [exact Hinputs_rel|]. intros [nf | pat src num] Hm; exact Hm.
  Qed.

  Lemma layout_sound gs t f :
    star distributed_step (initial_graph_state_with inputs) t gs ->
    flat_map inputs_of t = [] ->
    knows_fact graph_senders (flat_map outputs_of t) f ->
    exists os, comp_step^* (map op_input_of_input inputs) os /\ op_knows_fact is_input p os f.
  Proof. Admitted.

  Theorem interp_iff_distributed f :
    program.interp p (op_knows_fact is_input p (map op_input_of_input inputs)) f <->
    exists gs t,
      star distributed_step (initial_graph_state_with inputs) t gs /\
        flat_map inputs_of t = [] /\
        knows_fact graph_senders (flat_map outputs_of t) f.
  Proof.
    rewrite (prog_impl_iff_comp_step _ _ Hmeta_rules Hp_good Hrules _ op_inputs_good). split.
    - intros (os & Hsteps & Hknows). eapply layout_complete; eassumption.
    - intros (gs & t & Hstar & Ht & Hknows). eapply layout_sound; eassumption.
  Qed.
End __.
