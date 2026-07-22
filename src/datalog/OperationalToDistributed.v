From Stdlib Require Import List PeanoNat Lia Permutation Classical_Prop.
From Datalog Require Import Datalog Node Operational Smallstep Graph List Distributed.
From coqutil Require Import Map.Interface.
From coqutil Require Import Semantics.OmniSmallstepCombinators.
Import ListNotations.

Section __.
  Context {rel : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.
  Context (is_input : rel -> bool).
  Context (p : prog).
  Context (Hp_input : Forall (good_non_meta_rule is_input) p.(non_meta_rules)).
  Context (Hmeta_rules : meta_rules_valid (rules_of p)).
  Context (Hp_meta_input : Forall (good_meta_rule_inputs is_input) p.(meta_rules)).

  Context {graph_state : map.map node_id (graph_node_state dfact dfact_mod_count Node.node_state)}.
  Context {graph_state_ok : map.ok graph_state}.

  Local Notation R_senders := (Operational.R_senders is_input p).
  Local Notation ok_to_deduce_fact := (Node.ok_to_deduce_fact R_senders).
  Local Notation new_facts := (Node.new_facts R_senders).
  Local Notation fire_at_rule := (Operational.fire_at_rule is_input p).

  Definition node_rules_of (r : non_meta_rule) : list rule :=
    rule_of r :: map (fun '(c, h) => meta_rule c h) p.(meta_rules).

  Definition to_node_state (rs : node_state) : Node.node_state :=
    {| Node.known_facts := rs.(Operational.known_facts);
       Node.sent_facts := rs.(Operational.sent_facts) |}.

  Definition node_states_agree (rs : node_state)
    (gns : graph_node_state dfact dfact_mod_count Node.node_state) : Prop :=
    Permutation rs.(Operational.known_facts) gns.(gns_node_state).(Node.known_facts) /\
      Permutation rs.(Operational.sent_facts) gns.(gns_node_state).(Node.sent_facts) /\
      Permutation rs.(Operational.waiting_facts) gns.(gns_queue).

  Definition op_graph_equiv (ops : Operational.state) (gs : graph_state) : Prop :=
    forall n,
      match nth_error ops n, map.get gs n with
      | Some rs, Some gns => node_states_agree rs gns
      | None, None => True
      | _, _ => False
      end.

  (* Every deduced fact is broadcast to all nodes (including the deducer itself,
     matching [comp_step]'s [map (add_waiting_fact _)]). *)
  Definition forward (n : node_id) (m : dfact) : list node_id :=
    seq 0 (length p.(non_meta_rules)).

  (* External inputs are restricted here (so the graph's [A] can be total). *)
  Definition input_allowed (n : node_id) (m : dfact) : bool :=
    is_input_fact is_input m.

  Definition output_visible (n : node_id) (m : dfact) : bool := true.

  Definition A : list dfact -> Prop := fun _ => True.


  (* ---- Obvious equivalence to comp_step (delivery-as-stutter collapse). ---- *)

  (* [ok_to_deduce_fact] is vacuously true for any meta rule: a meta rule never
     deduces a normal fact ([non_meta_rule_impl] has no meta-rule constructor),
     so the only nontrivial side condition is the one on [rule_of r]. *)
  Lemma ok_to_deduce_meta (c h : list meta_clause) known sent f :
    ok_to_deduce_fact (meta_rule c h) known sent f.
  Proof.
    destruct f as [R args | R args src num].
    - exact I.
    - intros nf_args Hcdn _. destruct Hcdn as (hyps & Himpl & _). inversion Himpl.
  Qed.

  (* A node's deduce step is exactly a [fire_at_rule] at that rule. *)
  Lemma new_facts_iff_fire (r : non_meta_rule) (n : nat) (rs : node_state) (f : dfact) :
    new_facts (node_rules_of r) n (to_node_state rs) f <->
    fire_at_rule r n rs (send_fact f rs) f.
  Proof.
    unfold Node.new_facts, node_rules_of, to_node_state, Operational.fire_at_rule,
      can_fire_rule_at; cbn [Node.known_facts Node.sent_facts].
    split.
    - intros (Hex & Hall).
      pose proof (Forall_inv Hall) as Hok_hd.
      apply Exists_cons in Hex.
      destruct Hex as [Hhd | Htl].
      + exists (rule_of r).
        split; [left; reflexivity|]. split; [exact Hhd|]. split; [exact Hok_hd | reflexivity].
      + apply Exists_exists in Htl as (r' & Hin & Hcd).
        apply in_map_iff in Hin as ((c & h) & Heq & Hinm). subst r'.
        exists (meta_rule c h).
        split; [right; exists c, h; split; [exact Hinm | reflexivity]|].
        split; [exact Hcd|]. split; [exact Hok_hd | reflexivity].
    - intros (fired & Hfire & Hcd & Hok & _). split.
      + apply Exists_cons. destruct Hfire as [-> | (mc & mh & Hin & ->)].
        * left. exact Hcd.
        * right. apply Exists_exists. exists (meta_rule mc mh). split; [|exact Hcd].
          apply in_map_iff. exists (mc, mh). split; [reflexivity | exact Hin].
      + apply Forall_cons; [exact Hok |].
        apply Forall_forall. intros r' Hin.
        apply in_map_iff in Hin as ((c & h) & Heq & _). subst r'. apply ok_to_deduce_meta.
  Qed.

  (* Learning an input fact: Node.v's [node_input_step] moves the received fact
     into [known]; Operational.v realises the same move as a [learn_fact_at_rule]
     that dequeues it from [waiting_facts]. *)
  Lemma dequeue_learn (rs : node_state) (input : dfact) (rest : list dfact) :
    rs.(waiting_facts) = input :: rest ->
    learn_fact_at_rule rs
      {| known_facts := input :: rs.(known_facts);
        waiting_facts := rest;
        sent_facts := rs.(sent_facts) |}.
  Proof.
    intros Hwait. unfold learn_fact_at_rule. exists (@nil dfact), input, rest.
    cbn. rewrite Hwait. repeat split; reflexivity.
  Qed.

End __.
