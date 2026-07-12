(* Operational-to-distributed glue.

   This file connects a concrete datalog program [p] to the purely-distributed
   per-node semantics of Distributed.v.  It builds the graph program from [p] (one
   node per non-meta rule via [node_prog_of], with a broadcast [forward]) and
   proves the "very obviously equivalent to comp_step" facts: a node's deduce step
   is exactly a [fire_at_rule] ([new_facts_iff_fire]) and a node's dequeue step is
   a [learn_fact_at_rule] ([dequeue_learn]), under the delivery-as-stutter collapse
   that reads a node's [waiting_facts] as its queue together with the messages in
   flight to it.  The purely-distributed content -- the per-node liveness theorem
   [spec_node_can_implies_will] for an arbitrary [spec_node_prog] -- lives in
   Distributed.v. *)

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
  Context (R_senders : rel -> list nat).
  Context (p : prog).
  (* Standing program well-formedness (as in Operational), inherited as the
     assumptions of this operational-to-distributed layer. *)
  Context (Hp_input : Forall (good_non_meta_rule is_input) p.(non_meta_rules)).
  Context (Hmeta_rules : meta_rules_valid (rules_of p)).
  Context (Hp_meta_input : Forall (good_meta_rule_inputs is_input) p.(meta_rules)).

  Local Notation can_deduce_fact := (can_deduce_fact is_input R_senders).
  Local Notation can_deduce_normal_fact := (can_deduce_normal_fact is_input R_senders).
  Local Notation ok_to_deduce_fact := (ok_to_deduce_fact is_input R_senders).
  Local Notation fire_at_rule := (fire_at_rule is_input R_senders p).
  Local Notation new_facts := (Node.new_facts is_input R_senders).

  (* ---- The graph program built from [p]. ---- *)

  (* Node [n] runs the [n]-th non-meta rule together with all of [p]'s meta rules;
     [spec_node_label := n] is the node's id, used as the "source" in meta facts. *)
  Definition node_prog_of (r : non_meta_rule) (n : nat) : spec_node_prog :=
    {| spec_node_rules :=
        rule_of r :: map (fun '(c, h) => meta_rule c h) p.(meta_rules);
      spec_node_label := n |}.

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
    new_facts (node_prog_of r n) rs f <->
    fire_at_rule r n rs (send_fact f rs) f.
  Proof.
    unfold Node.new_facts, node_prog_of, fire_at_rule, Operational.fire_at_rule,
      can_fire_rule_at; cbn [spec_node_rules spec_node_label].
    split.
    - intros (Hex & Hall).
      apply Exists_cons in Hex.
      assert (Hok_hd : ok_to_deduce_fact (rule_of r) rs.(known_facts) rs.(sent_facts) f)
        by (inversion Hall; subst; assumption).
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

  (* A node's dequeue step is a [learn_fact_at_rule] (moving the queue head into
     [known]); the queue is the node's [waiting_facts]. *)
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
