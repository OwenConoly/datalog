(* Distributed (graph) semantics for a datalog program.

   The per-node step relation [spec_node_step] is moved here from Local.v and
   adapted to the labelled [IO_event] of Smallstep.v.  A datalog program [p] is
   turned into a graph program: one node per non-meta rule, each node running
   [spec_node_step] over the rule plus all of [p]'s meta rules, with a broadcast
   [forward].  This graph is meant to replace [comp_step_with_label] as the IO
   step relation; [can_implies_will] for it follows from [graph_can_implies_will]
   in Graph.v.

   The graph is "very obviously equivalent" to [comp_step]: a node's deduce step
   is exactly [fire_at_rule] ([new_facts_iff_fire]) and a node's dequeue step is a
   [learn_fact_at_rule] ([dequeue_learn]), under the collapse that reads a rule's
   [waiting_facts] as its queue together with the messages in flight to it
   (delivery being a stutter). *)

From Stdlib Require Import List PeanoNat.
From Datalog Require Import Datalog Operational Smallstep Graph.
From coqutil Require Import Map.Interface.
Import ListNotations.

Section __.
  Context {rel : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.
  Context (is_input : rel -> bool).
  Context (R_senders : rel -> list nat).
  Context (p : prog).

  Local Notation can_deduce_fact := (can_deduce_fact is_input R_senders).
  Local Notation ok_to_deduce_fact := (ok_to_deduce_fact is_input R_senders).
  Local Notation fire_at_rule := (fire_at_rule is_input R_senders p).

  (* ---- Per-node spec state and step (moved from Local.v, now labelled). ---- *)

  Record spec_node_state :=
    { known_facts : list dfact;
      sent_facts : list dfact }.

  Definition empty_spec_state :=
    {| known_facts := []; sent_facts := [] |}.

  Record spec_node_prog :=
    { spec_node_rules : list rule;
      spec_node_label : nat }.

  Definition new_facts (sp : spec_node_prog) (ss : spec_node_state) f :=
    Exists
      (fun r => can_deduce_fact r sp.(spec_node_label) ss.(known_facts) ss.(sent_facts) f)
      sp.(spec_node_rules) /\
      Forall
        (fun r => ok_to_deduce_fact r ss.(known_facts) f)
        sp.(spec_node_rules).

  Definition spec_input_fact ss f :=
    {| known_facts := f :: ss.(known_facts);
      sent_facts := ss.(sent_facts) |}.

  Definition spec_output_fact ss f :=
    {| known_facts := ss.(known_facts);
      sent_facts := f :: ss.(sent_facts) |}.

  (* "big" because it contains the node, plus its message queue. *)
  Record big_spec_state :=
    { bss_spec_node : spec_node_state;
      bss_queue : list dfact }.

  Definition empty_big_spec_state :=
    {| bss_spec_node := empty_spec_state;
      bss_queue := [] |}.

  (* A node's own labels: dequeue one queued message into [known] (always from the
     front, so unambiguous), or deduce and broadcast a new fact (recorded in the
     label). *)
  Variant spec_label :=
    | sl_dequeue
    | sl_deduce (f : dfact).

  Local Notation IO_event := (Smallstep.IO_event spec_label dfact).

  Inductive spec_node_step (sp : spec_node_prog) : big_spec_state -> IO_event -> big_spec_state -> Prop :=
  | spec_node_dequeue_step bss input rest :
    bss.(bss_queue) = input :: rest ->
    spec_node_step sp bss (O_event sl_dequeue [])
                   {| bss_spec_node := spec_input_fact bss.(bss_spec_node) input;
                     bss_queue := rest |}
  | spec_node_deduce_step bss output :
    new_facts sp bss.(bss_spec_node) output ->
    spec_node_step sp bss (O_event (sl_deduce output) [output])
                   {| bss_spec_node := spec_output_fact bss.(bss_spec_node) output;
                     bss_queue := bss.(bss_queue) ++ [output] |}
  | spec_node_input_step bss input :
    spec_node_step sp bss (I_event input)
                   {| bss_spec_node := bss.(bss_spec_node);
                     bss_queue := bss.(bss_queue) ++ [input] |}.

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

  (* The rule_state a node's (state, queue) collapses to. *)
  Definition rs_of (ss : spec_node_state) (q : list dfact) : rule_state :=
    {| Operational.known_facts := ss.(known_facts);
      Operational.waiting_facts := q;
      Operational.sent_facts := ss.(sent_facts) |}.

  (* [ok_to_deduce_fact] is vacuously true for any meta rule: a meta rule never
     deduces a normal fact ([non_meta_rule_impl] has no meta-rule constructor),
     so the only nontrivial side condition is the one on [rule_of r]. *)
  Lemma ok_to_deduce_meta (c h : list meta_clause) known f :
    ok_to_deduce_fact (meta_rule c h) known f.
  Proof.
    destruct f as [R args | R args src num].
    - exact I.
    - intros nf_args Hcdn _. destruct Hcdn as (hyps & Himpl & _). inversion Himpl.
  Qed.

  (* A node's deduce step is exactly a [fire_at_rule] at that rule. *)
  Lemma new_facts_iff_fire (r : non_meta_rule) (n : nat) (ss : spec_node_state) (q : list dfact) (f : dfact) :
    new_facts (node_prog_of r n) ss f <->
    fire_at_rule r n (rs_of ss q) (send_fact f (rs_of ss q)) f.
  Proof.
    unfold new_facts, node_prog_of, fire_at_rule, Operational.fire_at_rule,
      can_fire_rule_at; cbn [spec_node_rules spec_node_label].
    split.
    - intros (Hex & Hall).
      apply Exists_cons in Hex.
      assert (Hok_hd : ok_to_deduce_fact (rule_of r) (rs_of ss q).(Operational.known_facts) f)
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
     [known]); under the collapse the queue is the rule's [waiting_facts]. *)
  Lemma dequeue_learn (ss : spec_node_state) (input : dfact) (rest : list dfact) :
    learn_fact_at_rule (rs_of ss (input :: rest)) (rs_of (spec_input_fact ss input) rest).
  Proof.
    unfold learn_fact_at_rule, rs_of, spec_input_fact; cbn.
    exists (@nil dfact), input, rest. cbn. repeat split; reflexivity.
  Qed.

End __.
