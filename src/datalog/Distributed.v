(* Distributed (graph) semantics for a datalog program.

   The per-node step relation [spec_node_step] is moved here from Local.v and
   adapted to the labelled [IO_event] of Smallstep.v.  A node's state is exactly
   Operational's [node_state], with [waiting_facts] serving as the node's incoming
   message queue.  A datalog program [p] is turned into a graph program: one node
   per non-meta rule, each node running [spec_node_step] over that rule plus all of
   [p]'s meta rules, with a broadcast [forward].  This graph is meant to replace
   [comp_step_with_label] as the IO step relation; [can_implies_will] for it
   follows from [graph_can_implies_will] in Graph.v.

   The graph is "very obviously equivalent" to [comp_step]: a node's deduce step is
   exactly [fire_at_rule] ([new_facts_iff_fire]) and a node's dequeue step is a
   [learn_fact_at_rule] ([dequeue_learn]), under the collapse that reads a node's
   [waiting_facts] as its queue together with the messages in flight to it
   (delivery being a stutter). *)

From Stdlib Require Import List PeanoNat Lia Permutation.
From Datalog Require Import Datalog Operational Smallstep Graph List.
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
  (* Standing program well-formedness (as in Operational): non-meta rules never
     conclude input relations.  Needed so a derivable fact is non-input, hence
     "known ⇒ already output". *)
  Context (Hp_input : Forall (good_non_meta_rule is_input) p.(non_meta_rules)).

  Local Notation can_deduce_fact := (can_deduce_fact is_input R_senders).
  Local Notation ok_to_deduce_fact := (ok_to_deduce_fact is_input R_senders).
  Local Notation fire_at_rule := (fire_at_rule is_input R_senders p).

  (* ---- Per-node spec step (moved from Local.v, now labelled and over
     Operational's [node_state]). ---- *)

  Record spec_node_prog :=
    { spec_node_rules : list rule;
      spec_node_label : nat }.

  Definition new_facts (sp : spec_node_prog) (rs : node_state) f :=
    Exists
      (fun r => can_deduce_fact r sp.(spec_node_label) rs.(known_facts) rs.(sent_facts) f)
      sp.(spec_node_rules) /\
      Forall
        (fun r => ok_to_deduce_fact r rs.(known_facts) f)
        sp.(spec_node_rules).

  (* A node's own labels: dequeue one queued message into [known] (always from the
     front, so unambiguous), or deduce and broadcast a new fact (recorded in the
     label). *)
  Variant spec_label :=
    | sl_dequeue
    | sl_deduce (f : dfact).

  Local Notation IO_event := (Smallstep.IO_event spec_label dfact).

  Inductive spec_node_step (sp : spec_node_prog) : node_state -> IO_event -> node_state -> Prop :=
  | spec_node_dequeue_step rs input rest :
    rs.(waiting_facts) = input :: rest ->
    spec_node_step sp rs (O_event sl_dequeue [])
                   {| known_facts := input :: rs.(known_facts);
                     waiting_facts := rest;
                     sent_facts := rs.(sent_facts) |}
  | spec_node_deduce_step rs output :
    new_facts sp rs output ->
    spec_node_step sp rs (O_event (sl_deduce output) [output])
                   {| known_facts := rs.(known_facts);
                     waiting_facts := rs.(waiting_facts);
                     sent_facts := output :: rs.(sent_facts) |}
  | spec_node_input_step rs input :
    spec_node_step sp rs (I_event input)
                   {| known_facts := rs.(known_facts);
                     waiting_facts := rs.(waiting_facts) ++ [input];
                     sent_facts := rs.(sent_facts) |}.

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

  (* The per-node [allowed].  A node also receives internal (non-input) messages,
     so — unlike the graph as a whole — there is NO [is_input] restriction here;
     the only requirement is that the declared "expect num" meta-facts among the
     inputs are consistent (agree on their count, and never under-count the
     matching facts present).  This is [good_input_facts] minus the [is_input]
     conjunct. *)
  Definition consistent_inputs (input_facts : list dfact) : Prop :=
    (* [None]-declarations (expectations for input relations): unique count, and the
       matching facts present never exceed it. *)
    (forall R mf_args num,
        In (meta_dfact R mf_args None num) input_facts ->
        (forall num0, In (meta_dfact R mf_args None num0) input_facts -> num0 = num) /\
          exists num', num' <= num /\ Existsn (dfact_matches R mf_args) num' input_facts)
    /\
    (* [Some k]-declarations (done-sending from node k): unique count per sender. *)
    (forall R mf_args k num num0,
        In (meta_dfact R mf_args (Some k) num) input_facts ->
        In (meta_dfact R mf_args (Some k) num0) input_facts -> num0 = num)
    /\
    (* and the matching facts present never exceed the sum of the per-sender
       done-sending counts (bounds non-input aggregates). *)
    (forall R mf_args expected_msgss,
        Forall2 (fun k e => In (meta_dfact R mf_args (Some k) e) input_facts)
                (R_senders R) expected_msgss ->
        exists num', num' <= fold_left Nat.add expected_msgss 0 /\
                     Existsn (dfact_matches R mf_args) num' input_facts).

  (* ---- Obvious equivalence to comp_step (delivery-as-stutter collapse). ---- *)

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
  Lemma new_facts_iff_fire (r : non_meta_rule) (n : nat) (rs : node_state) (f : dfact) :
    new_facts (node_prog_of r n) rs f <->
    fire_at_rule r n rs (send_fact f rs) f.
  Proof.
    unfold new_facts, node_prog_of, fire_at_rule, Operational.fire_at_rule,
      can_fire_rule_at; cbn [spec_node_rules spec_node_label].
    split.
    - intros (Hex & Hall).
      apply Exists_cons in Hex.
      assert (Hok_hd : ok_to_deduce_fact (rule_of r) rs.(known_facts) f)
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

  (* ---- Forcing toolkit: drive a queued fact into [known] against the demon. ---- *)

  (* [known_facts] only grows under any node step / run. *)
  Lemma spec_step_known_incl sp s e s' :
    spec_node_step sp s e s' -> incl s.(known_facts) s'.(known_facts).
  Proof.
    inversion 1; subst; cbn [known_facts].
    - apply incl_tl. apply incl_refl.
    - apply incl_refl.
    - apply incl_refl.
  Qed.

  Lemma spec_steps_known_incl sp s td s' :
    star (spec_node_step sp) s td s' -> incl s.(known_facts) s'.(known_facts).
  Proof.
    induction 1 as [|s0 e s1 t0 s2 Hstep Hstar IH].
    - apply incl_refl.
    - eapply incl_tran; [eapply spec_step_known_incl; exact Hstep | exact IH].
  Qed.

  (* [sent_facts] only grows. *)
  Lemma spec_step_sent_incl sp s e s' :
    spec_node_step sp s e s' -> incl s.(sent_facts) s'.(sent_facts).
  Proof.
    inversion 1; subst; cbn [sent_facts].
    - apply incl_refl.
    - apply incl_tl. apply incl_refl.
    - apply incl_refl.
  Qed.

  Lemma spec_steps_sent_incl sp s td s' :
    star (spec_node_step sp) s td s' -> incl s.(sent_facts) s'.(sent_facts).
  Proof.
    induction 1 as [|s0 e s1 t0 s2 Hstep Hstar IH].
    - apply incl_refl.
    - eapply incl_tran; [eapply spec_step_sent_incl; exact Hstep | exact IH].
  Qed.

  (* [known ∪ waiting] only grows (a dequeue moves a fact between the two). *)
  Lemma spec_step_kw_incl sp s e s' :
    spec_node_step sp s e s' ->
    incl (s.(known_facts) ++ s.(waiting_facts)) (s'.(known_facts) ++ s'.(waiting_facts)).
  Proof.
    inversion 1 as [rs input rest Hq | rs out Hnf | rs inp]; subst;
      cbn [known_facts waiting_facts].
    - rewrite Hq. intros x Hx. apply in_app_or in Hx. destruct Hx as [Hk | Hir].
      + apply in_cons. apply in_or_app. left. exact Hk.
      + cbn [In] in Hir. destruct Hir as [Heq | Hr].
        * subst x. apply in_eq.
        * apply in_cons. apply in_or_app. right. exact Hr.
    - apply incl_refl.
    - intros x Hx. apply in_app_or in Hx. apply in_or_app.
      destruct Hx as [Hk | Hw]; [left; exact Hk | right; apply in_or_app; left; exact Hw].
  Qed.

  Lemma spec_steps_kw_incl sp s td s' :
    star (spec_node_step sp) s td s' ->
    incl (s.(known_facts) ++ s.(waiting_facts)) (s'.(known_facts) ++ s'.(waiting_facts)).
  Proof.
    induction 1 as [|s0 e s1 t0 s2 Hstep Hstar IH].
    - apply incl_refl.
    - eapply incl_tran; [eapply spec_step_kw_incl; exact Hstep | exact IH].
  Qed.

  (* [known] only ever grows by prepending: a later [known] is a suffix-extension. *)
  Lemma known_suffix sp s td s' :
    star (spec_node_step sp) s td s' ->
    exists pre, s'.(known_facts) = pre ++ s.(known_facts).
  Proof.
    induction 1 as [s0 | s0 e s1 t0 s2 Hstep Hstar IH].
    - exists []. reflexivity.
    - destruct IH as (pre & Hpre).
      inversion Hstep as [rs input rest Hq | rs out Hnf | rs inp]; subst;
        cbn [known_facts] in Hpre |- *.
      + exists (pre ++ [input]). rewrite Hpre, <- app_assoc. reflexivity.
      + exists pre. exact Hpre.
      + exists pre. exact Hpre.
  Qed.

  (* Multiset invariant: a node's [known ∪ waiting] is exactly the multiset of
     facts it has been sent (its trace's inputs).  This bounds the matching-fact
     counts via the inputs. *)
  Lemma kw_perm_step sp s e s' tr :
    Permutation (s.(known_facts) ++ s.(waiting_facts)) (inputs_of tr) ->
    spec_node_step sp s e s' ->
    Permutation (s'.(known_facts) ++ s'.(waiting_facts)) (inputs_of (e :: tr)).
  Proof.
    intros Hperm Hstep.
    inversion Hstep as [rs input rest Hq | rs out Hnf | rs inp]; subst;
      cbn [known_facts waiting_facts]; cbn [inputs_of flat_map].
    - (* dequeue: [input] moves from waiting to known; trace inputs unchanged *)
      rewrite Hq in Hperm. cbn [app].
      eapply perm_trans; [| exact Hperm].
      apply Permutation_middle.
    - (* deduce: nothing moves *)
      exact Hperm.
    - (* input: both [known∪waiting] and trace inputs gain [inp] *)
      rewrite app_assoc.
      eapply perm_trans;
        [apply Permutation_sym; apply Permutation_cons_append
        | apply perm_skip; exact Hperm].
  Qed.

  Lemma kw_perm_star sp s td s' tr :
    Permutation (s.(known_facts) ++ s.(waiting_facts)) (inputs_of tr) ->
    star (spec_node_step sp) s td s' ->
    Permutation (s'.(known_facts) ++ s'.(waiting_facts)) (inputs_of (rev td ++ tr)).
  Proof.
    intros Hperm Hstar. revert tr Hperm.
    induction Hstar as [s0 | s0 e s1 t0 s2 Hstep Hstar IH]; intros tr Hperm; cbn [rev].
    - cbn [app]. exact Hperm.
    - rewrite <- app_assoc. cbn [app].
      apply IH. apply (kw_perm_step sp s0 e s1 tr Hperm Hstep).
  Qed.

  (* One step keeps a queued [g] either in [known] or still queued, with its
     prefix never longer (the demon can only dequeue from the front / append to
     the back). *)
  Lemma spec_step_waiting_form sp g s e s' pre post :
    s.(waiting_facts) = pre ++ g :: post ->
    spec_node_step sp s e s' ->
    In g s'.(known_facts) \/
    exists pre' post', s'.(waiting_facts) = pre' ++ g :: post' /\ length pre' <= length pre.
  Proof.
    intros Hw Hstep.
    inversion Hstep as [rs input rest Hq | rs out Hnf | rs inp]; subst;
      cbn [known_facts waiting_facts].
    - rewrite Hw in Hq. destruct pre as [|y pre']; cbn [app] in Hq.
      + injection Hq as Hg Hr. subst. left. apply in_eq.
      + injection Hq as Hy Hr. subst. right. exists pre', post.
        split; [reflexivity | cbn [length]; lia].
    - right. exists pre, post. split; [exact Hw | apply le_n].
    - right. exists pre, (post ++ [inp]).
      rewrite Hw, <- app_assoc. split; [reflexivity | apply le_n].
  Qed.

  Lemma waiting_form_star sp g :
    forall s pre post td sdem,
      s.(waiting_facts) = pre ++ g :: post ->
      star (spec_node_step sp) s td sdem ->
      In g sdem.(known_facts) \/
      exists pre' post', sdem.(waiting_facts) = pre' ++ g :: post' /\ length pre' <= length pre.
  Proof.
    intros s pre post td sdem Hw Hstar. revert pre post Hw.
    induction Hstar as [s0 | s0 e s1 t0 s2 Hstep Hstar IH]; intros pre post Hw.
    - right. exists pre, post. split; [exact Hw | apply le_n].
    - destruct (spec_step_waiting_form sp g s0 e s1 pre post Hw Hstep)
        as [Hin | (pre1 & post1 & Hw1 & Hle1)].
      + left. apply (spec_steps_known_incl sp s1 t0 s2 Hstar). exact Hin.
      + destruct (IH pre1 post1 Hw1) as [Hin2 | (pre2 & post2 & Hw2 & Hle2)].
        * left. exact Hin2.
        * right. exists pre2, post2. split; [exact Hw2 | lia].
  Qed.

  (* If [g] is queued (split as [pre ++ g :: post]), the node can be forced to
     learn it: commit [sl_dequeue] each round; the demon can only shrink [g]'s
     prefix, so induction on [length pre] terminates. *)
  Lemma force_into_known sp g :
    forall n s pre post t,
      length pre <= n ->
      s.(waiting_facts) = pre ++ g :: post ->
      eventually (can_step (spec_node_step sp) (consistent_inputs))
                 (fun '(s'', _) => In g s''.(known_facts)) (s, t).
  Proof.
    intros n. induction n as [|n IH]; intros s pre post t Hlen Hw.
    - assert (pre = []) by (destruct pre; [reflexivity | cbn in Hlen; lia]). subst pre.
      apply eventually_step_cps. exists sl_dequeue. intros sdem tdem Hstar Hallowed.
      destruct (waiting_form_star sp g s [] post tdem sdem Hw Hstar)
        as [Hin | (pre' & post' & Hwd & Hle)].
      + left. apply eventually_done. cbn. exact Hin.
      + assert (pre' = []) by (destruct pre'; [reflexivity | cbn in Hle; lia]). subst pre'.
        cbn [app] in Hwd. right. eexists. exists (@nil dfact). split.
        * eapply spec_node_dequeue_step. exact Hwd.
        * apply eventually_done. cbn. apply in_eq.
    - apply eventually_step_cps. exists sl_dequeue. intros sdem tdem Hstar Hallowed.
      destruct (waiting_form_star sp g s pre post tdem sdem Hw Hstar)
        as [Hin | (pre' & post' & Hwd & Hle)].
      + left. apply eventually_done. cbn. exact Hin.
      + destruct pre' as [|y pre'']; cbn [app] in Hwd.
        * right. eexists. exists (@nil dfact). split.
          -- eapply spec_node_dequeue_step. exact Hwd.
          -- apply eventually_done. cbn. apply in_eq.
        * right. eexists. exists (@nil dfact). split.
          -- eapply spec_node_dequeue_step. exact Hwd.
          -- eapply (IH _ pre'' post' _).
             ++ cbn [length] in Hle. lia.
             ++ cbn [waiting_facts]. reflexivity.
  Qed.

  (* Every fact a node knows or has queued was either received as input or emitted
     as an output: [known ∪ waiting ⊆ inputs(trace) ∪ outputs(trace)].  This lets
     us conclude that a known non-input fact has actually been output. *)
  Definition traces_account (s : node_state)
      (tr : list (Smallstep.IO_event spec_label dfact)) : Prop :=
    forall f, In f s.(known_facts) \/ In f s.(waiting_facts) ->
              In f (inputs_of tr) \/ output_in_trace f tr.

  Lemma traces_account_step sp s e s' tr :
    traces_account s tr -> spec_node_step sp s e s' -> traces_account s' (e :: tr).
  Proof.
    intros Hacc Hstep.
    assert (Hweak : forall g, In g (inputs_of tr) \/ output_in_trace g tr ->
                              In g (inputs_of (e :: tr)) \/ output_in_trace g (e :: tr)).
    { intros g [Hin | (lbl & outs & Hino & Hing)].
      - left. destruct e as [m | lbl0 outs0]; cbn; [right; exact Hin | exact Hin].
      - right. exists lbl, outs. split; [right; exact Hino | exact Hing]. }
    inversion Hstep as [rs input rest Hq | rs out Hnf | rs inp]; subst;
      intros f Hf; cbn [known_facts waiting_facts] in Hf.
    - apply Hweak. apply Hacc. destruct Hf as [[Heq | Hf] | Hf].
      + subst f. right. rewrite Hq. apply in_eq.
      + left. exact Hf.
      + right. rewrite Hq. apply in_cons. exact Hf.
    - destruct Hf as [Hf | Hf].
      + apply Hweak. apply Hacc. left. exact Hf.
      + apply Hweak. apply Hacc. right. exact Hf.
    - destruct Hf as [Hf | Hf].
      + apply Hweak. apply Hacc. left. exact Hf.
      + apply in_app_or in Hf. destruct Hf as [Hf | [Heq | []]].
        * apply Hweak. apply Hacc. right. exact Hf.
        * subst f. left. cbn [inputs_of flat_map]. apply in_eq.
  Qed.

  Lemma traces_account_star sp s td s' tr :
    traces_account s tr ->
    star (spec_node_step sp) s td s' ->
    traces_account s' (rev td ++ tr).
  Proof.
    intros Hacc Hstar. revert tr Hacc.
    induction Hstar as [s0 | s0 e s1 t0 s2 Hstep Hstar IH]; intros tr Hacc; cbn [rev].
    - cbn [app]. exact Hacc.
    - rewrite <- app_assoc. cbn [app].
      apply IH. apply (traces_account_step sp s0 e s1 tr Hacc Hstep).
  Qed.

  Lemma inputs_of_rev_mem (x : dfact) (l : list (Smallstep.IO_event spec_label dfact)) :
    In x (inputs_of (rev l)) <-> In x (inputs_of l).
  Proof.
    unfold inputs_of. rewrite !in_flat_map. split.
    - intros (a & Ha & Hx). exists a. split; [rewrite in_rev; exact Ha | exact Hx].
    - intros (a & Ha & Hx). exists a. split; [rewrite <- in_rev; exact Ha | exact Hx].
  Qed.

  (* traces_account at the actual run trace [td ++ tr] (the accumulated form is
     [rev td ++ tr]; bridge via membership, since traces_account only reads the
     trace's input/output membership). *)
  Lemma traces_account_run sp s td s' tr :
    traces_account s tr ->
    star (spec_node_step sp) s td s' ->
    traces_account s' (td ++ tr).
  Proof.
    intros Hacc Hstar.
    pose proof (traces_account_star sp s td s' tr Hacc Hstar) as Hrev.
    intros f Hf. specialize (Hrev f Hf). destruct Hrev as [Hin | Hout].
    - left. rewrite inputs_of_app in Hin |- *. apply in_app_or in Hin. apply in_or_app.
      destruct Hin as [Hin | Hin]; [left; apply inputs_of_rev_mem; exact Hin | right; exact Hin].
    - right. apply output_in_trace_app. apply output_in_trace_app in Hout.
      destruct Hout as [Hout | Hout];
        [left; apply output_in_trace_rev; exact Hout | right; exact Hout].
  Qed.

  (* Accounting: every output is recorded in [sent].  (With no self-enqueue a
     deduced fact is NOT placed in [known ∪ waiting], so we only track [sent];
     this is what we need to recover [sent]-domination after forcing a deduce.) *)
  Definition output_in_state (s : node_state) (tr : list IO_event) : Prop :=
    forall g, output_in_trace g tr -> In g s.(sent_facts).

  Lemma output_in_state_step sp s e s' tr :
    output_in_state s tr -> spec_node_step sp s e s' -> output_in_state s' (e :: tr).
  Proof.
    intros Hos Hstep g Hg.
    pose proof (spec_step_sent_incl sp s e s' Hstep) as Hsent.
    change (e :: tr) with ([e] ++ tr) in Hg. apply output_in_trace_app in Hg.
    destruct Hg as [Hhead | Htail].
    - destruct Hhead as (lbl & outs & Hin & Hing). cbn [In] in Hin. destruct Hin as [Heq | []].
      subst e. inversion Hstep; subst; cbn [sent_facts] in *.
      + cbn in Hing. contradiction.
      + cbn in Hing. destruct Hing as [-> | []]. apply in_eq.
    - apply Hsent. apply Hos. exact Htail.
  Qed.

  Lemma output_in_state_star sp s td s' tr :
    output_in_state s tr ->
    star (spec_node_step sp) s td s' -> output_in_state s' (rev td ++ tr).
  Proof.
    intros Hacc Hstar. revert tr Hacc.
    induction Hstar as [s0 | s0 e s1 t0 s2 Hstep Hstar IH]; intros tr Hacc; cbn [rev].
    - cbn [app]. exact Hacc.
    - rewrite <- app_assoc. cbn [app].
      apply IH. apply (output_in_state_step sp s0 e s1 tr Hacc Hstep).
  Qed.

  Lemma output_in_state_run sp s td s' tr :
    output_in_state s tr ->
    star (spec_node_step sp) s td s' -> output_in_state s' (td ++ tr).
  Proof.
    intros Hacc Hstar. pose proof (output_in_state_star sp s td s' tr Hacc Hstar) as Hrev.
    intros g Hg. apply Hrev. apply output_in_trace_app in Hg. apply output_in_trace_app.
    destruct Hg as [Hg | Hg];
      [left; rewrite output_in_trace_rev; exact Hg | right; exact Hg].
  Qed.

  (* Carry a state/trace invariant [R] (preserved by demon runs and by an output
     step) through an eventually.  Verbatim single-node analogue of Graph.v's
     eventually_carry_inv2. *)
  Lemma eventually_carry_inv2 sp (R : node_state -> list IO_event -> Prop) :
    (forall s tt t_d s_d, R s tt ->
       star (spec_node_step sp) s t_d s_d -> R s_d (t_d ++ tt)) ->
    (forall s tt glbl outs s', R s tt ->
       spec_node_step sp s (O_event glbl outs) s' -> R s' (O_event glbl outs :: tt)) ->
    forall (P : node_state * list IO_event -> Prop) s tt,
      R s tt ->
      eventually (can_step (spec_node_step sp) (consistent_inputs)) P (s, tt) ->
      eventually (can_step (spec_node_step sp) (consistent_inputs))
        (fun '(s', t') => P (s', t') /\ R s' t') (s, tt).
  Proof.
    intros Hstarp Hostep P s tt HR Hev.
    remember (s, tt) as st eqn:Est. revert s tt HR Est.
    induction Hev as [[s' t'] HP | [s' t'] midset Hcan Hmid IH];
      intros s tt HR [= -> ->].
    - apply eventually_done. split; [exact HP | exact HR].
    - destruct Hcan as [glbl Hcan].
      apply eventually_step_cps. exists glbl.
      intros s_d t_d Hstar_d Hallow.
      specialize (Hcan s_d t_d Hstar_d Hallow).
      destruct Hcan as [Hmid_left | (s'' & outs & Hstep & Hmidset)].
      + left. apply (IH (s_d, t_d ++ tt) Hmid_left s_d (t_d ++ tt)
                        (Hstarp _ _ _ _ HR Hstar_d) eq_refl).
      + right. exists s'', outs. split; [exact Hstep|].
        apply (IH _ Hmidset s'' (O_event glbl outs :: t_d ++ tt)); [|reflexivity].
        apply (Hostep _ _ _ _ _ (Hstarp _ _ _ _ HR Hstar_d) Hstep).
  Qed.

  (* Force a deduce of [g]: commit [sl_deduce g].  The hypothesis [H] captures the
     only nontrivial obligation — at every state the demon can reach, either [g] is
     already output or it is still deducible ([new_facts]).  For normal facts that
     "still deducible" is where the meta-fact ("no premature done-sending")
     invariant is needed; this lemma isolates it. *)
  Lemma force_deduce sp g s t :
    (forall sdem tdem,
        star (spec_node_step sp) s tdem sdem ->
        consistent_inputs (inputs_of (tdem ++ t)) ->
        output_in_trace g (tdem ++ t) \/ new_facts sp sdem g) ->
    eventually (can_step (spec_node_step sp) (consistent_inputs))
               (fun '(_, t'') => output_in_trace g t'') (s, t).
  Proof.
    intros H. apply eventually_step_cps. exists (sl_deduce g).
    intros sdem tdem Hstar Hallowed.
    destruct (H sdem tdem Hstar Hallowed) as [Hout | Hnf].
    - left. apply eventually_done. cbn. exact Hout.
    - right. eexists. exists [g]. split.
      + apply spec_node_deduce_step. exact Hnf.
      + apply eventually_done. cbn. exists (sl_deduce g), [g].
        split; apply in_eq.
  Qed.

  (* ---- Per-node liveness: graph_can_implies_will's per-node obligation. ----

     A node fed consistent inputs ([consistent_inputs]) is live: whenever it
     [can_output] a fact, it [will_output] it (against an adversarial demon). *)
  Lemma spec_node_can_implies_will (r : non_meta_rule) (n : nat) :
    can_implies_will
      (spec_node_step (node_prog_of r n))
      (consistent_inputs)
      {| known_facts := []; waiting_facts := []; sent_facts := [] |}.
  Proof.
    intros t s o Hreach Hallowed Hcan.
    destruct Hcan as (t' & s' & Hrun & Hinp & Hout).
    apply output_in_trace_app in Hout as [Hout_t' | Hout_t].
    - (* o is produced inside the input-free run t' — the forcing argument *)
      admit.
    - (* o already appears in t: commit nothing, we are already done *)
      unfold will_output. apply eventually_done. exact Hout_t.
  Admitted.

End __.
