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

From Stdlib Require Import List PeanoNat Lia Permutation Classical_Prop.
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
  (* Meta-protocol validity (as in Operational): the program's meta rules are
     valid, so a done-sending meta's hyps "cover" the matching normal rule's hyps.
     Needed for the disabling argument. *)
  Context (Hmeta_rules : meta_rules_valid (rules_of p)).
  Context (Hp_meta_input : Forall (good_meta_rule_inputs is_input) p.(meta_rules)).

  Local Notation can_deduce_fact := (can_deduce_fact is_input R_senders).
  Local Notation can_deduce_normal_fact := (can_deduce_normal_fact is_input R_senders).
  Local Notation ok_to_deduce_fact := (ok_to_deduce_fact is_input R_senders).
  Local Notation fire_at_rule := (fire_at_rule is_input R_senders p).
  Local Notation knows_datalog_fact := (knows_datalog_fact is_input R_senders).
  Local Notation expect_num_R_facts := (expect_num_R_facts is_input R_senders).

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
        (fun r => ok_to_deduce_fact r rs.(known_facts) rs.(sent_facts) f)
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

  (* The per-node [allowed]: just consistent inputs.  (Under the sent-based
     [ok_to_deduce] there is no need to forbid a node from receiving its own
     conclusion relation — a done-meta in [sent] simply witnesses that the fact was
     already output, rather than disabling it.) *)
  Definition node_allowed (inputs : list dfact) : Prop :=
    consistent_inputs inputs.

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
    unfold new_facts, node_prog_of, fire_at_rule, Operational.fire_at_rule,
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

  (* If [l1] is (multiset-)contained in [m], its matching count is no larger. *)
  Lemma Existsn_app_le (P : dfact -> Prop) l1 l2 m n N :
    Permutation (l1 ++ l2) m -> Existsn P n l1 -> Existsn P N m -> n <= N.
  Proof.
    intros Hperm Hn HN.
    eapply (Existsn_perm P) in HN; [| apply Permutation_sym; exact Hperm].
    apply Existsn_split in HN. destruct HN as (n1 & n2 & Heq & Hn1 & Hn2).
    pose proof (Existsn_unique P n n1 l1 Hn Hn1). lia.
  Qed.

  (* Every list has a (classically unique) matching count. *)
  Lemma Existsn_total (P : dfact -> Prop) l : exists n, Existsn P n l.
  Proof.
    induction l as [|x l IH].
    - exists 0. constructor.
    - destruct IH as (n & Hn). destruct (classic (P x)).
      + exists (S n). apply Existsn_yes; assumption.
      + exists n. apply Existsn_no; assumption.
  Qed.

  (* The key count-pinning: if [known(s)] already holds [expected] matching facts
     and the inputs cap the matching count at [expected], then any later
     [known(s')] still holds exactly [expected] — the count cannot grow (capped by
     the inputs) nor shrink ([known] only extends). *)
  Lemma matching_pinned sp s td s' tr mf_rel mf_args expected :
    Permutation (s.(known_facts) ++ s.(waiting_facts)) (inputs_of tr) ->
    star (spec_node_step sp) s td s' ->
    Existsn (dfact_matches mf_rel mf_args) expected s.(known_facts) ->
    (forall N, Existsn (dfact_matches mf_rel mf_args) N (inputs_of (rev td ++ tr)) ->
               N <= expected) ->
    Existsn (dfact_matches mf_rel mf_args) expected s'.(known_facts).
  Proof.
    intros Hperm Hstar Hexp Hcap.
    destruct (Existsn_total (dfact_matches mf_rel mf_args) s'.(known_facts)) as (M & HM).
    enough (M = expected) by (subst; exact HM).
    destruct (Existsn_total (dfact_matches mf_rel mf_args) (inputs_of (rev td ++ tr)))
      as (N & HN).
    assert (Hupper : M <= N).
    { eapply Existsn_app_le;
        [apply (kw_perm_star sp s td s' tr Hperm Hstar) | exact HM | exact HN]. }
    pose proof (Hcap N HN) as HNexp.
    destruct (known_suffix sp s td s' Hstar) as (pre & Hpre).
    assert (HMsuf : Existsn (dfact_matches mf_rel mf_args) M (pre ++ s.(known_facts))).
    { rewrite <- Hpre; exact HM. }
    apply Existsn_split in HMsuf. destruct HMsuf as (mp & ma & HMeq & Hmp & Hma).
    pose proof (Existsn_unique _ expected ma s.(known_facts) Hexp Hma) as Hae.
    lia.
  Qed.

  Lemma known_In_mono sp s td s' x :
    star (spec_node_step sp) s td s' ->
    In x s.(known_facts) -> In x s'.(known_facts).
  Proof.
    intros Hstar Hin. destruct (known_suffix sp s td s' Hstar) as (pre & Hpre).
    rewrite Hpre. apply in_or_app. right. exact Hin.
  Qed.

  Lemma known_in_inputs s (tr : list IO_event) x :
    Permutation (s.(known_facts) ++ s.(waiting_facts)) (inputs_of tr) ->
    In x s.(known_facts) ->
    In x (inputs_of tr).
  Proof.
    intros Hperm Hin. eapply Permutation_in; [exact Hperm | apply in_or_app; left; exact Hin].
  Qed.

  (* The crux: a [knows_datalog_fact] survives any later demon state.  For normal
     facts this is plain monotonicity; for meta facts (aggregates) the matching
     count is pinned ([matching_pinned]) so the meta-hyp's set and count are
     unchanged. *)
  Lemma knows_datalog_fact_stable sp s td s' tr (f : fact) :
    consistent_inputs (inputs_of (rev td ++ tr)) ->
    Permutation (s.(known_facts) ++ s.(waiting_facts)) (inputs_of tr) ->
    star (spec_node_step sp) s td s' ->
    knows_datalog_fact s.(known_facts) f ->
    knows_datalog_fact s'.(known_facts) f.
  Proof.
    intros Hcons Hperm Hstar.
    destruct Hcons as (HconsN & HconsSu & HconsS).
    (* facts of known(s) are among the inputs at s' *)
    assert (Hin_inp : forall x, In x s.(known_facts) -> In x (inputs_of (rev td ++ tr))).
    { intros x Hin. rewrite inputs_of_app. apply in_or_app. right.
      eapply known_in_inputs; eauto. }
    destruct f as [R args | mf_rel mf_args mf_set]; cbn [knows_datalog_fact].
    - (* normal fact: monotone *) apply (known_In_mono sp s td s' _ Hstar).
    - (* meta fact *)
      intros (num & Hexpect & Hcount & Hsetcons).
      (* the cap: any matching count in the inputs is <= num *)
      assert (Hcap : forall N,
                 Existsn (dfact_matches mf_rel mf_args) N (inputs_of (rev td ++ tr)) ->
                 N <= num).
      { cbv [expect_num_R_facts] in Hexpect. destruct (is_input mf_rel) eqn:Hisinp.
        - (* input R: None-declaration bounds it *)
          specialize (Hin_inp _ Hexpect).
          destruct (HconsN mf_rel mf_args num Hin_inp) as (_ & num' & Hle' & Hex').
          intros N HN. pose proof (Existsn_unique _ N num' _ HN Hex'). lia.
        - (* non-input R: sum of Some-declarations bounds it *)
          destruct Hexpect as (ems & Hforall2 & Hnum).
          assert (Hforall2' : Forall2 (fun k e =>
                    In (meta_dfact mf_rel mf_args (Some k) e) (inputs_of (rev td ++ tr)))
                    (R_senders mf_rel) ems).
          { eapply Forall2_impl; [| exact Hforall2]. intros k e Hk. apply Hin_inp. exact Hk. }
          destruct (HconsS mf_rel mf_args ems Hforall2') as (num' & Hle' & Hex').
          intros N HN. pose proof (Existsn_unique _ N num' _ HN Hex'). lia. }
      exists num. split; [| split].
      + (* expect_num transports by In-monotonicity *)
        cbv [expect_num_R_facts] in Hexpect |- *. destruct (is_input mf_rel) eqn:Hisinp.
        * apply (known_In_mono sp s td s' _ Hstar). exact Hexpect.
        * destruct Hexpect as (ems & Hforall2 & Hnum). exists ems. split; [| exact Hnum].
          eapply Forall2_impl; [| exact Hforall2]. intros k e Hk.
          apply (known_In_mono sp s td s' _ Hstar). exact Hk.
      + (* count pinned *) eapply (matching_pinned sp s td s' tr); eauto.
      + (* set-consistency: matching facts are the same set *)
        destruct (known_suffix sp s td s' Hstar) as (pre & Hpre).
        assert (Hpin : Existsn (dfact_matches mf_rel mf_args) num s'.(known_facts))
          by (eapply (matching_pinned sp s td s' tr); eauto).
        rewrite Hpre in Hpin. apply Existsn_split in Hpin.
        destruct Hpin as (mp & ma & Hmpeq & Hmp & Hma).
        pose proof (Existsn_unique _ num ma _ Hcount Hma) as Hae.
        assert (mp = 0) by lia. subst mp.
        apply Existsn_0_Forall_not in Hmp.
        intros nf_args Hmatch. rewrite (Hsetcons nf_args Hmatch). rewrite Hpre.
        rewrite in_app_iff. split.
        * intros Hin_s. right. exact Hin_s.
        * intros [Hin_pre | Hin_s].
          -- exfalso. rewrite Forall_forall in Hmp. apply (Hmp _ Hin_pre).
             cbv [dfact_matches]. exists nf_args. split; [reflexivity | exact Hmatch].
          -- exact Hin_s.
  Qed.

  (* An input-free run preserves [known ∪ waiting] as a multiset (dequeue just moves
     a fact; deduce touches only sent; there are no inputs). *)
  Lemma input_free_kw_perm sp s td s' :
    star (spec_node_step sp) s td s' ->
    inputs_of td = [] ->
    Permutation (s'.(known_facts) ++ s'.(waiting_facts))
                (s.(known_facts) ++ s.(waiting_facts)).
  Proof.
    induction 1 as [s0 | s0 e s1 t0 s2 Hstep Hstar IH]; intros Hinp.
    - apply Permutation_refl.
    - destruct e as [m | el eo]; cbn [inputs_of flat_map] in Hinp; [discriminate|].
      eapply perm_trans; [apply IH; exact Hinp|].
      inversion Hstep as [rs input rest Hq | rs out Hnf | rs inp]; subst;
        cbn [known_facts waiting_facts].
      + rewrite Hq. cbn [app]. apply Permutation_middle.
      + apply Permutation_refl.
  Qed.

  (* Multiset analogue of [knows_datalog_fact_stable]: a [knows_datalog_fact] of
     [known spre] transfers to any [known sstart] that multiset-contains it, provided
     [sstart]'s inputs are consistent (so the matching count is pinned and the extra
     [q] holds no matching facts). *)
  Lemma knows_datalog_fact_super (spre sstart : node_state) (tr : list IO_event)
      (q : list dfact) (f : fact) :
    consistent_inputs (inputs_of tr) ->
    Permutation (sstart.(known_facts) ++ sstart.(waiting_facts)) (inputs_of tr) ->
    Permutation sstart.(known_facts) (spre.(known_facts) ++ q) ->
    knows_datalog_fact spre.(known_facts) f ->
    knows_datalog_fact sstart.(known_facts) f.
  Proof.
    intros Hcons Hperm Hsuper.
    destruct Hcons as (HconsN & HconsSu & HconsS).
    assert (Hmono : forall x, In x spre.(known_facts) -> In x sstart.(known_facts)).
    { intros x Hin. eapply Permutation_in;
        [apply Permutation_sym; exact Hsuper | apply in_or_app; left; exact Hin]. }
    assert (Hin_inp : forall x, In x spre.(known_facts) -> In x (inputs_of tr)).
    { intros x Hin. eapply known_in_inputs; [exact Hperm | apply Hmono; exact Hin]. }
    destruct f as [R args | mf_rel mf_args mf_set]; cbn [knows_datalog_fact].
    - apply Hmono.
    - intros (num & Hexpect & Hcount & Hsetcons).
      assert (Hcap : forall N,
                 Existsn (dfact_matches mf_rel mf_args) N (inputs_of tr) -> N <= num).
      { cbv [expect_num_R_facts] in Hexpect. destruct (is_input mf_rel) eqn:Hisinp.
        - specialize (Hin_inp _ Hexpect).
          destruct (HconsN mf_rel mf_args num Hin_inp) as (_ & num' & Hle' & Hex').
          intros N HN. pose proof (Existsn_unique _ N num' _ HN Hex'). lia.
        - destruct Hexpect as (ems & Hforall2 & Hnum).
          assert (Hforall2' : Forall2 (fun k e =>
                    In (meta_dfact mf_rel mf_args (Some k) e) (inputs_of tr))
                    (R_senders mf_rel) ems).
          { eapply Forall2_impl; [|exact Hforall2]. intros k e Hk. apply Hin_inp. exact Hk. }
          destruct (HconsS mf_rel mf_args ems Hforall2') as (num' & Hle' & Hex').
          intros N HN. pose proof (Existsn_unique _ N num' _ HN Hex'). lia. }
      (* count pinned: known(sstart) ~ known(spre) ++ q, q holds no matching facts *)
      destruct (Existsn_total (dfact_matches mf_rel mf_args) q) as (jq & Hjq).
      assert (Hexn_start : Existsn (dfact_matches mf_rel mf_args) (num + jq)
                             sstart.(known_facts)).
      { eapply Existsn_perm; [apply Existsn_app; [exact Hcount | exact Hjq]|].
        apply Permutation_sym; exact Hsuper. }
      assert (Hjq0 : jq = 0).
      { destruct (Existsn_total (dfact_matches mf_rel mf_args) sstart.(waiting_facts)) as (w & Hw).
        assert (Hall_inp : Existsn (dfact_matches mf_rel mf_args) (num + jq + w) (inputs_of tr)).
        { eapply Existsn_perm;
            [apply Existsn_app; [exact Hexn_start | exact Hw] | exact Hperm]. }
        pose proof (Hcap _ Hall_inp). lia. }
      subst jq. rewrite Nat.add_0_r in Hexn_start.
      exists num. split; [| split].
      + cbv [expect_num_R_facts] in Hexpect |- *. destruct (is_input mf_rel) eqn:Hi.
        * apply Hmono. exact Hexpect.
        * destruct Hexpect as (ems & Hforall2 & Hnum). exists ems. split; [|exact Hnum].
          eapply Forall2_impl; [|exact Hforall2]. intros k e Hk. apply Hmono. exact Hk.
      + exact Hexn_start.
      + (* set-cons: matching facts of known(sstart) are exactly those of known(spre) *)
        apply Existsn_0_Forall_not in Hjq.   (* q holds no matching facts (jq=0) *)
        intros nf_args Hmatch. rewrite (Hsetcons nf_args Hmatch). split.
        * intros Hin_pre. apply Hmono. exact Hin_pre.
        * intros Hin_start.
          eapply Permutation_in in Hin_start; [|exact Hsuper].
          apply in_app_or in Hin_start. destruct Hin_start as [Hp | Hq'].
          -- exact Hp.
          -- exfalso. rewrite Forall_forall in Hjq. apply (Hjq _ Hq').
             cbv [dfact_matches]. exists nf_args. split; [reflexivity | exact Hmatch].
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
  Lemma force_into_known sp (allowed : list dfact -> Prop) g :
    forall n s pre post t,
      length pre <= n ->
      s.(waiting_facts) = pre ++ g :: post ->
      eventually (can_step (spec_node_step sp) allowed)
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

  (* MULTIPLICITY-AWARE forcing.  [force_into_known] only guarantees set-membership
     (it dedups); to reconstruct an aggregate's [Existsn cnt] we must drive the whole
     [waiting] MULTISET into [known].  We track [waiting = osuf ++ extra] where [osuf]
     is the not-yet-drained suffix of the target prefix and [known ⊇ oc] (the drained
     part) as a multiset; a front dequeue moves one [osuf] element into [known]. *)
  Lemma drain_step_form sp s e s' oc osuf extra kr :
    s.(waiting_facts) = osuf ++ extra ->
    Permutation s.(known_facts) (oc ++ kr) ->
    spec_node_step sp s e s' ->
    exists oc' osuf' extra' kr',
      oc ++ osuf = oc' ++ osuf' /\
      s'.(waiting_facts) = osuf' ++ extra' /\
      Permutation s'.(known_facts) (oc' ++ kr') /\
      length osuf' <= length osuf /\
      (exists d, kr' = d ++ kr).
  Proof.
    intros Hw Hkn Hstep.
    inversion Hstep as [rs input rest Hq | rs out Hnf | rs inp]; subst;
      cbn [known_facts waiting_facts].
    - (* dequeue front *)
      destruct osuf as [|y osuf''].
      + (* osuf empty: dequeued front is a demon fact, recorded into [known]/[kr] *)
        exists oc, (@nil dfact), rest, (input :: kr).
        split; [reflexivity|]. split; [reflexivity|]. split.
        * eapply perm_trans; [apply perm_skip; exact Hkn|]. apply Permutation_middle.
        * split; [cbn [length]; lia | exists [input]; reflexivity].
      + (* osuf = y :: osuf'': front y goes to known *)
        cbn [app] in Hw. rewrite Hw in Hq. injection Hq as Hxy Hr.
        subst input. subst rest.
        exists (oc ++ [y]), osuf'', extra, kr. split.
        * rewrite <- app_assoc. reflexivity.
        * split; [reflexivity|]. split.
          -- rewrite <- app_assoc. cbn [app].
             eapply perm_trans; [apply perm_skip; exact Hkn|]. apply Permutation_middle.
          -- split; [cbn [length]; lia | exists (@nil dfact); reflexivity].
    - (* deduce: known/waiting unchanged *)
      exists oc, osuf, extra, kr. rewrite Hw.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact Hkn|].
      split; [lia | exists (@nil dfact); reflexivity].
    - (* input: appended to back of extra *)
      exists oc, osuf, (extra ++ [inp]), kr.
      rewrite Hw, <- app_assoc. split; [reflexivity|]. split; [reflexivity|].
      split; [exact Hkn|]. split; [lia | exists (@nil dfact); reflexivity].
  Qed.

  Lemma drain_form_star sp s :
    forall oc osuf extra kr td sdem,
      s.(waiting_facts) = osuf ++ extra ->
      Permutation s.(known_facts) (oc ++ kr) ->
      star (spec_node_step sp) s td sdem ->
      exists oc' osuf' extra' kr',
        oc ++ osuf = oc' ++ osuf' /\
        sdem.(waiting_facts) = osuf' ++ extra' /\
        Permutation sdem.(known_facts) (oc' ++ kr') /\
        length osuf' <= length osuf /\
        (exists d, kr' = d ++ kr).
  Proof.
    intros oc osuf extra kr td sdem Hw Hkn Hstar. revert oc osuf extra kr Hw Hkn.
    induction Hstar as [s0 | s0 e s1 t0 s2 Hstep Hstar IH];
      intros oc osuf extra kr Hw Hkn.
    - exists oc, osuf, extra, kr.
      split; [reflexivity|]. split; [exact Hw|]. split; [exact Hkn|].
      split; [lia | exists (@nil dfact); reflexivity].
    - destruct (drain_step_form sp s0 e s1 oc osuf extra kr Hw Hkn Hstep)
        as (oc1 & osuf1 & extra1 & kr1 & Hsplit1 & Hw1 & Hkn1 & Hle1 & d1 & Hd1).
      destruct (IH oc1 osuf1 extra1 kr1 Hw1 Hkn1)
        as (oc2 & osuf2 & extra2 & kr2 & Hsplit2 & Hw2 & Hkn2 & Hle2 & d2 & Hd2).
      exists oc2, osuf2, extra2, kr2.
      split; [rewrite <- Hsplit2, <- Hsplit1; reflexivity|].
      split; [exact Hw2|]. split; [exact Hkn2|]. split; [lia|].
      exists (d2 ++ d1). rewrite Hd2, Hd1, app_assoc. reflexivity.
  Qed.

  (* Force the whole queued multiset [orig = waiting(s)] into [known]: commit
     [sl_dequeue] until the suffix is exhausted.  Conclusion is multiset (Permutation
     to [orig ++ rest]), so an [Existsn] count over [orig] transfers to [known]. *)
  Lemma force_drain sp (allowed : list dfact -> Prop) :
    forall (n : nat) s t oc osuf extra kr,
      length osuf <= n ->
      s.(waiting_facts) = osuf ++ extra ->
      Permutation s.(known_facts) (oc ++ kr) ->
      eventually (can_step (spec_node_step sp) allowed)
        (fun '(s', _) => exists rest, Permutation s'.(known_facts) ((oc ++ osuf) ++ rest)
                                      /\ exists d, rest = d ++ kr)
        (s, t).
  Proof.
    induction n as [|n IH]; intros s t oc osuf extra kr Hlen Hw Hkn.
    - assert (osuf = []) by (destruct osuf; [reflexivity | cbn in Hlen; lia]). subst osuf.
      apply eventually_done. rewrite app_nil_r. exists kr.
      split; [exact Hkn | exists (@nil dfact); reflexivity].
    - destruct osuf as [|y osuf'].
      + apply eventually_done. rewrite app_nil_r. exists kr.
        split; [exact Hkn | exists (@nil dfact); reflexivity].
      + apply eventually_step_cps. exists sl_dequeue. intros sdem tdem Hstar Hallow.
        destruct (drain_form_star sp s oc (y :: osuf') extra kr tdem sdem Hw Hkn Hstar)
          as (ocd & osufd & extrad & krd & Hsplit & Hwd & Hknd & Hled & dd & Hdd).
        destruct osufd as [|z osufd'].
        * left. apply eventually_done. rewrite app_nil_r in Hsplit.
          exists krd. split; [rewrite Hsplit; exact Hknd | exists dd; exact Hdd].
        * right. eexists. exists (@nil dfact). split.
          -- eapply spec_node_dequeue_step. cbn [app] in Hwd. exact Hwd.
          -- assert (Heq : (ocd ++ [z]) ++ osufd' = oc ++ (y :: osuf')).
             { rewrite <- app_assoc. cbn [app]. symmetry. exact Hsplit. }
             eapply eventually_weaken.
             ++ eapply (IH _ _ (ocd ++ [z]) osufd' extrad krd).
                ** cbn [length] in Hled, Hlen. lia.
                ** cbn [waiting_facts]. reflexivity.
                ** cbn [known_facts].
                   eapply perm_trans; [apply perm_skip; exact Hknd|].
                   rewrite <- app_assoc. cbn [app]. apply Permutation_middle.
             ++ intros [s'' t''] (rest & Hperm & d' & Hd'). exists rest.
                split; [rewrite <- Heq; exact Hperm|].
                exists (d' ++ dd). rewrite Hd', Hdd, app_assoc. reflexivity.
  Qed.

  (* A pure multiset rearrangement used by the agg case: relate the drained
     [known sdem] to [known spre] using the input-free [known∪waiting] permutation. *)
  Lemma agg_perm (a wsrc d ksrc ksp wsp : list dfact) :
    Permutation (ksp ++ wsp) (ksrc ++ wsrc) ->
    Permutation (a ++ (wsrc ++ d ++ ksrc)) (ksp ++ (a ++ d ++ wsp)).
  Proof.
    intros H.
    transitivity (a ++ d ++ (ksrc ++ wsrc)).
    { apply Permutation_app_head.
      eapply perm_trans; [apply Permutation_app_comm|].
      rewrite <- app_assoc. apply Permutation_refl. }
    transitivity (a ++ d ++ (ksp ++ wsp)).
    { apply Permutation_app_head. apply Permutation_app_head.
      apply Permutation_sym; exact H. }
    rewrite (app_assoc a d).
    eapply perm_trans; [apply Permutation_app_comm|].
    rewrite <- app_assoc. apply Permutation_app_head.
    eapply perm_trans; [apply Permutation_app_comm|].
    rewrite <- app_assoc. apply Permutation_refl.
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

  (* Dual to [output_in_state]: every fact in [sent] was actually emitted as an
     output in the trace (a deduce step both appends to [sent] and emits the fact).
     This is what lets us conclude "[o] ∈ sent ⟹ [o] already output". *)
  Definition sent_account (s : node_state) (tr : list IO_event) : Prop :=
    forall f, In f s.(sent_facts) -> output_in_trace f tr.

  Lemma sent_account_step sp s e s' tr :
    sent_account s tr -> spec_node_step sp s e s' -> sent_account s' (e :: tr).
  Proof.
    intros Hsa Hstep f Hf.
    inversion Hstep as [rs input rest Hq | rs out Hnf | rs inp]; subst;
      cbn [sent_facts] in Hf.
    - destruct (Hsa f Hf) as (lbl & outs & Hin & Hing).
      exists lbl, outs. split; [right; exact Hin | exact Hing].
    - destruct Hf as [Heq | Hf].
      + subst f. exists (sl_deduce out), [out].
        split; [left; reflexivity | left; reflexivity].
      + destruct (Hsa f Hf) as (lbl & outs & Hin & Hing).
        exists lbl, outs. split; [right; exact Hin | exact Hing].
    - destruct (Hsa f Hf) as (lbl & outs & Hin & Hing).
      exists lbl, outs. split; [right; exact Hin | exact Hing].
  Qed.

  Lemma sent_account_star sp s td s' tr :
    sent_account s tr -> star (spec_node_step sp) s td s' ->
    sent_account s' (rev td ++ tr).
  Proof.
    intros Hacc Hstar. revert tr Hacc.
    induction Hstar as [s0 | s0 e s1 t0 s2 Hstep Hstar IH]; intros tr Hacc; cbn [rev].
    - cbn [app]. exact Hacc.
    - rewrite <- app_assoc. cbn [app].
      apply IH. apply (sent_account_step sp s0 e s1 tr Hacc Hstep).
  Qed.

  Lemma sent_account_run sp s td s' tr :
    sent_account s tr -> star (spec_node_step sp) s td s' ->
    sent_account s' (td ++ tr).
  Proof.
    intros Hacc Hstar. pose proof (sent_account_star sp s td s' tr Hacc Hstar) as Hrev.
    intros f Hf. specialize (Hrev f Hf).
    apply output_in_trace_app. apply output_in_trace_app in Hrev.
    destruct Hrev as [Hr | Hr];
      [left; apply output_in_trace_rev; exact Hr | right; exact Hr].
  Qed.

  (* Carry a state/trace invariant [R] (preserved by demon runs and by an output
     step) through an eventually.  Verbatim single-node analogue of Graph.v's
     eventually_carry_inv2. *)
  Lemma eventually_carry_inv2 sp (allowed : list dfact -> Prop) (R : node_state -> list IO_event -> Prop) :
    (forall s tt t_d s_d, R s tt ->
       star (spec_node_step sp) s t_d s_d -> R s_d (t_d ++ tt)) ->
    (forall s tt glbl outs s', R s tt ->
       spec_node_step sp s (O_event glbl outs) s' -> R s' (O_event glbl outs :: tt)) ->
    forall (P : node_state * list IO_event -> Prop) s tt,
      R s tt ->
      eventually (can_step (spec_node_step sp) allowed) P (s, tt) ->
      eventually (can_step (spec_node_step sp) allowed)
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

  (* [inputs_of] is invariant (up to permutation) under reversing the trace; lets
     us reconcile [kw_perm_star]'s [rev]-trace with [can_step]'s forward trace. *)
  Lemma inputs_of_rev_perm (l : list IO_event) :
    Permutation (inputs_of (rev l)) (inputs_of l).
  Proof.
    induction l as [|e l IH]; cbn [rev]; [apply Permutation_refl|].
    rewrite inputs_of_app. destruct e as [m | lbl outs]; cbn [inputs_of flat_map app].
    - eapply perm_trans; [apply Permutation_app_comm | cbn [app]].
      apply perm_skip. exact IH.
    - rewrite app_nil_r. exact IH.
  Qed.

  (* The carried invariant for the forcing: known∪waiting accounts exactly for the
     inputs received so far, and the state is reachable from the empty init. *)
  Definition node_inv (sp : spec_node_prog) (s' : node_state) (t' : list IO_event) : Prop :=
    Permutation (s'.(known_facts) ++ s'.(waiting_facts)) (inputs_of t') /\
    sent_account s' t' /\
    exists Tinit, star (spec_node_step sp)
                       {| known_facts := []; waiting_facts := []; sent_facts := [] |} Tinit s'.

  Lemma node_inv_star sp s tt t_d s_d :
    node_inv sp s tt ->
    star (spec_node_step sp) s t_d s_d ->
    node_inv sp s_d (t_d ++ tt).
  Proof.
    intros (Hperm & Hsa & Tinit & Hreach) Hstar. split; [|split].
    - eapply perm_trans; [apply (kw_perm_star sp s t_d s_d tt Hperm Hstar)|].
      rewrite !inputs_of_app. apply Permutation_app_tail. apply inputs_of_rev_perm.
    - eapply sent_account_run; eassumption.
    - exists (Tinit ++ t_d). eapply star_app; eassumption.
  Qed.

  Lemma node_inv_step sp s tt glbl outs s' :
    node_inv sp s tt ->
    spec_node_step sp s (O_event glbl outs) s' ->
    node_inv sp s' (O_event glbl outs :: tt).
  Proof.
    intros (Hperm & Hsa & Tinit & Hreach) Hstep. split; [|split].
    - apply (kw_perm_step sp s (O_event glbl outs) s' tt Hperm Hstep).
    - eapply sent_account_step; eassumption.
    - exists (Tinit ++ [O_event glbl outs]).
      eapply star_app; [exact Hreach | eapply star_step; [exact Hstep | apply star_refl]].
  Qed.

  (* Drive a whole list of input facts into [known] (each was received, so lives in
     [known ∪ waiting]); dequeue them one at a time, carrying [node_inv] and the
     already-known prefix.  After this the demon may have added more, but every [h]
     in [hs] is now in [known]. *)
  Lemma force_known_list sp (allowed : list dfact -> Prop) (hs : list dfact) :
    forall s t,
      node_inv sp s t ->
      Forall (fun h => In h (inputs_of t)) hs ->
      eventually (can_step (spec_node_step sp) allowed)
        (fun '(s', t') => Forall (fun h => In h s'.(known_facts)) hs /\ node_inv sp s' t')
        (s, t).
  Proof.
    induction hs as [|h hs IH]; intros s t Hinv Hall.
    - apply eventually_done. split; [constructor | exact Hinv].
    - pose proof (Forall_inv Hall) as Hh_in. pose proof (Forall_inv_tail Hall) as Hhs_in.
      assert (Hraw : eventually (can_step (spec_node_step sp) allowed)
                       (fun '(s_h, _) => In h s_h.(known_facts)) (s, t)).
      { destruct Hinv as (Hperm & _).
        assert (Hin_kw : In h (s.(known_facts) ++ s.(waiting_facts))).
        { apply Permutation_in with (l := inputs_of t);
            [apply Permutation_sym; exact Hperm | exact Hh_in]. }
        apply in_app_or in Hin_kw. destruct Hin_kw as [Hk | Hw].
        - apply eventually_done. exact Hk.
        - apply in_split in Hw. destruct Hw as (pre & post & Hweq).
          eapply (force_into_known sp allowed h (length pre) s pre post t (le_n _) Hweq). }
      eapply eventually_trans.
      { eapply (eventually_carry_inv2 sp allowed
                  (fun s' t' => node_inv sp s' t' /\ incl (inputs_of t) (inputs_of t'))).
        - intros s0 tt0 td0 sd0 (Hni & Hic) Hst. split.
          + eapply node_inv_star; eassumption.
          + intros x Hx. rewrite inputs_of_app. apply in_or_app. right. exact (Hic x Hx).
        - intros s0 tt0 gl0 ou0 sd0 (Hni & Hic) Hst. split.
          + eapply node_inv_step; eassumption.
          + intros x Hx. cbn [inputs_of flat_map app]. exact (Hic x Hx).
        - split; [exact Hinv | apply incl_refl].
        - exact Hraw. }
      intros [s_h t_h] (Hh & Hinv_h & Hic_h).
      assert (Hhs_h : Forall (fun h0 => In h0 (inputs_of t_h)) hs).
      { eapply Forall_impl; [|exact Hhs_in]. intros a Ha. exact (Hic_h a Ha). }
      eapply eventually_weaken.
      { eapply (eventually_carry_inv2 sp allowed (fun s' _ => In h s'.(known_facts))).
        - intros s0 tt0 td0 sd0 Hk Hst. eapply known_In_mono; eassumption.
        - intros s0 tt0 gl0 ou0 sd0 Hk Hst.
          eapply known_In_mono; [eapply star_step; [exact Hst | apply star_refl] | exact Hk].
        - exact Hh.
        - exact (IH s_h t_h Hinv_h Hhs_h). }
      intros [s_f t_f] ((Hhs_f & Hinv_f) & Hh_f).
      split; [constructor; assumption | exact Hinv_f].
  Qed.

  (* Force a deduce of [g]: commit [sl_deduce g].  The hypothesis [H] captures the
     only nontrivial obligation — at every state the demon can reach, either [g] is
     already output or it is still deducible ([new_facts]).  For normal facts that
     "still deducible" is where the meta-fact ("no premature done-sending")
     invariant is needed; this lemma isolates it. *)
  Lemma force_deduce sp (allowed : list dfact -> Prop) g s t :
    (forall sdem tdem,
        star (spec_node_step sp) s tdem sdem ->
        allowed (inputs_of (tdem ++ t)) ->
        output_in_trace g (tdem ++ t) \/ new_facts sp sdem g) ->
    eventually (can_step (spec_node_step sp) allowed)
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

  (* A node-level "meta facts correct": every done-sending meta in [sent] is
     justified by a valid meta-rule derivation whose hyps are known.  (We drop
     Operational's extra "no meta_fact of the same key in hyps" clause; the
     disabling argument doesn't need it.) *)
  Definition node_mfc (n : nat) (s : node_state) : Prop :=
    forall R margs num,
      In (meta_dfact R margs (Some n) num) s.(sent_facts) ->
      exists mc mh hyps,
        In (mc, mh) p.(meta_rules) /\
        can_deduce_meta_fact mc mh n s.(sent_facts) (meta_dfact R margs (Some n) num) hyps /\
        Forall (knows_datalog_fact s.(known_facts)) hyps.

  (* [node_mfc] is preserved by a node step.  Dequeue: meta-hyps stay known by
     [knows_datalog_fact_stable] (no [sane_state] needed, unlike Operational).
     Deduce: a newly-deduced done-meta gets its justification from [new_facts]; an
     existing one keeps its count because the negative condition in [can_deduce_fact]
     forbids deducing a matching normal fact while the done-meta is in [sent]. *)
  Lemma node_mfc_step (r : non_meta_rule) (n : nat) s e s' tr :
    consistent_inputs (inputs_of (e :: tr)) ->
    Permutation (s.(known_facts) ++ s.(waiting_facts)) (inputs_of tr) ->
    node_mfc n s ->
    spec_node_step (node_prog_of r n) s e s' ->
    node_mfc n s'.
  Proof.
    intros Hcons Hperm Hmfc Hstep.
    inversion Hstep as [rs input rest Hq | rs out Hnf | rs inp]; subst;
      cbv [node_mfc] in Hmfc |- *; cbn [known_facts waiting_facts sent_facts];
      intros R margs num HIn.
    - (* dequeue *)
      specialize (Hmfc R margs num HIn).
      destruct Hmfc as (mc & mh & hyps & Hinmr & Hcdm & Hknown).
      exists mc, mh, hyps. split; [exact Hinmr|]. split; [exact Hcdm|].
      eapply Forall_impl; [|exact Hknown]. intros h Hh.
      eapply (knows_datalog_fact_stable (node_prog_of r n) s
                [O_event sl_dequeue []]
                {| known_facts := input :: s.(known_facts);
                   waiting_facts := rest; sent_facts := s.(sent_facts) |}
                tr h Hcons Hperm); [|exact Hh].
      eapply star_step; [apply spec_node_dequeue_step; exact Hq | apply star_refl].
    - (* deduce: sent gains [out], known unchanged *)
      destruct HIn as [Heq | HIn].
      + (* the newly-deduced done-meta is [out] itself *)
        subst out. destruct Hnf as (Hex & _).
        apply Exists_exists in Hex. destruct Hex as (r' & Hr'in & Hcdf).
        cbv [can_deduce_fact] in Hcdf.
        destruct Hcdf as (Hsrc & mc & mh & hyps & Hr'eq & Hcdm & Hknown).
        assert (Hin_mr : In (mc, mh) p.(meta_rules)).
        { cbn [node_prog_of spec_node_rules] in Hr'in.
          destruct Hr'in as [Hr'eq2 | Hr'in].
          - exfalso. rewrite <- Hr'eq2 in Hr'eq. destruct r; cbn in Hr'eq; discriminate.
          - apply in_map_iff in Hr'in. destruct Hr'in as ((c & h) & Hmeq & Hin).
            rewrite Hr'eq in Hmeq. injection Hmeq as <- <-. exact Hin. }
        exists mc, mh, hyps. split; [exact Hin_mr|]. split; [|exact Hknown].
        cbv [can_deduce_meta_fact] in Hcdm |- *.
        destruct Hcdm as (ctx & mfr & mfa & mfc & Heq' & Hexn & Hconcl & Hinterp).
        exists ctx, mfr, mfa, mfc. split; [exact Heq'|].
        split; [|split; [exact Hconcl | exact Hinterp]].
        apply Existsn_no; [|exact Hexn].
        intros (na & Hcontra & _). discriminate Hcontra.
      + (* a pre-existing done-meta: out cannot be a matching normal fact *)
        assert (Hnm : ~ dfact_matches R margs out).
        { intros (oa & Hout & Hmatch). subst out.
          destruct Hnf as (Hex & _). apply Exists_exists in Hex.
          destruct Hex as (r' & _ & Hcdf). cbv [can_deduce_fact] in Hcdf.
          destruct Hcdf as (_ & Hneg). exact (Hneg margs num HIn Hmatch). }
        specialize (Hmfc R margs num HIn).
        destruct Hmfc as (mc & mh & hyps & Hinmr & Hcdm & Hknown).
        exists mc, mh, hyps. split; [exact Hinmr|]. split; [|exact Hknown].
        cbv [can_deduce_meta_fact] in Hcdm |- *.
        destruct Hcdm as (ctx & mfr & mfa & mfc & Heq' & Hexn & Hconcl & Hinterp).
        injection Heq' as <- <- <-.
        exists ctx, R, margs, num. split; [reflexivity|].
        split; [|split; [exact Hconcl | exact Hinterp]].
        apply Existsn_no; [exact Hnm | exact Hexn].
    - (* input: known and sent unchanged *)
      specialize (Hmfc R margs num HIn).
      destruct Hmfc as (mc & mh & hyps & Hinmr & Hcdm & Hknown).
      exists mc, mh, hyps. split; [exact Hinmr|]. split; [exact Hcdm | exact Hknown].
  Qed.

  (* If a done-receiving meta-fact (with matching count [cnt] = expected) is known,
     then [known] holds ALL matching facts that have been delivered — the count is
     capped at [cnt] by [consistent_inputs] and [known] already has [cnt] of them. *)
  Lemma matching_complete s (tr : list IO_event) S smargs cnt h :
    consistent_inputs (inputs_of tr) ->
    Permutation (s.(known_facts) ++ s.(waiting_facts)) (inputs_of tr) ->
    expect_num_R_facts S smargs s.(known_facts) cnt ->
    Existsn (dfact_matches S smargs) cnt s.(known_facts) ->
    dfact_matches S smargs h ->
    In h (inputs_of tr) ->
    In h s.(known_facts).
  Proof.
    intros (HconsN & _ & HconsS) Hperm Hexp Hknown_cnt Hmatch Hin.
    assert (Hcap : forall N, Existsn (dfact_matches S smargs) N (inputs_of tr) -> N <= cnt).
    { cbv [expect_num_R_facts] in Hexp. destruct (is_input S) eqn:His.
      - assert (Hdecl : In (meta_dfact S smargs None cnt) (inputs_of tr)).
        { eapply Permutation_in; [exact Hperm | apply in_or_app; left; exact Hexp]. }
        destruct (HconsN S smargs cnt Hdecl) as (_ & num' & Hle & Hex').
        intros N HN. pose proof (Existsn_unique _ N num' _ HN Hex'). lia.
      - destruct Hexp as (ems & Hf2 & Hsum).
        assert (Hf2' : Forall2 (fun k e =>
                  In (meta_dfact S smargs (Some k) e) (inputs_of tr)) (R_senders S) ems).
        { eapply Forall2_impl; [|exact Hf2]. intros k e Hk.
          eapply Permutation_in; [exact Hperm | apply in_or_app; left; exact Hk]. }
        destruct (HconsS S smargs ems Hf2') as (num' & Hle & Hex').
        intros N HN. pose proof (Existsn_unique _ N num' _ HN Hex'). lia. }
    destruct (Existsn_total (dfact_matches S smargs) s.(waiting_facts)) as (w & Hw).
    assert (Hinp_cnt : Existsn (dfact_matches S smargs) (cnt + w) (inputs_of tr)).
    { eapply Existsn_perm; [apply Existsn_app; [exact Hknown_cnt | exact Hw] | exact Hperm]. }
    pose proof (Hcap _ Hinp_cnt). assert (w = 0) by lia. subst w.
    apply Existsn_0_Forall_not in Hw.
    apply (Permutation_in h (Permutation_sym Hperm)) in Hin.
    apply in_app_or in Hin. destruct Hin as [Hk | Hwait]; [exact Hk|].
    exfalso. rewrite Forall_forall in Hw. exact (Hw h Hwait Hmatch).
  Qed.

  (* Every fact in [sent] at a later state was either already there or deduced en
     route (with its [new_facts] justification, at a state whose [known] is
     included in the later [known]). *)
  Lemma sent_justified sp s td s' :
    star (spec_node_step sp) s td s' ->
    forall f, In f s'.(sent_facts) ->
      In f s.(sent_facts) \/
      exists sd tdd, new_facts sp sd f /\ star (spec_node_step sp) sd tdd s'.
  Proof.
    induction 1 as [s0 | s0 e s1 t0 s2 Hstep Hstar IH]; intros f Hf.
    - left. exact Hf.
    - destruct (IH f Hf) as [Hin1 | (sd & tdd & Hnf & Hstd)].
      + (* f in sent(s1): trace back across the first step *)
        inversion Hstep as [rs input rest Hq | rs out Hnf | rs inp]; subst;
          cbn [sent_facts known_facts] in Hin1.
        * left. exact Hin1.
        * destruct Hin1 as [Heq | Hin0].
          -- right. subst out. exists s0, (O_event (sl_deduce f) [f] :: t0).
             split; [exact Hnf|]. eapply star_step; [exact Hstep | exact Hstar].
          -- left. exact Hin0.
        * left. exact Hin1.
      + (* f deduced en route (at sd, after the first step) *)
        right. exists sd, tdd. split; [exact Hnf | exact Hstd].
  Qed.

  (* Push a matching fact from a later [known] (= [pre ++ known_sd]) back to the
     deduction point's [known_sd]: the done-receiving count [cnt] is already met in
     [known_sd] and capped in the inputs, so [pre] holds no matching facts. *)
  Lemma push_to_sd sd sdem pre (tr : list IO_event) S smargs cnt h :
    consistent_inputs (inputs_of tr) ->
    Permutation (sdem.(known_facts) ++ sdem.(waiting_facts)) (inputs_of tr) ->
    sdem.(known_facts) = pre ++ sd.(known_facts) ->
    expect_num_R_facts S smargs sd.(known_facts) cnt ->
    Existsn (dfact_matches S smargs) cnt sd.(known_facts) ->
    dfact_matches S smargs h ->
    In h sdem.(known_facts) ->
    In h sd.(known_facts).
  Proof.
    intros (HconsN & _ & HconsS) Hperm Hsuf Hexp Hknown_cnt Hmatch Hin.
    (* declaration is in known_sd <= known_sdem <= inputs *)
    assert (Hsd_in : forall x, In x sd.(known_facts) -> In x (inputs_of tr)).
    { intros x Hx. eapply Permutation_in; [exact Hperm | apply in_or_app; left].
      rewrite Hsuf. apply in_or_app. right. exact Hx. }
    assert (Hcap : forall N, Existsn (dfact_matches S smargs) N (inputs_of tr) -> N <= cnt).
    { cbv [expect_num_R_facts] in Hexp. destruct (is_input S) eqn:His.
      - destruct (HconsN S smargs cnt (Hsd_in _ Hexp)) as (_ & num' & Hle & Hex').
        intros N HN. pose proof (Existsn_unique _ N num' _ HN Hex'). lia.
      - destruct Hexp as (ems & Hf2 & Hsum).
        assert (Hf2' : Forall2 (fun k e =>
                  In (meta_dfact S smargs (Some k) e) (inputs_of tr)) (R_senders S) ems).
        { eapply Forall2_impl; [|exact Hf2]. intros k e Hk. apply Hsd_in. exact Hk. }
        destruct (HconsS S smargs ems Hf2') as (num' & Hle & Hex').
        intros N HN. pose proof (Existsn_unique _ N num' _ HN Hex'). lia. }
    (* matching count in known_sdem = matching(pre) + cnt, and <= cnt, so matching(pre)=0 *)
    destruct (Existsn_total (dfact_matches S smargs) pre) as (mp & Hmp).
    assert (Hsdem_cnt : Existsn (dfact_matches S smargs) (mp + cnt) sdem.(known_facts)).
    { rewrite Hsuf. apply Existsn_app; [exact Hmp | exact Hknown_cnt]. }
    assert (Hle_inp : mp + cnt <= cnt).
    { destruct (Existsn_total (dfact_matches S smargs) sdem.(waiting_facts)) as (w & Hw).
      assert (Hall_inp : Existsn (dfact_matches S smargs) (mp + cnt + w) (inputs_of tr)).
      { eapply Existsn_perm;
          [apply Existsn_app; [exact Hsdem_cnt | exact Hw] | exact Hperm]. }
      pose proof (Hcap _ Hall_inp). lia. }
    assert (mp = 0) by lia. subst mp. apply Existsn_0_Forall_not in Hmp.
    rewrite Hsuf in Hin. apply in_app_or in Hin. destruct Hin as [Hpre | Hsd]; [|exact Hsd].
    exfalso. rewrite Forall_forall in Hmp. exact (Hmp h Hpre Hmatch).
  Qed.

  (* A hyp [h] of [o] that is potentially-supported by the done-meta's (known)
     hyps and known at the later [sdem] is already known at the deduction point
     [sd] — the supporting done-receiving fact pins its matching facts complete in
     [known sd], and [push_to_sd] moves [h] back. *)
  Lemma ohyp_known_sd (sd sdem : node_state) pre (tr : list IO_event)
      (hyps_mr : list fact) (h : fact) :
    consistent_inputs (inputs_of tr) ->
    Permutation (sdem.(known_facts) ++ sdem.(waiting_facts)) (inputs_of tr) ->
    sdem.(known_facts) = pre ++ sd.(known_facts) ->
    Forall (knows_datalog_fact sd.(known_facts)) hyps_mr ->
    fact_potentially_supported hyps_mr h ->
    knows_datalog_fact sdem.(known_facts) h ->
    knows_datalog_fact sd.(known_facts) h.
  Proof.
    intros Hcons Hperm Hsuf Hknown_mr Hpot Hh_sdem.
    destruct h as [Rh ah | Rh ah Sh]; cbv [fact_potentially_supported] in Hpot.
    - destruct Hpot as (mfa & mfs & Hin_mh & Hmatch).
      rewrite Forall_forall in Hknown_mr. specialize (Hknown_mr _ Hin_mh).
      cbn [knows_datalog_fact] in Hknown_mr |- *.
      destruct Hknown_mr as (cnt & Hexp & Hexn & _).
      eapply (push_to_sd sd sdem pre tr Rh mfa cnt (normal_dfact Rh ah));
        try eassumption.
      exists ah. split; [reflexivity | exact Hmatch].
    - destruct Hpot as (mfs & Hin_mh).
      rewrite Forall_forall in Hknown_mr. specialize (Hknown_mr _ Hin_mh).
      cbn [knows_datalog_fact] in Hknown_mr |- *.
      destruct Hknown_mr as (cnt & Hexp & Hexn & _).
      destruct Hh_sdem as (cnt_h & Hexp_h & Hexn_h & Hset_h).
      exists cnt. split; [exact Hexp|]. split; [exact Hexn|].
      intros args Hm. rewrite (Hset_h args Hm). split.
      + intros Hin_sdem.
        eapply (push_to_sd sd sdem pre tr Rh ah cnt (normal_dfact Rh args));
          try eassumption.
        exists args. split; [reflexivity | exact Hm].
      + intros Hin_sd. rewrite Hsuf. apply in_or_app. right. exact Hin_sd.
  Qed.

  (* THE DISABLING LEMMA (Resolution 2 / sent-based [ok_to_deduce]).  A done-sending
     meta for [o]'s relation in [sent] does NOT block [o] — on the contrary, it
     witnesses that [o] is ALREADY SENT (output): [meta_rules_valid] forces [o]'s
     hyps into [known] at the done-meta's deduction point [sd], making [o]
     derivable-from-[known sd], so the sent-based [ok_to_deduce] puts [o] in
     [sent sd] ⊆ [sent sdem].  So the demon can never disable [o] without having
     output it first. *)
  Lemma no_disabler (np : spec_node_prog) (ru : rule) sdem (tr : list IO_event)
      (R : rel) (margs : list (option T)) (num : nat)
      (oargs : list T) (ohyps : list fact)
      (sbase : node_state) (Tbase : list IO_event) :
    meta_rules_valid np.(spec_node_rules) ->
    In ru np.(spec_node_rules) ->
    consistent_inputs (inputs_of tr) ->
    Permutation (sdem.(known_facts) ++ sdem.(waiting_facts)) (inputs_of tr) ->
    sbase.(sent_facts) = [] ->
    star (spec_node_step np) sbase Tbase sdem ->
    non_meta_rule_impl ru R oargs ohyps ->
    Forall2 matches margs oargs ->
    Forall (knows_datalog_fact sdem.(known_facts)) ohyps ->
    In (meta_dfact R margs (Some np.(spec_node_label)) num) sdem.(sent_facts) ->
    In (normal_dfact R oargs) sdem.(sent_facts).
  Proof.
    intros Hmrv Hin_ru Hcons Hperm Hbase Hstar Himpl Hmatch Hohyps Hdone.
    destruct (sent_justified _ _ _ _ Hstar _ Hdone) as [Habs | (sd & tdd & Hnf & Hstd)].
    { rewrite Hbase in Habs. inversion Habs. }
    destruct (known_suffix _ _ _ _ Hstd) as (pre & Hsuf).
    destruct Hnf as (Hex & Hall).
    apply Exists_exists in Hex. destruct Hex as (r' & Hr'in & Hcdf).
    cbv [can_deduce_fact] in Hcdf.
    destruct Hcdf as (Hsrc & mc' & mh' & hyps_mr & Hr'eq & Hcdm & Hknown_mr).
    rewrite Hr'eq in Hr'in.
    pose (S_constr := fun args'' => one_step_derives np.(spec_node_rules) hyps_mr R args'').
    assert (Hri_meta : rule_impl (one_step_derives np.(spec_node_rules)) (meta_rule mc' mh')
                         (meta_fact R margs S_constr) hyps_mr).
    { cbv [can_deduce_meta_fact] in Hcdm.
      destruct Hcdm as (ctx_m & mfr & mfa & mfc & Heq_m & _ & Hconcl_m & Hinterp_m).
      injection Heq_m as <- <- <-.
      eapply meta_rule_impl with (ctx := ctx_m).
      - eapply Exists_impl; [|exact Hconcl_m].
        intros c (mfa' & mfs' & Hf2 & Heqv). injection Heqv as Hrel Hargs _.
        exists mfa', S_constr. split; [exact Hf2|]. rewrite Hargs, Hrel. reflexivity.
      - exact Hinterp_m.
      - intros args'' _. subst S_constr. simpl. reflexivity. }
    assert (Hri_normal : rule_impl (one_step_derives np.(spec_node_rules)) ru
                           (normal_fact R oargs) ohyps).
    { apply simple_rule_impl. exact Himpl. }
    pose proof (Hmrv _ _ _ _ _ Hr'in Hri_meta _ _ _ Hin_ru Hri_normal Hmatch) as Hpot.
    assert (Hohyps_sd : Forall (knows_datalog_fact sd.(known_facts)) ohyps).
    { rewrite Forall_forall in Hpot, Hohyps |- *. intros h Hh.
      eapply ohyp_known_sd; try eassumption.
      - exact (Hpot _ Hh).
      - exact (Hohyps _ Hh). }
    assert (Hcdn : can_deduce_normal_fact ru sd.(known_facts) R oargs).
    { exists ohyps. split; assumption. }
    rewrite Forall_forall in Hall. specialize (Hall ru Hin_ru).
    cbv [ok_to_deduce_fact] in Hall. specialize (Hall oargs Hcdn Hmatch).
    (* [Hall : In o (sent sd)]; [sent] only grows along [sd ->* sdem]. *)
    exact (spec_steps_sent_incl _ _ _ _ Hstd _ Hall).
  Qed.

  (* If [o] is output somewhere in a run, then at the pre-state of that deduce
     [new_facts] held.  We also record that the prefix is still input-free. *)
  Lemma run_output_new_facts sp s t' s' o :
    star (spec_node_step sp) s t' s' ->
    inputs_of t' = [] ->
    output_in_trace o t' ->
    exists spre tpre, star (spec_node_step sp) s tpre spre /\
                      inputs_of tpre = [] /\ new_facts sp spre o.
  Proof.
    induction 1 as [s0 | s0 e s1 t0 s2 Hstep Hstar IH]; intros Hinp Hout.
    - destruct Hout as (lbl & outs & Hin & _). inversion Hin.
    - destruct Hout as (lbl & outs & Hin & Hino). destruct Hin as [Heq | Hin].
      + subst e. inversion Hstep as [rs input rest Hq Hl Ho | rs output Hnf Hl Ho | rs inp Hl Ho].
        * subst. cbn in Hino. exact (match Hino with end).
        * subst. cbn in Hino. destruct Hino as [Heqo | []]. subst output.
          exists s0, []. split; [apply star_refl | split; [reflexivity | exact Hnf]].
      + destruct e as [m | el eo]; cbn [inputs_of flat_map] in Hinp.
        * discriminate.
        * destruct (IH Hinp (ex_intro _ lbl (ex_intro _ outs (conj Hin Hino))))
            as (spre & tpre & Hst & Hti & Hnf).
          exists spre, (O_event el eo :: tpre). split;
            [eapply star_step; eassumption | split; [cbn; exact Hti | exact Hnf]].
  Qed.

  (* Along an input-free run, [known] only gains facts that were already in
     [known ∪ waiting] at the start (dequeues move waiting→known; deduces touch only
     sent; there are no inputs). *)
  Lemma input_free_known_sub sp s td s' :
    star (spec_node_step sp) s td s' ->
    inputs_of td = [] ->
    forall x, In x s'.(known_facts) -> In x s.(known_facts) \/ In x s.(waiting_facts).
  Proof.
    induction 1 as [s0 | s0 e s1 t0 s2 Hstep Hstar IH]; intros Hinp x Hx.
    - left. exact Hx.
    - destruct e as [m | el eo]; cbn [inputs_of flat_map] in Hinp; [discriminate|].
      specialize (IH Hinp x Hx).
      inversion Hstep as [rs input rest Hq Hl Ho | rs output Hnf Hl Ho | rs inp Hl Ho];
        subst; cbn [known_facts waiting_facts] in IH.
      + destruct IH as [Hk | Hw].
        * destruct Hk as [Heq | Hk]; [right; rewrite Hq; left; exact Heq | left; exact Hk].
        * right. rewrite Hq. right. exact Hw.
      + exact IH.
  Qed.

  Definition df_of (h : fact) : dfact :=
    match h with
    | normal_fact r a => normal_dfact r a
    | meta_fact r a _ => meta_dfact r a None 0
    end.

  (* The force assembly for a normal output [normal_dfact R oargs] derivable by
     [rule_of r] from all-normal hyps [ohyps] that are input-derived: drive the hyps
     into [known] ([force_known_list]), then commit the deduce ([force_deduce]); the
     deduce never gets disabled ([no_disabler]). *)
  Lemma force_normal_output (np : spec_node_prog) (ru : rule) s t R oargs ohyps :
    meta_rules_valid np.(spec_node_rules) ->
    In ru np.(spec_node_rules) ->
    node_inv np s t ->
    non_meta_rule_impl ru R oargs ohyps ->
    Forall (fun h => exists hr ha, h = normal_fact hr ha) ohyps ->
    Forall (fun h => In (df_of h) (inputs_of t)) ohyps ->
    eventually (can_step (spec_node_step np) node_allowed)
      (fun '(_, t'') => output_in_trace (normal_dfact R oargs) t'') (s, t).
  Proof.
    intros Hmrv Hin_ru Hinv Himpl Hnorm Hin_inp.
    eapply eventually_trans.
    { apply (force_known_list np node_allowed (map df_of ohyps) s t Hinv).
      rewrite Forall_forall. intros d Hd. apply in_map_iff in Hd as (h & <- & Hh).
      rewrite Forall_forall in Hin_inp. exact (Hin_inp h Hh). }
    intros [s_start t_start] (Hknown & Hinv_start).
    apply force_deduce. intros sdem tdem Hstar_d Hallow_d.
    pose proof (node_inv_star np s_start t_start tdem sdem Hinv_start Hstar_d)
      as Hinv_dem.
    destruct Hinv_dem as (Hperm_dem & Hsa_dem & Tinit_dem & Hreach_dem).
    cbv [node_allowed] in Hallow_d. rename Hallow_d into Hcons_dem.
    (* If [o] is already in [sent], it was output (sent_account); else commit the
       deduce — no done-meta can disable it (no_disabler would put it in sent). *)
    destruct (classic (In (normal_dfact R oargs) sdem.(sent_facts))) as [Hin_o | Hnin_o].
    { left. exact (Hsa_dem _ Hin_o). }
    right.
    assert (Hohyps_dem : Forall (knows_datalog_fact sdem.(known_facts)) ohyps).
    { rewrite Forall_forall. intros h Hh.
      rewrite Forall_forall in Hnorm. destruct (Hnorm h Hh) as (hr & ha & ->).
      cbn [knows_datalog_fact].
      rewrite Forall_forall in Hknown.
      assert (Hin_start : In (df_of (normal_fact hr ha)) s_start.(known_facts)).
      { apply Hknown. apply in_map. exact Hh. }
      cbn [df_of] in Hin_start.
      eapply known_In_mono; [exact Hstar_d | exact Hin_start]. }
    split.
    - apply Exists_exists. exists ru. split.
      + exact Hin_ru.
      + cbn [can_deduce_fact]. split.
        * exists ohyps. split; [exact Himpl | exact Hohyps_dem].
        * intros mf_args num Hin_done Hmatch_done. apply Hnin_o.
          eapply (no_disabler np ru sdem (tdem ++ t_start) R mf_args num oargs ohyps
                    {| known_facts := []; waiting_facts := []; sent_facts := [] |} Tinit_dem);
            try eassumption.
          reflexivity.
    - rewrite Forall_forall. intros r'' Hr''. cbn [ok_to_deduce_fact]. exact I.
  Qed.

  (* ---- Per-node liveness: graph_can_implies_will's per-node obligation. ----

     A node fed consistent inputs ([consistent_inputs]) is live: whenever it
     [can_output] a fact, it [will_output] it (against an adversarial demon). *)
  Lemma spec_node_can_implies_will (np : spec_node_prog) :
    meta_rules_valid np.(spec_node_rules) ->
    can_implies_will
      (spec_node_step np)
      node_allowed
      {| known_facts := []; waiting_facts := []; sent_facts := [] |}.
  Proof.
    intros Hmrv t s o Hreach Hallowed Hcan.
    destruct Hcan as (t' & s' & Hrun & Hinp & Hout).
    assert (Hinv : node_inv np s t).
    { split; [|split].
      - assert (Hkp := kw_perm_star np
          {| known_facts := []; waiting_facts := []; sent_facts := [] |} t s []
          (Permutation_refl _) Hreach).
        eapply perm_trans; [exact Hkp|]. rewrite app_nil_r. apply inputs_of_rev_perm.
      - assert (Hsa0 : sent_account
          {| known_facts := []; waiting_facts := []; sent_facts := [] |} (@nil IO_event))
          by (intros f Hf; inversion Hf).
        pose proof (sent_account_run np _ t s [] Hsa0 Hreach) as Hsa.
        rewrite app_nil_r in Hsa. exact Hsa.
      - exists t. exact Hreach. }
    apply output_in_trace_app in Hout as [Hout_t' | Hout_t].
    2: { unfold will_output. apply eventually_done. exact Hout_t. }
    destruct (run_output_new_facts _ _ _ _ o Hrun Hinp Hout_t')
      as (spre & tpre & Hst_pre & Hti_pre & Hnf).
    destruct Hnf as (Hex & Hall).
    destruct o as [R oargs | R margs source num].
    2: { (* META DONE-MESSAGE OUTPUT.  Live under Resolution 2 (sent-based
            [ok_to_deduce]): "done sending R" = "every R-fact derivable from [known]
            is already in [sent]", which is maintainable (force an R-fact's output and
            it lands in [sent]).  Forcing it is a NESTED loop: drive every derivable
            R-fact into [sent] (each via the normal-output forcing), bounded by the
            finite candidate set, then [force_deduce] the done-message.  ~150 lines;
            the eventually-analogue of Operational's rule_can_force_normal_dfacts. *)
         admit. }
    apply Exists_exists in Hex. destruct Hex as (r' & Hr'in & Hcdf).
    cbn [can_deduce_fact] in Hcdf. destruct Hcdf as (Hcdn & Hneg).
    destruct Hcdn as (ohyps & Himpl & Hknown_pre).
    (* [r'] is whatever rule of [np] derives [o]; [Himpl] makes it non-meta. *)
    inversion Himpl as
      [concls hyps_cl ctx R0 oargs0 ohyps0 HExists HForall2 Heqrule
       | S vals concl_rel agg hyp_rel oargs0 Hset Heqrule Heqcc].
    - (* normal_rule: all hyps normal *)
      assert (Hnorm : Forall (fun h => exists hr ha, h = normal_fact hr ha) ohyps).
      { clear -HForall2. induction HForall2 as [|cl h hyps_cl' ohyps' Hic _ IH];
          constructor; [|exact IH].
        destruct Hic as (nf & _ & ->). exists (clause_rel cl), nf. reflexivity. }
      eapply force_normal_output; try eassumption.
      rewrite Forall_forall. intros h Hh.
      rewrite Forall_forall in Hnorm. destruct (Hnorm h Hh) as (hr & ha & ->).
      rewrite Forall_forall in Hknown_pre. pose proof (Hknown_pre _ Hh) as Hk.
      cbn [knows_datalog_fact] in Hk. cbn [df_of].
      destruct Hinv as (Hperm & _).
      destruct (input_free_known_sub _ _ _ _ Hst_pre Hti_pre _ Hk) as [Hk_s | Hw_s];
        (eapply Permutation_in; [exact Hperm|]).
      * apply in_or_app; left; exact Hk_s.
      * apply in_or_app; right; exact Hw_s.
    - (* AGG_RULE OUTPUT.  o is a normal fact; the agg meta-hyp's knows_datalog_fact is
         reconstructed at the driven state by draining the whole queue (force_drain,
         multiplicity-aware) into known and transferring via knows_datalog_fact_super
         (consistent_inputs pins the matching count). *)
      subst oargs. subst concl_rel.
      destruct Hinv as (Hperm_st & Hsa_st & Tinit_st & Hreach_st).
      eapply eventually_trans.
      { eapply (eventually_carry_inv2 np node_allowed
                  (fun s' t' => node_inv np s' t')).
        - intros s0 tt0 td0 sd0 HR Hst. eapply node_inv_star; eassumption.
        - intros s0 tt0 g0 o0 sd0 HR Hst. eapply node_inv_step; eassumption.
        - split; [exact Hperm_st | split; [exact Hsa_st | exists Tinit_st; exact Hreach_st]].
        - eapply (force_drain np node_allowed (length (waiting_facts s))
                    s t [] (waiting_facts s) [] (known_facts s)).
          + apply le_n.
          + rewrite app_nil_r. reflexivity.
          + rewrite app_nil_l. apply Permutation_refl. }
      intros [s_start t_start] ((rest & Hdrain & d & Hd) & Hinv_start).
      apply force_deduce. intros sdem tdem Hstar_d Hallow_d.
      pose proof (node_inv_star np s_start t_start tdem sdem Hinv_start Hstar_d)
        as Hinv_dem.
      destruct Hinv_dem as (Hperm_dem & Hsa_dem & Tinit_dem & Hreach_dem).
      cbv [node_allowed] in Hallow_d.
      destruct (known_suffix np s_start tdem sdem Hstar_d) as (pre' & Hpre').
      pose proof (input_free_kw_perm np s tpre spre Hst_pre Hti_pre) as Hifkw.
      rewrite Hd in Hdrain.
      assert (Hq : Permutation sdem.(known_facts)
                     (spre.(known_facts) ++ (pre' ++ d ++ spre.(waiting_facts)))).
      { rewrite Hpre'.
        eapply perm_trans; [apply Permutation_app_head; exact Hdrain|].
        apply (agg_perm pre' (waiting_facts s) d (known_facts s)
                 (known_facts spre) (waiting_facts spre) Hifkw). }
      assert (Hknown_dem : Forall (knows_datalog_fact sdem.(known_facts)) ohyps).
      { rewrite Forall_forall in Hknown_pre |- *. intros h Hh.
        eapply (knows_datalog_fact_super spre sdem (tdem ++ t_start)
                  (pre' ++ d ++ spre.(waiting_facts)) h);
          [exact Hallow_d | exact Hperm_dem | exact Hq | exact (Hknown_pre h Hh)]. }
      destruct (classic (In (normal_dfact R (interp_agg agg vals :: oargs0))
                            sdem.(sent_facts))) as [Hin_o | Hnin_o].
      { left. exact (Hsa_dem _ Hin_o). }
      right. split.
      + apply Exists_exists. exists r'. split.
        * exact Hr'in.
        * cbn [can_deduce_fact]. split.
          -- exists ohyps. split; [exact Himpl | exact Hknown_dem].
          -- intros mf_args num0 Hin_done Hmatch_done. apply Hnin_o.
             eapply (no_disabler np r' sdem (tdem ++ t_start) R mf_args num0
                       (interp_agg agg vals :: oargs0) ohyps
                       {| known_facts := []; waiting_facts := []; sent_facts := [] |} Tinit_dem);
               try eassumption.
             reflexivity.
      + rewrite Forall_forall. intros r'' Hr''. cbn [ok_to_deduce_fact]. exact I.
  Admitted.

End __.
