From Stdlib Require Import List Permutation RelationClasses.
From Datalog Require Import Datalog Node Graph Smallstep List Map Tactics.
From coqutil Require Import Map.Interface Tactics Tactics.fwd.
Import ListNotations.

Section Distributed.
  Context {rel : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.

  Context (R_senders : rel -> list node_name).

  Local Notation nstep := (node_step R_senders).
  Local Notation nallowed := (allowed_inputs R_senders).

  Context (rel_input_allowed : node_id -> rel -> bool).
  Context (rel_forward : node_id -> node_id -> rel -> bool).
  Context (rel_visible : node_id -> rel -> bool).

  Definition input_allowed n (f : dfact) := rel_input_allowed n (dfact_rel f).
  Definition forward n1 n2 (f : dfact) := rel_forward n1 n2 (dfact_rel f).
  Definition output_visible n (f : dfact) := rel_visible n (dfact_rel f).

  Lemma output_visible_equiv n a b :
    dfact_equiv a b ->
    output_visible n a = output_visible n b.
  Proof.
    intros Heq. unfold output_visible. f_equal.
    destruct a, b; simpl in Heq; fwd; congruence || reflexivity.
  Qed.

  Lemma forward_equiv n1 n2 a b :
    dfact_equiv a b ->
    forward n1 n2 a = forward n1 n2 b.
  Proof.
    intros Heq. unfold forward. f_equal.
    destruct a, b; simpl in Heq; fwd; congruence || reflexivity.
  Qed.

  Definition allowed_output n fs f :=
    match f with
    | normal_dfact _ _ => True
    | meta_dfact R mf_args src cnt =>
        n = src /\ exists cnt', cnt' <= cnt /\ Existsn (dfact_matches R mf_args) cnt' fs
    end.

  Definition allowed_outputs (n : option node_id) fs :=
    Forall (allowed_output n fs) fs /\
      forall R,
        In R (map dfact_rel fs) ->
        In n (R_senders R).

  (*TODO what is going wrong with typeclass inference here*)
  Definition is_sum R mf_args mfs total_cnt :=
    exists ls,
      NoDup (map fst ls) /\
        (forall src cnt, In (@meta_dfact rel _ R mf_args src cnt) mfs <-> In (src, cnt) ls) /\
        total_cnt = fold_right Nat.add O (map snd ls).

  Definition consistent_outputs mfs fs :=
    match mfs with
    | [meta_dfact R mf_args src cnt] =>
        exists cnt', cnt' >= cnt /\ Existsn (dfact_matches R mf_args) cnt' fs
    | _ => False
    end.

  Definition allowed_complement n fs :=
    exists fss ns,
      Permutation fs (concat fss) /\
        NoDup ns /\
        ~In n ns /\
        Forall2 allowed_outputs ns fss.

  Definition consistent (c l : list dfact) : Prop :=
    exists R mf_args nums,
      Forall3 (fun src num f => f = meta_dfact R mf_args src num) (R_senders R) nums c /\
        exists num,
          fold_right Nat.add O nums <= num /\
            Existsn (dfact_matches R mf_args) num l.

  Definition consistent_splits :=
    forall nodes mfss fss,
      NoDup nodes ->
      Forall2 allowed_outputs nodes fss ->
      Forall2 (@incl _) mfss fss ->
      consistent (concat mfss) (concat fss) <->
        Forall2 consistent_outputs mfss fss.

  Definition consistent_facts_from_source (src : node_id) (fs : list dfact) :=
    (*every meta-fact source is src, and meta-fact counts are consistent with numbers of normal facts*)

  Context (consistent_output : node_id -> list dfact -> Prop).
  Context (consistent_inputs : list dfact -> list dfact -> Prop).
  Context (Hcg : consistent_good forward consistent_output nconsistent consistent_inputs).
  Context (Hcim : consistent_monotone consistent_inputs nallowed).
  Context (consistent_inputs_equiv :
             forall c c' inps, Forall2 dfact_equiv c c' ->
                          consistent_inputs c inps -> consistent_inputs c' inps).

  Context {graph_state : map.map node_id (@graph_node_state dfact dfact_mod_count node_state)}.
  Context {graph_state_ok : map.ok graph_state}.
  Context (initial_gs : graph_state).
  Context (initial_gs_empty :
             forall n gns, map.get initial_gs n = Some gns ->
                           gns.(gns_trace) = [] /\ gns.(gns_queue) = []).
  Context (initial_gs_node_init :
             forall n gns, map.get initial_gs n = Some gns ->
                           gns.(gns_node_state) = node_init).

  Context (Howf : forall n, outputs_well_formed nstep (consistent_output n) node_init).

  #[local] Instance nequiv_equiv : Equivalence dfact_equiv.
  Proof.
    constructor.
    - intros f. apply dfact_equiv_refl.
    - intros f1 f2. apply dfact_equiv_sym.
    - intros [R1 a1 | R1 m1 s1 c1] [R2 a2 | R2 m2 s2 c2] [R3 a3 | R3 m3 s3 c3] H12 H23;
        cbn [dfact_equiv] in *; try congruence.
      destruct H12 as (-> & -> & ->), H23 as (-> & -> & ->). repeat split.
  Qed.

  Lemma nallowed_multiset_monotone : multiset_monotone nallowed.
  Proof. intros l1 l2 Hl2 Hsub. eapply allowed_inputs_submultiset; eauto. Qed.

  Lemma nstep_input_total : input_total nstep.
  Proof. intros s m. eexists. apply node_input_step. Qed.

  Lemma Hmono : monotone_mod_equiv nstep dfact_equiv nconsistent nallowed node_init.
  Admitted.

  Lemma Hcm : consistent_monotone nconsistent nallowed.
  Admitted.

  Lemma nodes_good_holds :
    Forall_map (node_good dfact_equiv consistent_output nconsistent nallowed nstep) initial_gs.
  Proof.
    intros n gns Hget. unfold node_good.
    rewrite (initial_gs_node_init n gns Hget).
    split; [apply Howf | split; [apply Hmono | apply node_might_implies_will; exact Hmrv]].
  Qed.

  Local Notation gstep := (graph_step input_allowed forward output_visible nstep).
  Local Notation gia := (graph_inputs_allowed forward consistent_output nallowed).

  Theorem distributed_might_implies_will
          (t : list (IO_event (@graph_label dfact dfact_mod_count) (dfact * node_id)))
          (gs : graph_state) (o : dfact * node_id) :
    star gstep initial_gs t gs ->
    gia (inputs_of t) ->
    might_output gstep gs t o ->
    will_output_equiv gstep (graph_equiv dfact_equiv) gia gs t o.
  Proof.
    intros Hstar Hga Hmight.
    apply graph_might_implies_will with
      (consistent := nconsistent) (consistent_inputs := consistent_inputs)
      (initial_gs := initial_gs); try assumption.
    - exact nequiv_equiv.
    - exact output_visible_equiv.
    - exact forward_equiv.
    - exact nallowed_multiset_monotone.
    - exact Hcm.
    - exact nstep_input_total.
    - exact nodes_good_holds.
  Qed.

End Distributed.
