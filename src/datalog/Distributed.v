From Stdlib Require Import List Permutation RelationClasses.
From Datalog Require Import Datalog Node Graph Smallstep List Map Tactics.
From coqutil Require Import Map.Interface Tactics Tactics.fwd.
Import ListNotations.

Section Distributed.
  Context {rel : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.

  Context (R_senders : rel -> list node_name).

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

  (* The graph runs one node program [np] replicated across nodes. *)
  Context (np : node_prog).
  Context (Hmrv : meta_rules_valid np.(np_rules)).

  Local Notation nstep := (node_step R_senders np).
  Local Notation nallowed := (allowed_inputs R_senders).

  #[local] Instance nequiv_equiv : Equivalence dfact_equiv.
  Proof.
    constructor.
    - intros f. apply dfact_equiv_refl.
    - intros f1 f2. apply dfact_equiv_sym.
    - intros [R1 a1 | R1 m1 s1 c1] [R2 a2 | R2 m2 s2 c2] [R3 a3 | R3 m3 s3 c3] H12 H23;
        cbn [dfact_equiv] in *; try congruence.
      destruct H12 as (-> & -> & ->), H23 as (-> & -> & ->). repeat split.
  Qed.

  (* ---- The abstract consistency interface Graph.v needs, at [stmt := (R, mf_args)].
     These, and the obligations below, are what still needs concrete definitions and
     proofs; for now they are assumed so the graph->node wiring typechecks. ---- *)
  Definition stmt : Type := (rel * list (option T))%type.

  Definition claim (s : stmt) (l : list dfact) : Prop :=
    let '(R, mf_args) := s in
    forall src, In src (R_senders R) ->
      exists cnt, In (meta_dfact R mf_args src cnt) l.

  Lemma claim_mono s ms1 ms2 :
    claim s ms1 -> incl_mod dfact_equiv ms1 ms2 -> claim s ms2.
  Proof.
    destruct s as [R mf_args]. intros Hcl Hincl src Hsrc.
    destruct (Hcl src Hsrc) as (cnt & Hin).
    destruct (Hincl _ Hin) as (f' & Hin' & Heq).
    destruct f' as [Rn an | Rm am sm cm]; cbn [dfact_equiv] in Heq.
    - discriminate Heq.
    - destruct Heq as (-> & -> & ->). eauto.
  Qed.

  Definition consistent_output (s : stmt) (n : option node_id) (fs : list dfact) : Prop :=
    let '(R, mf_args) := s in
    exists cnt, In (meta_dfact R mf_args n cnt) fs /\
      exists actual, actual >= cnt /\ Existsn (dfact_matches R mf_args) actual fs.
  Context (allowed_output : option node_id -> list dfact -> Prop).
  Context (consistent : stmt -> list dfact -> Prop).
  Context (consistent_mono :
             forall s ms1 ms2, consistent s ms1 -> submultiset ms1 ms2 -> consistent s ms2).
  Context (consistent_output_mono :
             forall s n ms1 ms2,
               consistent_output s n ms1 -> submultiset ms1 ms2 -> consistent_output s n ms2).
  Context (consistent_good_holds :
             consistent_good claim consistent_output allowed_output consistent).
  Context (allowed_output_submultiset :
             forall n, multiset_monotone_dec (allowed_output n)).
  Context (allowed_of_outputs :
             forall nodes mss, Forall2 allowed_output nodes mss -> nallowed (concat mss)).

  Context {graph_state : map.map node_id (@graph_node_state dfact dfact_mod_count node_state)}.
  Context {graph_state_ok : map.ok graph_state}.
  Context (initial_gs : graph_state).
  Context (initial_gs_empty :
             forall n gns, map.get initial_gs n = Some gns ->
                           gns.(gns_trace) = [] /\ gns.(gns_queue) = []).
  Context (initial_gs_node_init :
             forall n gns, map.get initial_gs n = Some gns ->
                           gns.(gns_node_state) = node_init).

  Lemma nallowed_multiset_monotone : multiset_monotone_dec nallowed.
  Proof. intros l1 l2 Hl2 Hsub. eapply allowed_inputs_submultiset; eauto. Qed.

  Lemma nstep_input_total : input_total nstep.
  Proof. intros s m. eexists. apply node_input_step. Qed.

  Lemma nodes_good_holds :
    Forall_map (node_good forward dfact_equiv claim consistent_output allowed_output
                          consistent nallowed nstep) initial_gs.
  Admitted.

  Local Notation gstep := (graph_step input_allowed forward output_visible nstep).
  Local Notation gia := (graph_inputs_allowed allowed_output).

  Theorem distributed_might_implies_will
          (t : list (IO_event (@graph_label dfact dfact_mod_count) (dfact * node_id)))
          (gs : graph_state) (o : dfact * node_id) :
    star gstep initial_gs t gs ->
    gia (inputs_of t) ->
    might_output gstep gs t o ->
    will_output_equiv gstep (graph_equiv dfact_equiv) gia gs t o.
  Proof.
    intros.
    eapply graph_might_implies_will; try eassumption.
    - exact nequiv_equiv.
    - exact output_visible_equiv.
    - exact forward_equiv.
    - exact claim_mono.
    - exact nallowed_multiset_monotone.
    - exact nstep_input_total.
    - exact nodes_good_holds.
  Qed.

End Distributed.
