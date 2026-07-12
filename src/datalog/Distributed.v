From Stdlib Require Import List Permutation RelationClasses.
From Datalog Require Import Datalog Node Graph Smallstep List Map.
From coqutil Require Import Map.Interface.
Import ListNotations.

Section Distributed.
  Context {rel : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.

  Context (R_senders : rel -> list node_name).
  Context (np : @node_prog rel exprvar fn aggregator).
  Context (Hmrv : meta_rules_valid np.(np_rules)).

  Local Notation nstep := (node_step R_senders np).
  Local Notation nallowed := (allowed_inputs R_senders).

  Context (input_allowed : node_id -> dfact -> bool).
  Context (forward : node_id -> node_id -> dfact -> bool).
  Context (output_visible : node_id -> dfact -> bool).
  Context (output_visible_equiv :
             forall n a b, dfact_equiv a b -> output_visible n a = output_visible n b).
  Context (forward_equiv :
             forall n1 n2 a b, dfact_equiv a b -> forward n1 n2 a = forward n1 n2 b).
  Context (consistent_output : node_id -> list dfact -> Prop).
  Context (consistent consistent_inputs : list dfact -> list dfact -> Prop).
  Context (Hcg : consistent_good forward consistent_output consistent consistent_inputs).
  Context (Hcm : consistent_monotone consistent nallowed).
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
  Context (Hmono : monotone_mod_equiv nstep dfact_equiv consistent nallowed node_init).

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

  Lemma nodes_good_holds :
    Forall_map (node_good dfact_equiv consistent_output consistent nallowed nstep) initial_gs.
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
      (consistent := consistent) (consistent_inputs := consistent_inputs)
      (initial_gs := initial_gs); try assumption.
    - exact nequiv_equiv.
    - exact nallowed_multiset_monotone.
    - exact nstep_input_total.
    - exact nodes_good_holds.
  Qed.

End Distributed.
