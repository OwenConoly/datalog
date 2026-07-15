From Stdlib Require Import List Permutation RelationClasses Classical_Prop Lia.
From Datalog Require Import Datalog Node Graph Smallstep List Map Tactics.
From coqutil Require Import Map.Interface Tactics Tactics.fwd.
Import ListNotations.

Section Distributed.
  Context {rel : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.

  Context (R_senders : rel -> list node_name).
  Context (R_senders_NoDup : forall R, NoDup (R_senders R)).

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
  Definition allowed_output (n : option node_id) (fs : list dfact) : Prop :=
    (forall R mf_args src cnt,
       In (meta_dfact R mf_args src cnt) fs ->
       n = src /\ exists actual, actual <= cnt /\ Existsn (dfact_matches R mf_args) actual fs) /\
    (forall f, In f fs -> In n (R_senders (dfact_rel f))).
  Definition consistent (s : stmt) (l : list dfact) : Prop :=
    let '(R, mf_args) := s in
    exists num, expect_num_R_facts R_senders R mf_args l num /\
      exists actual, actual >= num /\ Existsn (dfact_matches R mf_args) actual l.
  Context (consistent_mono :
             forall s ms1 ms2, consistent s ms1 -> submultiset ms1 ms2 -> consistent s ms2).
  Lemma Existsn_total {X} (P : X -> Prop) (l : list X) : exists n, Existsn P n l.
  Proof.
    induction l as [|x xs (n & Hn)].
    - exists 0. apply Existsn_nil.
    - destruct (classic (P x)); [ exists (S n); apply Existsn_yes | exists n; apply Existsn_no ];
        assumption.
  Qed.

  Lemma consistent_output_mono s n ms1 ms2 :
    consistent_output s n ms1 -> submultiset ms1 ms2 -> consistent_output s n ms2.
  Proof.
    destruct s as [R mf_args].
    intros (cnt & Hin & actual & Hge & Hexn) Hsub.
    pose proof (submultiset_incl _ _ Hsub) as Hincl.
    destruct Hsub as (rest & Hperm).
    destruct (Existsn_total (dfact_matches R mf_args) rest) as (k & Hk).
    exists cnt. split; [ apply Hincl; exact Hin | ].
    exists (actual + k). split; [ lia | ].
    eapply Existsn_perm with (l1 := ms1 ++ rest);
      [ apply Existsn_app; assumption | apply Permutation_sym; exact Hperm ].
  Qed.
  Context (consistent_good_holds :
             consistent_good claim consistent_output allowed_output consistent).
  Lemma allowed_output_submultiset n : multiset_monotone_dec (allowed_output n).
  Proof.
    intros l1 l2 (Hmeta2 & Hsender2) Hsub.
    pose proof (submultiset_incl _ _ Hsub) as Hincl.
    split; [ | intros f Hin; apply Hsender2, Hincl, Hin ].
    intros R mf_args src cnt Hin.
    destruct (Hmeta2 R mf_args src cnt (Hincl _ Hin)) as (Hsrc & actual2 & Hle2 & Hexn2).
    split; [ exact Hsrc | ].
    destruct Hsub as (rest & Hperm).
    pose proof (Existsn_perm _ _ _ _ Hexn2 Hperm) as Hexn2'.
    apply Existsn_split in Hexn2'. destruct Hexn2' as (n1 & n_rest & Hsum & Hex1 & _).
    exists n1. split; [ lia | exact Hex1 ].
  Qed.
  Definition natsum (l : list nat) := fold_left Nat.add l 0.

  Lemma fold_left_add_init l a : fold_left Nat.add l a = a + fold_left Nat.add l 0.
  Proof.
    revert a. induction l as [|x xs IH]; intros a; simpl; [ lia | ].
    rewrite (IH (a + x)), (IH x). lia.
  Qed.

  Lemma natsum_cons x l : natsum (x :: l) = x + natsum l.
  Proof. unfold natsum. simpl. rewrite fold_left_add_init. lia. Qed.

  Lemma natsum_app l1 l2 : natsum (l1 ++ l2) = natsum l1 + natsum l2.
  Proof. unfold natsum. rewrite fold_left_app, fold_left_add_init. lia. Qed.

  Lemma Forall2_In_combine {A B} (R : A -> B -> Prop) xs ys x y :
    Forall2 R xs ys -> In (x, y) (combine xs ys) -> R x y.
  Proof.
    induction 1 as [| a b xs' ys' Hab HF IH]; simpl; [ contradiction | ].
    intros [Heq | Hin]; [ injection Heq as -> ->; exact Hab | exact (IH Hin) ].
  Qed.

  Lemma In_concat_pair {A B} (xs : list A) (yss : list (list B)) y :
    length xs = length yss ->
    In y (concat yss) ->
    exists x ys, In (x, ys) (combine xs yss) /\ In y ys.
  Proof.
    revert xs. induction yss as [| ys yss' IH]; intros xs Hlen Hin; [ destruct Hin | ].
    destruct xs as [| x xs']; [ discriminate Hlen | ].
    simpl in Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    - exists x, ys. split; [ left; reflexivity | exact Hin ].
    - simpl in Hlen. injection Hlen as Hlen.
      destruct (IH xs' Hlen Hin) as (x' & ys' & Hcomb & Hin').
      exists x', ys'. split; [ right; exact Hcomb | exact Hin' ].
  Qed.

  Lemma meta_not_in_block R mf_args n0 ms0 k e mss' :
    allowed_output n0 ms0 ->
    k <> n0 ->
    In (meta_dfact R mf_args k e) (ms0 ++ concat mss') ->
    In (meta_dfact R mf_args k e) (concat mss').
  Proof.
    intros (Hmeta & _) Hne Hin. apply in_app_or in Hin.
    destruct Hin as [Hin | Hin]; [ | exact Hin ].
    destruct (Hmeta _ _ _ _ Hin) as (Hsrc & _). congruence.
  Qed.

  Lemma Forall2_meta_shift R mf_args n0 ms0 mss' senders ems :
    allowed_output n0 ms0 ->
    ~ In n0 senders ->
    Forall2 (fun k e => In (meta_dfact R mf_args k e) (ms0 ++ concat mss')) senders ems ->
    Forall2 (fun k e => In (meta_dfact R mf_args k e) (concat mss')) senders ems.
  Proof.
    intros Hao Hnin HF. induction HF as [| k e senders' ems' Hin HF IH]; constructor.
    - eapply meta_not_in_block; [ exact Hao | | exact Hin ].
      intros ->. apply Hnin. left. reflexivity.
    - apply IH. intros Hin'. apply Hnin. right. exact Hin'.
  Qed.

  Lemma allowed_of_outputs_bound R mf_args :
    forall nodes mss, Forall2 allowed_output nodes mss -> NoDup nodes ->
    forall senders ems, NoDup senders ->
      Forall2 (fun k e => In (meta_dfact R mf_args k e) (concat mss)) senders ems ->
      (forall n ms f, In (n, ms) (combine nodes mss) ->
                      In f ms -> dfact_matches R mf_args f -> In n senders) ->
      exists num', num' <= natsum ems /\ Existsn (dfact_matches R mf_args) num' (concat mss).
  Proof.
    intros nodes mss HF2. induction HF2 as [| n0 ms0 nodes' mss' Hao HF IH];
      intros Hnd senders ems Hnds Hems Hcover.
    - exists 0. split; [ lia | constructor ].
    - inversion Hnd as [| n0' nodes0 Hn0notin Hnd_tail]; subst.
      cbn [concat] in Hems |- *.
      destruct (classic (In n0 senders)) as [Hin0 | Hnin0].
      + apply in_split in Hin0. destruct Hin0 as (s1 & s2 & ->).
        apply Forall2_app_inv_l in Hems.
        destruct Hems as (e1 & ems2 & He1 & Hems2 & ->).
        destruct ems2 as [| e0 e2]; [ solve [ inversion Hems2 ] | ].
        assert (Hmeta0 : In (meta_dfact R mf_args n0 e0) (ms0 ++ concat mss'))
          by (inversion Hems2; assumption).
        assert (He2 : Forall2 (fun k e => In (meta_dfact R mf_args k e) (ms0 ++ concat mss')) s2 e2)
          by (inversion Hems2; assumption).
        assert (Hin_ms0 : In (meta_dfact R mf_args n0 e0) ms0).
        { apply in_app_or in Hmeta0. destruct Hmeta0 as [H | H]; [ exact H | exfalso ].
          edestruct (In_concat_pair nodes' mss') as (n' & ms' & Hcomb & Hin');
            [ eapply Forall2_length; exact HF | exact H | ].
          pose proof (Forall2_In_combine _ _ _ _ _ HF Hcomb) as (Hm' & _).
          destruct (Hm' _ _ _ _ Hin') as (Hsrc & _). subst n'.
          apply Hn0notin. eapply in_combine_l; exact Hcomb. }
        destruct (proj1 Hao _ _ _ _ Hin_ms0) as (_ & actual & Hle & Hexn0).
        pose proof (NoDup_remove_2 _ _ _ Hnds) as Hnin0'.
        assert (Hems' : Forall2 (fun k e => In (meta_dfact R mf_args k e) (concat mss'))
                                (s1 ++ s2) (e1 ++ e2)).
        { eapply Forall2_meta_shift; [ exact Hao | exact Hnin0' | apply Forall2_app; assumption ]. }
        assert (Hcover' : forall n ms f, In (n, ms) (combine nodes' mss') ->
                            In f ms -> dfact_matches R mf_args f -> In n (s1 ++ s2)).
        { intros n ms f Hcomb Hf Hmatch.
          assert (Hne : n <> n0) by (intros ->; apply Hn0notin; eapply in_combine_l; exact Hcomb).
          pose proof (Hcover n ms f (or_intror Hcomb) Hf Hmatch) as Hin_s.
          apply in_app_or in Hin_s. apply in_or_app.
          destruct Hin_s as [H | [H | H]]; [ left; exact H | congruence | right; exact H ]. }
        destruct (IH Hnd_tail (s1 ++ s2) (e1 ++ e2) (NoDup_remove_1 _ _ _ Hnds) Hems' Hcover')
          as (num'' & Hle'' & Hexn'').
        exists (actual + num''). split.
        * rewrite natsum_app, natsum_cons. rewrite natsum_app in Hle''. lia.
        * apply Existsn_app; assumption.
      + assert (Hno : Existsn (dfact_matches R mf_args) 0 ms0).
        { apply Forall_not_Existsn_0. apply Forall_forall. intros f Hf Hmatch.
          apply Hnin0. eapply (Hcover n0 ms0 f); [ left; reflexivity | exact Hf | exact Hmatch ]. }
        assert (Hems' : Forall2 (fun k e => In (meta_dfact R mf_args k e) (concat mss')) senders ems)
          by (eapply Forall2_meta_shift; [ exact Hao | exact Hnin0 | exact Hems ]).
        assert (Hcover' : forall n ms f, In (n, ms) (combine nodes' mss') ->
                            In f ms -> dfact_matches R mf_args f -> In n senders)
          by (intros n ms f Hcomb Hf Hmatch; exact (Hcover n ms f (or_intror Hcomb) Hf Hmatch)).
        destruct (IH Hnd_tail senders ems Hnds Hems' Hcover') as (num'' & Hle'' & Hexn'').
        exists num''. split; [ lia | ].
        replace num'' with (0 + num'') by lia. apply Existsn_app; assumption.
  Qed.

  Lemma allowed_of_outputs nodes mss :
    NoDup nodes -> Forall2 allowed_output nodes mss -> nallowed (concat mss).
  Proof.
    intros Hnd HF2 R mf_args ems Hems.
    edestruct (allowed_of_outputs_bound R mf_args nodes mss HF2 Hnd (R_senders R) ems
                 (R_senders_NoDup R) Hems) as (num' & Hle & Hexn).
    - intros n ms f Hcomb Hf Hmatch.
      pose proof (Forall2_In_combine _ _ _ _ _ HF2 Hcomb) as (_ & Hsend).
      destruct Hmatch as (nf_args & -> & _). exact (Hsend _ Hf).
    - exists num'. split; [ exact Hle | exact Hexn ].
  Qed.

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
    - exact consistent_output_mono.
    - exact nallowed_multiset_monotone.
    - exact allowed_output_submultiset.
    - exact allowed_of_outputs.
    - exact nstep_input_total.
    - exact nodes_good_holds.
  Qed.

End Distributed.
