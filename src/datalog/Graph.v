From coqutil Require Import Map.Interface.
From coqutil Require Import Map.Properties.
From coqutil Require Import Semantics.OmniSmallstepCombinators.
From coqutil Require Import Eqb.
From Stdlib Require Import List PeanoNat Permutation.
From Stdlib Require Import RelationClasses Morphisms Classical_Prop.
From Datalog Require Import OmniSmallstep Smallstep Map List Eqb.
From Datalog Require Import Tactics.
From coqutil Require Import Tactics Tactics.fwd.
Import ListNotations.

Definition node_id := nat.
#[export] Instance node_id_eqb : Eqb.Eqb node_id := Eqb.nat_eqb.
#[export] Instance node_id_eqb_ok : Eqb.Eqb_ok node_id_eqb := Eqb.nat_eqb_ok.
Section __.
  Context {message : Type}.
  Context {label : Type}.
  Context (input_allowed : node_id -> message -> bool).
  (* Context (forward : node_id -> message -> list node_id). *)
  Context (forward : node_id (*sender*) -> node_id (*receiver*) -> message -> bool (*send?*)).
  Context (output_visible : node_id -> message -> bool).

  Context (equiv : message -> message -> Prop).
  Context {equiv_equiv : Equivalence equiv}.
  Context (output_visible_equiv :
             forall n a b, equiv a b -> output_visible n a = output_visible n b).
  (* Forwarding cannot distinguish [equiv]-related messages: a forced re-emission
     produces [mu' ~ mu] and must reach the same consumers as [mu]. *)
  Context (forward_equiv :
             forall n1 n2 a b, equiv a b -> forward n1 n2 a = forward n1 n2 b).
  Context (consistent_output : node_id -> list message -> Prop).
  Context (consistent : list message -> list message -> Prop).
  Context (consistent_inputs : list message -> list message -> Prop).

  Local Notation IO_event := (Smallstep.IO_event label message).

  Variant graph_label :=
    | receive (_ : node_id) (_ : message)
    | run (_ : node_id) (_ : label).

  Local Notation gevent := (Smallstep.IO_event graph_label (message * node_id)).

  Definition consistent_internal_inputs_to n inps :=
    exists nodes partition,
      NoDup nodes /\
        Forall2 consistent_output nodes partition /\
        inps = flat_map
                 (fun '(n0, fs) => filter (forward n0 n) fs)
                 (combine nodes partition).

  Definition consistent_good :=
    forall internal_inps inps n c,
      consistent_internal_inputs_to n internal_inps ->
      consistent c (internal_inps ++ inps) <-> consistent_inputs c inps.

  Context (allowed : list message -> Prop).
  Context (allowed_submultiset : multiset_monotone allowed).

  Lemma Permutation_allowed l1 l2 : Permutation l1 l2 -> allowed l2 -> allowed l1.
  Proof.
    intros HP Ha. eapply allowed_submultiset; [ exact Ha | ].
    exists []. rewrite app_nil_r. symmetry. exact HP.
  Qed.

  Definition matching_inps n (inps : list (message * node_id)) :=
    map fst (filter (fun '(_, n0) => eqb n n0) inps).

  Definition graph_inputs_allowed (inps : list (message * node_id)) :=
    forall n internal_inps,
      consistent_internal_inputs_to n internal_inps ->
      allowed (internal_inps ++ matching_inps n inps).

  Context (Hcg : consistent_good).
  Context (Hcm : consistent_monotone consistent allowed).

  Context (Hcim : consistent_monotone consistent_inputs allowed).

  Context (consistent_inputs_equiv :
             forall c c' inps, Forall2 equiv c c' ->
               consistent_inputs c inps -> consistent_inputs c' inps).

  Section graph.
    Context {node_state : Type} (node_step : node_state -> IO_event -> node_state -> Prop).

    Record graph_node_state :=
      { gns_node_state : node_state;
        gns_trace : list IO_event;
        gns_queue : list message }.

    Context {graph_state : map.map node_id graph_node_state}.

    Definition enqueue inps gns :=
      {| gns_node_state := gns.(gns_node_state);
        gns_trace := gns.(gns_trace);
        gns_queue := inps ++ gns.(gns_queue) |}.

    Inductive graph_step : graph_state -> gevent -> graph_state -> Prop :=
    | gstep_input gs n m :
      input_allowed n m = true ->
      graph_step gs (I_event (m, n)) (mupd gs n (enqueue [m]))
    | gstep_run gs n ns ns' lbl outs :
      map.get gs n = Some ns ->
      node_step ns.(gns_node_state) (O_event lbl outs) ns' ->
      graph_step gs (O_event (run n lbl) (map (fun m => (m, n)) (filter (output_visible n) outs)))
        (map_values' (fun m => enqueue (filter (forward n m) outs))
           (map.put gs n
                    {| gns_node_state := ns';
                      gns_trace := O_event lbl outs :: ns.(gns_trace);
                      gns_queue := ns.(gns_queue) |}))
    | gstep_receive gs n ns ns' m ms1 ms2 :
      map.get gs n = Some ns ->
      node_step ns.(gns_node_state) (I_event m) ns' ->
      ns.(gns_queue) = ms1 ++ m :: ms2 ->
      graph_step gs (O_event (receive n m) [])
        (map.put gs n
                 {| gns_node_state := ns';
                   gns_trace := I_event m :: ns.(gns_trace);
                   gns_queue := ms1 ++ ms2 |}).
  End graph.
  Arguments graph_node_state : clear implicits.

  Section graph.
    Context {node_state : Type}.
    Context {graph_state : map.map node_id (graph_node_state node_state)}.
    Context {graph_state_ok : map.ok graph_state}.
    Context (initial_gs : graph_state).
    Context (initial_gs_empty :
               forall n gns, map.get initial_gs n = Some gns ->
                             gns.(gns_trace) = [] /\ gns.(gns_queue) = []).
    Context (node_step : node_state -> IO_event -> node_state -> Prop).
    Context (nodes_input_total : input_total node_step).

    Local Notation gstep := (graph_step node_step).

    Definition node_good (n : node_id) : graph_node_state node_state -> Prop :=
      fun gns =>
        outputs_well_formed    node_step (consistent_output n) gns.(gns_node_state) /\
        monotone_mod_equiv     node_step equiv consistent allowed gns.(gns_node_state) /\
        might_implies_will_equiv node_step equiv allowed gns.(gns_node_state).

    Definition le_weak (g1 g2 : graph_state) :=
      Forall2_map (fun n gns1 gns2 =>
                     incl_mod_weak equiv (inputs_of gns1.(gns_trace) ++ gns1.(gns_queue)) (inputs_of gns2.(gns_trace) ++ gns2.(gns_queue)))
        g1 g2.

    Definition le_strong (g1 g2 : graph_state) :=
      Forall2_map (fun n gns1 gns2 =>
                     submultiset (inputs_of gns1.(gns_trace)) (inputs_of gns2.(gns_trace)) /\
                     submultiset (inputs_of gns1.(gns_trace) ++ gns1.(gns_queue)) (inputs_of gns2.(gns_trace) ++ gns2.(gns_queue)))
        g1 g2.

    Definition le (g1 g2 : graph_state) :=
      Forall2_map (fun n gns1 gns2 =>
                     incl_mod equiv consistent (inputs_of gns1.(gns_trace)) (inputs_of gns2.(gns_trace)))
        g1 g2.

    Definition node_has_output (gs : graph_state) (n : node_id) (o : message) : Prop :=
      exists ns, map.get gs n = Some ns /\ In o (outputs_of (gns_trace ns)).

    Let graph_will_step := (will_step (graph_step node_step) graph_inputs_allowed).

    Context (nodes_good : Forall_map node_good initial_gs).

    Ltac map_func :=
      repeat match goal with
        | H1: map.get ?x ?y = _, H2: map.get ?x ?y = _ |- _ => rewrite H1 in H2; invert H2
        end.

    #[local] Hint Constructors star eventually : core.
    #[local] Hint Resolve
      incl_mod_weak_refl incl_mod_weak_of_incl incl_mod_weak_trans
      in_or_app impl_in_map impl_in_filter star_app submultiset_app_r : core.
    #[local] Hint Unfold val_sat might_output : core.
    #[local] Hint Extern 5 (In _ _) => simpl : core.

    Lemma le_weak_refl g : le_weak g g.
    Proof. apply Forall2_map_refl. intros. apply incl_mod_weak_refl; assumption. Qed.

    Lemma le_refl g : le g g.
    Proof. apply Forall2_map_refl. intros. apply incl_mod_refl; assumption. Qed.

    Lemma le_weak_trans g1 g2 g3 : le_weak g1 g2 -> le_weak g2 g3 -> le_weak g1 g3.
    Proof.
      apply Forall2_map_trans. intros k a b c. apply incl_mod_weak_trans; assumption.
    Qed.

    Lemma le_strong_trans g1 g2 g3 : le_strong g1 g2 -> le_strong g2 g3 -> le_strong g1 g3.
    Proof.
      apply Forall2_map_trans. intros k a b c [Ht1 Hq1] [Ht2 Hq2].
      split; eapply submultiset_trans; eassumption.
    Qed.

    Lemma le_le_strong a b c :
      Forall_map (fun _ ns => allowed (inputs_of ns.(gns_trace) ++ ns.(gns_queue))) b ->
      Forall_map (fun _ ns => allowed (inputs_of ns.(gns_trace) ++ ns.(gns_queue))) c ->
      le a b -> le_strong b c -> le a c.
    Proof.
      intros Hb Hc Hab Hbc.
      cbv [le le_strong Forall_map Forall2_map] in *. intros k.
      specialize (Hab k); specialize (Hbc k).
      destruct (map.get a k) as [va|] eqn:Ha, (map.get b k) as [vb|] eqn:Hgb,
               (map.get c k) as [vc|] eqn:Hgc;
        try contradiction; try exact I.
      destruct Hbc as [Hbc_t Hbc_q].
      pose proof (Hb k vb Hgb) as Halb. pose proof (Hc k vc Hgc) as Halc.
      intros x Hx_incl Hx_cons.
      destruct (Hab x Hx_incl Hx_cons) as (y & Hy_incl & Hy_equiv & Hy_cons).
      exists y. split; [| split; [exact Hy_equiv|]].
      - eapply incl_tran; [exact Hy_incl | apply submultiset_incl, Hbc_t].
      - eapply Hcm.
        + eapply allowed_submultiset; [exact Halb | apply submultiset_app_r].
        + eapply allowed_submultiset; [exact Halc | apply submultiset_app_r].
        + exact Hbc_t.
        + exact Hy_cons.
    Qed.

    Lemma gstep_le_strong g e g' : gstep g e g' -> le_strong g g'.
    Proof.
      intros Hstep. cbv [le_strong Forall2_map]. intros k. invert Hstep.
      - rewrite get_mupd. destr (eqb n k).
        + destruct (map.get g k) as [v|]; [|exact I].
          cbn [option_map enqueue gns_node_state gns_trace gns_queue].
          split; [apply submultiset_refl | apply submultiset_app_mid].
        + destruct (map.get g k) as [v|]; [|exact I]. split; apply submultiset_refl.
      - rewrite get_map_values'. destr (eqb n k).
        + rewrite map.get_put_same, H.
          cbn [option_map enqueue gns_node_state gns_trace gns_queue].
          replace (inputs_of (O_event lbl outs :: gns_trace ns))
            with (inputs_of (gns_trace ns)) by reflexivity.
          split; [apply submultiset_refl | apply submultiset_app_mid].
        + rewrite map.get_put_diff by congruence.
          destruct (map.get g k) as [v|]; [|exact I].
          cbn [option_map enqueue gns_node_state gns_trace gns_queue].
          split; [apply submultiset_refl | apply submultiset_app_mid].
      - destr (eqb n k).
        + rewrite map.get_put_same, H. cbn [gns_trace gns_queue].
          replace (inputs_of (I_event m :: gns_trace ns))
            with (m :: inputs_of (gns_trace ns)) by reflexivity.
          rewrite H1. split; [apply submultiset_cons | apply submultiset_perm, perm_recv].
        + rewrite map.get_put_diff by congruence.
          destruct (map.get g k) as [v|]; [|exact I]. split; apply submultiset_refl.
    Qed.

    Lemma le_strong_refl g : le_strong g g.
    Proof. apply Forall2_map_refl. intros. split; apply submultiset_refl. Qed.

    Lemma star_gstep_le_strong g T g' : star gstep g T g' -> le_strong g g'.
    Proof.
      induction 1; [apply le_strong_refl|].
      eapply le_strong_trans; [eassumption | eapply gstep_le_strong; eassumption].
    Qed.

    Lemma le_strong_le_weak a b : le_strong a b -> le_weak a b.
    Proof.
      intros. eapply Forall2_map_impl; eauto. simpl.
      intros. fwd. auto using incl_mod_weak_of_submultiset.
    Qed.

    Lemma graph_step_to_node_step gs gt gs' :
      star gstep gs gt gs' ->
      Forall2_map (fun _ gns1 gns2 =>
                     exists t'',
                       gns2.(gns_trace) = t'' ++ gns1.(gns_trace) /\
                         star node_step gns1.(gns_node_state) t'' gns2.(gns_node_state))
        gs gs'.
    Proof.
      induction 1 as [ | gt2 smid e gs' Hstar IH Hstep].
      - apply Forall2_map_dup. intros n gns _. exists []. ssplit; eauto.
      - invert Hstep.
        + apply Forall2_map_mupd_r; [intros ? ? HR; exact HR | exact IH].
        + apply Forall2_map_map_values'_r. simpl.
          epose proof (Forall2_map_get_r _ _ _ _ _ IH H) as (v1 & Hv1 & Hrel).
          eapply Forall2_map_put_r; try eassumption.
          -- eapply Forall2_map_impl; [exact IH|]. intros k' w1 w2 (t'' & ? & ?) ?.
             exists t''. ssplit; eauto.
          -- destruct Hrel as (t'' & Htr & Hst). exists (O_event lbl outs :: t''). ssplit; eauto.
             simpl. rewrite Htr. reflexivity.
        + simpl. epose proof (Forall2_map_get_r _ _ _ _ _ IH H) as (v1 & Hv1 & Hrel).
          eapply Forall2_map_put_r; try eassumption.
          -- eapply Forall2_map_impl; [exact IH|]. intros k' w1 w2 (t'' & ? & ?) ?.
             exists t''. ssplit; eauto.
          -- destruct Hrel as (t'' & Htr & Hst). exists (I_event m :: t''). ssplit; eauto.
             simpl. rewrite Htr. reflexivity.
    Qed.

    Lemma graph_step_to_node_step_from_beginning gs gt :
      star gstep initial_gs gt gs ->
      Forall2_map (fun _ gns0 gns =>
                     star node_step gns0.(gns_node_state) gns.(gns_trace) gns.(gns_node_state))
        initial_gs gs.
    Proof.
      intros. eapply Forall2_map_impl_strong.
      { eapply graph_step_to_node_step; eauto. }
      intros n gns0 gns H1 _ (t'' & Htr & Hst).
      apply initial_gs_empty in H1. destruct H1 as [Htr0 _].
      rewrite Htr0, app_nil_r in Htr. subst t''. eauto.
    Qed.

    (* [node_fold proj gs] collects, over every node [k] of [gs], the projection
       [proj k] of node [k]'s outputs.  all_outputs / fwd_total / output_total are
       instances, so the structural lemmas are proved once here. *)
    Definition node_fold {X} (proj : node_id -> list message -> list X) (gs : graph_state) : list X :=
      flat_map (fun '(k, v) => proj k (outputs_of v.(gns_trace))) (map.tuples gs).

    Lemma node_fold_put_None {X} (proj : node_id -> list message -> list X) gs k v :
      map.get gs k = None ->
      Permutation (node_fold proj (map.put gs k v))
                  (proj k (outputs_of v.(gns_trace)) ++ node_fold proj gs).
    Proof.
      intros Hk. unfold node_fold.
      assert (Hperm : Permutation (map.tuples (map.put gs k v)) ((k, v) :: map.tuples gs)).
      { apply NoDup_Permutation.
        - apply map.tuples_NoDup.
        - constructor.
          + intro Hin. apply map.tuples_spec in Hin. congruence.
          + apply map.tuples_NoDup.
        - intros [k0 v0]. exact (map.tuples_put gs k v Hk k0 v0). }
      eapply perm_trans; [ apply (Permutation_flat_map _ Hperm) | ].
      cbn [flat_map]. apply Permutation_refl.
    Qed.

    Lemma node_fold_put_cons {X} (proj : node_id -> list message -> list X) gs k v0 v :
      map.get gs k = Some v0 ->
      Permutation (node_fold proj (map.put gs k v))
                  (proj k (outputs_of v.(gns_trace)) ++ node_fold proj (map.remove gs k)).
    Proof.
      intros Hk.
      replace (map.put gs k v) with (map.put (map.remove gs k) k v).
      2:{ apply map.map_ext. intro j. rewrite !map.get_put_dec, map.get_remove_dec.
          destr_sth Nat.eqb; reflexivity. }
      apply node_fold_put_None. apply map.get_remove_same.
    Qed.

    Lemma node_fold_put_same {X} (proj : node_id -> list message -> list X) gs k v0 v :
      map.get gs k = Some v0 ->
      outputs_of v.(gns_trace) = outputs_of v0.(gns_trace) ->
      Permutation (node_fold proj (map.put gs k v)) (node_fold proj gs).
    Proof.
      intros Hk Ho.
      assert (Eq : node_fold proj gs = node_fold proj (map.put gs k v0))
        by (rewrite (map.put_noop k v0 gs Hk); reflexivity).
      rewrite Eq.
      eapply perm_trans; [ apply (node_fold_put_cons proj gs k v0 v Hk) | ].
      rewrite Ho. apply Permutation_sym. apply (node_fold_put_cons proj gs k v0 v0 Hk).
    Qed.

    Lemma node_fold_map_values' {X} (proj : node_id -> list message -> list X)
        (H : node_id -> graph_node_state node_state -> graph_node_state node_state) (M : graph_state) :
      (forall k v, (H k v).(gns_trace) = v.(gns_trace)) ->
      Permutation (node_fold proj (map_values' H M)) (node_fold proj M).
    Proof.
      intros Htr. induction M as [| m IH k v Hk] using map.map_ind.
      - assert (E : map_values' H map.empty = (map.empty : graph_state)).
        { apply map.map_ext. intro j. rewrite get_map_values', !map.get_empty. reflexivity. }
        rewrite E. apply Permutation_refl.
      - rewrite map_values'_put.
        eapply perm_trans.
        { apply (node_fold_put_None proj (map_values' H m) k (H k v)).
          rewrite get_map_values', Hk. reflexivity. }
        rewrite (Htr k v).
        eapply perm_trans; [ apply Permutation_app_head; exact IH | ].
        apply Permutation_sym. apply (node_fold_put_None proj m k v Hk).
    Qed.

    Lemma node_fold_run {X} (proj : node_id -> list message -> list X)
        (Hproj : forall k a b, proj k (a ++ b) = proj k a ++ proj k b)
        gs n ns lbl outs ns' :
      map.get gs n = Some ns ->
      Permutation
        (node_fold proj (map_values' (fun k => enqueue (filter (forward n k) outs))
             (map.put gs n {| gns_node_state := ns';
                              gns_trace := O_event lbl outs :: ns.(gns_trace);
                              gns_queue := ns.(gns_queue) |})))
        (proj n outs ++ node_fold proj gs).
    Proof.
      intros Hget.
      eapply perm_trans.
      { apply node_fold_map_values'. intros k0 v0. reflexivity. }
      eapply perm_trans; [ apply (node_fold_put_cons proj gs n ns _ Hget) | ].
      cbn [gns_trace].
      replace (outputs_of (O_event lbl outs :: ns.(gns_trace)))
        with (outs ++ outputs_of ns.(gns_trace)) by reflexivity.
      rewrite Hproj, <- app_assoc. apply Permutation_app_head.
      pose proof (node_fold_put_cons proj gs n ns ns Hget) as Hc.
      rewrite (map.put_noop n ns gs Hget) in Hc. symmetry. exact Hc.
    Qed.

    Lemma node_fold_mupd_enqueue {X} (proj : node_id -> list message -> list X) gs n inps :
      Permutation (node_fold proj (mupd gs n (enqueue inps))) (node_fold proj gs).
    Proof.
      unfold mupd. destruct (map.get gs n) as [vn|] eqn:Hgn; [| apply Permutation_refl].
      apply (node_fold_put_same proj gs n vn (enqueue inps vn) Hgn). reflexivity.
    Qed.

    Lemma node_fold_initial {X} (proj : node_id -> list message -> list X) :
      (forall k, proj k [] = []) ->
      node_fold proj initial_gs = [].
    Proof.
      intros Hnil. unfold node_fold. apply flat_map_all_nil. intros [k v] Hin.
      apply map.tuples_spec in Hin.
      rewrite (proj1 (initial_gs_empty k v Hin)). apply Hnil.
    Qed.

    Lemma node_fold_get {X} (proj : node_id -> list message -> list X) gs n vn :
      map.get gs n = Some vn -> incl (proj n (outputs_of vn.(gns_trace))) (node_fold proj gs).
    Proof.
      intros Hn x Hx. unfold node_fold. apply in_flat_map.
      exists (n, vn). split; [ apply map.tuples_spec; exact Hn | exact Hx ].
    Qed.

    Definition all_outputs := node_fold (fun k => map (pair k)).
    Definition fwd_total (nn : node_id) := node_fold (fun k => filter (forward k nn)).
    Definition output_total :=
      node_fold (fun k outs => map (fun m => (m, k)) (filter (output_visible k) outs)).

    Lemma fwd_total_get gs n k vn :
      map.get gs n = Some vn ->
      incl (filter (forward n k) (outputs_of (gns_trace vn))) (fwd_total k gs).
    Proof. exact (node_fold_get (fun k' => filter (forward k' k)) gs n vn). Qed.

    Lemma outputs_are_node_outputs gt gs :
      star gstep initial_gs gt gs ->
      Permutation (outputs_of gt) (output_total gs).
    Proof.
      unfold output_total.
      induction 1 as [ | gt0 gmid e gs Hstar IH Hstep ].
      - rewrite node_fold_initial by (intros; reflexivity). reflexivity.
      - invert Hstep.
        + eapply perm_trans; [ exact IH | ]. symmetry. apply node_fold_mupd_enqueue.
        + eapply perm_trans;
            [ | symmetry; eapply node_fold_run;
                [ intros; rewrite filter_app, map_app; reflexivity | eassumption ] ].
          cbn [outputs_of flat_map]. apply Permutation_app_head. exact IH.
        + eapply perm_trans; [ exact IH | ]. symmetry.
          eapply node_fold_put_same; [ eassumption | reflexivity ].
    Qed.

    Lemma matching_inps_app nn (e1 e2 : list (message * node_id)) :
      matching_inps nn (e1 ++ e2) = matching_inps nn e1 ++ matching_inps nn e2.
    Proof. unfold matching_inps. rewrite filter_app, map_app. reflexivity. Qed.

    Lemma matching_inps_single nn n0 m :
      matching_inps nn [(m, n0)] = if eqb nn n0 then [m] else [].
    Proof. unfold matching_inps. cbn [filter]. destr (eqb nn n0); reflexivity. Qed.

    Lemma matching_inps_perm nn e1 e2 :
      Permutation e1 e2 -> Permutation (matching_inps nn e1) (matching_inps nn e2).
    Proof. intros HP. unfold matching_inps. rewrite HP. reflexivity. Qed.

    Definition conserved (gs : graph_state) (ext : list (message * node_id)) : Prop :=
      forall nn nsn, map.get gs nn = Some nsn ->
        Permutation (inputs_of nsn.(gns_trace) ++ nsn.(gns_queue))
                    (fwd_total nn gs ++ matching_inps nn ext).

    Lemma conservation_step gs e gs' :
      gstep gs e gs' ->
      forall ext, conserved gs ext -> conserved gs' (ext ++ inputs_of [e]).
    Proof.
      intros Hstep ext IH. cbv [conserved] in IH |- *. intros nn nsn Hg'. invert Hstep.
      - rewrite get_mupd in Hg'.
        change (inputs_of [I_event (m, n)]) with [(m, n)].
        rewrite matching_inps_app, (matching_inps_single nn n m), (eqb_sym nn n).
        eapply perm_trans;
          [ | symmetry; apply Permutation_app_tail;
              apply (node_fold_mupd_enqueue (fun k => filter (forward k nn)) gs n [m]) ].
        destr (eqb n nn).
        + destruct (map.get gs nn) as [vn|] eqn:Hgn.
          2:{ cbn [option_map] in Hg'. discriminate. }
          cbn [option_map] in Hg'. injection Hg' as Hnsn. subst nsn.
          cbn [enqueue gns_trace gns_queue]. change ([m] ++ gns_queue vn) with (m :: gns_queue vn).
          transitivity (m :: (inputs_of (gns_trace vn) ++ gns_queue vn));
            [ symmetry; apply Permutation_middle | ].
          transitivity (m :: (fwd_total nn gs ++ matching_inps nn ext));
            [ apply perm_skip; apply (IH nn vn Hgn) | ].
          transitivity ((fwd_total nn gs ++ matching_inps nn ext) ++ [m]);
            [ apply Permutation_cons_append | ].
          rewrite app_assoc. apply Permutation_refl.
        + rewrite app_nil_r. apply IH. exact Hg'.
      - rewrite get_map_values', map.get_put_dec in Hg'.
        match goal with |- context[matching_inps nn (ext ++ ?x)] =>
          replace x with (@nil (message * node_id)) by reflexivity end.
        rewrite app_nil_r.
        eapply perm_trans;
          [ | symmetry; apply Permutation_app_tail;
              apply (node_fold_run (fun k => filter (forward k nn))
                       ltac:(intros; apply filter_app) gs n ns lbl outs ns' H) ].
        destr_sth Nat.eqb.
        + cbn [option_map] in Hg'. injection Hg' as Hnsn. subst nsn.
          cbn [enqueue gns_trace gns_queue].
          change (inputs_of (O_event lbl outs :: gns_trace ns)) with (inputs_of (gns_trace ns)).
          rewrite <- app_assoc. apply perm_ins. apply (IH nn ns H).
        + destruct (map.get gs nn) as [vn|] eqn:Hgn.
          2:{ cbn [option_map] in Hg'. discriminate. }
          cbn [option_map] in Hg'. injection Hg' as Hnsn. subst nsn.
          cbn [enqueue gns_trace gns_queue].
          rewrite <- app_assoc. apply perm_ins. apply (IH nn vn Hgn).
      - rewrite map.get_put_dec in Hg'.
        match goal with |- context[matching_inps nn (ext ++ ?x)] =>
          replace x with (@nil (message * node_id)) by reflexivity end.
        rewrite app_nil_r.
        pose proof (node_fold_put_same (fun k => filter (forward k nn)) gs n ns
                      {| gns_node_state := ns'; gns_trace := I_event m :: ns.(gns_trace);
                         gns_queue := ms1 ++ ms2 |} H eq_refl) as Hfwd.
        eapply perm_trans; [ | symmetry; apply Permutation_app_tail; exact Hfwd ].
        destr_sth Nat.eqb.
        + injection Hg' as Hnsn. subst nsn. cbn [gns_trace gns_queue].
          change (inputs_of (I_event m :: gns_trace ns)) with (m :: inputs_of (gns_trace ns)).
          transitivity (inputs_of (gns_trace ns) ++ gns_queue ns); [ | apply (IH nn ns H) ].
          rewrite H1, <- app_comm_cons.
          rewrite (app_assoc (inputs_of (gns_trace ns)) ms1 ms2),
                  (app_assoc (inputs_of (gns_trace ns)) ms1 (m :: ms2)).
          apply Permutation_middle.
        + apply IH. exact Hg'.
    Qed.

    Lemma conserved_perm_ext gs e1 e2 :
      Permutation e1 e2 -> conserved gs e1 -> conserved gs e2.
    Proof.
      intros HP Hc nn nsn Hget. eapply perm_trans; [ apply (Hc nn nsn Hget) | ].
      apply Permutation_app_head. apply matching_inps_perm. exact HP.
    Qed.

    Lemma conservation_gen gs0 T gs1 :
      star gstep gs0 T gs1 ->
      forall ext, conserved gs0 ext -> conserved gs1 (ext ++ inputs_of T).
    Proof.
      induction 1 as [ | T0 smid e sfin Hstar IH Hstep ]; intros ext Hconv.
      - cbn [inputs_of flat_map]. rewrite app_nil_r. exact Hconv.
      - eapply conserved_perm_ext;
          [ | apply (conservation_step _ _ _ Hstep _ (IH ext Hconv)) ].
        change (e :: T0) with ([e] ++ T0). rewrite inputs_of_app, <- !app_assoc.
        apply Permutation_app_head. apply Permutation_app_comm.
    Qed.

    Lemma inputs_are_outputs gt gs :
      star gstep initial_gs gt gs ->
      Forall_map (fun nn ns =>
                    Permutation (inputs_of ns.(gns_trace) ++ ns.(gns_queue))
                                (fwd_total nn gs ++ matching_inps nn (inputs_of gt)))
        gs.
    Proof.
      intros Hstar. cbv [Forall_map]. intros nn nsn Hget.
      assert (Hbase : conserved initial_gs []).
      { intros k v Hget0. pose proof (initial_gs_empty k v Hget0) as [Ht Hq].
        rewrite Ht, Hq. unfold fwd_total. rewrite node_fold_initial by (intros; reflexivity).
        reflexivity. }
      pose proof (conservation_gen initial_gs gt gs Hstar [] Hbase) as Hcons.
      rewrite app_nil_l in Hcons. exact (Hcons nn nsn Hget).
    Qed.

    Lemma fwd_total_consistent_internal gt gs nn :
      star gstep initial_gs gt gs ->
      consistent_internal_inputs_to nn (fwd_total nn gs).
    Proof.
      intros Hstar. unfold consistent_internal_inputs_to.
      exists (map fst (map.tuples gs)),
             (map (fun kv => outputs_of (snd kv).(gns_trace)) (map.tuples gs)).
      ssplit.
      - rewrite <- keys_eq_tuples. apply map.keys_NoDup.
      - apply Forall2_map_map. apply Forall_forall. intros [k v] Hin. cbn [fst snd].
        apply map.tuples_spec in Hin.
        pose proof (graph_step_to_node_step_from_beginning gs gt Hstar) as Hnodes.
        destruct (Forall2_map_get_r _ _ _ _ _ Hnodes Hin) as (gns0 & Hget0 & Hrun).
        pose proof (nodes_good k gns0 Hget0) as (Howf & _ & _).
        exact (Howf _ _ Hrun).
      - unfold fwd_total, node_fold. rewrite combine_map, flat_map_map.
        apply flat_map_ext. intros [k v]. reflexivity.
    Qed.

    Lemma everything_allowed gt gs :
      star gstep initial_gs gt gs ->
      graph_inputs_allowed (inputs_of gt) ->
      Forall_map (fun _ ns => allowed (inputs_of ns.(gns_trace) ++ ns.(gns_queue))) gs.
    Proof.
      intros Hstar Hallow. cbv [Forall_map]. intros nn nsn Hget.
      eapply Permutation_allowed.
      - apply (inputs_are_outputs gt gs Hstar nn nsn Hget).
      - apply Hallow. apply (fwd_total_consistent_internal gt gs nn Hstar).
    Qed.

    Lemma node_run_allowed t gs :
      star gstep initial_gs t gs ->
      graph_inputs_allowed (inputs_of t) ->
      Forall2_map (fun n gns0 gns =>
                     star node_step (gns_node_state gns0) (gns_trace gns) (gns_node_state gns) /\
                     allowed (inputs_of (gns_trace gns)))
        initial_gs gs.
    Proof.
      intros Hstar Hallow.
      pose proof (everything_allowed t gs Hstar Hallow) as Hall.
      eapply Forall2_map_impl_strong;
        [ eapply graph_step_to_node_step_from_beginning; exact Hstar | ].
      intros n gns0 gns Hget0 Hget Hrun. split; [ exact Hrun | ].
      eapply allowed_submultiset; [ apply (Hall n gns Hget) | apply submultiset_app_r ].
    Qed.

    Lemma graph_will_step_of_node_will_step n P gs gt gns :
      star gstep initial_gs gt gs ->
      map.get gs n = Some gns ->
      will_step node_step allowed (gns.(gns_node_state), gns.(gns_trace)) P ->
      graph_will_step
        (gs, gt)
        (fun '(gs', _) =>
           val_sat gs' n (fun gns' => P (gns'.(gns_node_state), gns'.(gns_trace)))).
    Proof.
      intros H Hn Hns. induction Hns.
      - cbv [graph_will_step will_step]. eexists. intros.
        pose proof H1 as HD.
        apply graph_step_to_node_step in H1.
        eapply Forall2_map_get_l in H1; eauto. fwd.
        specialize (H0 _ _ ltac:(eassumption)). specialize' H0.
        { eapply allowed_submultiset.
          - eapply everything_allowed. 2: eassumption. all: eauto.
          - rewrite H1p1p0. eexists. apply Permutation_refl. }
        destruct H0; fwd.
        + left. cbv [val_sat]. eexists. rewrite H1p1p0. eauto.
        + right. do 2 eexists. split.
          * eapply gstep_run; eassumption.
          * cbv [val_sat]. eexists. split.
            -- rewrite get_map_values', map.get_put_same. simpl. reflexivity.
            -- simpl. rewrite H1p1p0. assumption.
    Qed.

    (*TODO replace stuff about initial_graph_state with hypotheses just about gs*)
    Lemma graph_eventually_of_node_eventually n P gs gt gns :
      star gstep initial_gs gt gs ->
      graph_inputs_allowed (inputs_of gt) ->
      map.get gs n = Some gns ->
      eventually (will_step node_step allowed) P (gns.(gns_node_state), gns.(gns_trace)) ->
      eventually graph_will_step
        (fun '(gs', _) =>
           val_sat gs' n (fun gns' => P (gns'.(gns_node_state), gns'.(gns_trace))))
        (gs, gt).
    Proof.
      intros Hstar Hallow Hget Hev.
      remember (gns.(gns_node_state), gns.(gns_trace)) as nodeSt eqn:E.
      revert gs gt gns Hstar Hallow Hget E.
      induction Hev; intros gs gt gns Hstar Hallow Hget E; subst.
      { eauto. }
      eapply eventually_step_cps. apply will_step_reach. eapply will_step_impl.
      { eapply graph_will_step_of_node_will_step; eauto. }
      simpl. cbv [val_sat reachable]. intros. fwd. intros. fwd. eauto.
    Qed.

    (*TODO also specify that internal_inps are the same as internal_outs, which could
      be ensured using node traces?*)
    Definition consistency_le n ms1 ms2 :=
      exists internal_inps1 exts1 internal_inps2 exts2,
        Permutation ms1 (internal_inps1 ++ exts1) /\
          consistent_internal_inputs_to n internal_inps1 /\
          Permutation ms2 (internal_inps2 ++ exts2) /\
          consistent_internal_inputs_to n internal_inps2 /\
          submultiset exts1 exts2.

    Lemma incl_mod_weak_consistency_le_le ms1 ms2 n :
      allowed ms1 ->
      allowed ms2 ->
      incl_mod_weak equiv ms1 ms2 ->
      consistency_le n ms1 ms2 ->
      incl_mod equiv consistent ms1 ms2.
    Proof.
      intros Hal1 Hal2 Hweak Hc. cbv [incl_mod]. intros a Ha Hca.
      assert (Hbs: exists bs, incl bs ms2 /\ Forall2 equiv a bs).
      { eauto using incl_mod_weak_Forall2. }
      fwd. exists bs. ssplit; auto.
      cbv [consistent_good] in Hcg. cbv [consistency_le] in Hc. fwd.
      assert (allowed (internal_inps1 ++ exts1)) as Hal1'.
      { eauto using Permutation_allowed, Permutation_sym. }
      assert (allowed (internal_inps2 ++ exts2)) as Hal2'.
      { eauto using Permutation_allowed, Permutation_sym. }
      assert (allowed exts1) as Hae1.
      { eapply allowed_submultiset; [ exact Hal1' | exists internal_inps1; apply Permutation_app_comm ]. }
      assert (allowed exts2) as Hae2.
      { eapply allowed_submultiset; [ exact Hal2' | exists internal_inps2; apply Permutation_app_comm ]. }
      enough (consistent bs (internal_inps2 ++ exts2)).
      { eapply consistent_perm;
          [ exact Hcm | exact Hal2' | exact Hal2 | apply Permutation_sym; exact Hcp2 | eassumption ]. }
      rewrite Hcg. 2: exact Hcp3.
      eapply Hcim; [ exact Hae1 | exact Hae2 | exact Hcp4 | ].
      enough (consistent_inputs a exts1).
      { eapply consistent_inputs_equiv; eassumption. }
      rewrite <- Hcg. 2: exact Hcp1.
      enough (consistent a ms1).
      { eapply consistent_perm;
          [ exact Hcm | exact Hal1 | exact Hal1' | exact Hcp0 | eassumption ]. }
      assumption.
    Qed.

    Lemma reachable_domain t gs nn :
      star gstep initial_gs t gs ->
      (map.get initial_gs nn = None <-> map.get gs nn = None).
    Proof.
      intros Hstar.
      eapply Forall2_map_get_None.
      eapply graph_step_to_node_step_from_beginning. exact Hstar.
    Qed.

    Lemma submultiset_matching_inps nn l1 l2 :
      submultiset l1 l2 -> submultiset (matching_inps nn l1) (matching_inps nn l2).
    Proof.
      intros (rest & Hperm). exists (matching_inps nn rest).
      rewrite <- matching_inps_app. apply matching_inps_perm. exact Hperm.
    Qed.

    Lemma graph_inputs_allowed_submultiset i1 i2 :
      submultiset i1 i2 -> graph_inputs_allowed i2 -> graph_inputs_allowed i1.
    Proof.
      intros Hsub Hga n ii Hii.
      eapply allowed_submultiset; [ apply (Hga n ii Hii) | ].
      destruct (submultiset_matching_inps n _ _ Hsub) as (rest & Hp).
      exists rest. rewrite <- app_assoc. apply Permutation_app_head. exact Hp.
    Qed.

    Lemma consistency_le_reachable t1 t2 gs1 gs2 n ns1 ns2 :
      star gstep initial_gs t1 gs1 ->
      star gstep initial_gs t2 gs2 ->
      submultiset (inputs_of t1) (inputs_of t2) ->
      map.get gs1 n = Some ns1 ->
      map.get gs2 n = Some ns2 ->
      consistency_le n (inputs_of ns1.(gns_trace) ++ ns1.(gns_queue))
                       (inputs_of ns2.(gns_trace) ++ ns2.(gns_queue)).
    Proof.
      intros Hstar1 Hstar2 Hsub Hget1 Hget2.
      cbv [consistency_le].
      pose proof (inputs_are_outputs _ _ Hstar1) as Hio1. cbv [Forall_map] in Hio1.
      specialize (Hio1 _ _ Hget1).
      pose proof (inputs_are_outputs _ _ Hstar2) as Hio2. cbv [Forall_map] in Hio2.
      specialize (Hio2 _ _ Hget2).
      exists (fwd_total n gs1), (matching_inps n (inputs_of t1)),
             (fwd_total n gs2), (matching_inps n (inputs_of t2)).
      ssplit.
      - exact Hio1.
      - eapply fwd_total_consistent_internal. exact Hstar1.
      - exact Hio2.
      - eapply fwd_total_consistent_internal. exact Hstar2.
      - apply submultiset_matching_inps. exact Hsub.
    Qed.

    Lemma eventually_deliver n :
      forall N owed gc tc nc,
        length owed <= N ->
        star gstep initial_gs tc gc ->
        graph_inputs_allowed (inputs_of tc) ->
        map.get gc n = Some nc ->
        submultiset owed (gns_queue nc) ->
        eventually graph_will_step
          (fun '(gc', _) => exists nc', map.get gc' n = Some nc' /\
             submultiset (inputs_of (gns_trace nc) ++ owed) (inputs_of (gns_trace nc')))
          (gc, tc).
    Proof.
      induction N as [| N IHN]; intros owed gc tc nc HN Hstar Hga Hget Hsub;
        (destruct owed as [| a owed'];
         [ apply eventually_done; exists nc; split;
           [ exact Hget | rewrite app_nil_r; apply submultiset_refl ] | ]).
      - simpl in HN. inversion HN.
      - assert (Hlen' : length owed' <= N) by (simpl in HN; apply le_S_n; exact HN).
        assert (Ha_q : submultiset [a] (gns_queue nc)).
        { eapply submultiset_trans; [ | exact Hsub ]. exists owed'. reflexivity. }
        eapply eventually_step_cps. exists (receive n a).
        intros gs_d td Hstar_d Hga_d.
        pose proof (star_gstep_le_strong _ _ _ Hstar_d) as Hls. cbv [le_strong] in Hls.
        destruct (Forall2_map_get_l _ _ _ _ _ Hls Hget) as (nd & Hget_d & Htr & Htot).
        assert (Hstar_di : star gstep initial_gs (td ++ tc) gs_d)
          by (eapply star_app; [ exact Hstar | exact Hstar_d ]).
        assert (Htot_owed : submultiset (inputs_of (gns_trace nc) ++ a :: owed')
                              (inputs_of (gns_trace nd) ++ gns_queue nd))
          by (eapply submultiset_trans; [ apply submultiset_app_head; exact Hsub | exact Htot ]).
        destruct (classic (In a (gns_queue nd))) as [Hin_d | Hnin_d].
        + apply in_split in Hin_d. destruct Hin_d as (ms1 & ms2 & Hq).
          destruct (nodes_input_total (gns_node_state nd) a) as (nd' & Hns).
          right. eexists _, []. split.
          { eapply gstep_receive; [ exact Hget_d | exact Hns | exact Hq ]. }
          set (ndr := {| gns_node_state := nd'; gns_trace := I_event a :: gns_trace nd;
                         gns_queue := ms1 ++ ms2 |}).
          assert (Hget_r : map.get (map.put gs_d n ndr) n = Some ndr)
            by (apply map.get_put_same).
          assert (Hitr : inputs_of (gns_trace ndr) = a :: inputs_of (gns_trace nd))
            by reflexivity.
          assert (Ha_del : submultiset (inputs_of (gns_trace nc) ++ [a]) (inputs_of (gns_trace ndr))).
          { rewrite Hitr. eapply submultiset_perm_l; [ apply Permutation_cons_append | ].
            apply submultiset_cons_mono. exact Htr. }
          assert (Htot_r : submultiset (inputs_of (gns_trace nc) ++ a :: owed')
                             (inputs_of (gns_trace ndr) ++ gns_queue ndr)).
          { eapply submultiset_perm_r; [ | exact Htot_owed ].
            rewrite Hitr. subst ndr. cbn [gns_queue]. rewrite Hq.
            rewrite !app_assoc. symmetry. apply Permutation_middle. }
          destruct (submultiset_absorb (inputs_of (gns_trace nc)) owed'
                      (inputs_of (gns_trace ndr)) (gns_queue ndr) a Htot_r Ha_del)
            as (owed'' & HQ'' & Habs & Hlen'').
          eapply eventually_weaken.
          { eapply (IHN owed'' (map.put gs_d n ndr) (O_event (receive n a) [] :: td ++ tc) ndr).
            - eapply Nat.le_trans; [ exact Hlen'' | exact Hlen' ].
            - eapply star_step;
                [ exact Hstar_di | eapply gstep_receive; [ exact Hget_d | exact Hns | exact Hq ] ].
            - exact Hga_d.
            - exact Hget_r.
            - exact HQ''. }
          intros [gc'' t''] (nc'' & Hgc'' & Hcov). exists nc''. split; [ exact Hgc'' | ].
          eapply submultiset_trans; [ exact Habs | exact Hcov ].
        + left.
          assert (Ha_del : submultiset (inputs_of (gns_trace nc) ++ [a]) (inputs_of (gns_trace nd))).
          { eapply submultiset_cons_of_not_in; [ exact Htr | | exact Hnin_d ].
            eapply submultiset_trans; [ apply submultiset_app_head; exact Ha_q | exact Htot ]. }
          destruct (submultiset_absorb (inputs_of (gns_trace nc)) owed'
                      (inputs_of (gns_trace nd)) (gns_queue nd) a Htot_owed Ha_del)
            as (owed'' & HQ'' & Habs & Hlen'').
          eapply eventually_weaken.
          { eapply (IHN owed'' gs_d (td ++ tc) nd).
            - eapply Nat.le_trans; [ exact Hlen'' | exact Hlen' ].
            - exact Hstar_di.
            - exact Hga_d.
            - exact Hget_d.
            - exact HQ''. }
          intros [gc'' t''] (nc'' & Hgc'' & Hcov). exists nc''. split; [ exact Hgc'' | ].
          eapply submultiset_trans; [ exact Habs | exact Hcov ].
    Qed.

    Lemma eventually_received t2 gs2 :
      star gstep initial_gs t2 gs2 ->
      graph_inputs_allowed (inputs_of t2) ->
      eventually graph_will_step
        (fun '(gs2', _) =>
           Forall2_map (fun _ ns2 ns2' =>
                          submultiset (inputs_of ns2.(gns_trace) ++ ns2.(gns_queue))
                            (inputs_of ns2'.(gns_trace))) gs2 gs2')
        (gs2, t2).
    Proof.
      intros Hstar Hga.
      apply eventually_will_step_reach.
      eapply eventually_weaken.
      { eapply eventually_will_step_Forall with
          (Ps := map (fun '(k, v) =>
                    (fun '(gc', _) => exists nc', map.get gc' k = Some nc' /\
                       submultiset (inputs_of (gns_trace v) ++ gns_queue v)
                                   (inputs_of (gns_trace nc'))))
                    (map.tuples gs2)).
        - apply List.Forall_map. apply Forall_forall. intros [k v] _.
          cbv [ev_stable]. intros s s' e t (nc' & Hgk & Hsm) Hstep.
          pose proof (gstep_le_strong _ _ _ Hstep) as Hls. cbv [le_strong] in Hls.
          destruct (Forall2_map_get_l _ _ _ _ _ Hls Hgk) as (nc'' & Hgk' & Htr & _).
          exists nc''. split; [ exact Hgk' | eapply submultiset_trans; [ exact Hsm | exact Htr ] ].
        - apply List.Forall_map. apply Forall_forall. intros [k v] Hin.
          apply map.tuples_spec in Hin.
          eapply (eventually_deliver k (length (gns_queue v)) (gns_queue v) gs2 t2 v);
            [ apply le_n | exact Hstar | exact Hga | exact Hin | apply submultiset_refl ]. }
      intros [gs2' t2'] Hall Hreach.
      destruct Hreach as (tr & Hstar_gg & _ & _).
      pose proof (star_gstep_le_strong _ _ _ Hstar_gg) as Hls.
      eapply Forall2_map_impl_strong; [ exact Hls | ].
      intros k v v' Hgk Hgk' _. rewrite Forall_forall in Hall.
      destruct (Hall _ ltac:(apply in_map_iff; exists (k, v);
                  split; [ reflexivity | apply map.tuples_spec; exact Hgk ]))
        as (nc' & Hgk'' & Hsm).
      rewrite Hgk' in Hgk''. injection Hgk'' as <-. exact Hsm.
    Qed.

    Lemma le_weak_to_le gs1 t1 gs2 t2 :
      star gstep initial_gs t1 gs1 ->
      star gstep initial_gs t2 gs2 ->
      submultiset (inputs_of t1) (inputs_of t2) ->
      graph_inputs_allowed (inputs_of t2) ->
      le_weak gs1 gs2 ->
      eventually graph_will_step (fun '(gs2', _) => le gs1 gs2') (gs2, t2).
    Proof.
      intros Hstar1 Hstar2 Hsub Hga2 Hlew.
      assert (Hga1 : graph_inputs_allowed (inputs_of t1))
        by (eapply graph_inputs_allowed_submultiset; eassumption).
      pose proof (everything_allowed _ _ Hstar1 Hga1) as Hall1. cbv [Forall_map] in Hall1.
      pose proof (everything_allowed _ _ Hstar2 Hga2) as Hall2. cbv [Forall_map] in Hall2.
      apply eventually_will_step_reach.
      eapply eventually_weaken.
      { exact (eventually_received _ _ Hstar2 Hga2). }
      intros [gs2' t2'] Hrecv (tr & Htr & -> & Hga2imp).
      assert (Hreach2' : star gstep initial_gs (tr ++ t2) gs2')
        by (eapply star_app; [ exact Hstar2 | exact Htr ]).
      specialize (Hga2imp Hga2).
      pose proof (everything_allowed _ _ Hreach2' Hga2imp) as Hall2'. cbv [Forall_map] in Hall2'.
      cbv [le]. apply Forall2_map_intro.
      { intros k. split; intros HN.
        - apply (proj1 (reachable_domain _ _ k Hreach2')).
          apply (proj2 (reachable_domain _ _ k Hstar1)). exact HN.
        - apply (proj1 (reachable_domain _ _ k Hstar1)).
          apply (proj2 (reachable_domain _ _ k Hreach2')). exact HN. }
      intros k ns1 ns2' Hg1 Hg2'.
      destruct (Forall2_map_get_r _ _ _ _ _ Hrecv Hg2') as (ns2 & Hg2 & Hrec).
      destruct (Forall2_map_get_l _ _ _ _ _ Hlew Hg1) as (ns2b & Hg2b & Hlewk).
      assert (ns2b = ns2) by congruence. subst ns2b.
      pose proof (consistency_le_reachable _ _ _ _ _ _ _ Hstar1 Hstar2 Hsub Hg1 Hg2) as Hcle.
      specialize (Hall1 _ _ Hg1).
      specialize (Hall2 _ _ Hg2).
      specialize (Hall2' _ _ Hg2').
      assert (Hall1tr : allowed (inputs_of (gns_trace ns1)))
        by (eapply allowed_submultiset; [ exact Hall1 | apply submultiset_app_r ]).
      assert (Hall2'tr : allowed (inputs_of (gns_trace ns2')))
        by (eapply allowed_submultiset; [ exact Hall2' | apply submultiset_app_r ]).
      apply (incl_mod_weaken_r equiv consistent allowed Hcm _ _ _ Hrec Hall2 Hall2'tr).
      apply (incl_mod_weaken_l equiv consistent allowed Hcm _ _ _
               (submultiset_app_r _ _) Hall1tr Hall1).
      apply (incl_mod_weak_consistency_le_le _ _ _ Hall1 Hall2 Hlewk Hcle).
    Qed.

    Lemma fwd_total_sub_combined T r k vk :
      star gstep initial_gs T r ->
      map.get r k = Some vk ->
      submultiset (fwd_total k r) (inputs_of (gns_trace vk) ++ gns_queue vk).
    Proof.
      intros HT Hk. pose proof (inputs_are_outputs _ _ HT) as Hio.
      cbv [Forall_map] in Hio. specialize (Hio _ _ Hk).
      eapply submultiset_trans;
        [ apply submultiset_app_r | apply submultiset_perm, Permutation_sym, Hio ].
    Qed.

    Lemma forwarded_in_state T r n k vn vk os :
      star gstep initial_gs T r ->
      map.get r n = Some vn ->
      map.get r k = Some vk ->
      Forall (fun o => exists o', equiv o o' /\ In o' (outputs_of (gns_trace vn))) os ->
      incl_mod_weak equiv (filter (forward n k) os)
                          (inputs_of (gns_trace vk) ++ gns_queue vk).
    Proof.
      intros HT Hn Hk Hos.
      assert (Hl1 : incl_mod_weak equiv (filter (forward n k) os)
                      (filter (forward n k) (outputs_of (gns_trace vn)))).
      { intros x Hx. apply filter_In in Hx. destruct Hx as [Hxos Hxf].
        rewrite Forall_forall in Hos. destruct (Hos x Hxos) as (x' & Hequiv & Hx'out).
        exists x'. split.
        - apply filter_In. split;
            [ exact Hx'out | rewrite <- (forward_equiv n k x x' Hequiv); exact Hxf ].
        - exact Hequiv. }
      assert (Hl2 : incl_mod_weak equiv (filter (forward n k) (outputs_of (gns_trace vn)))
                      (fwd_total k r)) by eauto using fwd_total_get.
      assert (Hl3 : incl_mod_weak equiv (fwd_total k r)
                      (inputs_of (gns_trace vk) ++ gns_queue vk))
        by eauto using incl_mod_weak_of_submultiset, fwd_total_sub_combined.
      eauto using incl_mod_weak_trans.
    Qed.

    Lemma node_will_match' gs1 t1 lbl outs gs1' gs2 t2 :
      star gstep initial_gs t1 gs1 ->
      star gstep initial_gs t2 gs2 ->
      graph_inputs_allowed (inputs_of t1) ->
      graph_inputs_allowed (inputs_of t2) ->
      gstep gs1 (O_event lbl outs) gs1' ->
      le gs1 gs2 ->
      le_weak gs1 gs2 ->
      eventually graph_will_step (fun '(gs2', _) => le_weak gs1' gs2') (gs2, t2).
    Proof.
      intros H1 H2 H3 H4 Hstep Hle Hlew.
      epose proof Forall2_map_get_l as Hle'. specialize Hle' with (1 := Hle).
      epose proof Forall2_map_get_l as Hlew'. specialize Hlew' with (1 := Hlew).

      epose proof (graph_step_to_node_step_from_beginning gs1 t1) as Hns1'.
      epose proof (graph_step_to_node_step_from_beginning gs2 t2) as Hns2'.
      especialize Hns1'; eauto. especialize Hns2'; eauto.

      invert Hstep.
      - especialize Hle'; eauto. especialize Hlew'; eauto. fwd. map_func.
        eapply Forall2_map_get_r in Hns1'; eauto. fwd.
        eapply Forall2_map_get_l in Hns2'; eauto. fwd.
        map_func. simpl in *.

        pose proof nodes_good as H'. cbv [Forall_map] in H'. especialize H'; eauto.
        cbv [node_good] in H'. fwd.

        pose proof (everything_allowed _ gs1 ltac:(eauto) ltac:(eauto)) as Hall1.
        pose proof (everything_allowed _ gs2 ltac:(eauto) ltac:(eauto)) as Hall2.
        assert (allowed (inputs_of (gns_trace ns) ++ gns_queue ns)) by eauto.
        assert (allowed (inputs_of (gns_trace v0) ++ gns_queue v0)) by eauto.

        eassert (Hmo: Forall (might_output_equiv _ _ (gns_node_state v0) (gns_trace v0)) outs0).
        { apply Forall_forall. intros m Hm.
          eapply (H'p1 (gns_trace ns)). all: eauto. eauto 10. }

        eapply will_output_all in Hmo; eauto.
        eapply graph_eventually_of_node_eventually in Hmo; eauto.

        apply eventually_will_step_reach.
        eapply eventually_weaken; [eassumption|].
        cbv [val_sat reachable]. intros [r l] Hval Hreach. fwd.
        pose proof (star_gstep_le_strong _ _ _ Hreachp0) as Hlsr.
        pose proof (le_weak_trans _ _ _ Hlew (le_strong_le_weak _ _ Hlsr)) as Hlwr.
        assert (Hrinit : star gstep initial_gs (tr ++ t2) r) by (eapply star_app; eauto).

        cbv [le_weak] in Hlwr |- *.
        apply Forall2_map_map_values'_l.
        eapply Forall2_map_put_l; [ | exact Hvalp0 | ].
        + eapply Forall2_map_impl_strong; [ exact Hlwr | ].
          intros k w1 w2 _ Hgr Hbase _. cbn [gns_trace gns_queue enqueue].
          apply incl_mod_weak_insert; eauto. eapply forwarded_in_state; eauto.
        + apply incl_mod_weak_insert.
          -- eapply Forall2_map_get_l in Hlwr; eauto. fwd. map_func. assumption.
          -- eapply forwarded_in_state; eauto.
      - especialize Hle'; eauto. especialize Hlew'; eauto. fwd.
        apply eventually_done.
        cbv [le_weak] in Hlew |- *.
        eapply Forall2_map_put_l; [ | exact Hlew'p0 | ].
        + eapply Forall2_map_impl; [ exact Hlew | ]. intros k w1 w2 HH _. exact HH.
        + cbn [gns_trace gns_queue].
          rewrite H9 in Hlew'p1.
          eapply incl_mod_weak_perm_l; [ apply perm_recv | exact Hlew'p1 ].
    Qed.

    Lemma node_will_match gs1 t1 lbl outs gs1' gs2 t2 :
      star gstep initial_gs t1 gs1 ->
      star gstep initial_gs t2 gs2 ->
      submultiset (inputs_of t1) (inputs_of t2) ->
      graph_inputs_allowed (inputs_of t1) ->
      graph_inputs_allowed (inputs_of t2) ->
      gstep gs1 (O_event lbl outs) gs1' ->
      le gs1 gs2 ->
      le_weak gs1 gs2 ->
      eventually graph_will_step
        (fun '(gs2', _) => le gs1' gs2' /\ le_weak gs1' gs2') (gs2, t2).
    Proof.
      intros Hstar1 Hstar2 Hsub Hga1 Hga2 Hstep Hle Hlew.
      assert (Hstar1' : star gstep initial_gs (O_event lbl outs :: t1) gs1')
        by (eapply star_step; [ exact Hstar1 | exact Hstep ]).
      pose proof (node_will_match' _ _ _ _ _ _ _ Hstar1 Hstar2 Hga1 Hga2 Hstep Hle Hlew) as Hev.
      apply eventually_will_step_annotate in Hev.
      eapply eventually_trans; [ exact Hev | ].
      intros [gs2' t2'] (Hreach' & Hlw).
      destruct Hreach' as (tr & Hstar_gg & -> & Hga_imp).
      assert (Hstar2' : star gstep initial_gs (tr ++ t2) gs2')
        by (eapply star_app; [ exact Hstar2 | exact Hstar_gg ]).
      specialize (Hga_imp Hga2).
      assert (Hsub' : submultiset (inputs_of (O_event lbl outs :: t1)) (inputs_of (tr ++ t2))).
      { rewrite inputs_of_app. change (inputs_of (O_event lbl outs :: t1)) with (inputs_of t1).
        eapply submultiset_trans;
          [ exact Hsub | exists (inputs_of tr); apply Permutation_app_comm ]. }
      pose proof (le_weak_to_le _ _ _ _ Hstar1' Hstar2' Hsub' Hga_imp Hlw) as Hle2.
      eapply eventually_weaken.
      { eapply eventually_carry_stable_gen with (P := (fun '(s, _) => le_weak gs1' s));
          [ | exact Hlw | exact Hle2 ].
        intros s s' e t Hlws Hst.
        eapply le_weak_trans;
          [ exact Hlws | apply le_strong_le_weak; eapply gstep_le_strong; exact Hst ]. }
      intros [s t] (Hlw_s & Hle_s). split; [ exact Hle_s | exact Hlw_s ].
    Qed.

    Lemma le_node_output t1 gs1 gs2 t2 n o :
      star gstep initial_gs t1 gs1 ->
      star gstep initial_gs t2 gs2 ->
      graph_inputs_allowed (inputs_of t1) ->
      graph_inputs_allowed (inputs_of t2) ->
      le gs1 gs2 ->
      node_has_output gs1 n o ->
      eventually graph_will_step
        (fun '(gs2', _) => exists o', node_has_output gs2' n o' /\ equiv o' o) (gs2, t2).
    Proof.
      intros Hstar1 Hstar2 Hga1 Hga2 Hle (ns1 & Hget1 & Hout1).
      destruct (Forall2_map_get_l _ _ _ _ _ Hle Hget1) as (ns2 & Hget2 & Hincl).
      destruct (Forall2_map_get_r _ _ _ _ _ (node_run_allowed t1 gs1 Hstar1 Hga1) Hget1)
        as (ns0 & Hget0 & Hrun1 & Hall1).
      destruct (Forall2_map_get_r _ _ _ _ _ (node_run_allowed t2 gs2 Hstar2 Hga2) Hget2)
        as (ns0' & Hget0' & Hrun2 & Hall2).
      assert (ns0' = ns0) by (rewrite Hget0 in Hget0'; congruence). subst ns0'.
      pose proof (nodes_good n ns0 Hget0) as (_ & Hmono & Hmiw).
      assert (Hmiw' : might_implies_will_equiv' node_step equiv consistent allowed
                        (gns_node_state ns0)).
      { apply ciw'_iff_ciw_and_monotone'; try assumption;
          try (split; [ exact Hmiw | exact Hmono ]). }
      pose proof (Hmiw' _ _ _ Hrun1 Hall1 Hout1 _ _ Hincl Hrun2 Hall2) as Hwoe.
      eapply eventually_weaken.
      { eapply (graph_eventually_of_node_eventually n _ gs2 t2 ns2);
          [ exact Hstar2 | exact Hga2 | exact Hget2 | exact Hwoe ]. }
      intros [gs2' t2'] (gns' & Hgetf & o' & Hequiv & Hino').
      exists o'. split; [ exists gns'; split; [ exact Hgetf | exact Hino' ] | exact Hequiv ].
    Qed.

    Definition graph_equiv (p1 p2 : message * node_id) : Prop :=
      equiv (fst p1) (fst p2) /\ snd p1 = snd p2.

    Global Instance graph_equiv_equiv : Equivalence graph_equiv.
    Proof.
      destruct equiv_equiv as [Href Hsym Htrans]. constructor.
      - intros [m n]. split; [ apply Href | reflexivity ].
      - intros [m1 n1] [m2 n2] (He & Hn). split; [ apply Hsym; exact He | symmetry; exact Hn ].
      - intros [m1 n1] [m2 n2] [m3 n3] (He1 & Hn1) (He2 & Hn2).
        split; [ eapply Htrans; eassumption | congruence ].
    Qed.

    Lemma in_output_total gs o :
      In o (output_total gs) ->
      exists m n, o = (m, n) /\ node_has_output gs n m /\ output_visible n m = true.
    Proof.
      unfold output_total, node_fold. intros Hin.
      apply in_flat_map in Hin. destruct Hin as ([k v] & Htup & Hin).
      apply in_map_iff in Hin. destruct Hin as (m0 & Heq & Hinf).
      apply filter_In in Hinf. destruct Hinf as (Hinout & Hvis).
      exists m0, k. split; [ symmetry; exact Heq | ].
      split; [ exists v; split; [ apply map.tuples_spec; exact Htup | exact Hinout ] | exact Hvis ].
    Qed.

    Lemma output_total_in gs n m :
      node_has_output gs n m -> output_visible n m = true -> In (m, n) (output_total gs).
    Proof.
      intros (v & Hget & Hinout) Hvis.
      unfold output_total, node_fold. apply in_flat_map. exists (n, v). split.
      - apply map.tuples_spec; exact Hget.
      - apply in_map_iff. exists m. split;
          [ reflexivity | apply filter_In; split; [ exact Hinout | exact Hvis ] ].
    Qed.

    Lemma drive_to_dominate t0 gs0 t' gs_f :
      star gstep initial_gs t0 gs0 ->
      graph_inputs_allowed (inputs_of t0) ->
      star gstep gs0 t' gs_f ->
      inputs_of t' = [] ->
      eventually graph_will_step
        (fun '(gs2, _) => le gs_f gs2 /\ le_weak gs_f gs2) (gs0, t0).
    Proof.
      intros Hstar0 Hga0 Hrun Hinp. revert Hinp.
      induction Hrun as [ | T0 gmid e gsf Hrun' IH Hstep ]; intros Hinp.
      - apply eventually_done. split; [ apply le_refl | apply le_weak_refl ].
      - destruct e as [m | lbl outs].
        { discriminate Hinp. }
        simpl in Hinp.
        specialize (IH Hinp).
        apply eventually_will_step_annotate in IH.
        eapply eventually_trans; [ exact IH | ].
        intros [gs2 t2] (Hreach & Hle_mid & Hlw_mid).
        destruct Hreach as (tr & Hstar_gg & -> & Hga_imp).
        specialize (Hga_imp Hga0).
        assert (Hstar2 : star gstep initial_gs (tr ++ t0) gs2) by eauto using star_app.
        assert (Hstarmid : star gstep initial_gs (T0 ++ t0) gmid) by eauto using star_app.
        assert (Hgamid : graph_inputs_allowed (inputs_of (T0 ++ t0))).
        { rewrite inputs_of_app, Hinp. cbn [app]. exact Hga0. }
        assert (Hsub : submultiset (inputs_of (T0 ++ t0)) (inputs_of (tr ++ t0))).
        { rewrite !inputs_of_app, Hinp. cbn [app].
          eexists. apply Permutation_app_comm. }
        eauto using node_will_match.
    Qed.

    Lemma graph_might_implies_will t gs o :
      star gstep initial_gs t gs ->
      graph_inputs_allowed (inputs_of t) ->
      might_output gstep gs t o ->
      will_output_equiv gstep graph_equiv graph_inputs_allowed gs t o.
    Proof.
      intros Hstar Hga (t' & gs_f & Hrun & Hinp & Hino).
      assert (Hstarf : star gstep initial_gs (t' ++ t) gs_f) by eauto using star_app.
      assert (Hgaf : graph_inputs_allowed (inputs_of (t' ++ t))).
      { rewrite inputs_of_app, Hinp. cbn [app]. exact Hga. }
      assert (Hint : In o (output_total gs_f)).
      { eapply Permutation_in;
          [ apply (outputs_are_node_outputs (t' ++ t) gs_f Hstarf) | exact Hino ]. }
      apply in_output_total in Hint. destruct Hint as (m & n & -> & Hnho & Hvis).
      pose proof (drive_to_dominate t gs t' gs_f Hstar Hga Hrun Hinp) as Hdrive.
      apply eventually_will_step_annotate in Hdrive.
      unfold will_output_equiv.
      eapply eventually_trans; [ exact Hdrive | ].
      intros [gs2 t2] (Hreach & Hle2 & _).
      destruct Hreach as (tr & Hstar_gg & -> & Hga_imp). specialize (Hga_imp Hga).
      assert (Hstar2 : star gstep initial_gs (tr ++ t) gs2) by eauto using star_app.
      pose proof (le_node_output (t' ++ t) gs_f gs2 (tr ++ t) n m
                    Hstarf Hstar2 Hgaf Hga_imp Hle2 Hnho) as Hemit.
      apply eventually_will_step_annotate in Hemit.
      eapply eventually_weaken; [ exact Hemit | ].
      intros [gs2' t2'] (Hreach' & m' & Hnho' & Heqm).
      destruct Hreach' as (tr' & Hstar_gg' & -> & _).
      assert (Hstar2' : star gstep initial_gs (tr' ++ tr ++ t) gs2') by eauto using star_app.
      exists (m', n). split.
      - split; [ exact Heqm | reflexivity ].
      - eapply Permutation_in;
          [ apply Permutation_sym;
            apply (outputs_are_node_outputs (tr' ++ (tr ++ t)) gs2' Hstar2') | ].
        apply output_total_in; [ exact Hnho' | ].
        rewrite (output_visible_equiv n m' m Heqm). exact Hvis.
    Qed.
  End graph.

End __.
