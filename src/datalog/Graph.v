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
  Context (forward_equiv :
            forall n1 n2 a b, equiv a b -> forward n1 n2 a = forward n1 n2 b).
  Axiom stmt : Type.
  Context (claim : stmt -> list message -> Prop).
  Context (claim_mono :
            forall s ms1 ms2, claim s ms1 ->
                         incl_mod_weak equiv ms1 ms2 ->
                         claim s ms2).

  Context (consistent_output : stmt -> option node_id -> list message -> Prop).
  Context (allowed_output : option node_id -> list message -> Prop).
  Context (consistent : stmt -> list message -> Prop).

  Context (consistent_mono :
            forall s ms1 ms2,
            consistent s ms1 ->
            submultiset ms1 ms2 ->
            consistent s ms2).

  Context (consistent_output_mono :
            forall s n ms1 ms2,
            consistent_output s n ms1 ->
            submultiset ms1 ms2 ->
            consistent_output s n ms2).

  Local Notation IO_event := (Smallstep.IO_event label message).

  Variant graph_label :=
    | receive (_ : node_id) (_ : message)
    | run (_ : node_id) (_ : label).

  Local Notation gevent := (Smallstep.IO_event graph_label (message * node_id)).

  Definition consistent_good :=
    forall s nodes mss,
      NoDup nodes ->
      Forall2 allowed_output nodes mss ->
      claim s (concat mss) ->
      consistent s (concat mss) <-> Forall2 (consistent_output s) nodes mss.

  Context (consistent_good_holds : consistent_good).

  Context (allowed : list message -> Prop).
  Context (allowed_submultiset : multiset_monotone_dec allowed).
  Context (allowed_output_submultiset : forall n, multiset_monotone_dec (allowed_output n)).
  Context (allowed_of_outputs :
             forall nodes mss, Forall2 allowed_output nodes mss -> allowed (concat mss)).

  Lemma Permutation_allowed l1 l2 : Permutation l1 l2 -> allowed l2 -> allowed l1.
  Proof.
    intros HP Ha. eapply allowed_submultiset; [ exact Ha | ].
    exists []. rewrite app_nil_r. symmetry. exact HP.
  Qed.

  Definition matching_inps n (inps : list (message * node_id)) :=
    map fst (filter (fun '(_, n0) => eqb n n0) inps).

  Definition graph_inputs_allowed (inps : list (message * node_id)) :=
    forall n, allowed_output None (matching_inps n inps).

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

    Definition good_inputs_from (n : node_id) inps :=
        allowed_output (Some n) inps /\
          forall c, consistent_output c (Some n) inps.

    Definition good_node_output n outs :=
      forall dest, good_inputs_from n (filter (forward n dest) outs).

    Definition consistent_internal_inputs inps :=
      exists nodes partition,
        NoDup nodes /\
          Forall2 good_inputs_from nodes partition /\
          inps = concat partition.

    Definition node_good (n : node_id) : graph_node_state node_state -> Prop :=
      fun gns =>
        outputs_well_formed    node_step (good_node_output n) gns.(gns_node_state) /\
        monotone_mod_equiv     node_step equiv claim consistent allowed gns.(gns_node_state) /\
        might_implies_will_equiv node_step equiv allowed gns.(gns_node_state).

    (* [node_fold proj gs] collects, over every node [k] of [gs], the projection
       [proj k] of node [k]'s outputs.  all_outputs / fwd_total / output_total are
       instances, so the structural lemmas are proved once (below). *)
    Definition node_fold {X} (proj : node_id -> list message -> list X) (gs : graph_state) : list X :=
      flat_map (fun '(k, v) => proj k (outputs_of v.(gns_trace))) (map.tuples gs).
    Definition fwd_total (nn : node_id) := node_fold (fun k => filter (forward k nn)).

    Definition le_weak g1 (t1 : list gevent) g2 (t2 : list gevent) :=
      Forall2_map (fun n _ _ =>
        incl_mod_weak equiv (fwd_total n g1) (fwd_total n g2) /\
        submultiset (matching_inps n (inputs_of t1)) (matching_inps n (inputs_of t2)))
        g1 g2.

    Definition le_strong g1 (t1 : list gevent) g2 (t2 : list gevent) :=
      Forall2_map (fun n gns1 gns2 =>
        submultiset (inputs_of gns1.(gns_trace)) (inputs_of gns2.(gns_trace)) /\
        submultiset (fwd_total n g1) (fwd_total n g2) /\
        submultiset (matching_inps n (inputs_of t1)) (matching_inps n (inputs_of t2)))
        g1 g2.

    Lemma le_strong_le_weak g1 t1 g2 t2 : le_strong g1 t1 g2 t2 -> le_weak g1 t1 g2 t2.
    Proof.
      intros H. eapply Forall2_map_impl; [ exact H | ].
      intros k gns1 gns2 (_ & Hfwd & Hext). split; auto using incl_mod_weak_of_submultiset.
    Qed.

    Definition le (g1 g2 : graph_state) :=
      Forall2_map (fun n gns1 gns2 =>
                     consistently_incl equiv claim consistent (inputs_of gns1.(gns_trace)) (inputs_of gns2.(gns_trace)))
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

    Lemma le_weak_refl g t : le_weak g t g t.
    Proof. apply Forall2_map_refl. intros. split; auto using submultiset_refl. Qed.

    Lemma le_refl g : le g g.
    Proof. apply Forall2_map_refl. intros. apply (consistently_incl_refl equiv claim consistent). Qed.

    Lemma le_weak_trans g1 t1 g2 t2 g3 t3 :
      le_weak g1 t1 g2 t2 -> le_weak g2 t2 g3 t3 -> le_weak g1 t1 g3 t3.
    Proof.
      intros H12 H23. cbv [le_weak Forall2_map] in *. intros k.
      specialize (H12 k); specialize (H23 k).
      destruct (map.get g1 k), (map.get g2 k), (map.get g3 k);
        cbn in *; try contradiction; try exact I.
      destruct H12 as [Hi1 He1], H23 as [Hi2 He2].
      split; [ eapply incl_mod_weak_trans; eassumption | eapply submultiset_trans; eassumption ].
    Qed.

    Lemma le_strong_trans g1 t1 g2 t2 g3 t3 :
      le_strong g1 t1 g2 t2 -> le_strong g2 t2 g3 t3 -> le_strong g1 t1 g3 t3.
    Proof.
      intros H12 H23. cbv [le_strong Forall2_map] in *. intros k.
      specialize (H12 k); specialize (H23 k).
      destruct (map.get g1 k), (map.get g2 k), (map.get g3 k);
        cbn in *; try contradiction; try exact I.
      destruct H12 as (Hr1 & Hi1 & He1), H23 as (Hr2 & Hi2 & He2).
      split; [ eapply submultiset_trans; eassumption
             | split; eapply submultiset_trans; eassumption ].
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
        + apply Forall2_map_mupd_r; eauto.
        + apply Forall2_map_map_values'_r. simpl.
          epose proof (Forall2_map_get_r _ _ _ _ _ IH H) as (v1 & Hv1 & Hrel). fwd.
          eapply Forall2_map_put_r; try eassumption.
          -- eapply Forall2_map_impl; [eassumption|]. simpl. intros. fwd. eauto.
          -- simpl. rewrite Hrelp0. eexists (_ :: _). simpl. eauto.
        + simpl. epose proof (Forall2_map_get_r _ _ _ _ _ IH H) as (v1 & Hv1 & Hrel).
          eapply Forall2_map_put_r; try eassumption.
          -- eapply Forall2_map_impl; [eassumption|]. simpl. intros. fwd. eauto.
          -- simpl. fwd. rewrite Hrelp0. eexists (_ :: _). simpl. eauto.
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

    Lemma gstep_le_strong g e g' t : gstep g e g' -> le_strong g t g' (e :: t).
    Proof.
      intros Hstep. cbv [le_strong]. invert Hstep.
      - apply Forall2_map_mupd_r; [solve[auto]|].
        apply Forall2_map_dup. intros k v Hv. ssplit.
        + apply submultiset_refl.
        + apply submultiset_perm, Permutation_sym, node_fold_mupd_enqueue.
        + change (inputs_of (I_event (m, n) :: t)) with ([(m, n)] ++ inputs_of t).
          rewrite matching_inps_app. exists (matching_inps k [(m, n)]). apply Permutation_app_comm.
      - apply Forall2_map_map_values'_r. eapply Forall2_map_put_r; [ | exact H | ].
        + apply Forall2_map_dup. intros k v Hv Hne. cbn [enqueue gns_trace]. ssplit.
          * apply submultiset_refl.
          * exists (filter (forward n k) outs). eapply perm_trans.
            { apply node_fold_run; auto using filter_app. }
            apply Permutation_app_comm.
          * simpl. apply submultiset_refl.
        + cbn [enqueue gns_trace]. ssplit.
          * simpl. apply submultiset_refl.
          * exists (filter (forward n n) outs). eapply perm_trans.
            { apply node_fold_run; auto using filter_app. }
            apply Permutation_app_comm.
          * simpl. apply submultiset_refl.
      - eapply Forall2_map_put_r; [ | exact H | ].
        + apply Forall2_map_dup. intros k v Hv Hne. ssplit.
          * apply submultiset_refl.
          * apply submultiset_perm, Permutation_sym.
            eapply node_fold_put_same; eauto.
          * simpl. apply submultiset_refl.
        + cbn [gns_trace]. ssplit.
          * simpl. apply submultiset_cons.
          * apply submultiset_perm, Permutation_sym.
            eapply node_fold_put_same; eauto.
          * simpl. apply submultiset_refl.
    Qed.

    Lemma le_strong_refl g t : le_strong g t g t.
    Proof. apply Forall2_map_refl. intros. split; [ | split ]; apply submultiset_refl. Qed.

    Lemma star_gstep_le_strong g t T g' : star gstep g T g' -> le_strong g t g' (T ++ t).
    Proof.
      induction 1 as [ | t0 s' e s'' Hstar IH Hstep ]; [ apply le_strong_refl | ].
      eapply le_strong_trans; [ exact IH | apply gstep_le_strong; exact Hstep ].
    Qed.

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
      consistent_internal_inputs (fwd_total nn gs).
    Proof.
      intros Hstar. unfold consistent_internal_inputs.
      exists (map fst (map.tuples gs)),
             (map (fun kv => filter (forward (fst kv) nn) (outputs_of (snd kv).(gns_trace))) (map.tuples gs)).
      ssplit.
      - rewrite <- keys_eq_tuples. apply map.keys_NoDup.
      - apply Forall2_map_map. apply Forall_forall. intros [k v] Hin. cbn [fst snd].
        apply map.tuples_spec in Hin.
        pose proof (graph_step_to_node_step_from_beginning gs gt Hstar) as Hnodes.
        destruct (Forall2_map_get_r _ _ _ _ _ Hnodes Hin) as (gns0 & Hget0 & Hrun).
        pose proof (nodes_good k gns0 Hget0) as (Howf & _ & _).
        exact (Howf _ _ Hrun nn).
      - unfold fwd_total, node_fold. rewrite <- flat_map_concat_map.
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
      - destruct (fwd_total_consistent_internal gt gs nn Hstar)
          as (nodes & partition & Hnd & Hgif & Hconcat).
        rewrite Hconcat.
        assert (Heq : concat (partition ++ [matching_inps nn (inputs_of gt)])
                      = concat partition ++ matching_inps nn (inputs_of gt))
          by (rewrite concat_app; cbn [concat]; rewrite app_nil_r; reflexivity).
        rewrite <- Heq.
        apply (allowed_of_outputs (map Some nodes ++ [None])).
        apply Forall2_app.
        + rewrite <- Forall2_map_l. eapply Forall2_impl; [ | exact Hgif ].
          intros k b Hgb. exact (proj1 Hgb).
        + constructor; [ apply Hallow | constructor ].
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

    Lemma consistent_perm s l1 l2 : Permutation l1 l2 -> consistent s l1 -> consistent s l2.
    Proof. intros Hp Hc. eapply consistent_mono; [ exact Hc | apply submultiset_perm; exact Hp ]. Qed.

    Lemma claim_perm s l1 l2 : Permutation l1 l2 -> claim s l1 -> claim s l2.
    Proof.
      intros Hp Hc. eapply claim_mono; [ exact Hc | ].
      apply (incl_mod_weak_of_submultiset equiv). apply submultiset_perm. exact Hp.
    Qed.

    Lemma consistent_good_ext s nodes partition ext :
      NoDup nodes ->
      Forall2 good_inputs_from nodes partition ->
      allowed_output None ext ->
      claim s (ext ++ concat partition) ->
      consistent s (ext ++ concat partition) <->
        (consistent_output s None ext /\
         Forall2 (fun n => consistent_output s (Some n)) nodes partition).
    Proof.
      intros Hnd Hgif Hae Hclaim.
      assert (Hnd' : NoDup (None :: map Some nodes)).
      { constructor.
        - intros Hin. apply in_map_iff in Hin. destruct Hin as (x & Hx & _). discriminate.
        - apply FinFun.Injective_map_NoDup; [ intros a b; congruence | exact Hnd ]. }
      assert (Hall' : Forall2 allowed_output (None :: map Some nodes) (ext :: partition)).
      { constructor; [ exact Hae | ].
        rewrite <- Forall2_map_l. eapply Forall2_impl; [ | exact Hgif ].
        intros k b Hb. exact (proj1 Hb). }
      pose proof (consistent_good_holds s (None :: map Some nodes) (ext :: partition) Hnd' Hall') as Hcg.
      cbn [concat] in Hcg. specialize (Hcg Hclaim).
      rewrite Hcg. split.
      - inversion 1; subst. split; [ assumption | ].
        rewrite Forall2_map_l. assumption.
      - intros [Hhead Htail]. constructor; [ exact Hhead | ].
        rewrite <- Forall2_map_l. exact Htail.
    Qed.

    Lemma consistent_transfer internal_inps1 internal_inps2 exts1 exts2 :
      consistent_internal_inputs internal_inps1 ->
      consistent_internal_inputs internal_inps2 ->
      incl_mod_weak equiv internal_inps1 internal_inps2 ->
      allowed_output None exts1 ->
      allowed_output None exts2 ->
      submultiset exts1 exts2 ->
      consistently_incl equiv claim consistent
        (internal_inps1 ++ exts1) (internal_inps2 ++ exts2).
    Proof.
      intros Hci1 Hci2 Hwint Hae1 Hae2 Hsubext.
      destruct Hci1 as (nodes1 & part1 & Hnd1 & Hgif1 & Heq1).
      destruct Hci2 as (nodes2 & part2 & Hnd2 & Hgif2 & Heq2).
      subst internal_inps1 internal_inps2.
      assert (Hincl_pool : incl_mod_weak equiv (concat part1 ++ exts1) (concat part2 ++ exts2)).
      { apply incl_mod_weak_app.
        - apply incl_mod_weak_app_r. exact Hwint.
        - eapply (incl_mod_weak_trans equiv);
            [ apply (incl_mod_weak_of_submultiset equiv _ _ Hsubext)
            | apply (incl_mod_weak_of_incl equiv); intros x Hx; apply in_or_app; right; exact Hx ]. }
      split; [ exact Hincl_pool | ].
      intros s Hclaim Hcons.
      assert (Hext1 : consistent_output s None exts1).
      { pose proof (consistent_good_ext s nodes1 part1 exts1 Hnd1 Hgif1 Hae1
                      (claim_perm s _ _ (Permutation_app_comm (concat part1) exts1) Hclaim)) as Hce.
        refine (proj1 (proj1 Hce _)).
        eapply consistent_perm; [ apply Permutation_app_comm | exact Hcons ]. }
      assert (Hext2 : consistent_output s None exts2)
        by (eapply consistent_output_mono; [ exact Hext1 | exact Hsubext ]).
      assert (Hint2 : Forall2 (fun n => consistent_output s (Some n)) nodes2 part2).
      { eapply Forall2_impl; [ | exact Hgif2 ]. intros k b Hb. exact (proj2 Hb s). }
      assert (Hclaim2 : claim s (exts2 ++ concat part2)).
      { eapply claim_perm; [ apply Permutation_app_comm | ].
        eapply claim_mono; [ exact Hclaim | exact Hincl_pool ]. }
      eapply consistent_perm; [ apply Permutation_app_comm | ].
      apply (proj2 (consistent_good_ext s nodes2 part2 exts2 Hnd2 Hgif2 Hae2 Hclaim2)).
      split; [ exact Hext2 | exact Hint2 ].
    Qed.

    Lemma consistently_incl_perm l1 l1' l2 l2' :
      Permutation l1 l1' -> Permutation l2 l2' ->
      consistently_incl equiv claim consistent l1 l2 ->
      consistently_incl equiv claim consistent l1' l2'.
    Proof.
      intros Hp1 Hp2 [Hincl Hle]. split.
      - eapply (incl_mod_weak_trans equiv).
        + eapply incl_mod_weak_perm_l; [ exact Hp1 | exact Hincl ].
        + apply (incl_mod_weak_of_submultiset equiv). apply submultiset_perm. exact Hp2.
      - intros s Hclaim' Hcons'.
        eapply consistent_perm; [ exact Hp2 | ].
        apply Hle.
        + eapply claim_perm; [ apply Permutation_sym; exact Hp1 | exact Hclaim' ].
        + eapply consistent_perm; [ apply Permutation_sym; exact Hp1 | exact Hcons' ].
    Qed.

    Lemma consistently_incl_shrink_l l1 l1' l2 :
      submultiset l1' l1 ->
      consistently_incl equiv claim consistent l1 l2 ->
      consistently_incl equiv claim consistent l1' l2.
    Proof.
      intros Hsub [Hincl Hle]. split.
      - eapply (incl_mod_weak_trans equiv);
          [ apply (incl_mod_weak_of_submultiset equiv _ _ Hsub) | exact Hincl ].
      - intros s Hclaim' Hcons'. apply Hle.
        + eapply claim_mono; [ exact Hclaim' | apply (incl_mod_weak_of_submultiset equiv _ _ Hsub) ].
        + eapply consistent_mono; [ exact Hcons' | exact Hsub ].
    Qed.

    Lemma consistently_incl_grow_r l1 l2 l2' :
      submultiset l2 l2' ->
      consistently_incl equiv claim consistent l1 l2 ->
      consistently_incl equiv claim consistent l1 l2'.
    Proof.
      intros Hsub [Hincl Hle]. split.
      - eapply (incl_mod_weak_trans equiv);
          [ exact Hincl | apply (incl_mod_weak_of_submultiset equiv _ _ Hsub) ].
      - intros s Hclaim' Hcons'.
        eapply consistent_mono; [ apply Hle; [ exact Hclaim' | exact Hcons' ] | exact Hsub ].
    Qed.

    Lemma incl_mod_of_le_weak t1 gs1 t2 gs2 n ns1 ns2 :
      star gstep initial_gs t1 gs1 ->
      star gstep initial_gs t2 gs2 ->
      graph_inputs_allowed (inputs_of t1) ->
      graph_inputs_allowed (inputs_of t2) ->
      map.get gs1 n = Some ns1 ->
      map.get gs2 n = Some ns2 ->
      incl_mod_weak equiv (fwd_total n gs1) (fwd_total n gs2) ->
      submultiset (matching_inps n (inputs_of t1)) (matching_inps n (inputs_of t2)) ->
      consistently_incl equiv claim consistent
        (inputs_of ns1.(gns_trace) ++ ns1.(gns_queue))
        (inputs_of ns2.(gns_trace) ++ ns2.(gns_queue)).
    Proof.
      intros Hstar1 Hstar2 Hga1 Hga2 Hg1 Hg2 Hwint Hmatch.
      pose proof (inputs_are_outputs _ _ Hstar1) as Hio1. cbv [Forall_map] in Hio1.
      specialize (Hio1 _ _ Hg1).
      pose proof (inputs_are_outputs _ _ Hstar2) as Hio2. cbv [Forall_map] in Hio2.
      specialize (Hio2 _ _ Hg2).
      pose proof (fwd_total_consistent_internal _ _ n Hstar1) as Hci1.
      pose proof (fwd_total_consistent_internal _ _ n Hstar2) as Hci2.
      eapply consistently_incl_perm;
        [ apply Permutation_sym; exact Hio1
        | apply Permutation_sym; exact Hio2
        | ].
      apply consistent_transfer; try assumption.
      - apply Hga1.
      - apply Hga2.
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
      intros Hsub Hga n.
      eapply allowed_output_submultiset; [ apply (Hga n) | ].
      apply submultiset_matching_inps. exact Hsub.
    Qed.

    Lemma le_strong_combined g1 t1 g2 t2 :
      star gstep initial_gs t1 g1 ->
      star gstep initial_gs t2 g2 ->
      le_strong g1 t1 g2 t2 ->
      Forall2_map (fun _ ns1 ns2 =>
        submultiset (inputs_of ns1.(gns_trace)) (inputs_of ns2.(gns_trace)) /\
        submultiset (inputs_of ns1.(gns_trace) ++ ns1.(gns_queue))
                    (inputs_of ns2.(gns_trace) ++ ns2.(gns_queue))) g1 g2.
    Proof.
      intros Hstar1 Hstar2 Hls.
      pose proof (inputs_are_outputs _ _ Hstar1) as Hio1. cbv [Forall_map] in Hio1.
      pose proof (inputs_are_outputs _ _ Hstar2) as Hio2. cbv [Forall_map] in Hio2.
      cbv [le_strong Forall2_map] in Hls |- *. intros k. specialize (Hls k).
      destruct (map.get g1 k) as [ns1|] eqn:Hg1, (map.get g2 k) as [ns2|] eqn:Hg2;
        cbn in Hls |- *; try contradiction; try exact I.
      destruct Hls as (Htr & Hfwd & Hmatch). split; [ exact Htr | ].
      specialize (Hio1 _ _ Hg1). specialize (Hio2 _ _ Hg2).
      eapply submultiset_perm_l; [ apply Permutation_sym; exact Hio1 | ].
      eapply submultiset_perm_r; [ apply Permutation_sym; exact Hio2 | ].
      eapply submultiset_trans; [ | apply submultiset_app_head; exact Hmatch ].
      eapply submultiset_perm_l; [ apply Permutation_app_comm | ].
      eapply submultiset_perm_r; [ apply Permutation_app_comm | ].
      apply submultiset_app_head. exact Hfwd.
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
        assert (Hstar_di : star gstep initial_gs (td ++ tc) gs_d)
          by (eapply star_app; [ exact Hstar | exact Hstar_d ]).
        pose proof (le_strong_combined gc tc gs_d (td ++ tc) Hstar Hstar_di
                      (star_gstep_le_strong gc tc td gs_d Hstar_d)) as Hls.
        destruct (Forall2_map_get_l _ _ _ _ _ Hls Hget) as (nd & Hget_d & Htr & Htot).
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
          pose proof (gstep_le_strong _ _ _ t Hstep) as Hls. cbv [le_strong] in Hls.
          destruct (Forall2_map_get_l _ _ _ _ _ Hls Hgk) as (nc'' & Hgk' & Htr & _).
          exists nc''. split; [ exact Hgk' | eapply submultiset_trans; [ exact Hsm | exact Htr ] ].
        - apply List.Forall_map. apply Forall_forall. intros [k v] Hin.
          apply map.tuples_spec in Hin.
          eapply (eventually_deliver k (length (gns_queue v)) (gns_queue v) gs2 t2 v);
            [ apply le_n | exact Hstar | exact Hga | exact Hin | apply submultiset_refl ]. }
      intros [gs2' t2'] Hall Hreach.
      destruct Hreach as (tr & Hstar_gg & _ & _).
      pose proof (star_gstep_le_strong _ [] _ _ Hstar_gg) as Hls.
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
      le_weak gs1 t1 gs2 t2 ->
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
      destruct (Forall2_map_get_l _ _ _ _ _ Hlew Hg1) as (ns2b & Hg2b & Hlfwd & Hlmatch).
      assert (ns2b = ns2) by congruence. subst ns2b.
      specialize (Hall1 _ _ Hg1).
      specialize (Hall2 _ _ Hg2).
      specialize (Hall2' _ _ Hg2').
      assert (Hall1tr : allowed (inputs_of (gns_trace ns1)))
        by (eapply allowed_submultiset; [ exact Hall1 | apply submultiset_app_r ]).
      assert (Hall2'tr : allowed (inputs_of (gns_trace ns2')))
        by (eapply allowed_submultiset; [ exact Hall2' | apply submultiset_app_r ]).
      apply (consistently_incl_shrink_l (inputs_of (gns_trace ns1) ++ gns_queue ns1));
        [ apply submultiset_app_r | ].
      apply (consistently_incl_grow_r _ (inputs_of (gns_trace ns2) ++ gns_queue ns2));
        [ exact Hrec | ].
      apply (incl_mod_of_le_weak t1 gs1 t2 gs2 k ns1 ns2
               Hstar1 Hstar2 Hga1 Hga2 Hg1 Hg2 Hlfwd Hlmatch).
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

    Lemma forwarded_in_state T r n k vn os :
      star gstep initial_gs T r ->
      map.get r n = Some vn ->
      Forall (fun o => exists o', equiv o o' /\ In o' (outputs_of (gns_trace vn))) os ->
      incl_mod_weak equiv (filter (forward n k) os) (fwd_total k r).
    Proof.
      intros HT Hn Hos.
      assert (Hl1 : incl_mod_weak equiv (filter (forward n k) os)
                      (filter (forward n k) (outputs_of (gns_trace vn)))).
      { intros x Hx. apply filter_In in Hx. destruct Hx as [Hxos Hxf].
        rewrite Forall_forall in Hos. destruct (Hos x Hxos) as (x' & Hequiv & Hx'out).
        exists x'. split.
        - apply filter_In. split;
            [ exact Hx'out | rewrite <- (forward_equiv n k x x' Hequiv); exact Hxf ].
        - exact Hequiv. }
      eauto using fwd_total_get, incl_mod_weak_trans.
    Qed.

    Lemma node_will_match' gs1 t1 lbl outs gs1' gs2 t2 :
      star gstep initial_gs t1 gs1 ->
      star gstep initial_gs t2 gs2 ->
      graph_inputs_allowed (inputs_of t1) ->
      graph_inputs_allowed (inputs_of t2) ->
      gstep gs1 (O_event lbl outs) gs1' ->
      le gs1 gs2 ->
      le_weak gs1 t1 gs2 t2 ->
      eventually graph_will_step
        (fun '(gs2', t2') => le_weak gs1' (O_event lbl outs :: t1) gs2' t2') (gs2, t2).
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
        pose proof (star_gstep_le_strong _ t2 _ _ Hreachp0) as Hlsr.
        pose proof (le_weak_trans _ _ _ _ _ _ Hlew (le_strong_le_weak _ _ _ _ Hlsr)) as Hlwr.
        assert (Hrinit : star gstep initial_gs (tr ++ t2) r) by (eapply star_app; eauto).

        cbv [le_weak] in Hlwr |- *.
        apply Forall2_map_map_values'_l.
        eapply Forall2_map_put_l; [ | exact Hvalp0 | ].
        + eapply Forall2_map_impl; [ exact Hlwr | ].
          intros k w1 w2 (Hkf & Hkm) _. split; [ | exact Hkm ].
          eapply incl_mod_weak_perm_l;
            [ apply Permutation_sym; apply node_fold_run; eauto using filter_app | ].
          apply incl_mod_weak_app; [ eapply forwarded_in_state; eauto | exact Hkf ].
        + eapply Forall2_map_get_l in Hlwr; eauto. fwd. map_func. split; [ | assumption ].
          eapply incl_mod_weak_perm_l;
            [ apply Permutation_sym; apply node_fold_run; eauto using filter_app | ].
          apply incl_mod_weak_app; [ eapply forwarded_in_state; eauto | eassumption ].
      - especialize Hle'; eauto. especialize Hlew'; eauto. fwd.
        apply eventually_done.
        cbv [le_weak] in Hlew |- *.
        eapply Forall2_map_put_l; [ | exact Hlew'p0 | ].
        + eapply Forall2_map_impl; [ exact Hlew | ].
          intros k w1 w2 (Hkf & Hkm) _. split; [ | exact Hkm ].
          eapply incl_mod_weak_perm_l;
            [ apply Permutation_sym; apply node_fold_put_same with (v0 := ns); [ eassumption | reflexivity ] | exact Hkf ].
        + eapply Forall2_map_get_l in Hlew; eauto. fwd. split; [ | assumption ].
          eapply incl_mod_weak_perm_l;
            [ apply Permutation_sym; apply node_fold_put_same with (v0 := ns); [ eassumption | reflexivity ] | eassumption ].
    Qed.

    Lemma node_will_match gs1 t1 lbl outs gs1' gs2 t2 :
      star gstep initial_gs t1 gs1 ->
      star gstep initial_gs t2 gs2 ->
      submultiset (inputs_of t1) (inputs_of t2) ->
      graph_inputs_allowed (inputs_of t1) ->
      graph_inputs_allowed (inputs_of t2) ->
      gstep gs1 (O_event lbl outs) gs1' ->
      le gs1 gs2 ->
      le_weak gs1 t1 gs2 t2 ->
      eventually graph_will_step
        (fun '(gs2', t2') => le gs1' gs2' /\ le_weak gs1' (O_event lbl outs :: t1) gs2' t2') (gs2, t2).
    Proof.
      intros Hstar1 Hstar2 Hsub Hga1 Hga2 Hstep Hle Hlew.
      assert (Hstar1' : star gstep initial_gs (O_event lbl outs :: t1) gs1') by eauto.
      pose proof (node_will_match' _ _ _ _ _ _ _ Hstar1 Hstar2 Hga1 Hga2 Hstep Hle Hlew) as Hev.
      apply eventually_will_step_annotate in Hev.
      eapply eventually_trans; [ exact Hev | ].
      intros [gs2' t2'] (Hreach' & Hlw).
      destruct Hreach' as (tr & Hstar_gg & -> & Hga_imp).
      assert (Hstar2' : star gstep initial_gs (tr ++ t2) gs2')
        by (eapply star_app; [ exact Hstar2 | exact Hstar_gg ]).
      specialize (Hga_imp Hga2).
      assert (Hsub' : submultiset (inputs_of (O_event lbl outs :: t1)) (inputs_of (tr ++ t2))).
      { rewrite inputs_of_app. simpl.
        eapply submultiset_trans;
          [ exact Hsub | exists (inputs_of tr); apply Permutation_app_comm ]. }
      pose proof (le_weak_to_le _ _ _ _ Hstar1' Hstar2' Hsub' Hga_imp Hlw) as Hle2.
      eapply eventually_weaken.
      { eapply eventually_carry_stable_gen with (P := (fun '(s, t) => le_weak gs1' (O_event lbl outs :: t1) s t));
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
      assert (Hmiw' : might_implies_will_equiv' node_step equiv claim consistent allowed
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
        (fun '(gs2, t2) => le gs_f gs2 /\ le_weak gs_f (t' ++ t0) gs2 t2) (gs0, t0).
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
