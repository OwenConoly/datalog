From coqutil Require Import Map.Interface.
From coqutil Require Import Map.Properties.
From coqutil Require Import Map.MapKeys.
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
  Context {stmt : Type}.
  Context (claim : stmt -> list message -> Prop).
  Context (claim_output : stmt -> option node_id -> list message -> Prop).
  Context (claim_mono :
            forall s ms1 ms2, claim s ms1 ->
                         incl_mod equiv ms1 ms2 ->
                         claim s ms2).

  Context (consistent_output : stmt -> option node_id -> list message -> Prop).
  Context (allowed_output : option node_id -> list message -> Prop).
  Context (consistent : stmt -> list message -> Prop).
  Context {node_map : map.map (option node_id) (list message)}.
  Context {node_map_ok : map.ok node_map}.

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

  (*we could alo consider something like this?*)
  (*
    Definition claim_good :=
    forall s nodes mss,
      is_all_nodes nodes ->
      Forall2 allowed_output nodes mss ->
      (claim s (concat mss) <->
         Forall2 (claim_output s) nodes mss).

Definition consistent_good :=
    forall s nodes mss,
      is_all_nodes nodes ->
      Forall2 allowed_output nodes mss ->
      (consistent s (concat mss) <->
         Forall2 (consistent_output s) nodes mss).
   *)

  Definition consistent_good :=
    forall s (partition : node_map),
      Forall_map allowed_output partition ->
      claim s (concat (values partition)) ->
      Forall_map (claim_output s) partition /\
        (consistent s (concat (values partition)) <->
           Forall_map (consistent_output s) partition).

  Context (consistent_good_holds : consistent_good).

  Context (allowed : list message -> Prop).
  Context (allowed_submultiset : multiset_monotone_dec allowed).
  Context (allowed_output_submultiset : forall n, multiset_monotone_dec (allowed_output n)).
  Context (allowed_of_outputs :
             forall (partition : node_map),
               Forall_map allowed_output partition -> allowed (concat (values partition))).

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
    Context {node_state : Type} (node_step : node_id -> node_state -> IO_event -> node_state -> Prop).

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
      node_step n ns.(gns_node_state) (O_event lbl outs) ns' ->
      graph_step gs (O_event (run n lbl) (map (fun m => (m, n)) (filter (output_visible n) outs)))
        (map_values' (fun m => enqueue (filter (forward n m) outs))
           (map.put gs n
                    {| gns_node_state := ns';
                      gns_trace := O_event lbl outs :: ns.(gns_trace);
                      gns_queue := ns.(gns_queue) |}))
    | gstep_receive gs n ns ns' m ms1 ms2 :
      map.get gs n = Some ns ->
      node_step n ns.(gns_node_state) (I_event m) ns' ->
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
    Context {msg_map : map.map node_id (list message)}.
    Context {msg_map_ok : map.ok msg_map}.
    Context {omap : map.map node_id (list (message * node_id))}.
    Context {omap_ok : map.ok omap}.
    Context (initial_gs : graph_state).
    Context (initial_gs_empty :
               forall n gns, map.get initial_gs n = Some gns ->
                             gns.(gns_trace) = [] /\ gns.(gns_queue) = []).
    Context (node_step : node_id -> node_state -> IO_event -> node_state -> Prop).
    Context (nodes_input_total : forall n, input_total (node_step n)).

    Local Notation gstep := (graph_step node_step).

    Definition good_inputs_from n inps :=
        allowed_output n inps /\
          forall c, claim_output c n inps -> consistent_output c n inps.

    Definition good_node_output n outs :=
      forall dest, good_inputs_from (Some n) (filter (forward n dest) outs).

    Definition consistent_internal_inputs inps :=
      exists partition : msg_map,
        Forall_map (fun sender => good_inputs_from (Some sender)) partition /\
          inps = concat (values partition).

    Definition node_good (n : node_id) : graph_node_state node_state -> Prop :=
      fun gns =>
        outputs_well_formed    (node_step n) (good_node_output n) gns.(gns_node_state) /\
        monotone_mod_equiv     (node_step n) equiv claim consistent allowed gns.(gns_node_state) /\
        might_implies_will_equiv (node_step n) equiv allowed gns.(gns_node_state).

    Definition outputs_partition (gs : graph_state) : msg_map :=
      map_values' (fun _ ns => outputs_of ns.(gns_trace)) gs.

    Definition output_map {A} {mp' : map.map node_id (list A)} {mp'_ok : map.ok mp'}
        (F : node_id -> list message -> list A) (gs : graph_state) : list A :=
      concat (values (map_values' (mp' := mp') F (outputs_partition gs))).

    Definition fwd_partition (nn : node_id) (gs : graph_state) : msg_map :=
      map_values' (fun sender outs => filter (forward sender nn) outs) (outputs_partition gs).

    Definition fwd_total (nn : node_id) (gs : graph_state) : list message :=
      output_map (fun sender outs => filter (forward sender nn) outs) gs.

    Definition le_weak g1 g2 :=
      Forall2_map (fun _ => incl_mod equiv) (outputs_partition g1) (outputs_partition g2).

    Definition le (g1 g2 : graph_state) :=
      Forall2_map (fun n gns1 gns2 =>
                     consistently_incl equiv claim consistent (inputs_of gns1.(gns_trace)) (inputs_of gns2.(gns_trace)))
        g1 g2.

    Definition node_has_output (gs : graph_state) (n : node_id) (o : message) : Prop :=
      exists ns, map.get gs n = Some ns /\ In o (outputs_of (gns_trace ns)).

    Let graph_will_step := (will_step (graph_step node_step) graph_inputs_allowed).

    Context (nodes_good : Forall_map node_good initial_gs).

    #[local] Hint Constructors star eventually : core.
    #[local] Hint Resolve
      incl_mod_refl incl_mod_of_incl incl_mod_trans
      in_or_app impl_in_map impl_in_filter star_app submultiset_app_r : core.
    #[local] Hint Unfold val_sat might_output : core.
    #[local] Hint Extern 5 (In _ _) => simpl : core.

    Lemma le_weak_refl g : le_weak g g.
    Proof. apply Forall2_map_refl. auto using incl_mod_refl. Qed.

    Lemma le_refl g : le g g.
    Proof. apply Forall2_map_refl. auto using consistently_incl_refl. Qed.

    Lemma le_weak_trans g1 g2 g3 :
      le_weak g1 g2 -> le_weak g2 g3 -> le_weak g1 g3.
    Proof. apply Forall2_map_trans. eauto using incl_mod_trans. Qed.

    Lemma graph_step_to_node_step gs gt gs' :
      star gstep gs gt gs' ->
      Forall2_map (fun n gns1 gns2 =>
                     exists t'',
                       gns2.(gns_trace) = t'' ++ gns1.(gns_trace) /\
                         star (node_step n) gns1.(gns_node_state) t'' gns2.(gns_node_state))
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
      Forall2_map (fun n gns0 gns =>
                     star (node_step n) gns0.(gns_node_state) gns.(gns_trace) gns.(gns_node_state))
        initial_gs gs.
    Proof.
      intros. eapply Forall2_map_impl_strong.
      { eapply graph_step_to_node_step; eauto. }
      intros n gns0 gns H1 _ (t'' & Htr & Hst).
      apply initial_gs_empty in H1. destruct H1 as [Htr0 _].
      rewrite Htr0, app_nil_r in Htr. subst t''. eauto.
    Qed.

    (* the visible outputs of every node, each tagged with its node. *)
    Definition output_total (gs : graph_state) : list (message * node_id) :=
      output_map (mp' := omap)
        (fun k outs => map (fun m => (m, k)) (filter (output_visible k) outs)) gs.

    Lemma outputs_partition_get gs n :
      map.get (outputs_partition gs) n =
        option_map (fun ns => outputs_of ns.(gns_trace)) (map.get gs n).
    Proof. apply get_map_values'. Qed.

    Lemma fwd_partition_get nn gs sender :
      map.get (fwd_partition nn gs) sender =
        option_map (fun ns => filter (forward sender nn) (outputs_of ns.(gns_trace))) (map.get gs sender).
    Proof.
      unfold fwd_partition. rewrite get_map_values', outputs_partition_get.
      destruct (map.get gs sender); reflexivity.
    Qed.

    Lemma outputs_partition_put gs n v :
      outputs_partition (map.put gs n v) = map.put (outputs_partition gs) n (outputs_of v.(gns_trace)).
    Proof.
      apply map.map_ext. intro j.
      rewrite outputs_partition_get, !map.get_put_dec, outputs_partition_get.
      destruct (Nat.eqb n j); reflexivity.
    Qed.

    Lemma outputs_partition_map_values' (g : node_id -> graph_node_state node_state -> graph_node_state node_state) M :
      (forall k v, (g k v).(gns_trace) = v.(gns_trace)) ->
      outputs_partition (map_values' g M) = outputs_partition M.
    Proof.
      intros Hg. apply map.map_ext. intro j.
      rewrite !outputs_partition_get, get_map_values'.
      destruct (map.get M j) as [w|]; cbn [option_map]; [ rewrite Hg | ]; reflexivity.
    Qed.

    Lemma outputs_partition_put_output_eq gs n v0 v :
      map.get gs n = Some v0 ->
      outputs_of v.(gns_trace) = outputs_of v0.(gns_trace) ->
      outputs_partition (map.put gs n v) = outputs_partition gs.
    Proof.
      intros Hn Ho.
      assert (Hg : map.get (outputs_partition gs) n = Some (outputs_of v0.(gns_trace)))
        by (rewrite outputs_partition_get, Hn; reflexivity).
      rewrite outputs_partition_put, Ho.
      rewrite (map.put_noop n (outputs_of v0.(gns_trace)) (outputs_partition gs) Hg). reflexivity.
    Qed.

    Lemma outputs_partition_mupd_enqueue gs n inps :
      outputs_partition (mupd gs n (enqueue inps)) = outputs_partition gs.
    Proof.
      unfold mupd. destruct (map.get gs n) as [v|] eqn:Hn; [ | reflexivity ].
      apply (outputs_partition_put_output_eq gs n v _ Hn). reflexivity.
    Qed.

    Lemma output_map_run {A} {mp' : map.map node_id (list A)} {mp'_ok : map.ok mp'}
        (F : node_id -> list message -> list A)
        (Hdist : forall k a b, F k (a ++ b) = F k a ++ F k b)
        gs n ns lbl outs ns' :
      map.get gs n = Some ns ->
      Permutation
        (output_map (mp' := mp') F
           (map_values' (fun k => enqueue (filter (forward n k) outs))
              (map.put gs n {| gns_node_state := ns';
                               gns_trace := O_event lbl outs :: ns.(gns_trace);
                               gns_queue := ns.(gns_queue) |})))
        (F n outs ++ output_map F gs).
    Proof.
      intros Hn. unfold output_map.
      erewrite outputs_partition_map_values'; [|reflexivity].
      rewrite outputs_partition_put.
      eapply Permutation_trans; [ apply concat_values_map_values'_put | ].
      simpl. rewrite Hdist, <- app_assoc. apply Permutation_app_head.
      apply Permutation_sym.
      apply concat_values_map_values'_get.
      rewrite outputs_partition_get, Hn. reflexivity.
    Qed.

    Lemma output_map_mupd_enqueue {A} {mp' : map.map node_id (list A)} {mp'_ok : map.ok mp'}
        (F : node_id -> list message -> list A) gs n inps :
      output_map (mp' := mp') F (mupd gs n (enqueue inps)) = output_map F gs.
    Proof. unfold output_map. rewrite outputs_partition_mupd_enqueue. reflexivity. Qed.

    Lemma output_map_put_output_eq {A} {mp' : map.map node_id (list A)} {mp'_ok : map.ok mp'}
        (F : node_id -> list message -> list A) gs n v0 v :
      map.get gs n = Some v0 ->
      outputs_of v.(gns_trace) = outputs_of v0.(gns_trace) ->
      output_map (mp' := mp') F (map.put gs n v) = output_map F gs.
    Proof.
      intros Hn Ho. unfold output_map.
      erewrite outputs_partition_put_output_eq; eauto.
    Qed.

    Lemma output_map_initial {A} {mp' : map.map node_id (list A)} {mp'_ok : map.ok mp'}
        (F : node_id -> list message -> list A) :
      (forall k, F k [] = []) -> output_map (mp' := mp') F initial_gs = [].
    Proof.
      intros Hnil. unfold output_map. apply concat_nil_Forall, values_Forall.
      intros k v Hv. rewrite get_map_values', outputs_partition_get in Hv.
      apply option_map_Some in Hv. fwd. apply option_map_Some in Hvp0. fwd.
      pose proof initial_gs_empty as He. especialize He; eauto.
      fwd. erewrite Hep0. auto.
    Qed.

    Lemma outputs_are_node_outputs gt gs :
      star gstep initial_gs gt gs ->
      Permutation (outputs_of gt) (output_total gs).
    Proof.
      unfold output_total.
      induction 1 as [ | gt0 gmid e gs Hstar IH Hstep ].
      - rewrite output_map_initial by (intros; reflexivity). reflexivity.
      - invert Hstep.
        + rewrite output_map_mupd_enqueue. exact IH.
        + cbn [outputs_of]. eapply perm_trans; [ apply Permutation_app_head; exact IH | ].
          apply Permutation_sym.
          apply (output_map_run (fun k outs => map (fun m => (m, k)) (filter (output_visible k) outs)));
            [ intros; rewrite filter_app, map_app; reflexivity | eassumption ].
        + erewrite (output_map_put_output_eq _ _ _ ns) by (eassumption || reflexivity). exact IH.
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

    Hint Resolve matching_inps_perm : core.

    Lemma star_gstep_le_weak g T g' : star gstep g T g' -> le_weak g g'.
    Proof.
      intros Hstar. cbv [le_weak outputs_partition].
      apply Forall2_map_map_values'_l. apply Forall2_map_map_values'_r.
      eapply Forall2_map_impl; [ apply (graph_step_to_node_step g T g' Hstar) | ].
      intros k gns1 gns2 (t'' & Htr & _). rewrite Htr, outputs_of_app.
      apply (incl_mod_of_incl equiv). intros x Hx. apply in_or_app. right. exact Hx.
    Qed.

    Lemma le_weak_fwd_total g1 g2 n :
      le_weak g1 g2 -> incl_mod equiv (fwd_total n g1) (fwd_total n g2).
    Proof.
      intros Hle x Hx. unfold fwd_total, output_map in Hx.
      apply In_concat_values in Hx. destruct Hx as (k & vs & Hget & Hin).
      rewrite get_map_values', outputs_partition_get in Hget.
      destruct (map.get g1 k) as [gns1|] eqn:Hg1; cbn [option_map] in Hget; [ | discriminate ].
      fwd. apply filter_In in Hin. destruct Hin as (Hxout & Hfwd).
      cbv [le_weak Forall2_map] in Hle. specialize (Hle k).
      rewrite !outputs_partition_get, Hg1 in Hle. simpl in Hle.
      destruct (map.get g2 k) as [gns2|] eqn:Hg2; cbn [option_map] in Hle; [ | contradiction ].
      destruct (Hle x Hxout) as (x' & Hx'out & Hequiv).
      exists x'. split; [ | exact Hequiv ].
      unfold fwd_total, output_map. apply In_concat_values.
      exists k, (filter (forward k n) (outputs_of gns2.(gns_trace))). split.
      - rewrite get_map_values', outputs_partition_get, Hg2. reflexivity.
      - apply filter_In. split; [ exact Hx'out | ].
        rewrite <- (forward_equiv k n x x' Hequiv). exact Hfwd.
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
              unfold fwd_total; rewrite output_map_mupd_enqueue; reflexivity ].
        destr (eqb n nn).
        + apply option_map_Some in Hg'. fwd.
          cbn [enqueue gns_trace gns_queue]. simpl.
          eauto with perm.
        + rewrite app_nil_r. apply IH. exact Hg'.
      - rewrite get_map_values', map.get_put_dec in Hg'.
        apply option_map_Some in Hg'. fwd.
        simpl. rewrite app_nil_r.
        etransitivity;
          [ | symmetry; apply Permutation_app_tail;
              apply (output_map_run (fun sender outs => filter (forward sender nn) outs)
                       ltac:(intros; apply filter_app) gs n ns lbl outs ns' H) ].
        destr_sth Nat.eqb.
        + fwd. cbn [enqueue gns_trace gns_queue]. simpl.
          rewrite <- app_assoc. eauto with perm.
        + cbn [enqueue gns_trace gns_queue].
          rewrite <- app_assoc. eauto with perm.
      - rewrite map.get_put_dec in Hg'. simpl. rewrite app_nil_r.
        etransitivity;
          [ | symmetry; apply Permutation_app_tail;
              unfold fwd_total;
              erewrite output_map_put_output_eq by (eassumption || reflexivity); reflexivity ].
        destr_sth Nat.eqb; eauto.
        fwd. simpl. specialize (IH _ _ ltac:(eassumption)). rewrite H1 in IH.
        eauto with perm.
    Qed.

    Lemma conserved_perm_ext gs e1 e2 :
      Permutation e1 e2 -> conserved gs e1 -> conserved gs e2.
    Proof.
      intros HP Hc nn nsn Hget.
      eapply perm_trans; [ apply (Hc nn nsn Hget) | eauto with perm ].
    Qed.

    Lemma conservation_gen gs0 T gs1 :
      star gstep gs0 T gs1 ->
      forall ext, conserved gs0 ext -> conserved gs1 (ext ++ inputs_of T).
    Proof.
      induction 1 as [ | T0 smid e sfin Hstar IH Hstep ]; intros ext Hconv.
      - cbn [inputs_of flat_map]. rewrite app_nil_r. exact Hconv.
      - eapply conserved_perm_ext;
          [ | apply (conservation_step _ _ _ Hstep _ (IH ext Hconv)) ].
        simpl. repeat rewrite <- app_assoc. eauto with perm.
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
        rewrite Ht, Hq. unfold fwd_total.
        rewrite output_map_initial by (intros; reflexivity). reflexivity. }
      pose proof (conservation_gen initial_gs gt gs Hstar [] Hbase) as Hcons.
      rewrite app_nil_l in Hcons. exact (Hcons nn nsn Hget).
    Qed.

    Lemma fwd_total_consistent_internal gt gs nn :
      star gstep initial_gs gt gs ->
      consistent_internal_inputs (fwd_total nn gs).
    Proof.
      intros Hstar. exists (fwd_partition nn gs). split; [ | reflexivity ].
      intros sender v Hv. rewrite fwd_partition_get in Hv.
      destruct (map.get gs sender) as [gns|] eqn:Hgs; cbn [option_map] in Hv; [ | discriminate ].
      injection Hv as Hv. subst v.
      pose proof (graph_step_to_node_step_from_beginning gs gt Hstar) as Hnodes.
      destruct (Forall2_map_get_r _ _ _ _ _ Hnodes Hgs) as (gns0 & Hget0 & Hrun).
      pose proof (nodes_good sender gns0 Hget0) as (Howf & _ & _).
      exact (Howf _ _ Hrun nn).
    Qed.

    Definition with_external (partition : msg_map) (ext : list message) : node_map :=
      map.put (map.map_keys Some partition) None ext.

    Lemma with_external_get_None partition ext :
      map.get (with_external partition ext) None = Some ext.
    Proof. unfold with_external. apply map.get_put_same. Qed.

    Lemma with_external_get_Some partition ext k :
      map.get (with_external partition ext) (Some k) = map.get partition k.
    Proof.
      unfold with_external. rewrite map.get_put_diff by discriminate.
      apply map.get_map_keys_always_invertible. congruence.
    Qed.

    Lemma values_with_external partition ext :
      Permutation (concat (values (with_external partition ext)))
                  (ext ++ concat (values partition)).
    Proof.
      unfold with_external.
      eapply Permutation_trans.
      { apply Permutation_concat, values_put_None.
        apply get_map_keys_None. intros ?; discriminate. }
      cbn [concat]. apply Permutation_app_head, Permutation_concat.
      apply values_map_keys. intros a b H; congruence.
    Qed.

    Lemma Forall_map_with_external (P : option node_id -> list message -> Prop) partition ext :
      P None ext ->
      Forall_map (fun n => P (Some n)) partition ->
      Forall_map P (with_external partition ext).
    Proof.
      intros HN HS q v Hq. destruct q as [k|].
      - rewrite with_external_get_Some in Hq. exact (HS k v Hq).
      - rewrite with_external_get_None in Hq. injection Hq as Hq. subst v. exact HN.
    Qed.

    Lemma with_external_None (P : option node_id -> list message -> Prop) partition ext :
      Forall_map P (with_external partition ext) -> P None ext.
    Proof. intros H. apply (H None ext (with_external_get_None partition ext)). Qed.

    Lemma everything_allowed gt gs :
      star gstep initial_gs gt gs ->
      graph_inputs_allowed (inputs_of gt) ->
      Forall_map (fun _ ns => allowed (inputs_of ns.(gns_trace) ++ ns.(gns_queue))) gs.
    Proof.
      intros Hstar Hallow. cbv [Forall_map]. intros nn nsn Hget.
      eapply Permutation_allowed.
      - apply (inputs_are_outputs gt gs Hstar nn nsn Hget).
      - destruct (fwd_total_consistent_internal gt gs nn Hstar)
          as (partition & Hgif & Hconcat).
        rewrite Hconcat.
        eapply Permutation_allowed with
          (l2 := concat (values (with_external partition (matching_inps nn (inputs_of gt))))).
        + eapply Permutation_trans; [ apply Permutation_app_comm | ].
          apply Permutation_sym, values_with_external.
        + apply allowed_of_outputs. apply Forall_map_with_external; [ apply Hallow | ].
          intros k v Hk. exact (proj1 (Hgif k v Hk)).
    Qed.

    Lemma node_run_allowed t gs :
      star gstep initial_gs t gs ->
      graph_inputs_allowed (inputs_of t) ->
      Forall2_map (fun n gns0 gns =>
                     star (node_step n) (gns_node_state gns0) (gns_trace gns) (gns_node_state gns) /\
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
      will_step (node_step n) allowed (gns.(gns_node_state), gns.(gns_trace)) P ->
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
      map.get gs n = Some gns ->
      eventually (will_step (node_step n) allowed) P (gns.(gns_node_state), gns.(gns_trace)) ->
      eventually graph_will_step
        (fun '(gs', _) =>
           val_sat gs' n (fun gns' => P (gns'.(gns_node_state), gns'.(gns_trace))))
        (gs, gt).
    Proof.
      intros Hstar Hget Hev.
      remember (gns.(gns_node_state), gns.(gns_trace)) as nodeSt eqn:E.
      revert gs gt gns Hstar Hget E.
      induction Hev; intros gs gt gns Hstar Hget E; subst.
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
      apply (incl_mod_of_submultiset equiv). apply submultiset_perm. exact Hp.
    Qed.

    Lemma consistent_good_ext s (partition : msg_map) ext :
      Forall_map (fun n => good_inputs_from (Some n)) partition ->
      allowed_output None ext ->
      claim s (ext ++ concat (values partition)) ->
      consistent s (ext ++ concat (values partition)) <-> consistent_output s None ext.
    Proof.
      intros Hgif Hae Hclaim.
      assert (Hall : Forall_map allowed_output (with_external partition ext)).
      { apply Forall_map_with_external; [ exact Hae | ].
        intros k v Hk. exact (proj1 (Hgif k v Hk)). }
      assert (Hcl : claim s (concat (values (with_external partition ext)))).
      { eapply claim_perm; [ apply Permutation_sym, values_with_external | exact Hclaim ]. }
      pose proof (consistent_good_holds s (with_external partition ext) Hall Hcl)
        as (Hclaim_out & Hbicond).
      assert (Hint : Forall_map (fun n => consistent_output s (Some n)) partition).
      { intros k v Hk. apply (proj2 (Hgif k v Hk)).
        apply (Hclaim_out (Some k) v). rewrite with_external_get_Some. exact Hk. }
      split.
      - intros Hc.
        apply (consistent_perm s _ _ (Permutation_sym (values_with_external partition ext))) in Hc.
        apply Hbicond in Hc. exact (with_external_None _ _ _ Hc).
      - intros Hext.
        apply (consistent_perm s _ _ (values_with_external partition ext)).
        apply Hbicond. apply Forall_map_with_external; [ exact Hext | exact Hint ].
    Qed.

    Lemma consistent_transfer internal_inps1 internal_inps2 exts1 exts2 :
      consistent_internal_inputs internal_inps1 ->
      consistent_internal_inputs internal_inps2 ->
      incl_mod equiv internal_inps1 internal_inps2 ->
      allowed_output None exts1 ->
      allowed_output None exts2 ->
      submultiset exts1 exts2 ->
      consistently_incl equiv claim consistent
        (internal_inps1 ++ exts1) (internal_inps2 ++ exts2).
    Proof.
      intros Hci1 Hci2 Hwint Hae1 Hae2 Hsubext.
      destruct Hci1 as (part1 & Hgif1 & Heq1).
      destruct Hci2 as (part2 & Hgif2 & Heq2).
      subst internal_inps1 internal_inps2.
      assert (Hincl_pool : incl_mod equiv (concat (values part1) ++ exts1)
                                          (concat (values part2) ++ exts2)).
      { apply incl_mod_app.
        - apply incl_mod_app_r. exact Hwint.
        - eapply (incl_mod_trans equiv);
            [ apply (incl_mod_of_submultiset equiv _ _ Hsubext)
            | apply (incl_mod_of_incl equiv); intros x Hx; apply in_or_app; right; exact Hx ]. }
      split; [ exact Hincl_pool | ].
      intros s Hclaim Hcons.
      assert (Hext1 : consistent_output s None exts1).
      { pose proof (consistent_good_ext s part1 exts1 Hgif1 Hae1
                      (claim_perm s _ _ (Permutation_app_comm (concat (values part1)) exts1) Hclaim)) as Hce.
        apply (proj1 Hce).
        eapply consistent_perm; [ apply Permutation_app_comm | exact Hcons ]. }
      assert (Hext2 : consistent_output s None exts2)
        by (eapply consistent_output_mono; [ exact Hext1 | exact Hsubext ]).
      assert (Hclaim2 : claim s (exts2 ++ concat (values part2))).
      { eapply claim_perm; [ apply Permutation_app_comm | ].
        eapply claim_mono; [ exact Hclaim | exact Hincl_pool ]. }
      eapply consistent_perm; [ apply Permutation_app_comm | ].
      apply (proj2 (consistent_good_ext s part2 exts2 Hgif2 Hae2 Hclaim2)).
      exact Hext2.
    Qed.

    Lemma consistently_incl_shrink_l l1 l1' l2 :
      submultiset l1' l1 ->
      consistently_incl equiv claim consistent l1 l2 ->
      consistently_incl equiv claim consistent l1' l2.
    Proof.
      intros Hsub [Hincl Hle]. split.
      - eapply (incl_mod_trans equiv);
          [ apply (incl_mod_of_submultiset equiv _ _ Hsub) | exact Hincl ].
      - intros s Hclaim' Hcons'. apply Hle.
        + eapply claim_mono; [ exact Hclaim' | apply (incl_mod_of_submultiset equiv _ _ Hsub) ].
        + eapply consistent_mono; [ exact Hcons' | exact Hsub ].
    Qed.

    Lemma consistently_incl_grow_r l1 l2 l2' :
      submultiset l2 l2' ->
      consistently_incl equiv claim consistent l1 l2 ->
      consistently_incl equiv claim consistent l1 l2'.
    Proof.
      intros Hsub [Hincl Hle]. split.
      - eapply (incl_mod_trans equiv);
          [ exact Hincl | apply (incl_mod_of_submultiset equiv _ _ Hsub) ].
      - intros s Hclaim' Hcons'.
        eapply consistent_mono; [ apply Hle; [ exact Hclaim' | exact Hcons' ] | exact Hsub ].
    Qed.

    Lemma consistently_incl_perm l1 l1' l2 l2' :
      Permutation l1 l1' -> Permutation l2 l2' ->
      consistently_incl equiv claim consistent l1 l2 ->
      consistently_incl equiv claim consistent l1' l2'.
    Proof.
      intros Hp1 Hp2 H.
      eapply consistently_incl_shrink_l; [ apply submultiset_perm, Permutation_sym; exact Hp1 | ].
      eapply consistently_incl_grow_r; [ apply submultiset_perm; exact Hp2 | exact H ].
    Qed.

    Lemma incl_mod_of_le_weak t1 gs1 t2 gs2 n ns1 ns2 :
      star gstep initial_gs t1 gs1 ->
      star gstep initial_gs t2 gs2 ->
      graph_inputs_allowed (inputs_of t1) ->
      graph_inputs_allowed (inputs_of t2) ->
      map.get gs1 n = Some ns1 ->
      map.get gs2 n = Some ns2 ->
      incl_mod equiv (fwd_total n gs1) (fwd_total n gs2) ->
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

    Lemma gstep_pool_step g e g' :
      gstep g e g' ->
      Forall2_map (fun _ ns1 ns2 =>
        submultiset (inputs_of ns1.(gns_trace)) (inputs_of ns2.(gns_trace)) /\
        submultiset (inputs_of ns1.(gns_trace) ++ ns1.(gns_queue))
                    (inputs_of ns2.(gns_trace) ++ ns2.(gns_queue))) g g'.
    Proof.
      intros Hstep. invert Hstep.
      - apply Forall2_map_mupd_r.
        + intros v1 v2 (Ht & Hp). cbn [enqueue gns_trace gns_queue]. split; [ exact Ht | ].
          eapply submultiset_trans; [ exact Hp | eauto with submultiset perm ].
        + apply Forall2_map_dup. intros k v Hv. split; apply submultiset_refl.
      - apply Forall2_map_map_values'_r. eapply Forall2_map_put_r; [ | exact H | ].
        + apply Forall2_map_dup. intros k v Hv Hne. cbn [enqueue gns_trace gns_queue]. split.
          * apply submultiset_refl.
          * eauto with submultiset perm.
        + cbn [enqueue gns_trace gns_queue].
          change (inputs_of (O_event lbl outs :: gns_trace ns)) with (inputs_of (gns_trace ns)).
          split.
          * apply submultiset_refl.
          * eauto with submultiset perm.
      - eapply Forall2_map_put_r; [ | exact H | ].
        + apply Forall2_map_dup. intros k v Hv Hne. split; apply submultiset_refl.
        + cbn [gns_trace gns_queue].
          change (inputs_of (I_event m :: gns_trace ns)) with (m :: inputs_of (gns_trace ns)).
          split.
          * apply submultiset_cons.
          * rewrite H1. eauto with submultiset perm.
    Qed.

    Lemma pool_submultiset g1 T g2 :
      star gstep g1 T g2 ->
      Forall2_map (fun _ ns1 ns2 =>
        submultiset (inputs_of ns1.(gns_trace)) (inputs_of ns2.(gns_trace)) /\
        submultiset (inputs_of ns1.(gns_trace) ++ ns1.(gns_queue))
                    (inputs_of ns2.(gns_trace) ++ ns2.(gns_queue))) g1 g2.
    Proof.
      induction 1 as [ | t0 s' e s'' Hstar IH Hstep ].
      - apply Forall2_map_refl. intros. split; apply submultiset_refl.
      - eapply Forall2_map_trans; [ | exact IH | apply (gstep_pool_step _ _ _ Hstep) ].
        intros k a b c (Ht1 & Hp1) (Ht2 & Hp2). split; eapply submultiset_trans; eassumption.
    Qed.

    Lemma eventually_deliver n :
      forall N owed gc tc nc,
        length owed <= N ->
        map.get gc n = Some nc ->
        submultiset owed (gns_queue nc) ->
        eventually graph_will_step
          (fun '(gc', _) => exists nc', map.get gc' n = Some nc' /\
             submultiset (inputs_of (gns_trace nc) ++ owed) (inputs_of (gns_trace nc')))
          (gc, tc).
    Proof.
      induction N as [| N IHN]; intros owed gc tc nc HN Hget Hsub;
        (destruct owed as [| a owed'];
         [ apply eventually_done; exists nc; split;
           [ exact Hget | rewrite app_nil_r; apply submultiset_refl ] | ]).
      - simpl in HN. inversion HN.
      - assert (Hlen' : length owed' <= N) by (simpl in HN; apply le_S_n; exact HN).
        assert (Ha_q : submultiset [a] (gns_queue nc)).
        { eapply submultiset_trans; [ | exact Hsub ]. exists owed'. reflexivity. }
        eapply eventually_step_cps. exists (receive n a).
        intros gs_d td Hstar_d _.
        pose proof (pool_submultiset gc td gs_d Hstar_d) as Hls.
        destruct (Forall2_map_get_l _ _ _ _ _ Hls Hget) as (nd & Hget_d & Htr & Htot).
        assert (Htot_owed : submultiset (inputs_of (gns_trace nc) ++ a :: owed')
                              (inputs_of (gns_trace nd) ++ gns_queue nd))
          by (eapply submultiset_trans; [ apply submultiset_app_head; exact Hsub | exact Htot ]).
        destruct (classic (In a (gns_queue nd))) as [Hin_d | Hnin_d].
        + apply in_split in Hin_d. destruct Hin_d as (ms1 & ms2 & Hq).
          destruct (nodes_input_total n (gns_node_state nd) a) as (nd' & Hns).
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
            - exact Hget_d.
            - exact HQ''. }
          intros [gc'' t''] (nc'' & Hgc'' & Hcov). exists nc''. split; [ exact Hgc'' | ].
          eapply submultiset_trans; [ exact Habs | exact Hcov ].
    Qed.

    Lemma eventually_received t2 gs2 :
      eventually graph_will_step
        (fun '(gs2', _) =>
           Forall2_map (fun _ ns2 ns2' =>
                          submultiset (inputs_of ns2.(gns_trace) ++ ns2.(gns_queue))
                            (inputs_of ns2'.(gns_trace))) gs2 gs2')
        (gs2, t2).
    Proof.
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
          pose proof (gstep_pool_step _ _ _ Hstep) as Hls.
          destruct (Forall2_map_get_l _ _ _ _ _ Hls Hgk) as (nc'' & Hgk' & Htr & _).
          exists nc''. split; [ exact Hgk' | eapply submultiset_trans; [ exact Hsm | exact Htr ] ].
        - apply List.Forall_map. apply Forall_forall. intros [k v] Hin.
          apply map.tuples_spec in Hin.
          eapply (eventually_deliver k (length (gns_queue v)) (gns_queue v) gs2 t2 v);
            [ apply le_n | exact Hin | apply submultiset_refl ]. }
      intros [gs2' t2'] Hall Hreach.
      destruct Hreach as (tr & Hstar_gg & _ & _).
      pose proof (pool_submultiset _ _ _ Hstar_gg) as Hls.
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
      apply eventually_will_step_reach.
      eapply eventually_weaken.
      { exact (eventually_received _ _). }
      intros [gs2' t2'] Hrecv _.
      cbv [le]. unfold le_weak, outputs_partition in Hlew.
      pose proof (Forall2_map_map_values'_inv _ _ _ _ _ Hlew) as Hout.
      eapply Forall2_map_compose_strong; [ | eassumption | eassumption ].
      intros k ns1 ns2 ns2' Hg1 Hg2 Hg3 _ Hrec.
      eapply consistently_incl_shrink_l; [ apply submultiset_app_r | ].
      eapply consistently_incl_grow_r; [ exact Hrec | ].
      apply (incl_mod_of_le_weak t1 gs1 t2 gs2 k ns1 ns2
               Hstar1 Hstar2 Hga1 Hga2 Hg1 Hg2
               (le_weak_fwd_total _ _ k Hlew)
               (submultiset_matching_inps k _ _ Hsub)).
    Qed.

    Lemma node_will_match' gs1 t1 lbl outs gs1' gs2 t2 :
      star gstep initial_gs t1 gs1 ->
      star gstep initial_gs t2 gs2 ->
      graph_inputs_allowed (inputs_of t1) ->
      graph_inputs_allowed (inputs_of t2) ->
      gstep gs1 (O_event lbl outs) gs1' ->
      le gs1 gs2 ->
      le_weak gs1 gs2 ->
      eventually graph_will_step
        (fun '(gs2', _) => le_weak gs1' gs2') (gs2, t2).
    Proof.
      intros H1 H2 H3 H4 Hstep Hle Hlew.
      epose proof Forall2_map_get_l as Hle'. specialize Hle' with (1 := Hle).
      epose proof (graph_step_to_node_step_from_beginning gs1 t1) as Hns1'.
      epose proof (graph_step_to_node_step_from_beginning gs2 t2) as Hns2'.
      especialize Hns1'; eauto. especialize Hns2'; eauto.
      invert Hstep.
      - especialize Hle'; eauto. fwd. map_func.
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
        pose proof (le_weak_trans _ _ _ Hlew (star_gstep_le_weak _ _ _ Hreachp0)) as Hlwr.
        cbv [le_weak] in Hlwr |- *.
        rewrite (outputs_partition_map_values'
                   (fun k => enqueue (filter (forward n k) outs0)) _ ltac:(intros; reflexivity)),
                outputs_partition_put.
        eapply Forall2_map_put_l;
          [ eapply Forall2_map_impl; [ exact Hlwr | ]; intros ? ? ? Hkf ?; exact Hkf
          | rewrite outputs_partition_get, Hvalp0; reflexivity
          | ].
        simpl. apply incl_mod_app.
        + intros x Hx. rewrite Forall_forall in Hvalp1.
          destruct (Hvalp1 x Hx) as (x' & Hequiv & Hin). exists x'. split; [ exact Hin | exact Hequiv ].
        + specialize (Hlwr n). rewrite !outputs_partition_get, H6, Hvalp0 in Hlwr.
          cbn [option_map] in Hlwr. exact Hlwr.
      - especialize Hle'; eauto. fwd.
        apply eventually_done. cbv [le_weak].
        erewrite (outputs_partition_put_output_eq gs1 n ns) by (eassumption || reflexivity).
        exact Hlew.
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
      assert (Hstar1' : star gstep initial_gs (O_event lbl outs :: t1) gs1') by eauto.
      pose proof (node_will_match' _ _ _ _ _ _ _ Hstar1 Hstar2 Hga1 Hga2 Hstep Hle Hlew) as Hev.
      apply eventually_will_step_annotate in Hev.
      eapply eventually_trans; [ exact Hev | ].
      intros [gs2' t2'] (Hreach' & Hlw).
      destruct Hreach' as (tr & Hstar_gg & -> & Hga_imp).
      assert (Hstar2' : star gstep initial_gs (tr ++ t2) gs2') by eauto using star_app.
      specialize (Hga_imp Hga2).
      assert (Hsub' : submultiset (inputs_of (O_event lbl outs :: t1)) (inputs_of (tr ++ t2))).
      { rewrite inputs_of_app. simpl.
        eapply submultiset_trans;
          [ exact Hsub | exists (inputs_of tr); apply Permutation_app_comm ]. }
      pose proof (le_weak_to_le _ _ _ _ Hstar1' Hstar2' Hsub' Hga_imp Hlw) as Hle2.
      eapply eventually_weaken.
      { eapply eventually_carry_stable_gen with (P := (fun '(s, _) => le_weak gs1' s));
          [ | exact Hlw | exact Hle2 ].
        intros s s' e t Hlws Hst.
        eapply le_weak_trans;
          [ exact Hlws | exact (star_gstep_le_weak _ _ _ (star_one _ _ _ _ Hst)) ]. }
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
      assert (Hmiw' : might_implies_will_equiv' (node_step n) equiv claim consistent allowed
                        (gns_node_state ns0)).
      { apply ciw'_iff_ciw_and_monotone'; try assumption;
          try (split; [ exact Hmiw | exact Hmono ]). }
      pose proof (Hmiw' _ _ _ Hrun1 Hall1 Hout1 _ _ Hincl Hrun2 Hall2) as Hwoe.
      eapply eventually_weaken.
      { eapply (graph_eventually_of_node_eventually n _ gs2 t2 ns2);
          [ exact Hstar2 | exact Hget2 | exact Hwoe ]. }
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
      unfold output_total, output_map. intros Hin.
      apply In_concat_values in Hin. destruct Hin as (k & vs & Hget & Hin).
      rewrite get_map_values', outputs_partition_get in Hget.
      rewrite option_map_option_map in Hget. apply option_map_Some in Hget. fwd.
      apply in_map_iff in Hin. destruct Hin as (m0 & Heq & Hinf).
      apply filter_In in Hinf. fwd. subst. do 2 eexists. ssplit; eauto.
      cbv [node_has_output]. eauto.
    Qed.

    Lemma output_total_in gs n m :
      node_has_output gs n m -> output_visible n m = true -> In (m, n) (output_total gs).
    Proof.
      intros (v & Hget & Hinout) Hvis.
      unfold output_total, output_map. apply In_concat_values.
      do 2 eexists.
      split.
      - rewrite get_map_values', outputs_partition_get, Hget. reflexivity.
      - apply in_map_iff. eauto using filter_In.
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
