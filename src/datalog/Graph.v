From coqutil Require Import Map.Interface.
From coqutil Require Import Map.Properties.
From coqutil Require Import Semantics.OmniSmallstepCombinators.
From coqutil Require Import Eqb.
From Stdlib Require Import List PeanoNat Permutation.
From Stdlib Require Import RelationClasses.
From Datalog Require Import OmniSmallstep Smallstep Map List.
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
  Context (equiv_equiv : Equivalence equiv).
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

  (* A graph input fact [(m, n0)] (fact [m] destined for node [n0]) is well-formed iff [m]
     is a well-formed input at [n0] -- i.e. w.r.t. the facts delivered to [n0].  (Constraint
     type is the graph message [message * node_id], matching [allowed] at the graph level.) *)
  Definition consistent_graph_inputs : list (message * node_id) -> list (message * node_id) -> Prop. Admitted. (* := *)
    (* fun '(m, n0) inps => consistent_inputs m (map fst (filter (fun '(_, n') => Nat.eqb n0 n') inps)). *)

  Local Notation gevent := (Smallstep.IO_event graph_label (message * node_id)).

  Definition equiv_g : message * node_id -> message * node_id -> Prop :=
    fun '(m1, n1) '(m2, n2) => n1 = n2 /\ equiv m1 m2.

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

  Definition graph_inputs_allowed (inps : list (message * node_id)) :=
    forall n internal_inps,
      consistent_internal_inputs_to n internal_inps ->
      allowed (internal_inps ++ map fst (filter (fun '(_, n0) => eqb n n0) inps)).

  Context (Hcg : consistent_good).
  Context (Hcm : consistent_monotone consistent allowed).

  Context (Hcim : consistent_monotone consistent_inputs allowed).

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
        outputs_well_formed_from      node_step (consistent_output n) gns.(gns_node_state) gns.(gns_trace) /\
        monotone_mod_equiv_from       node_step equiv consistent allowed gns.(gns_node_state) gns.(gns_trace) /\
        might_implies_will_equiv_from node_step equiv allowed gns.(gns_node_state) gns.(gns_trace).

    Definition le (g1 g2 : graph_state) :=
      Forall2_map (fun n gns1 gns2 =>
                     incl_mod equiv consistent
                       (inputs_of gns1.(gns_trace)) (inputs_of gns2.(gns_trace)) /\
                       incl gns1.(gns_queue) (gns2.(gns_queue) ++ (inputs_of gns2.(gns_trace))))
        g1 g2.

    Let graph_will_step := (will_step (graph_step node_step) graph_inputs_allowed).

    From Datalog Require Import Tactics.
    From coqutil Require Import Tactics Tactics.fwd.

    Context (nodes_good : Forall_map node_good initial_gs).

    Ltac map_func :=
      repeat match goal with
        | H1: map.get ?x ?y = _, H2: map.get ?x ?y = _ |- _ => rewrite H1 in H2; invert H2
        end.

    Lemma impl_in_map [A B] (f : A -> B) x l y :
      In x l ->
      f x = y ->
      In y (map f l).
    Proof. intros. apply in_map_iff. eauto. Qed.

    Lemma impl_in_filter [A] (f : A -> bool) x l :
      In x l ->
      f x = true ->
      In x (filter f l).
    Proof. intros. apply filter_In. auto. Qed.

    Hint Constructors star : core.
    Hint Resolve in_or_app impl_in_map impl_in_filter : core.

    Lemma graph_step_to_node_step gs gt gs' :
      star gstep gs gt gs' ->
      Forall2_map (fun n gns1 gns2 =>
                     exists t'',
                       gns2.(gns_trace) = t'' ++ gns1.(gns_trace) /\
                         star node_step gns1.(gns_node_state) t'' gns2.(gns_node_state) /\
                         (forall o, output_visible n o = true ->
                               In o (outputs_of t'') ->
                               In (o, n) (outputs_of gt)))
        gs gs'.
    Proof.
      induction 1 as [ | gt2 smid e gs' Hstar IH Hstep].
      - apply Forall2_map_dup. intros n gns _. exists []. ssplit; eauto.
      - invert Hstep.
        + apply Forall2_map_mupd_r; [intros ? ? HR; exact HR | exact IH].
        + eapply Forall2_map_map_values'_r; [intros ? ? ? HR; exact HR |]. simpl.
          epose proof (Forall2_map_get_r _ _ _ _ _ IH H) as (v1 & Hv1 & Hrel).
          eapply Forall2_map_put_r; try eassumption.
          -- eapply Forall2_map_impl; [exact IH|]. intros k' w1 w2 (t'' & ? & ? & ?) ?.
             exists t''. ssplit; eauto.
          -- destruct Hrel as (t'' & Htr & Hst & Hout). exists (O_event lbl outs :: t''). ssplit; eauto.
             ++ simpl. rewrite Htr. reflexivity.
             ++ simpl. intros o Ho1 Ho2. apply in_app_iff in Ho2. destruct Ho2; eauto.
        + simpl. epose proof (Forall2_map_get_r _ _ _ _ _ IH H) as (v1 & Hv1 & Hrel).
          eapply Forall2_map_put_r; try eassumption.
          -- eapply Forall2_map_impl; [exact IH|]. intros k' w1 w2 (t'' & ? & ? & ?) ?.
             exists t''. ssplit; eauto.
          -- destruct Hrel as (t'' & Htr & Hst & Hout). exists (I_event m :: t''). ssplit; eauto.
             ++ simpl. rewrite Htr. reflexivity.
    Qed.

    Lemma graph_step_to_node_step_from_beginning gs gt :
      star gstep initial_gs gt gs ->
      Forall2_map (fun n gns0 gns =>
                     star node_step gns0.(gns_node_state) gns.(gns_trace) gns.(gns_node_state) /\
                       (forall o, output_visible n o = true ->
                             In o (outputs_of gns.(gns_trace)) -> In (o, n) (outputs_of gt)))
        initial_gs gs.
    Proof.
      intros. eapply Forall2_map_impl_strong.
      { apply graph_step_to_node_step; eauto. }
      intros n gns0 gns H1 H2 (t'' & Htr & Hst & Hout).
      apply initial_gs_empty in H1. destruct H1 as [Htr0 _].
      rewrite Htr0, app_nil_r in Htr. subst t''. eauto.
    Qed.

    Hint Constructors eventually : core.
    Hint Constructors graph_step : core.

    Lemma graph_will_step_of_node_will_step n P gs gt gns :
      Forall_map node_good gs ->
      map.get gs n = Some gns ->
      will_step node_step allowed (gns.(gns_node_state), gns.(gns_trace)) P ->
      graph_will_step
        (gs, gt)
        (fun '(gs', _) =>
           val_sat gs' n (fun gns' => P (gns'.(gns_node_state), gns'.(gns_trace)))).
    Proof.
      intros H Hn Hns. induction Hns.
      - cbv [graph_will_step will_step]. eexists. intros.
        apply graph_step_to_node_step in H1.
        eapply Forall2_map_get_l in H1; eauto. fwd.
        specialize (H0 _ _ ltac:(eassumption)).

    Admitted.

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
    Admitted.

    Definition node_received (gs : graph_state) n m :=
      val_sat gs n (fun gns => In m (inputs_of gns.(gns_trace))).

    Ltac inv_gstep :=
      match goal with
      | H: gstep _ _ _ |- _ => invert H; simpl in *
      end.

    Hint Extern 5 (In _ _) => simpl : core.
    Lemma node_received_stable_step gs e gs' n m :
      node_received gs n m ->
      gstep gs e gs' ->
      node_received gs' n m.
    Proof.
      intros (gns & Hget & Hin) Hstep. cbv [node_received val_sat]. invert Hstep.
      - rewrite get_mupd. destr (eqb n0 n);
          (rewrite Hget; cbn [option_map]; eexists; split; [reflexivity | exact Hin]).
      - rewrite get_map_values', map.get_put_dec. destr_sth Nat.eqb;
          [ map_func | rewrite Hget ];
          (cbn [option_map]; eexists; split; [reflexivity | exact Hin]).
      - rewrite map.get_put_dec. destr_sth Nat.eqb;
          [ map_func | rewrite Hget ]; (eexists; split; [reflexivity | simpl; eauto]).
    Qed.

    Lemma message_stable_step gs e gs' n m :
      val_sat gs n (fun gns => In m gns.(gns_queue)) ->
      gstep gs e gs' ->
      val_sat gs' n (fun gns => In m gns.(gns_queue)) \/ node_received gs' n m.
    Proof.
      intros (gns & Hget & Hin) Hstep. cbv [val_sat node_received]. invert Hstep.
      - left. rewrite get_mupd. destr (eqb n0 n);
          (rewrite Hget; cbn [option_map]; eexists;
           split; [reflexivity | cbn [enqueue gns_queue]; eauto using in_or_app]).
      - left. rewrite get_map_values', map.get_put_dec. destr_sth Nat.eqb;
          [ map_func | rewrite Hget ];
          (cbn [option_map]; eexists;
           split; [reflexivity | cbn [enqueue gns_queue]; eauto using in_or_app]).
      - rewrite map.get_put_dec. destr_sth Nat.eqb; eauto.
        map_func. rewrite H1 in Hin. apply in_app_or in Hin.
        destruct Hin as [Hin | [Hm | Hin]]; [left | right | left];
          (eexists; split; try reflexivity; simpl; eauto).
    Qed.

    Lemma message_stable_steps gs gt gs' n m :
      val_sat gs n (fun gns => In m gns.(gns_queue)) ->
      star gstep gs gt gs' ->
      val_sat gs' n (fun gns => In m gns.(gns_queue)) \/ node_received gs' n m.
    Proof.
      induction 2; eauto.
      destruct IHstar; eauto using message_stable_step, node_received_stable_step.
    Qed.

    Lemma node_will_receive n m gs gt :
      val_sat gs n (fun gns => In m gns.(gns_queue)) ->
      graph_will_step (gs, gt) (fun '(gs', _) => node_received gs' n m).
    Proof.
      intros Hq. cbv [graph_will_step will_step].
      exists (receive n m). intros s' t' Hs' Ht'.
      eapply message_stable_steps in Hs'; [| exact Hq].
      destruct Hs' as [Hs' | Hs']; [| left; exact Hs'].
      right. destruct Hs' as (gns' & Hget & Hin).
      apply in_split in Hin. destruct Hin as (ms1 & ms2 & Hqeq).
      destruct (nodes_input_total gns'.(gns_node_state) m) as (ns'' & Hstep).
      do 2 eexists. split.
      { eapply gstep_receive; [exact Hget | exact Hstep | exact Hqeq]. }
      cbv [node_received val_sat]. eexists. rewrite map.get_put_same.
      split; [reflexivity |]. cbn [gns_trace inputs_of]. left. reflexivity.
    Qed.

    Lemma node_will_match gs1 t1 lbl outs gs1' gs2 t2 :
      star gstep initial_graph_state t1 gs1 ->
      star gstep initial_graph_state t2 gs2 ->
      graph_inputs_allowed (inputs_of t1) ->
      graph_inputs_allowed (inputs_of t2) ->
      gstep gs1 (O_event lbl outs) gs1' ->
      le gs1 gs2 ->
      eventually graph_will_step (fun '(gs2', t2') => le gs1' gs2') (gs2, t2).
    Proof.
      intros H1 H2 H3 H4 Hstep [Hle1 Hle2]. invert Hstep.
      - epose proof Forall2_map_get_l as H. especialize H; eauto.
        destruct H as [[ns2 tn2] [Hns2 Hincl]].

        epose proof (graph_step_to_node_step_from_beginning gs1) as Hns1'.
        especialize Hns1'; eauto. eapply Forall3_map_get_l in Hns1'; eauto.
        fwd. destruct v2, v3. fwd. map_func.

        epose proof (graph_step_to_node_step_from_beginning gs2) as Hns2'.
        especialize Hns2'; eauto. eapply Forall3_map_get_l in Hns2'; eauto.
        fwd. destruct v2, v3. fwd. map_func.

        pose proof nodes_good as H'. eapply Forall2_map_get_l in H'; eauto.
        fwd. simpl in *. map_func. cbv [node_good] in H'p1. fwd.

        eassert (Hmo: Forall (might_output_equiv _ _ n3 l2) outs0).
        { apply Forall_forall. intros m Hm. eapply H'p1p1.
          5: eassumption. all: try eassumption. 1,2: admit.
          cbv [might_output]. do 2 eexists. ssplit.
          - apply star_one. eassumption.
          - reflexivity.
          - simpl. auto. }

        eapply will_output_all in Hmo; try eassumption. 2: admit.
        eapply graph_eventually_of_node_eventually in Hmo; eauto.

        eapply eventually_weaken; [eassumption|].
        intros [? ?] ?. fwd. admit.
      - rewrite H10 in Hle2. apply Forall_app in Hle2. fwd.
        destruct Hle2p1p0 as [Hle_case1|Hle_case2].
        +

        admit.
        map_func. csimpl.
        Print eventually.
        Search will_step.

        might_implies_will_equiv (node_step np) equiv allowed n2
        cbv [monotone_mod_equiv] in H'p1p1.
        epose_dep H'p1p1. specialize (H'p1p1 Hns1'p2p0 Hns2'p2p0).
        specialize' H'p1p1. 1: admit.
        specialize' H'p1p1. 1: admit.
        specialize (H'p1p1 Hincl).
        simpl in Hnsp0.
        destruct H
        pose proof apply eventually_done. cbv [le]. simpl. split. Search Forall2_map.
        +
        admit.
      -
        assert (Forall (fun o => might_output (node_step np) ns t o) outs0).
        { apply Forall_forall. intros m Hm. cbv [might_output].
          eexists. exists ns'. ssplit; eauto. simpl. apply in_app_iff; auto. }

      cbv [graph_will_step].

    Proof.
      intros T gs0 gs Hstar.
      induction Hstar as [s|s e s' t0 s'' Hstep Hstar IH];
        intros n np ns t Hp Hg0.
      - exists ns, []. rewrite app_nil_r. split; [exact Hg0|]. split; [constructor|].
        intros o _ Hout. cbn in Hout. contradiction.
      - inv_gstep Hstep; subst.
        + destruct (IH n np ns t Hp Hg0) as (ns' & td & Hg & Hstd & Hpres).
          exists ns', td. split; [exact Hg|]. split; [exact Hstd|].
          intros o Hvis Hout. exact (Hpres o Hvis Hout).
        + destruct (Nat.eq_dec n ni) as [Heq|Hne].
          * subst ni. assert (npi = np) by congruence. subst npi.
            assert (Heqp : (nsi, ti) = (ns, t)) by congruence.
            injection Heqp as Hns Ht; subst nsi ti.
            destruct (IH n np nsi' (t ++ [O_event lbli outsi]) Hp) as (ns' & td & Hg & Hstd & Hpres).
            { cbn. apply map.get_put_same. }
            exists ns', (O_event lbli outsi :: td).
            replace (t ++ O_event lbli outsi :: td) with ((t ++ [O_event lbli outsi]) ++ td)
              by (rewrite <- app_assoc; reflexivity).
            split; [exact Hg|]. split; [econstructor; [exact Hsi | exact Hstd]|].
            intros o Hvis Hout.
            apply in_app_or in Hout as [Hhead | Hrest].
            -- apply in_or_app. left.
               apply In_tag. apply filter_In. split; [exact Hhead|exact Hvis].
            -- apply in_or_app. right. exact (Hpres o Hvis Hrest).
          * destruct (IH n np ns t Hp) as (ns' & td & Hg & Hstd & Hpres).
            { cbn. rewrite map.get_put_diff by auto. exact Hg0. }
            exists ns', td. split; [exact Hg|]. split; [exact Hstd|].
            intros o Hvis Hout. specialize (Hpres o Hvis Hout).
            apply in_or_app. right. exact Hpres.
        + destruct (Nat.eq_dec n ni) as [Heq|Hne].
          * subst ni. assert (npi = np) by congruence. subst npi.
            assert (Heqp : (nsi, ti) = (ns, t)) by congruence.
            injection Heqp as Hns Ht; subst nsi ti.
            destruct (IH n np nsi' (t ++ [I_event mi]) Hp) as (ns' & td & Hg & Hstd & Hpres).
            { cbn. apply map.get_put_same. }
            exists ns', (I_event mi :: td).
            replace (t ++ I_event mi :: td) with ((t ++ [I_event mi]) ++ td)
              by (rewrite <- app_assoc; reflexivity).
            split; [exact Hg|]. split; [econstructor; [exact Hsi | exact Hstd]|].
            intros o Hvis Hout.
            exact (Hpres o Hvis Hout).
          * destruct (IH n np ns t Hp) as (ns' & td & Hg & Hstd & Hpres).
            { cbn. rewrite map.get_put_diff by auto. exact Hg0. }
            exists ns', td. split; [exact Hg|]. split; [exact Hstd|].
            intros o Hvis Hout. exact (Hpres o Hvis Hout).
    Qed.

    (* Specialization to runs from the initial graph state: a node's stored trace
       IS its projection — a valid node run from its bare initial state, whose
       visible outputs all appear in the graph trace. *)
    Proof.
      intros T gs Hstar n np ns0 Hp Hns0.
      pose proof (initial_ns_empty n ns0 Hns0) as Hempty.
      destruct ns0 as [ns0b t0b]. cbn in Hempty. subst t0b. cbn [fst].
      destruct (node_drive_delta _ _ _ Hstar n np ns0b [] Hp Hns0)
        as (ns' & td & Hg & Hstd & Hpres).
      rewrite app_nil_l in Hg.
      exists td, ns'. split; [exact Hstd|]. split; [exact Hg|]. exact Hpres.
    Qed.

    (* The "backward" reading of project_node_gen: given a node's current stored
       state (ns, t) at a reachable graph state, recover its run from the bare
       initial state and the fact that its visible outputs reach the graph trace.
       Saves the caller the project + congruence dance. *)
    Lemma node_run :
      forall T gs, star gstep initial_graph_state T gs ->
      forall n np ns0 ns t,
        map.get p n = Some np ->
        map.get initial_ns n = Some ns0 ->
        map.get gs.(g_nodes) n = Some (ns, t) ->
        star (node_step np) (fst ns0) t ns /\
        (forall o, output_visible n o = true ->
                   In o (outputs_of t) -> In (o, n) (outputs_of T)).
    Proof.
      intros T gs Hstar n np ns0 ns t Hp Hns0 Hg.
      destruct (project_node_gen _ _ Hstar n np ns0 Hp Hns0)
        as (tau & ns_at & Hrun & Hgat & Hpres).
      assert (ns_at = ns) by congruence. assert (tau = t) by congruence. subst ns_at tau.
      split; [exact Hrun | exact Hpres].
    Qed.

    (* With traces stored in the state, "node n has received message mu" is simply:
       mu appears in the inputs of n's stored trace. *)
    (* Lift a node-level will_output for node n to a graph-level will_output,
       provided o is visible from n and the graph's node n is at the right state. *)

    (* Helper: find the producing step inside an angel's path. *)
    Lemma find_producing_step :
      forall (gs_start : graph_state) (T : list gevent) (s_f : graph_state),
        star gstep gs_start T s_f ->
        inputs_of T = [] ->
        forall (o : message) (n_o : node_id),
          In (o, n_o) (outputs_of T) ->
          exists (T_pre T_post : list gevent)
                 (np_o : node_prog)
                 (ns_o ns_o' : node_state) (t_o : list IO_event)
                 (outs_o : list message) (lbl_o : label)
                 (gs_pre gs_post : graph_state),
            T = T_pre ++ O_event (run n_o lbl_o) (map (fun m => (m, n_o)) (filter (output_visible n_o) outs_o)) :: T_post /\
            star gstep gs_start T_pre gs_pre /\
            gstep gs_pre
                       (O_event (run n_o lbl_o) (map (fun m => (m, n_o)) (filter (output_visible n_o) outs_o))) gs_post /\
            star gstep gs_post T_post s_f /\
            inputs_of T_pre = [] /\
            map.get p n_o = Some np_o /\
            map.get gs_pre.(g_nodes) n_o = Some (ns_o, t_o) /\
            node_step np_o ns_o (O_event lbl_o outs_o) ns_o' /\
            In o outs_o /\
            output_visible n_o o = true.
    Proof.
      intros gs_start T s_f Hstar Hinp o n_o.
      induction Hstar as [s|s e s' t0 s'' Hstep Hstar IH]; intros Hout.
      - cbn in Hout. contradiction.
      - cbn in Hinp. destruct e as [m|lbl_e outs_e]; [discriminate|]. cbn in Hinp.

        apply in_app_or in Hout as [Hino0|Hout_rest].
        + (* o is in the head event *)
          inversion Hstep as [
            | gs0 n0 np0 ns0 t0n ns0' lbl0 outs_full Hp0 Hg0 Hns0
            | gs0 n0 np0 ns0 t0n ns0' m0 ms1 ms2 Hp0 Hg0 Hns0 Hmsg ]; subst.
          * (* gstep_run for n0 *)
            apply In_tag_inv in Hino0 as [Hn0eq Hino_filt]. subst n0.
            rewrite filter_In in Hino_filt. destruct Hino_filt as [Hino_full Hvis].
            exists [], t0, np0, ns0, ns0', t0n, outs_full, lbl0, s,
              {| g_nodes := map.put s.(g_nodes) n_o (ns0', t0n ++ [O_event lbl0 outs_full]);
                 g_messages := s.(g_messages) ++
                   flat_map (fun m => map (fun n' => (n', m)) (forward n_o m)) outs_full |}.
            split; [reflexivity|]. split; [constructor|].
            split; [eapply gstep_run; eassumption|].
            split; [exact Hstar|]. split; [reflexivity|].
            split; [exact Hp0|]. split; [exact Hg0|].
            split; [exact Hns0|]. split; [exact Hino_full | exact Hvis].
          * (* gstep_receive: outs = [] contradicts Hino0 *)
            cbn in Hino0. contradiction.
        + (* o is deeper *)
          specialize (IH Hinp Hout_rest).
          destruct IH as (T_pre & T_post & np_o & ns_o & ns_o' & t_o & outs_o & lbl_o
                          & gs_pre & gs_post & Heq_T & Hstar_pre & Hstep_prod
                          & Hstar_post & Hinp_pre & Hp_o & Hg_o & Hns_o
                          & Hino_o & Hvis_o).
          exists (O_event lbl_e outs_e :: T_pre), T_post, np_o, ns_o, ns_o', t_o, outs_o, lbl_o,
                 gs_pre, gs_post.
          split; [cbn; rewrite Heq_T; reflexivity|].
          split; [econstructor; [exact Hstep|exact Hstar_pre]|].
          split; [exact Hstep_prod|]. split; [exact Hstar_post|].
          split; [cbn; exact Hinp_pre|].
          split; [exact Hp_o|]. split; [exact Hg_o|].
          split; [exact Hns_o|]. split; [exact Hino_o | exact Hvis_o].
    Qed.

    (* General version of find_producing_step that does NOT require the run to be
       input-free: an input step in the path simply cannot carry the output, so we
       skip past it.  Used to locate the emission inside a producer run (which has
       its inputs interspersed).  The price is that T_pre may contain inputs. *)
    Lemma find_producing_step' :
      forall (gs_start : graph_state) (T : list gevent) (s_f : graph_state),
        star gstep gs_start T s_f ->
        forall (o : message) (n_o : node_id),
          In (o, n_o) (outputs_of T) ->
          exists (T_pre T_post : list gevent)
                 (np_o : node_prog)
                 (ns_o ns_o' : node_state) (t_o : list IO_event)
                 (outs_o : list message) (lbl_o : label)
                 (gs_pre gs_post : graph_state),
            T = T_pre ++ O_event (run n_o lbl_o) (map (fun m => (m, n_o)) (filter (output_visible n_o) outs_o)) :: T_post /\
            star gstep gs_start T_pre gs_pre /\
            gstep gs_pre
                       (O_event (run n_o lbl_o) (map (fun m => (m, n_o)) (filter (output_visible n_o) outs_o))) gs_post /\
            star gstep gs_post T_post s_f /\
            map.get p n_o = Some np_o /\
            map.get gs_pre.(g_nodes) n_o = Some (ns_o, t_o) /\
            node_step np_o ns_o (O_event lbl_o outs_o) ns_o' /\
            In o outs_o /\
            output_visible n_o o = true.
    Proof.
      intros gs_start T s_f Hstar o n_o.
      induction Hstar as [s|s e s' t0 s'' Hstep Hstar IH]; intros Hout.
      - cbn in Hout. contradiction.
      - destruct e as [m | lbl_e outs_e].
        + (* I_event m: the output cannot live in an input event; recurse. *)
          assert (Hout' : In (o, n_o) (outputs_of t0))
            by (exact Hout).
          specialize (IH Hout').
          destruct IH as (T_pre & T_post & np_o & ns_o & ns_o' & t_o & outs_o & lbl_o
                          & gs_pre & gs_post & Heq_T & Hstar_pre & Hstep_prod
                          & Hstar_post & Hp_o & Hg_o & Hns_o & Hino_o & Hvis_o).
          exists (I_event m :: T_pre), T_post, np_o, ns_o, ns_o', t_o, outs_o, lbl_o,
                 gs_pre, gs_post.
          split; [cbn; rewrite Heq_T; reflexivity|].
          split; [econstructor; [exact Hstep|exact Hstar_pre]|].
          split; [exact Hstep_prod|]. split; [exact Hstar_post|].
          split; [exact Hp_o|]. split; [exact Hg_o|].
          split; [exact Hns_o|]. split; [exact Hino_o | exact Hvis_o].
        +
          apply in_app_or in Hout as [Hino0|Hout_rest].
          * inversion Hstep as [
              | gs0 n0 np0 ns0 t0n ns0' lbl0 outs_full Hp0 Hg0 Hns0
              | gs0 n0 np0 ns0 t0n ns0' m0 ms1 ms2 Hp0 Hg0 Hns0 Hmsg ]; subst.
            -- apply In_tag_inv in Hino0 as [Hn0eq Hino_filt]. subst n0.
               rewrite filter_In in Hino_filt. destruct Hino_filt as [Hino_full Hvis].
               exists [], t0, np0, ns0, ns0', t0n, outs_full, lbl0, s,
                 {| g_nodes := map.put s.(g_nodes) n_o (ns0', t0n ++ [O_event lbl0 outs_full]);
                    g_messages := s.(g_messages) ++
                      flat_map (fun m => map (fun n' => (n', m)) (forward n_o m)) outs_full |}.
               split; [reflexivity|]. split; [constructor|].
               split; [eapply gstep_run; eassumption|].
               split; [exact Hstar|].
               split; [exact Hp0|]. split; [exact Hg0|].
               split; [exact Hns0|]. split; [exact Hino_full | exact Hvis].
            -- cbn in Hino0. contradiction.
          * specialize (IH Hout_rest).
            destruct IH as (T_pre & T_post & np_o & ns_o & ns_o' & t_o & outs_o & lbl_o
                            & gs_pre & gs_post & Heq_T & Hstar_pre & Hstep_prod
                            & Hstar_post & Hp_o & Hg_o & Hns_o & Hino_o & Hvis_o).
            exists (O_event lbl_e outs_e :: T_pre), T_post, np_o, ns_o, ns_o', t_o, outs_o, lbl_o,
                   gs_pre, gs_post.
            split; [cbn; rewrite Heq_T; reflexivity|].
            split; [econstructor; [exact Hstep|exact Hstar_pre]|].
            split; [exact Hstep_prod|]. split; [exact Hstar_post|].
            split; [exact Hp_o|]. split; [exact Hg_o|].
            split; [exact Hns_o|]. split; [exact Hino_o | exact Hvis_o].
    Qed.

    (* node_received is monotone under graph evolution: a node's stored trace only
       grows, so a delivered message stays recorded. *)
    Lemma node_received_mono :
      forall gs T gs', star gstep gs T gs' ->
        forall n m, node_received gs n m -> node_received gs' n m.
    Proof.
      intros gs T gs' Hstar.
      induction Hstar as [s | s e s' T' s'' Hstep Hstar IH]; intros n m Hr.
      - exact Hr.
      - apply (IH n m). destruct Hr as (ns & t & Hg & Hin).
        inv_gstep Hstep; subst.
        + exists ns, t. split; [exact Hg | exact Hin].
        + destruct (Nat.eq_dec n ni) as [->|Hne].
          * rewrite Hgi in Hg. injection Hg as Hns Ht; subst nsi ti.
            exists nsi', (t ++ [O_event lbli outsi]).
            split; [cbn; apply map.get_put_same|].
            rewrite inputs_of_app. apply in_or_app. left. exact Hin.
          * exists ns, t.
            split; [cbn; rewrite map.get_put_diff by auto; exact Hg | exact Hin].
        + destruct (Nat.eq_dec n ni) as [->|Hne].
          * rewrite Hgi in Hg. injection Hg as Hns Ht; subst nsi ti.
            exists nsi', (t ++ [I_event mi]).
            split; [cbn; apply map.get_put_same|].
            rewrite inputs_of_app. apply in_or_app. left. exact Hin.
          * exists ns, t.
            split; [cbn; rewrite map.get_put_diff by auto; exact Hg | exact Hin].
    Qed.

    (* Message provenance: a message queued at gs is, after any graph evolution,
       either still queued, or has been delivered to its destination (recorded in
       that node's stored trace). *)
    Lemma queue_fate :
      forall gs T gs', star gstep gs T gs' ->
        forall n m, In (n, m) gs.(g_messages) ->
          In (n, m) gs'.(g_messages) \/ node_received gs' n m.
    Proof.
      intros gs T gs' Hstar.
      induction Hstar as [s | s e s' T' s'' Hstep Hstar IH]; intros n m Hin.
      - left. exact Hin.
      - inv_gstep Hstep; subst; cbn [g_nodes g_messages] in IH |- *.
        + edestruct (IH n m) as [Hq | Hr];
            [right; exact Hin | left; exact Hq | right; exact Hr].
        + edestruct (IH n m) as [Hq | Hr];
            [apply in_or_app; left; exact Hin | left; exact Hq | right; exact Hr].
        + rewrite Hmsg in Hin. apply in_app_or in Hin.
          destruct Hin as [Hin_a | Hin_mid].
          * edestruct (IH n m) as [Hq | Hr];
              [apply in_or_app; left; exact Hin_a | left; exact Hq | right; exact Hr].
          * cbn in Hin_mid. destruct Hin_mid as [Heq2 | Hin_b].
            -- injection Heq2 as Hnieq Hmieq; subst ni mi.
               right. apply (node_received_mono _ _ _ Hstar).
               exists nsi', (ti ++ [I_event m]). split; [cbn; apply map.get_put_same|].
               rewrite inputs_of_app. apply in_or_app. right. left. reflexivity.
            -- edestruct (IH n m) as [Hq | Hr];
                 [apply in_or_app; right; exact Hin_b | left; exact Hq | right; exact Hr].
    Qed.
    (* A graph state is "saturated" if every message any node has emitted (recorded
       in its stored trace) is still queued or already delivered to its target. *)
    Definition saturated (gs : @graph_state node_state node_states) : Prop :=
      forall n np ns t,
        map.get p n = Some np ->
        map.get gs.(g_nodes) n = Some (ns, t) ->
        forall mu n', In mu (outputs_of t) -> In n' (forward n mu) ->
          In (n', mu) gs.(g_messages) \/ node_received gs n' mu.

    Lemma sat_step :
      forall gs e gs', gstep gs e gs' -> saturated gs -> saturated gs'.
    Proof.
      intros gs e gs' Hstep Hsat n np ns t Hp Hg mu n' Hout Hfwd.
      assert (Hmono1 : forall n0 m0, node_received gs n0 m0 -> node_received gs' n0 m0).
      { intros n0 m0 Hr.
        apply (node_received_mono _ _ _ (star_step _ _ _ _ _ _ Hstep (star_refl _ _))).
        exact Hr. }
      inv_gstep Hstep; subst.
      - (* gstep_input *)
        cbn in Hg.
        destruct (Hsat n np ns t Hp Hg mu n' Hout Hfwd) as [Hq | Hr].
        + left. cbn. right. exact Hq.
        + right. apply Hmono1. exact Hr.
      - (* gstep_run ni *)
        destruct (Nat.eq_dec n ni) as [->|Hne].
        + cbn in Hg. rewrite map.get_put_same in Hg. inversion Hg; subst.
          apply outputs_of_in_app in Hout as [Hout_old | Hout_new].
          * destruct (Hsat ni npi nsi ti Hpi Hgi mu n' Hout_old Hfwd) as [Hq | Hr].
            -- left. cbn. apply in_or_app. left. exact Hq.
            -- right. apply Hmono1. exact Hr.
          *
            apply in_app_or in Hout_new as [Hino0 | Hcontra];
              [|cbn in Hcontra; contradiction].
            left. cbn. apply in_or_app. right.
            apply in_flat_map. exists mu. split; [exact Hino0|].
            apply in_map_iff. exists n'. split; [reflexivity | exact Hfwd].
        + cbn in Hg. rewrite map.get_put_diff in Hg by auto.
          destruct (Hsat n np ns t Hp Hg mu n' Hout Hfwd) as [Hq | Hr].
          * left. cbn. apply in_or_app. left. exact Hq.
          * right. apply Hmono1. exact Hr.
      - (* gstep_receive ni mi *)
        destruct (Nat.eq_dec n ni) as [->|Hne].
        + cbn in Hg. rewrite map.get_put_same in Hg. inversion Hg; subst.
          assert (Hout_ti : In mu (outputs_of ti)).
          { apply outputs_of_in_app in Hout as [H|H]; [exact H|].
            cbn in H. contradiction. }
          destruct (Hsat ni npi nsi ti Hpi Hgi mu n' Hout_ti Hfwd) as [Hq | Hr].
          * rewrite Hmsg in Hq. apply in_app_or in Hq. destruct Hq as [Hqa | Hqm].
            -- left. cbn. apply in_or_app. left. exact Hqa.
            -- cbn in Hqm. destruct Hqm as [Heqm | Hqb].
               ++ injection Heqm as Hn'eq Hmueq; subst n' mu.
                  right. exists ns, (ti ++ [I_event mi]).
                  split; [cbn; apply map.get_put_same|].
                  rewrite inputs_of_app. apply in_or_app. right. left. reflexivity.
               ++ left. cbn. apply in_or_app. right. exact Hqb.
          * right. apply Hmono1. exact Hr.
        + cbn in Hg. rewrite map.get_put_diff in Hg by auto.
          destruct (Hsat n np ns t Hp Hg mu n' Hout Hfwd) as [Hq | Hr].
          * rewrite Hmsg in Hq. apply in_app_or in Hq. destruct Hq as [Hqa | Hqm].
            -- left. cbn. apply in_or_app. left. exact Hqa.
            -- cbn in Hqm. destruct Hqm as [Heqm | Hqb].
               ++ injection Heqm as Hn'eq Hmueq; subst n' mu.
                  right. exists nsi', (ti ++ [I_event mi]).
                  split; [cbn; apply map.get_put_same|].
                  rewrite inputs_of_app. apply in_or_app. right. left. reflexivity.
               ++ left. cbn. apply in_or_app. right. exact Hqb.
          * right. apply Hmono1. exact Hr.
    Qed.

    Lemma saturated_star :
      forall gs0 T gs, star gstep gs0 T gs ->
        saturated gs0 -> saturated gs.
    Proof.
      intros gs0 T gs Hstar. induction Hstar as [s | s e s' T' s'' Hstep Hstar IH];
        intro Hsat; [exact Hsat | apply IH; eapply sat_step; eauto].
    Qed.

    Lemma graph_saturated :
      forall T gs, star gstep initial_graph_state T gs -> saturated gs.
    Proof.
      intros T gs Hstar. eapply saturated_star; [exact Hstar|].
      intros n np ns t Hp Hg mu n' Hout Hfwd.
      cbn in Hg. apply initial_ns_empty in Hg as Ht. cbn in Ht. subst t.
      cbn in Hout. contradiction.
    Qed.

    (* Read the three [node_good] obligations off the per-node hypothesis at a
       node's bare initial state. *)
    Lemma pernode_spec_good :
      Forall2_map node_good p initial_ns ->
      forall n np ns0,
        map.get p n = Some np ->
        map.get initial_ns n = Some ns0 ->
        outputs_well_formed    (node_step np) (well_formed_output n) (fst ns0) /\
        monotone_mod_equiv     (node_step np) equiv well_formed (fst ns0) /\
        can_implies_will_equiv (node_step np) equiv well_formed (fst ns0).
    Proof.
      intros Hgood n np ns0 Hp Hns0.
      pose proof (Hgood n) as Hn. rewrite Hp, Hns0 in Hn.
      destruct ns0 as [ns tr]. exact Hn.
    Qed.
    Lemma sub_nil (l : list message) : submultiset [] l.
    Proof. exists l. reflexivity. Qed.

    Lemma sub_cons (x : message) (a b : list message) :
      submultiset a b -> submultiset (x :: a) (x :: b).
    Proof. intros (rest & Hp). exists rest. cbn. apply perm_skip. exact Hp. Qed.

    Lemma sub_app_r (a b c : list message) :
      submultiset a b -> submultiset a (b ++ c).
    Proof.
      intros (rest & Hp). exists (rest ++ c).
      rewrite app_assoc. apply Permutation_app_tail. exact Hp.
    Qed.

    Lemma sub_app_mono (a1 b1 a2 b2 : list message) :
      submultiset a1 b1 -> submultiset a2 b2 -> submultiset (a1 ++ a2) (b1 ++ b2).
    Proof.
      intros (r1 & H1) (r2 & H2). exists (r1 ++ r2).
      eapply perm_trans; [apply Permutation_app; eassumption|].
      rewrite <- !app_assoc. apply Permutation_app_head.
      rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
    Qed.

    Lemma sub_trans (a b c : list message) :
      submultiset a b -> submultiset b c -> submultiset a c.
    Proof.
      intros (r1 & H1) (r2 & H2). exists (r1 ++ r2).
      eapply perm_trans; [exact H2|].
      eapply perm_trans; [apply Permutation_app_tail; exact H1|].
      rewrite <- app_assoc. reflexivity.
    Qed.

    Lemma sub_perm_r (a b b' : list message) :
      Permutation b b' -> submultiset a b -> submultiset a b'.
    Proof. intros Hp (rest & H). exists rest. eapply perm_trans; [symmetry; exact Hp | exact H]. Qed.

    Lemma sub_perm_l (a a' b : list message) :
      Permutation a a' -> submultiset a b -> submultiset a' b.
    Proof. intros Hp (rest & H). exists rest. eapply perm_trans; [exact H | apply Permutation_app_tail; exact Hp]. Qed.

    Lemma sub_perm_both (a a' b b' : list message) :
      Permutation a a' -> Permutation b b' -> submultiset a b -> submultiset a' b'.
    Proof.
      intros Ha Hb H. apply (sub_perm_r a' b b' Hb). apply (sub_perm_l a a' b Ha). exact H.
    Qed.

    Lemma perm_mid_move (X Y Z : list message) (b : message) :
      Permutation (X ++ (Y ++ b :: Z)) ((X ++ [b]) ++ (Y ++ Z)).
    Proof.
      rewrite <- (app_assoc X [b] (Y ++ Z)). apply Permutation_app_head.
      symmetry. apply Permutation_cons_app. apply Permutation_refl.
    Qed.

    Lemma sub_map_fst {B} (a b : list (message * B)) :
      submultiset a b -> submultiset (map fst a) (map fst b).
    Proof.
      intros (rest & H). exists (map fst rest).
      rewrite <- map_app. apply Permutation_map. exact H.
    Qed.

    Lemma flat_map_sub (g : message -> list message) (l : list message) :
      (forall a, submultiset (g a) [a]) -> submultiset (flat_map g l) l.
    Proof.
      intro Hg. induction l as [|a l IH]; [apply sub_nil|].
      cbn. change (a :: l) with ([a] ++ l). apply sub_app_mono; [apply Hg | exact IH].
    Qed.

    Lemma filter_flat_map {X Y} (q : Y -> bool) (ff : X -> list Y) (l : list X) :
      filter q (flat_map ff l) = flat_map (fun x => filter q (ff x)) l.
    Proof.
      induction l as [|a l IH]; [reflexivity|]. cbn. rewrite filter_app, IH. reflexivity.
    Qed.

    Lemma map_flat_map {X Y Z} (g : Y -> Z) (ff : X -> list Y) (l : list X) :
      map g (flat_map ff l) = flat_map (fun x => map g (ff x)) l.
    Proof.
      induction l as [|a l IH]; [reflexivity|]. cbn. rewrite map_app, IH. reflexivity.
    Qed.

    Lemma filter_tag_nil (nn : node_id) (m0 : message) (L : list node_id) :
      ~ In nn L ->
      filter (fun de => Nat.eqb (fst de) nn) (map (fun n' => (n', m0)) L) = [].
    Proof.
      induction L as [|a L IH]; [reflexivity|]. cbn. intro Hni.
      destruct (Nat.eqb a nn) eqn:E.
      - apply Nat.eqb_eq in E; subst a. exfalso. apply Hni. left. reflexivity.
      - apply IH. intro; apply Hni; right; assumption.
    Qed.

    Lemma forwarded_one_sub (ni nn : node_id) (m0 : message) :
      submultiset (map snd (filter (fun de => Nat.eqb (fst de) nn)
                                   (map (fun n' => (n', m0)) (forward ni m0)))) [m0].
    Proof.
      pose proof (forward_nodup ni m0) as Hnd. induction (forward ni m0) as [|a L IH].
      - apply sub_nil.
      - cbn. destruct (Nat.eqb a nn) eqn:E.
        + apply Nat.eqb_eq in E; subst a. inversion Hnd; subst.
          rewrite filter_tag_nil by assumption. cbn. apply submultiset_refl.
        + apply IH. inversion Hnd; subst; assumption.
    Qed.

    Lemma forwarded_sub (ni nn : node_id) (outsi : list message) :
      submultiset
        (map snd (filter (fun de => Nat.eqb (fst de) nn)
           (flat_map (fun m0 => map (fun n' => (n', m0)) (forward ni m0)) outsi)))
        outsi.
    Proof.
      rewrite filter_flat_map, map_flat_map. apply flat_map_sub.
      intro a. apply forwarded_one_sub.
    Qed.
    Definition node_outputs_total (m : node_states) : list message :=
      concat (map (fun k => match map.get m k with
                            | Some (_, t) => outputs_of t | None => [] end) (map.keys p)).

    (* [node_outputs_total] decomposes, around node [ni], into [ni]'s contribution
       plus a [rest] that is unaffected by updating [ni]'s entry. *)
    Lemma node_outputs_total_put (m : node_states) (ni : node_id)
        (v : node_state * list IO_event) :
      In ni (map.keys p) -> NoDup (map.keys p) ->
      exists rest,
        Permutation (node_outputs_total m)
          ((match map.get m ni with Some (_, t) => outputs_of t | None => [] end) ++ rest) /\
        Permutation (node_outputs_total (map.put m ni v)) (outputs_of (snd v) ++ rest).
    Proof.
      intros Hin Hnd. destruct v as [xv tv]. apply in_split in Hin as (la & lb & Heq).
      rewrite Heq in Hnd. apply NoDup_remove_2 in Hnd.
      assert (Hla : ~ In ni la) by (intro; apply Hnd; apply in_or_app; left; assumption).
      assert (Hlb : ~ In ni lb) by (intro; apply Hnd; apply in_or_app; right; assumption).
      exists (concat (map (fun k => match map.get m k with Some (_, t) => outputs_of t | None => [] end) la)
              ++ concat (map (fun k => match map.get m k with Some (_, t) => outputs_of t | None => [] end) lb)).
      assert (Hla' : forall (M : node_states),
                map (fun k => match map.get (map.put M ni (xv, tv)) k with Some (_,t)=>outputs_of t|None=>[] end) la
                = map (fun k => match map.get M k with Some (_,t)=>outputs_of t|None=>[] end) la).
      { intro M. apply map_ext_in. intros k Hk. rewrite map.get_put_diff; [reflexivity|].
        intro; subst; contradiction. }
      assert (Hlb' : forall (M : node_states),
                map (fun k => match map.get (map.put M ni (xv, tv)) k with Some (_,t)=>outputs_of t|None=>[] end) lb
                = map (fun k => match map.get M k with Some (_,t)=>outputs_of t|None=>[] end) lb).
      { intro M. apply map_ext_in. intros k Hk. rewrite map.get_put_diff; [reflexivity|].
        intro; subst; contradiction. }
      split.
      - unfold node_outputs_total. rewrite Heq, map_app. cbn [map].
        rewrite concat_app. cbn [concat]. apply Permutation_app_swap_app.
      - unfold node_outputs_total. rewrite Heq, map_app. cbn [map].
        rewrite concat_app. cbn [concat].
        rewrite map.get_put_same, Hla' with (M := m), Hlb' with (M := m).
        apply Permutation_app_swap_app.
    Qed.

    Lemma node_outputs_total_grow (m : node_states) (ni : node_id)
        (x : node_state) (ti : list IO_event) (v : node_state * list IO_event)
        (delta : list message) :
      In ni (map.keys p) -> NoDup (map.keys p) ->
      map.get m ni = Some (x, ti) -> outputs_of (snd v) = outputs_of ti ++ delta ->
      Permutation (node_outputs_total (map.put m ni v)) (node_outputs_total m ++ delta).
    Proof.
      intros Hin Hnd Hget Hout.
      destruct (node_outputs_total_put m ni v Hin Hnd) as (rest & H1 & H2).
      rewrite Hget in H1. cbn in H1. rewrite Hout in H2.
      eapply perm_trans; [exact H2|].
      eapply perm_trans; [| apply Permutation_app_tail; symmetry; exact H1].
      rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_comm.
    Qed.

    Lemma node_outputs_total_same (m : node_states) (ni : node_id)
        (x : node_state) (ti : list IO_event) (v : node_state * list IO_event) :
      In ni (map.keys p) -> NoDup (map.keys p) ->
      map.get m ni = Some (x, ti) -> outputs_of (snd v) = outputs_of ti ->
      Permutation (node_outputs_total (map.put m ni v)) (node_outputs_total m).
    Proof.
      intros Hin Hnd Hget Hout.
      pose proof (node_outputs_total_grow m ni x ti v [] Hin Hnd Hget
                    ltac:(rewrite Hout, app_nil_r; reflexivity)) as H.
      rewrite app_nil_r in H. exact H.
    Qed.

    (* [node_outputs_total] filtered per producer by [q] -- e.g. the FORWARDED slice to a
       receiver [nn] takes [q k f := nn in forward k f].  Same decomposition lemmas. *)
    Definition node_outputs_total_f (q : node_id -> message -> bool) (m : node_states) : list message :=
      concat (map (fun k => match map.get m k with
                            | Some (_, t) => filter (q k) (outputs_of t) | None => [] end) (map.keys p)).

    Lemma node_outputs_total_f_put (q : node_id -> message -> bool) (m : node_states) (ni : node_id)
        (v : node_state * list IO_event) :
      In ni (map.keys p) -> NoDup (map.keys p) ->
      exists rest,
        Permutation (node_outputs_total_f q m)
          ((match map.get m ni with Some (_, t) => filter (q ni) (outputs_of t) | None => [] end) ++ rest) /\
        Permutation (node_outputs_total_f q (map.put m ni v)) (filter (q ni) (outputs_of (snd v)) ++ rest).
    Proof.
      intros Hin Hnd. destruct v as [xv tv]. apply in_split in Hin as (la & lb & Heq).
      rewrite Heq in Hnd. apply NoDup_remove_2 in Hnd.
      assert (Hla : ~ In ni la) by (intro; apply Hnd; apply in_or_app; left; assumption).
      assert (Hlb : ~ In ni lb) by (intro; apply Hnd; apply in_or_app; right; assumption).
      exists (concat (map (fun k => match map.get m k with Some (_, t) => filter (q k) (outputs_of t) | None => [] end) la)
              ++ concat (map (fun k => match map.get m k with Some (_, t) => filter (q k) (outputs_of t) | None => [] end) lb)).
      assert (Hla' : forall (M : node_states),
                map (fun k => match map.get (map.put M ni (xv, tv)) k with Some (_,t)=>filter (q k) (outputs_of t)|None=>[] end) la
                = map (fun k => match map.get M k with Some (_,t)=>filter (q k) (outputs_of t)|None=>[] end) la).
      { intro M. apply map_ext_in. intros k Hk. rewrite map.get_put_diff; [reflexivity|].
        intro; subst; contradiction. }
      assert (Hlb' : forall (M : node_states),
                map (fun k => match map.get (map.put M ni (xv, tv)) k with Some (_,t)=>filter (q k) (outputs_of t)|None=>[] end) lb
                = map (fun k => match map.get M k with Some (_,t)=>filter (q k) (outputs_of t)|None=>[] end) lb).
      { intro M. apply map_ext_in. intros k Hk. rewrite map.get_put_diff; [reflexivity|].
        intro; subst; contradiction. }
      split.
      - unfold node_outputs_total_f. rewrite Heq, map_app. cbn [map].
        rewrite concat_app. cbn [concat]. apply Permutation_app_swap_app.
      - unfold node_outputs_total_f. rewrite Heq, map_app. cbn [map].
        rewrite concat_app. cbn [concat].
        rewrite map.get_put_same, Hla' with (M := m), Hlb' with (M := m).
        apply Permutation_app_swap_app.
    Qed.

    Lemma node_outputs_total_f_grow (q : node_id -> message -> bool) (m : node_states) (ni : node_id)
        (x : node_state) (ti : list IO_event) (v : node_state * list IO_event)
        (delta : list message) :
      In ni (map.keys p) -> NoDup (map.keys p) ->
      map.get m ni = Some (x, ti) -> outputs_of (snd v) = outputs_of ti ++ delta ->
      Permutation (node_outputs_total_f q (map.put m ni v)) (node_outputs_total_f q m ++ filter (q ni) delta).
    Proof.
      intros Hin Hnd Hget Hout.
      destruct (node_outputs_total_f_put q m ni v Hin Hnd) as (rest & H1 & H2).
      rewrite Hget in H1. cbn in H1. rewrite Hout, filter_app in H2.
      eapply perm_trans; [exact H2|].
      eapply perm_trans; [| apply Permutation_app_tail; symmetry; exact H1].
      rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_comm.
    Qed.

    Lemma node_outputs_total_f_same (q : node_id -> message -> bool) (m : node_states) (ni : node_id)
        (x : node_state) (ti : list IO_event) (v : node_state * list IO_event) :
      In ni (map.keys p) -> NoDup (map.keys p) ->
      map.get m ni = Some (x, ti) -> outputs_of (snd v) = outputs_of ti ->
      Permutation (node_outputs_total_f q (map.put m ni v)) (node_outputs_total_f q m).
    Proof.
      intros Hin Hnd Hget Hout.
      pose proof (node_outputs_total_f_grow q m ni x ti v [] Hin Hnd Hget
                    ltac:(rewrite Hout, app_nil_r; reflexivity)) as H.
      cbn [filter] in H. rewrite app_nil_r in H. exact H.
    Qed.

    (* The messages forwarded to [nn] by a single emit of [outsi] from producer [ni]
       are exactly [outsi] filtered by "[nn] is a forward target". *)
    Lemma forwarded_slice_eq (ni nn : node_id) (outsi : list message) :
      map snd (filter (fun de => Nat.eqb (fst de) nn)
                 (flat_map (fun m0 => map (fun n' => (n', m0)) (forward ni m0)) outsi))
      = filter (fun f => existsb (Nat.eqb nn) (forward ni f)) outsi.
    Proof.
      rewrite filter_flat_map, map_flat_map.
      assert (Hper : forall m0,
                map snd (filter (fun de => Nat.eqb (fst de) nn) (map (fun n' => (n', m0)) (forward ni m0)))
                = if existsb (Nat.eqb nn) (forward ni m0) then [m0] else []).
      { intro m0. pose proof (forward_nodup ni m0) as Hnd0.
        induction (forward ni m0) as [|a l IHl]; [reflexivity|].
        apply NoDup_cons_iff in Hnd0. destruct Hnd0 as [Hnotin Hnd'].
        cbn [map filter existsb fst].
        destruct (Nat.eqb a nn) eqn:Ea.
        - apply Nat.eqb_eq in Ea. subst a.
          rewrite Nat.eqb_refl. cbn [orb map snd].
          assert (map snd (filter (fun de => Nat.eqb (fst de) nn) (map (fun n' => (n', m0)) l)) = []) as Hnil.
          { clear -Hnotin. induction l as [|b l0 IH0]; [reflexivity|].
            cbn [map filter fst]. destruct (Nat.eqb b nn) eqn:Eb.
            - apply Nat.eqb_eq in Eb. subst b. exfalso. apply Hnotin. left. reflexivity.
            - cbn [map snd]. apply IH0. intro H. apply Hnotin. right. exact H. }
          rewrite Hnil. reflexivity.
        - assert (Nat.eqb nn a = false) as Ena by (rewrite Nat.eqb_sym; exact Ea).
          rewrite Ena. cbn [orb map snd]. rewrite (IHl Hnd'). reflexivity. }
      induction outsi as [|m0 outsi IH]; cbn [flat_map filter]; [reflexivity|].
      rewrite IH, Hper. destruct (existsb (Nat.eqb nn) (forward ni m0)); reflexivity.
    Qed.
    Local Notation queued nn gs :=
      (map snd (filter (fun de => Nat.eqb (fst de) nn) gs.(g_messages))).

    (* Per-node conservation: a node's received inputs plus what's still queued to it
       are a submultiset of all emitted outputs plus the external inputs addressed to
       it -- the [nn]-slice of the external trace [ext]. *)
    Local Notation conserved gs ext :=
      (forall nn nsn tnn, map.get gs.(g_nodes) nn = Some (nsn, tnn) ->
         submultiset (inputs_of tnn ++ queued nn gs)
           (node_outputs_total_f (fun k f => existsb (Nat.eqb nn) (forward k f)) gs.(g_nodes)
            ++ map fst (filter (fun de => Nat.eqb (snd de) nn) ext))).

    Lemma conservation_step (gs gs' : graph_state) (e : gevent) :
      gstep gs e gs' ->
      forall ext, conserved gs ext -> conserved gs' (ext ++ inputs_of [e]).
    Proof.
      pose proof (map.keys_NoDup p) as Hnd_all.
      intros Hstep ext IH nn nsn tnn Hg'.
      inv_gstep Hstep; subst; cbn [g_nodes g_messages] in Hg' |- *.
      - (* gstep_input : g_nodes (hence forwarded total) unchanged *)
        specialize (IH nn nsn tnn Hg').
        cbn [inputs_of flat_map app]. rewrite filter_app, map_app.
        cbn [filter fst snd]. destruct (Nat.eqb ni nn) eqn:E; cbn [map fst snd].
        + apply (sub_perm_both
                   (mi :: (inputs_of tnn ++ map snd (filter (fun de => Nat.eqb (fst de) nn) (g_messages gs)))) _
                   (mi :: (node_outputs_total_f (fun k f => existsb (Nat.eqb nn) (forward k f)) (g_nodes gs)
                           ++ map fst (filter (fun de => Nat.eqb (snd de) nn) ext))) _).
          * apply Permutation_cons_app. apply Permutation_refl.
          * rewrite app_assoc. apply Permutation_cons_append.
          * apply sub_cons. exact IH.
        + rewrite app_nil_r. exact IH.
      - (* gstep_run ni : forwarded total to nn grows by outsi filtered to nn; queue grows the same *)
        cbn [inputs_of flat_map]. rewrite app_nil_r.
        assert (Hin_ni : In ni (map.keys p)) by (eapply map.in_keys; eauto).
        pose proof (node_outputs_total_f_grow (fun k f => existsb (Nat.eqb nn) (forward k f))
                      gs.(g_nodes) ni nsi ti (nsi', ti ++ [O_event lbli outsi]) outsi Hin_ni Hnd_all Hgi
                      ltac:(cbn [snd]; rewrite outputs_of_app; cbn [outputs_of flat_map]; rewrite ?app_nil_r;
                            reflexivity)) as Hgrow.
        rewrite filter_app, map_app.
        assert (Hbody : forall (tx : list IO_event) (Qx : list message),
                  submultiset (inputs_of tx ++ Qx)
                    (node_outputs_total_f (fun k f => existsb (Nat.eqb nn) (forward k f)) (g_nodes gs)
                     ++ map fst (filter (fun de => Nat.eqb (snd de) nn) ext)) ->
                  submultiset
                    (inputs_of tx ++ (Qx ++ map snd (filter (fun de => Nat.eqb (fst de) nn)
                       (flat_map (fun m0 => map (fun n' => (n', m0)) (forward ni m0)) outsi))))
                    (node_outputs_total_f (fun k f => existsb (Nat.eqb nn) (forward k f))
                       (map.put (g_nodes gs) ni (nsi', ti ++ [O_event lbli outsi]))
                     ++ map fst (filter (fun de => Nat.eqb (snd de) nn) ext))).
        { intros tx Qx Hsub. rewrite forwarded_slice_eq.
          apply (sub_perm_both
                   ((inputs_of tx ++ Qx) ++ filter (fun f => existsb (Nat.eqb nn) (forward ni f)) outsi) _
                   ((node_outputs_total_f (fun k f => existsb (Nat.eqb nn) (forward k f)) (g_nodes gs)
                     ++ map fst (filter (fun de => Nat.eqb (snd de) nn) ext))
                    ++ filter (fun f => existsb (Nat.eqb nn) (forward ni f)) outsi) _).
          - rewrite app_assoc. apply Permutation_refl.
          - eapply perm_trans; [| apply Permutation_app_tail; symmetry; exact Hgrow].
            rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_comm.
          - apply sub_app_mono; [exact Hsub | apply submultiset_refl]. }
        destruct (Nat.eq_dec nn ni) as [->|Hne].
        + rewrite map.get_put_same in Hg'. injection Hg' as <- <-.
          rewrite inputs_of_app; cbn [inputs_of flat_map]; rewrite ?app_nil_r.
          apply Hbody. apply (IH ni nsi ti Hgi).
        + rewrite map.get_put_diff in Hg' by auto.
          apply Hbody. apply (IH nn nsn tnn Hg').
      - (* gstep_receive ni mi : outputs (hence forwarded total) unchanged; dequeue mi *)
        cbn [inputs_of flat_map]. rewrite app_nil_r.
        assert (Hin_ni : In ni (map.keys p)) by (eapply map.in_keys; eauto).
        pose proof (node_outputs_total_f_same (fun k f => existsb (Nat.eqb nn) (forward k f))
                      gs.(g_nodes) ni nsi ti (nsi', ti ++ [I_event mi]) Hin_ni Hnd_all Hgi
                      ltac:(cbn [snd]; rewrite outputs_of_app; cbn [outputs_of flat_map]; rewrite ?app_nil_r;
                            reflexivity)) as Hsame.
        eapply sub_perm_r; [apply Permutation_app_tail; symmetry; exact Hsame|].
        rewrite filter_app, map_app.
        destruct (Nat.eq_dec nn ni) as [->|Hne].
        + rewrite map.get_put_same in Hg'. injection Hg' as <- <-.
          rewrite inputs_of_app; cbn [inputs_of flat_map app].
          specialize (IH ni nsi ti Hgi). rewrite Hmsg, filter_app, map_app in IH.
          cbn [filter fst] in IH. rewrite Nat.eqb_refl in IH. cbn [map snd] in IH.
          eapply sub_perm_l; [apply perm_mid_move | exact IH].
        + rewrite map.get_put_diff in Hg' by auto.
          cbn [filter fst]. replace (Nat.eqb ni nn) with false
            by (symmetry; apply Nat.eqb_neq; auto). cbn [map].
          specialize (IH nn nsn tnn Hg'). rewrite Hmsg, filter_app in IH.
          cbn [filter fst] in IH.
          replace (Nat.eqb ni nn) with false in IH
            by (symmetry; apply Nat.eqb_neq; auto). rewrite map_app in IH.
          exact IH.
    Qed.

    Lemma conservation_gen (gs0 : graph_state) (T0 : list gevent) (gs1 : graph_state) :
      star gstep gs0 T0 gs1 ->
      forall ext0, conserved gs0 ext0 -> conserved gs1 (ext0 ++ inputs_of T0).
    Proof.
      intro Hs. induction Hs as [s | s e s' T' s'' Hstep Hs IH]; intros ext0 Hconv.
      - intros nn nsn tnn Hg. cbn [inputs_of flat_map]. rewrite app_nil_r. apply (Hconv nn nsn tnn Hg).
      - pose proof (conservation_step _ _ _ Hstep ext0 Hconv) as Hconv'.
        pose proof (IH _ Hconv') as Hfin.
        intros nn nsn tnn Hg.
        eapply sub_perm_r; [| apply (Hfin nn nsn tnn Hg)].
        apply Permutation_app_head.
        change (e :: T') with ([e] ++ T'). rewrite inputs_of_app, app_assoc.
        apply Permutation_refl.
    Qed.

    Lemma conservation_run (T : list gevent) (gs : graph_state) :
      star gstep initial_graph_state T gs ->
      conserved gs (inputs_of T).
    Proof.
      intro Hstar.
      pose proof (conservation_gen initial_graph_state T gs Hstar []) as H.
      rewrite app_nil_l in H. apply H.
      intros nn nsn tnn Hg.
      pose proof (initial_ns_empty nn (nsn, tnn) Hg) as Hemp. cbn in Hemp. subst tnn.
      cbn. apply sub_nil.
    Qed.

    (* A node, once it has a stored state, keeps one along any run. *)
    Lemma node_state_persists (gs0 : graph_state) (T : list gevent) (gs : graph_state) :
      star gstep gs0 T gs ->
      forall k y, map.get gs0.(g_nodes) k = Some y ->
      exists y', map.get gs.(g_nodes) k = Some y'.
    Proof.
      intro Hstar. induction Hstar as [s | s e s' T' s'' Hstep Hs IH]; intros k y Hget.
      - eauto.
      - inv_gstep Hstep; subst; cbn [g_nodes] in *.
        + apply (IH k y Hget).
        + destruct (Nat.eq_dec k ni) as [->|Hne].
          * apply (IH ni (nsi', ti ++ [O_event lbli outsi])). apply map.get_put_same.
          * apply (IH k y). rewrite map.get_put_diff by auto. exact Hget.
        + destruct (Nat.eq_dec k ni) as [->|Hne].
          * apply (IH ni (nsi', ti ++ [I_event mi])). apply map.get_put_same.
          * apply (IH k y). rewrite map.get_put_diff by auto. exact Hget.
    Qed.

    Lemma Forall2_map_self {Bt} (R : node_id -> Bt -> Prop) (g : node_id -> Bt)
        (l : list node_id) :
      (forall k, In k l -> R k (g k)) -> Forall2 R l (map g l).
    Proof.
      induction l as [|a l IH]; cbn; intros H; constructor;
        [apply H; left; reflexivity | apply IH; intros k Hk; apply H; right; exact Hk].
    Qed.

    Lemma perm_filter {A} (q : A -> bool) (l l' : list A) :
      Permutation l l' -> Permutation (filter q l) (filter q l').
    Proof.
      induction 1; cbn.
      - apply Permutation_refl.
      - destruct (q x); [apply perm_skip|]; assumption.
      - destruct (q x), (q y); try apply perm_swap; apply Permutation_refl.
      - eapply perm_trans; eassumption.
    Qed.

    Lemma sub_slice (q : message * node_id -> bool) (l1 l2 : list (message * node_id)) :
      submultiset l1 l2 -> submultiset (map fst (filter q l1)) (map fst (filter q l2)).
    Proof.
      intros (rest & Hp). exists (map fst (filter q rest)).
      rewrite <- map_app, <- filter_app. apply Permutation_map. apply perm_filter. exact Hp.
    Qed.

    (* The forwarded-slice-to-[n] total equals [well_formed_good]'s [combine]-based slice
       (over each node's current outputs) -- so [Hwfg] applies to the pool built from
       conservation. *)
    Lemma node_fwd_total_eq (n : node_id) (m : node_states) :
      node_outputs_total_f (fun k f => existsb (Nat.eqb n) (forward k f)) m
      = concat (map (fun '(n0, fs) => filter (fun f => existsb (Nat.eqb n) (forward n0 f)) fs)
                  (combine (map.keys p)
                     (map (fun k => match map.get m k with Some (_, t) => outputs_of t | None => [] end)
                          (map.keys p)))).
    Proof.
      unfold node_outputs_total_f. f_equal.
      induction (map.keys p) as [|k ks IHks]; cbn [map combine]; [reflexivity|].
      rewrite IHks. f_equal.
      destruct (map.get m k) as [[nsk tk]|]; reflexivity.
    Qed.

    (* At a reachable graph state, a node's stored inputs are [allowed] (bounded by a
       [well_formed] pool): conservation puts them inside the messages FORWARDED to the
       node plus its external slice, and [Hwfg] certifies that pool is well-formed. *)
    Lemma node_inputs_allowed :
      Forall2_map node_good p initial_ns ->
      forall T gs, star gstep initial_graph_state T gs ->
        allowed well_formed_graph_inputs (inputs_of T) ->
        forall n np ns tn,
          map.get p n = Some np ->
          map.get gs.(g_nodes) n = Some (ns, tn) ->
          allowed well_formed (inputs_of tn).
    Proof.
      intros Hgood T gs Hstar Hall n np ns tn Hp Hg.
      destruct Hall as (Wg & Hwf_g & Hsub_g).
      pose proof (conservation_run T gs Hstar n ns tn Hg) as Hcons.
      set (fss := map (fun k => match map.get gs.(g_nodes) k with
                                | Some (_, t) => outputs_of t | None => [] end) (map.keys p)).
      assert (Hconcat : node_outputs_total gs.(g_nodes) = concat fss) by reflexivity.
      assert (HF2 : Forall2 well_formed_output (map.keys p) fss).
      { apply Forall2_map_self. intros k Hk.
        apply map.in_keys_inv in Hk.
        destruct (map.get p k) as [npk|] eqn:Hpk; [| exfalso; apply Hk; reflexivity].
        destruct (p_initial_dom k npk Hpk) as (xk & Hxk).
        destruct (node_state_persists initial_graph_state T gs Hstar k xk
                    ltac:(cbn [g_nodes initial_graph_state]; exact Hxk)) as (yk & Hgk).
        destruct yk as [nsk tk]. rewrite Hgk.
        destruct (pernode_spec_good Hgood k npk xk Hpk Hxk) as (Howf & _).
        destruct (node_run T gs Hstar k npk xk nsk tk Hpk Hxk Hgk) as (Hrun & _).
        exact (Howf tk nsk Hrun). }
      assert (Hfeq : map fst (filter (fun de => Nat.eqb (snd de) n) Wg)
                   = map fst (filter (fun '(_, n') => Nat.eqb n n') Wg)).
      { f_equal. apply filter_ext. intros [m n']. cbn. apply Nat.eqb_sym. }
      exists (node_outputs_total_f (fun k f => existsb (Nat.eqb n) (forward k f)) gs.(g_nodes)
              ++ map fst (filter (fun de => Nat.eqb (snd de) n) Wg)).
      split.
      - (* well_formed c (forwarded-slice-to-n ++ ext-slice): the forwarded slice is
           [well_formed_good]'s slice, so [Hwfg] reduces it to [well_formed_inputs c ext-slice]. *)
        intro c. rewrite node_fwd_total_eq.
        apply (proj2 (Hwfg (map.keys p) fss (map.keys_NoDup p) HF2 c _ n)).
        rewrite Hfeq. apply (Hwf_g (c, n)).
      - eapply sub_trans;
          [| apply sub_app_mono;
               [apply submultiset_refl
               | apply (sub_slice (fun de => Nat.eqb (snd de) n) (inputs_of T) Wg Hsub_g)]].
        eapply sub_trans; [| exact Hcons].
        apply sub_app_r. apply submultiset_refl.
    Qed.

    (* ---- Domination modulo [equiv] (drives the graph to re-arm a node) ---- *)

    Definition node_received_mod (gs : @graph_state node_state node_states)
        (n : node_id) (mu : message) : Prop :=
      exists ns t mu', map.get gs.(g_nodes) n = Some (ns, t) /\
                       In mu' (inputs_of t) /\ equiv mu mu'.

    Lemma incl_mod_refl l : incl_mod equiv l l.
    Proof. intros a Hin. exists a. split; [exact Hin | reflexivity]. Qed.

    Lemma incl_mod_trans l1 l2 l3 :
      incl_mod equiv l1 l2 -> incl_mod equiv l2 l3 -> incl_mod equiv l1 l3.
    Proof.
      intros H12 H23 a Hin1.
      destruct (H12 a Hin1) as (b & Hin2 & Hab).
      destruct (H23 b Hin2) as (c & Hin3 & Hbc).
      exists c. split; [exact Hin3 | etransitivity; eassumption].
    Qed.

    (* Domination up to [equiv]: each [gsA] node's inputs are [incl_mod]-covered by
       the corresponding [gsB] node's, and each [gsA]-queued message is queued (up to
       [equiv]) or already received (up to [equiv]) at [gsB]. *)
    Definition core_dom_mod (gsA gsB : @graph_state node_state node_states) : Prop :=
      (forall n np nsA tA,
         map.get p n = Some np ->
         map.get gsA.(g_nodes) n = Some (nsA, tA) ->
         exists nsB tB,
           map.get gsB.(g_nodes) n = Some (nsB, tB) /\
           incl_mod equiv (inputs_of tA) (inputs_of tB))
      /\
      (forall n m, In (n, m) gsA.(g_messages) ->
         (exists m', In (n, m') gsB.(g_messages) /\ equiv m m') \/ node_received_mod gsB n m).

    Lemma core_dom_mod_refl gs : core_dom_mod gs gs.
    Proof.
      split.
      - intros n np ns t Hp Hg. exists ns, t. split; [exact Hg | apply incl_mod_refl].
      - intros n m Hin. left. exists m. split; [exact Hin | reflexivity].
    Qed.

    (* A node's inputs only grow (as a multiset) along a run. *)
    Lemma node_inputs_grow (gs0 : graph_state) (T : list gevent) (gs : graph_state) :
      star gstep gs0 T gs ->
      forall n ns0 t0, map.get gs0.(g_nodes) n = Some (ns0, t0) ->
      exists ns t, map.get gs.(g_nodes) n = Some (ns, t) /\
                   submultiset (inputs_of t0) (inputs_of t).
    Proof.
      intro Hstar. induction Hstar as [s | s e s' T' s'' Hstep Hs IH]; intros n ns0 t0 Hget.
      - exists ns0, t0. split; [exact Hget | apply submultiset_refl].
      - assert (Hgrow1 : exists ns1 t1, map.get s'.(g_nodes) n = Some (ns1, t1) /\
                           submultiset (inputs_of t0) (inputs_of t1)).
        { inv_gstep Hstep; subst; cbn [g_nodes] in *.
          - exists ns0, t0. split; [exact Hget | apply submultiset_refl].
          - destruct (Nat.eq_dec n ni) as [->|Hne].
            + assert (ti = t0) by congruence. subst ti.
              exists nsi', (t0 ++ [O_event lbli outsi]).
              split; [apply map.get_put_same|].
              rewrite inputs_of_app; cbn [inputs_of flat_map]; rewrite app_nil_r. apply submultiset_refl.
            + rewrite map.get_put_diff by auto. exists ns0, t0. split; [exact Hget | apply submultiset_refl].
          - destruct (Nat.eq_dec n ni) as [->|Hne].
            + assert (ti = t0) by congruence. subst ti.
              exists nsi', (t0 ++ [I_event mi]).
              split; [apply map.get_put_same|]. eexists. rewrite inputs_of_app. apply Permutation_refl.
            + rewrite map.get_put_diff by auto. exists ns0, t0. split; [exact Hget | apply submultiset_refl]. }
        destruct Hgrow1 as (ns1 & t1 & Hg1 & Hsub1).
        destruct (IH n ns1 t1 Hg1) as (ns & t & Hg & Hsub).
        exists ns, t. split; [exact Hg | eapply sub_trans; eassumption].
    Qed.

    (* Modulo-domination survives any run of the dominating state: node inputs only
       grow (so [incl_mod] witnesses persist) and queued messages stay queued or
       become received ([queue_fate]).  No [active] guard, so unlike the old proof
       this needs neither allowedness nor [node_inputs_allowed]. *)
    Lemma core_dom_mod_run gs_pre gs' gs'' :
      forall T, star gstep gs' T gs'' ->
      core_dom_mod gs_pre gs' -> core_dom_mod gs_pre gs''.
    Proof.
      intros T Hrun [Hdom_n Hdom_q]. split.
      - intros n np nsA tA Hp Hg.
        destruct (Hdom_n n np nsA tA Hp Hg) as (ns' & t' & Hg' & Hincl').
        destruct (node_inputs_grow gs' T gs'' Hrun n ns' t' Hg') as (ns'' & t'' & Hg'' & Hsub).
        exists ns'', t''. split; [exact Hg''|].
        intros a Hin_a.
        destruct (Hincl' a Hin_a) as (b & Hin_b & Hab).
        exists b. split; [| exact Hab].
        destruct Hsub as (rest & Hperm). eapply Permutation_in;
          [symmetry; exact Hperm | apply in_or_app; left; exact Hin_b].
      - intros n m Hin.
        destruct (Hdom_q n m Hin) as [(m' & Hin' & Hmm') | Hrcv].
        + destruct (queue_fate gs' T gs'' Hrun n m' Hin') as [Hq'' | (ns & t & Hg'' & Hin_mu)].
          * left. exists m'. split; [exact Hq'' | exact Hmm'].
          * right. exists ns, t, m'. split; [exact Hg'' | split; [exact Hin_mu | exact Hmm']].
        + right. destruct Hrcv as (ns & t & mu' & Hg' & Hin_mu & Hmmu).
          destruct (node_inputs_grow gs' T gs'' Hrun n ns t Hg') as (ns2 & t2 & Hg2 & Hsub2).
          exists ns2, t2, mu'. split; [exact Hg2 | split; [| exact Hmmu]].
          destruct Hsub2 as (rest & Hperm). eapply Permutation_in;
            [symmetry; exact Hperm | apply in_or_app; left; exact Hin_mu].
    Qed.

    (* A node capability at a reachable, allowed graph state lifts to the node's
       modulo-[equiv] liveness, via the node's own [can_implies_will_equiv]
       obligation (fed [node_inputs_allowed]). *)
    Lemma node_will_equiv :
      Forall2_map node_good p initial_ns ->
      forall n np, map.get p n = Some np ->
      forall T gs ns t, star gstep initial_graph_state T gs ->
        allowed well_formed_graph_inputs (inputs_of T) ->
        map.get gs.(g_nodes) n = Some (ns, t) ->
      forall o, might_output (node_step np) ns t o ->
                will_output_equiv (node_step np) equiv well_formed ns t o.
    Proof.
      intros Hgood n np Hp T gs ns t HT Hall Hg o Hcan.
      destruct (p_initial_dom n np Hp) as (ns0 & Hns0).
      destruct (node_run T gs HT n np ns0 ns t Hp Hns0 Hg) as (Hrun & _).
      destruct (pernode_spec_good Hgood n np ns0 Hp Hns0) as (_ & _ & Hciw).
      apply (Hciw t ns o Hrun
               (node_inputs_allowed Hgood T gs HT Hall n np ns t Hp Hg) Hcan).
    Qed.

    (* Force a queued (or matched-received) message to be delivered to its consumer:
       if the demon already delivered it the angel is done; otherwise the angel
       delivers it ([nodes_input_total] supplies the receive step). *)
    Lemma force_deliver_equiv :
      forall TX gsX, star gstep initial_graph_state TX gsX ->
      forall c m npc ns0c,
        map.get p c = Some npc ->
        map.get initial_ns c = Some ns0c ->
        (In (c, m) gsX.(g_messages) \/ node_received gsX c m) ->
      forall t,
        eventually (will_step gstep well_formed_graph_inputs)
          (fun '(gs', _) => node_received gs' c m) (gsX, t).
    Proof.
      intros TX gsX HTX c m npc ns0c Hpc Hns0c Hcm t.
      destruct Hcm as [Hq | Hr].
      - apply eventually_step_cps. exists (receive c m).
        intros gs_d t_d Hstar_d Hallow.
        pose proof (star_app _ _ _ _ _ _ HTX Hstar_d) as HTd.
        destruct (queue_fate _ _ _ Hstar_d c m Hq) as [Hqd | Hrd].
        + right.
          destruct (project_node_gen _ _ HTd c npc ns0c Hpc Hns0c)
            as (tauc & nsc & _ & Hgc & _).
          apply in_split in Hqd as (ms1 & ms2 & Hsplit).
          destruct (nodes_input_total c npc Hpc nsc m) as (nsc' & Hstepc).
          exists {| g_nodes := map.put gs_d.(g_nodes) c (nsc', tauc ++ [I_event m]);
                    g_messages := ms1 ++ ms2 |}, [].
          split.
          * eapply gstep_receive; [exact Hpc | exact Hgc | exact Hstepc | exact Hsplit].
          * apply eventually_done. cbn. exists nsc', (tauc ++ [I_event m]).
            split; [apply map.get_put_same|].
            rewrite inputs_of_app. apply in_or_app. right. left. reflexivity.
        + left. apply eventually_done. exact Hrd.
      - apply eventually_done. exact Hr.
    Qed.


    (* Carry [core_dom_mod gs_pre] plus a reachable-allowed bundle through a driven
       eventually.  [core_dom_mod_run] needs no allowedness now, but the bundle still
       carries [allowed ...] for the downstream capability transfer. *)
    Lemma eventually_carry_dom (gs_pre : graph_state) :
      Forall2_map node_good p initial_ns ->
      forall (P : graph_state * list gevent -> Prop) gs t T0,
        star gstep initial_graph_state T0 gs ->
        allowed well_formed_graph_inputs (inputs_of T0) ->
        Permutation (inputs_of T0) (inputs_of t) ->
        core_dom_mod gs_pre gs ->
        eventually (will_step gstep well_formed_graph_inputs) P (gs, t) ->
        eventually (will_step gstep well_formed_graph_inputs)
          (fun '(gs', t') => P (gs', t') /\
             (exists T', star gstep initial_graph_state T' gs' /\
                         allowed well_formed_graph_inputs (inputs_of T') /\
                         Permutation (inputs_of T') (inputs_of t') /\
                         core_dom_mod gs_pre gs')) (gs, t).
    Proof.
      intros Hgood P gs t T0 HT0 Hall0 Hperm0 Hdom Hev.
      remember (gs, t) as st eqn:Est. revert gs t T0 HT0 Hall0 Hperm0 Hdom Est.
      induction Hev as [[s' t'] HP | [s' t'] midset Hcan Hmid IH];
        intros gs t T0 HT0 Hall0 Hperm0 Hdom [= -> ->].
      - apply eventually_done. split; [exact HP|].
        exists T0. split; [exact HT0 | split; [exact Hall0 | split; [exact Hperm0 | exact Hdom]]].
      - destruct Hcan as [glbl Hcan].
        apply eventually_step_cps. exists glbl.
        intros gs_d t_d Hstar_d Hallow.
        assert (HT0d : star gstep initial_graph_state (T0 ++ t_d) gs_d)
          by (eapply star_app; eassumption).
        assert (Hall0d : allowed well_formed_graph_inputs (inputs_of (T0 ++ t_d))).
        { eapply allowed_perm; [| exact Hallow].
          rewrite !inputs_of_app. eapply perm_trans; [apply Permutation_app_comm|].
          apply Permutation_app_tail. symmetry. exact Hperm0. }
        assert (Hperm0d : Permutation (inputs_of (T0 ++ t_d)) (inputs_of (t_d ++ t))).
        { rewrite !inputs_of_app. eapply perm_trans;
            [apply Permutation_app_tail; exact Hperm0 | apply Permutation_app_comm]. }
        pose proof (core_dom_mod_run gs_pre gs gs_d t_d Hstar_d Hdom) as Hdom_d.
        specialize (Hcan gs_d t_d Hstar_d Hallow).
        destruct Hcan as [Hmid_left | (s'' & outs & Hstep & Hmidset)].
        + left. apply (IH (gs_d, t_d ++ t) Hmid_left gs_d (t_d ++ t) (T0 ++ t_d)
                          HT0d Hall0d Hperm0d Hdom_d eq_refl).
        + right. exists s'', outs. split; [exact Hstep|].
          assert (HT0d' : star gstep initial_graph_state ((T0 ++ t_d) ++ [O_event glbl outs]) s'')
            by (eapply star_app; [exact HT0d | econstructor; [exact Hstep | constructor]]).
          assert (Hall0d' : allowed well_formed_graph_inputs (inputs_of ((T0 ++ t_d) ++ [O_event glbl outs]))).
          { eapply allowed_perm; [| exact Hall0d].
            replace (inputs_of ((T0 ++ t_d) ++ [O_event glbl outs])) with (inputs_of (T0 ++ t_d))
              by (rewrite (inputs_of_app (T0 ++ t_d) [O_event glbl outs]); cbn [inputs_of flat_map app]; rewrite ?app_nil_r; reflexivity).
            apply Permutation_refl. }
          assert (Hperm0d' : Permutation (inputs_of ((T0 ++ t_d) ++ [O_event glbl outs]))
                                         (inputs_of (O_event glbl outs :: t_d ++ t))).
          { replace (inputs_of ((T0 ++ t_d) ++ [O_event glbl outs])) with (inputs_of (T0 ++ t_d))
              by (rewrite (inputs_of_app (T0 ++ t_d) [O_event glbl outs]); cbn [inputs_of flat_map app]; rewrite ?app_nil_r; reflexivity).
            replace (inputs_of (O_event glbl outs :: t_d ++ t)) with (inputs_of (t_d ++ t))
              by reflexivity.
            exact Hperm0d. }
          pose proof (core_dom_mod_run gs_pre gs_d s''
                        [O_event glbl outs] (star_step _ _ _ _ _ _ Hstep (star_refl _ _))
                        Hdom_d) as Hdom_d'.
          apply (IH _ Hmidset s'' (O_event glbl outs :: t_d ++ t)
                    ((T0 ++ t_d) ++ [O_event glbl outs]) HT0d' Hall0d' Hperm0d' Hdom_d');
            reflexivity.
    Qed.

    (* Capability transfer up to [equiv]: a single [monotone_mod_equiv] step.  Both
       node states are reachable so their inputs are [allowed] ([node_inputs_allowed]);
       [gs2]'s inputs [equiv]-cover [gs1]'s ([incl_mod]); constraint-preservation is
       [well_formed_mono_mod]. *)
    Lemma node_cap_transfer_equiv :
      Forall2_map node_good p initial_ns ->
      forall n np, map.get p n = Some np ->
      forall T1 gs1 ns1 t1, star gstep initial_graph_state T1 gs1 ->
        allowed well_formed_graph_inputs (inputs_of T1) ->
        map.get gs1.(g_nodes) n = Some (ns1, t1) ->
      forall T2 gs2 ns2 t2, star gstep initial_graph_state T2 gs2 ->
        allowed well_formed_graph_inputs (inputs_of T2) ->
        map.get gs2.(g_nodes) n = Some (ns2, t2) ->
        incl_mod equiv (inputs_of t1) (inputs_of t2) ->
      forall o, might_output (node_step np) ns1 t1 o ->
                might_output_equiv (node_step np) equiv ns2 t2 o.
    Proof.
      intros Hgood n np Hp T1 gs1 ns1 t1 HT1 Hall1 Hg1 T2 gs2 ns2 t2 HT2 Hall2 Hg2 Hincl o Hmight.
      destruct (p_initial_dom n np Hp) as (ns0 & Hns0).
      destruct (node_run T1 gs1 HT1 n np ns0 ns1 t1 Hp Hns0 Hg1) as (Hrun1 & _).
      destruct (node_run T2 gs2 HT2 n np ns0 ns2 t2 Hp Hns0 Hg2) as (Hrun2 & _).
      destruct (pernode_spec_good Hgood n np ns0 Hp Hns0) as (_ & Hmono_eq & _).
      pose proof (node_inputs_allowed Hgood T1 gs1 HT1 Hall1 n np ns1 t1 Hp Hg1) as Hallt1.
      pose proof (node_inputs_allowed Hgood T2 gs2 HT2 Hall2 n np ns2 t2 Hp Hg2) as Hallt2.
      apply (Hmono_eq t1 t2 ns1 ns2 o Hrun1 Hrun2 Hallt1 Hallt2 Hincl).
      - (* constraint-preservation.  PLAN: strengthen domination to submultiset, then
           this is [well_formed_monotone]. *)
        intros c Hin_c Hwf1. admit.
      - exact Hmight.
    Admitted.

    Lemma will_output_equiv_weaken (np : node_prog) (s : node_state)
        (tr : list IO_event) (a b : message) :
      equiv a b ->
      will_output_equiv (node_step np) equiv well_formed s tr a ->
      will_output_equiv (node_step np) equiv well_formed s tr b.
    Proof.
      intros Hab Hwill. unfold will_output_equiv in *.
      eapply eventually_weaken; [exact Hwill|].
      intros [s' t'] (o'' & Ho'' & Hin). exists o''.
      split; [etransitivity; eassumption | exact Hin].
    Qed.

    (* "node [n'] has, up to [equiv], been forwarded [mu]": queued or received. *)
    Definition forwarded_mod (gs : @graph_state node_state node_states)
        (n' : node_id) (mu : message) : Prop :=
      (exists m', In (n', m') gs.(g_messages) /\ equiv mu m') \/ node_received_mod gs n' mu.

    (* [forwarded_mod] survives any run: queued stays queued or becomes received
       ([queue_fate]); received persists as inputs only grow ([node_inputs_grow]). *)
    Lemma forwarded_mod_run gs T gs' n' mu :
      star gstep gs T gs' -> forwarded_mod gs n' mu -> forwarded_mod gs' n' mu.
    Proof.
      intros Hrun [(m' & Hin & Hmm') | (ns & t & mu' & Hg & Hin_mu & Hmmu)].
      - destruct (queue_fate gs T gs' Hrun n' m' Hin) as [Hq | (ns & t & Hg & Hin_mu)].
        + left. exists m'. split; [exact Hq | exact Hmm'].
        + right. exists ns, t, m'. split; [exact Hg | split; [exact Hin_mu | exact Hmm']].
      - right. destruct (node_inputs_grow gs T gs' Hrun n' ns t Hg) as (ns2 & t2 & Hg2 & Hsub).
        exists ns2, t2, mu'. split; [exact Hg2 | split; [| exact Hmmu]].
        destruct Hsub as (rest & Hperm). eapply Permutation_in;
          [symmetry; exact Hperm | apply in_or_app; left; exact Hin_mu].
    Qed.

    (* Carry a run-closed state invariant [Inv] through a driven eventually. *)
    Lemma eventually_carry_inv :
      forall (Inv : graph_state -> Prop),
        (forall gs T gs', star gstep gs T gs' -> Inv gs -> Inv gs') ->
        forall (P : graph_state * list gevent -> Prop) gs t,
          Inv gs ->
          eventually (will_step gstep well_formed_graph_inputs) P (gs, t) ->
          eventually (will_step gstep well_formed_graph_inputs)
            (fun '(gs', t') => P (gs', t') /\ Inv gs') (gs, t).
    Proof.
      intros Inv Hinv P gs t HInv Hev.
      remember (gs, t) as st eqn:Est. revert gs t HInv Est.
      induction Hev as [[s' t'] HP | [s' t'] midset Hcan Hmid IH];
        intros gs t HInv [= -> ->].
      - apply eventually_done. split; [exact HP | exact HInv].
      - destruct Hcan as [glbl Hcan].
        apply eventually_step_cps. exists glbl.
        intros gs_d t_d Hstar_d Hallow.
        specialize (Hcan gs_d t_d Hstar_d Hallow).
        destruct Hcan as [Hmid_left | (s'' & outs & Hstep & Hmidset)].
        + left. apply (IH (gs_d, t_d ++ t) Hmid_left gs_d (t_d ++ t)
                          (Hinv _ _ _ Hstar_d HInv) eq_refl).
        + right. exists s'', outs. split; [exact Hstep|].
          apply (IH _ Hmidset s'' (O_event glbl outs :: t_d ++ t)); [|reflexivity].
          eapply Hinv; [|exact HInv].
          eapply star_app; [exact Hstar_d | econstructor; [exact Hstep | constructor]].
    Qed.

    (* Force node [c] to receive every message in [ms] (each currently queued to [c] or
       already received), by chaining [force_deliver_equiv] and carrying the ones already
       delivered.  This is the "force the node to receive all its forwarded messages" step. *)
    Lemma force_deliver_node_all :
      forall (c : node_id) npc ns0c,
        map.get p c = Some npc -> map.get initial_ns c = Some ns0c ->
      forall (ms : list message),
      forall TX gsX, star gstep initial_graph_state TX gsX ->
        (forall m, In m ms -> In (c, m) gsX.(g_messages) \/ node_received gsX c m) ->
      forall t,
        eventually (will_step gstep well_formed_graph_inputs)
          (fun '(gs', _) => forall m, In m ms -> node_received gs' c m) (gsX, t).
    Proof.
      intros c npc ns0c Hpc Hns0c ms.
      induction ms as [|m ms IH]; intros TX gsX HTX Hall t.
      - apply eventually_done. intros m [].
      - eapply eventually_trans.
        { apply (eventually_carry_inv
                   (fun gs => (exists T, star gstep initial_graph_state T gs) /\
                              (forall m', In m' ms -> In (c, m') gs.(g_messages) \/ node_received gs c m'))
                   ltac:(intros ga T0 gb Hs Hinv; destruct Hinv as (HT & Hq); split;
                         [ destruct HT as (Tg & HTg); exists (Tg ++ T0); eapply star_app; eassumption
                         | intros m' Hm'; destruct (Hq m' Hm') as [Hqm | Hrm];
                           [ destruct (queue_fate _ _ _ Hs c m' Hqm) as [Hq2 | (ns2 & t2 & Hg2 & Hin2)];
                             [ left; exact Hq2 | right; exists ns2, t2; split; [exact Hg2 | exact Hin2] ]
                           | right; apply (node_received_mono _ _ _ Hs c m' Hrm) ] ])
                   _ gsX t
                   (conj (ex_intro _ TX HTX)
                         (fun m' Hm' => Hall m' (or_intror Hm')))
                   (force_deliver_equiv TX gsX HTX c m npc ns0c Hpc Hns0c
                      (Hall m (or_introl eq_refl)) t)). }
        intros [gs' t'] (Hrcv_m & (HTg' & Hall')).
        destruct HTg' as (TX' & HTX').
        eapply eventually_trans.
        { apply (eventually_carry_inv (fun gs => node_received gs c m)
                   ltac:(intros ga T0 gb Hs Hr; apply (node_received_mono _ _ _ Hs c m Hr))
                   _ gs' t' Hrcv_m
                   (IH TX' gs' HTX' Hall' t')). }
        intros [gs'' t''] (Hallms & Hrcv_m').
        apply eventually_done.
        intros m0 [Hm0 | Hm0]; [subst m0; exact Hrcv_m' | apply Hallms; exact Hm0].
    Qed.

    (* The node-state domain is invariant under runs. *)
    Lemma dom_preserved :
      forall gs0 T gs, star gstep gs0 T gs ->
      forall n x, map.get gs.(g_nodes) n = Some x ->
      exists x0, map.get gs0.(g_nodes) n = Some x0.
    Proof.
      intros gs0 T gs Hstar.
      induction Hstar as [s | s e s' t0 s'' Hstep Hstar IH]; intros n x Hg.
      - eauto.
      - destruct (IH n x Hg) as (x1 & Hx1).
        inv_gstep Hstep; subst; cbn in Hx1.
        + eauto.
        + destruct (Nat.eq_dec n ni) as [->|Hne]; [eauto|].
          rewrite map.get_put_diff in Hx1 by auto. eauto.
        + destruct (Nat.eq_dec n ni) as [->|Hne]; [eauto|].
          rewrite map.get_put_diff in Hx1 by auto. eauto.
    Qed.

    Lemma reachable_state_initial :
      forall T gs, star gstep initial_graph_state T gs ->
      forall n x, map.get gs.(g_nodes) n = Some x ->
      exists ns0, map.get initial_ns n = Some ns0.
    Proof.
      intros T gs Hstar n x Hg.
      destruct (dom_preserved _ _ _ Hstar n x Hg) as (x0 & Hx0).
      cbn in Hx0. eauto.
    Qed.

    (* "node [n] has, up to [equiv], emitted [mu]". *)
    Definition node_emitted_mod (gs : @graph_state node_state node_states)
        (n : node_id) (mu : message) : Prop :=
      exists ns t mu', map.get gs.(g_nodes) n = Some (ns, t) /\
                       In mu' (outputs_of t) /\ equiv mu mu'.


    (* A reachable, allowed from-initial trace matching (up to permutation) the
       eventually's trace component -- carried through the graph-level drive. *)
    Definition reach_allow (gs : graph_state) (t : list gevent) : Prop :=
      exists T0, star gstep initial_graph_state T0 gs /\
                 allowed well_formed_graph_inputs (inputs_of T0) /\
                 Permutation (inputs_of T0) (inputs_of t).

    (* Drive a single node [n] -- whose own run [will_output_equiv]-emits a relative
       of [mu] -- at the graph level, until [n] has emitted some [equiv]-relative of
       [mu] ([node_emitted_mod]). *)
    Lemma drive_node_emit_equiv :
      Forall2_map node_good p initial_ns ->
      forall (np : node_prog) (n : node_id) (mu : message),
        map.get p n = Some np ->
        forall (s : node_state * list IO_event),
          eventually (will_step (node_step np) well_formed)
                     (fun '(_, t') => exists mu', equiv mu' mu /\ In mu' (outputs_of t')) s ->
          forall gs t,
            reach_allow gs t ->
            (exists tr, map.get gs.(g_nodes) n = Some (fst s, tr) /\
                        Permutation (inputs_of (snd s)) (inputs_of tr) /\
                        (forall x, In x (outputs_of (snd s)) -> In x (outputs_of tr))) ->
            eventually (will_step gstep well_formed_graph_inputs)
                       (fun '(gs', _) => node_emitted_mod gs' n mu) (gs, t).
    Proof.
      intros Hgood np n mu Hp s Hwill.
      assert (Hio_snoc_g : forall (l : list gevent) glbl (o : list (message * node_id)),
                inputs_of (l ++ [O_event glbl o]) = inputs_of l)
        by (intros ll gg oo; rewrite inputs_of_app; cbn [inputs_of flat_map app];
            rewrite ?app_nil_r; reflexivity).
      assert (Hio_snoc_n : forall (l : list IO_event) glbl (o : list message),
                inputs_of (l ++ [O_event glbl o]) = inputs_of l)
        by (intros ll gg oo; rewrite inputs_of_app; cbn [inputs_of flat_map app];
            rewrite ?app_nil_r; reflexivity).
      induction Hwill as [[ns_curr trace_curr] HP|
                          [ns_curr trace_curr] midset Hcan Hmid IH];
        intros gs t Hreach (tr & Hg & Hpermtr & Hsub); cbn [fst snd] in Hg, Hpermtr, Hsub.
      - apply eventually_done. destruct HP as (mu' & Heqmu' & Hin).
        exists ns_curr, tr, mu'. split; [exact Hg|]. split; [apply Hsub; exact Hin|].
        symmetry. exact Heqmu'.
      - destruct Hreach as (T0 & HT0 & HallT0 & HpermT0).
        destruct Hcan as [node_lbl Hcan].
        apply eventually_step_cps. exists (run n node_lbl).
        intros gs_demon t_demon Hstar_demon Hallow_g.
        destruct (node_drive_delta _ _ _ Hstar_demon n np ns_curr tr Hp Hg)
          as (ns_d & tau_d & Hg_d & Htau_d & Hpres_d).
        pose proof (Hcan ns_d tau_d Htau_d) as Hcan'.
        assert (HreachD : star gstep initial_graph_state (T0 ++ t_demon) gs_demon)
          by (eapply star_app; eassumption).
        assert (HallowD : allowed well_formed_graph_inputs (inputs_of (T0 ++ t_demon))).
        { eapply allowed_perm; [| exact Hallow_g].
          rewrite !inputs_of_app. eapply perm_trans; [apply Permutation_app_comm|].
          apply Permutation_app_tail. symmetry. exact HpermT0. }
        assert (HpermD : Permutation (inputs_of (T0 ++ t_demon)) (inputs_of (t_demon ++ t))).
        { rewrite !inputs_of_app. eapply perm_trans;
            [apply Permutation_app_tail; exact HpermT0 | apply Permutation_app_comm]. }
        assert (Hpermtr_d : Permutation (inputs_of (tau_d ++ trace_curr)) (inputs_of (tr ++ tau_d))).
        { rewrite !inputs_of_app. eapply perm_trans; [apply Permutation_app_comm|].
          apply Permutation_app_tail. exact Hpermtr. }
        assert (Hallow_n : allowed well_formed (inputs_of (tau_d ++ trace_curr))).
        { eapply allowed_perm;
            [ symmetry; exact Hpermtr_d
            | apply (node_inputs_allowed Hgood (T0 ++ t_demon) gs_demon HreachD HallowD
                       n np ns_d (tr ++ tau_d) Hp Hg_d)]. }
        specialize (Hcan' Hallow_n).
        assert (Hsub_d : forall x, In x (outputs_of (tau_d ++ trace_curr)) ->
                  In x (outputs_of (tr ++ tau_d))).
        { intros x Hx. rewrite outputs_of_app in Hx. apply in_app_or in Hx as [Hx|Hx];
            rewrite outputs_of_app; apply in_or_app; [right; exact Hx | left; apply Hsub; exact Hx]. }
        destruct Hcan' as [Hmid_left | (s'' & outs & Hns_step & Hmidset_at)].
        { left.
          apply (IH (ns_d, tau_d ++ trace_curr) Hmid_left gs_demon (t_demon ++ t)).
          - exists (T0 ++ t_demon). split; [exact HreachD|]. split; [exact HallowD | exact HpermD].
          - exists (tr ++ tau_d). cbn [fst snd].
            split; [exact Hg_d|]. split; [exact Hpermtr_d | exact Hsub_d]. }
        right.
        set (gs_next :=
               {| g_nodes := map.put gs_demon.(g_nodes) n (s'', (tr ++ tau_d) ++ [O_event node_lbl outs]);
                  g_messages :=
                    gs_demon.(g_messages) ++
                    flat_map (fun m0 => map (fun n' => (n', m0))
                                            (forward n m0)) outs |}).
        exists gs_next, (map (fun m => (m, n)) (filter (output_visible n) outs)).
        split.
        { eapply gstep_run; [exact Hp | exact Hg_d | exact Hns_step]. }
        apply (IH (s'', O_event node_lbl outs :: tau_d ++ trace_curr) Hmidset_at gs_next
                  (O_event (run n node_lbl) (map (fun m => (m, n)) (filter (output_visible n) outs))
                     :: t_demon ++ t)).
        + exists ((T0 ++ t_demon) ++
                  [O_event (run n node_lbl) (map (fun m => (m, n)) (filter (output_visible n) outs))]).
          split; [eapply star_app; [exact HreachD | econstructor;
                   [eapply gstep_run; [exact Hp | exact Hg_d | exact Hns_step] | constructor]]|].
          split.
          * eapply allowed_perm; [| exact HallowD]. rewrite Hio_snoc_g. apply Permutation_refl.
          * rewrite Hio_snoc_g. exact HpermD.
        + exists ((tr ++ tau_d) ++ [O_event node_lbl outs]). cbn [fst snd].
          split; [apply map.get_put_same|]. split.
          * rewrite Hio_snoc_n. exact Hpermtr_d.
          * intros x Hx. cbn [outputs_of flat_map] in Hx. apply in_app_or in Hx as [Hx | Hx].
            -- rewrite outputs_of_app. apply in_or_app. right. cbn [outputs_of flat_map].
               apply in_or_app. left. exact Hx.
            -- rewrite outputs_of_app. apply in_or_app. left. apply Hsub_d. exact Hx.
    Qed.
    Lemma force_emit_list_equiv :
      Forall2_map node_good p initial_ns ->
      forall (outs : list message) (f : node_id) npf,
        map.get p f = Some npf ->
        forall T gsX, star gstep initial_graph_state T gsX -> allowed well_formed_graph_inputs (inputs_of T) ->
        forall nsf tf, map.get gsX.(g_nodes) f = Some (nsf, tf) ->
        (forall mu, In mu outs -> might_output_equiv (node_step npf) equiv nsf tf mu) ->
        forall t, Permutation (inputs_of T) (inputs_of t) ->
        eventually (will_step gstep well_formed_graph_inputs)
          (fun '(gs', t') =>
             (core_dom_mod gsX gs' /\
              (exists T', star gstep initial_graph_state T' gs' /\ allowed well_formed_graph_inputs (inputs_of T') /\
                          Permutation (inputs_of T') (inputs_of t'))) /\
             (forall mu n', In mu outs -> In n' (forward f mu) -> forwarded_mod gs' n' mu))
          (gsX, t).
    Proof.
      intros Hgood outs. induction outs as [|mu outs IH];
        intros f npf Hpf T gsX HT Hall nsf tf HgX Hcan t Hperm.
      - apply eventually_done. split.
        + split; [apply core_dom_mod_refl|].
          exists T. split; [exact HT | split; [exact Hall | exact Hperm]].
        + intros mu n' [] _.
      - (* drive f to emit a relative of mu *)
        destruct (Hcan mu (or_introl eq_refl)) as (o' & Heqo' & Hmight_o').
        pose proof (node_will_equiv Hgood f npf Hpf T gsX nsf tf HT Hall HgX o' Hmight_o') as Hwill_o'.
        pose proof (will_output_equiv_weaken npf nsf tf o' mu Heqo' Hwill_o') as Hwill_mu.
        pose proof (drive_node_emit_equiv Hgood npf f mu Hpf (nsf, tf) Hwill_mu gsX t
                      (ex_intro _ T (conj HT (conj Hall Hperm)))
                      (ex_intro _ tf (conj HgX (conj (Permutation_refl _) (fun x H => H)))))
          as Hemit.
        eapply eventually_trans.
        { apply (eventually_carry_dom gsX Hgood _ gsX t T HT Hall Hperm
                   (core_dom_mod_refl gsX) Hemit). }
        intros [gsM tM] (Hemitted & (TM & HTM & HallM & HpermM & HdomM)).
        (* f's state at gsM, and its input-domination from gsX *)
        destruct Hemitted as (nsM & tfM & mu'' & HgfM & Hout_mu'' & Hmu_mu'').
        destruct (proj1 HdomM f npf nsf tf Hpf HgX) as (nsM' & tfM' & HgfM' & Hincl_f).
        assert (nsM' = nsM /\ tfM' = tfM) as [-> ->] by (split; congruence).
        (* the forwarded relatives of mu are queued/received at gsM *)
        assert (Hfwd_mu : forall n', In n' (forward f mu) -> forwarded_mod gsM n' mu).
        { intros n' Hn'. rewrite (forward_equiv f mu mu'' Hmu_mu'') in Hn'.
          destruct (graph_saturated _ _ HTM f npf nsM tfM Hpf HgfM mu'' n' Hout_mu'' Hn')
            as [Hq | Hr].
          - left. exists mu''. split; [exact Hq | exact Hmu_mu''].
          - right. destruct Hr as (ns & t0 & Hg & Hin_mu). exists ns, t0, mu''.
            split; [exact Hg | split; [exact Hin_mu | exact Hmu_mu'']]. }
        (* re-arm f for the rest of outs at gsM *)
        assert (Hcan_M : forall mu0, In mu0 outs ->
                  might_output_equiv (node_step npf) equiv nsM tfM mu0).
        { intros mu0 Hin0. destruct (Hcan mu0 (or_intror Hin0)) as (o0 & Heqo0 & Hmight_o0).
          destruct (node_cap_transfer_equiv Hgood f npf Hpf T gsX nsf tf HT Hall HgX
                      TM gsM nsM tfM HTM HallM HgfM Hincl_f o0 Hmight_o0) as (x & Hxo0 & Hmightx).
          exists x. split; [etransitivity; eassumption | exact Hmightx]. }
        pose proof (IH f npf Hpf TM gsM HTM HallM nsM tfM HgfM Hcan_M tM HpermM) as Hrec.
        (* carry core_dom_mod gsX and forwarded-mu through the recursion *)
        pose proof (eventually_carry_dom gsX Hgood _ gsM tM TM HTM HallM HpermM HdomM Hrec)
          as Hrec1.
        eapply eventually_trans.
        { apply (eventually_carry_inv
                   (fun gs => forall n', In n' (forward f mu) -> forwarded_mod gs n' mu)
                   ltac:(intros gs T0 gs' Hs Hinv n' Hn'; exact (forwarded_mod_run gs T0 gs' n' mu Hs (Hinv n' Hn')))
                   _ gsM tM Hfwd_mu Hrec1). }
        intros [gsF tF] ((((_ & _) & Hfwd_outs) & (T2 & HT2 & Hall2 & Hperm2 & HdomX))
                         & Hfwd_mu_F).
        apply eventually_done. split.
        + split; [exact HdomX|]. exists T2. split; [exact HT2 | split; [exact Hall2 | exact Hperm2]].
        + intros mu0 n' Hin0 Hn'. cbn in Hin0. destruct Hin0 as [-> | Hin0'].
          * apply Hfwd_mu_F. exact Hn'.
          * apply Hfwd_outs; assumption.
    Qed.
    Lemma drive_node_must_equiv :
      Forall2_map node_good p initial_ns ->
      forall (np : node_prog) (n : node_id) (o : message),
        map.get p n = Some np ->
        output_visible n o = true ->
        forall (s : node_state * list IO_event),
          eventually (will_step (node_step np) well_formed)
                     (fun '(_, t') => exists o', equiv o' o /\ In o' (outputs_of t')) s ->
          forall gs t,
            reach_allow gs t ->
            (exists tr, map.get gs.(g_nodes) n = Some (fst s, tr) /\
                        Permutation (inputs_of (snd s)) (inputs_of tr)) ->
            ((exists o', equiv o' o /\ In o' (outputs_of (snd s))) ->
             exists go, equiv_g go (o, n) /\ In go (outputs_of t)) ->
            eventually (will_step gstep well_formed_graph_inputs)
                       (fun '(_, t') => exists go, equiv_g go (o, n) /\ In go (outputs_of t'))
                       (gs, t).
    Proof.
      intros Hgood np n o Hp Hvis s Hwill.
      assert (Hio_snoc_g : forall (l : list gevent) glbl (o0 : list (message * node_id)),
                inputs_of (l ++ [O_event glbl o0]) = inputs_of l)
        by (intros ll gg oo; rewrite inputs_of_app; cbn [inputs_of flat_map app];
            rewrite ?app_nil_r; reflexivity).
      assert (Hio_snoc_n : forall (l : list IO_event) glbl (o0 : list message),
                inputs_of (l ++ [O_event glbl o0]) = inputs_of l)
        by (intros ll gg oo; rewrite inputs_of_app; cbn [inputs_of flat_map app];
            rewrite ?app_nil_r; reflexivity).
      induction Hwill as [[ns_curr trace_curr] HP|
                          [ns_curr trace_curr] midset Hcan Hmid IH];
        intros gs t Hreach Hg Hout_proj.
      - apply eventually_done. cbn. apply Hout_proj. cbn in HP. exact HP.
      - destruct Hreach as (T0 & HT0 & HallT0 & HpermT0).
        destruct Hg as (tr & Hg & Hpermtr). cbn [fst snd] in Hg, Hpermtr.
        destruct Hcan as [node_lbl Hcan].
        apply eventually_step_cps. exists (run n node_lbl).
        intros gs_demon t_demon Hstar_demon Hallow_g.
        destruct (node_drive_delta _ _ _ Hstar_demon n np ns_curr tr Hp Hg)
          as (ns_d & tau_d & Hg_d & Htau_d & Hpres_d).
        pose proof (Hcan ns_d tau_d Htau_d) as Hcan'.
        assert (HreachD : star gstep initial_graph_state (T0 ++ t_demon) gs_demon)
          by (eapply star_app; eassumption).
        assert (HallowD : allowed well_formed_graph_inputs (inputs_of (T0 ++ t_demon))).
        { eapply allowed_perm; [| exact Hallow_g].
          rewrite !inputs_of_app. eapply perm_trans; [apply Permutation_app_comm|].
          apply Permutation_app_tail. symmetry. exact HpermT0. }
        assert (HpermD : Permutation (inputs_of (T0 ++ t_demon)) (inputs_of (t_demon ++ t))).
        { rewrite !inputs_of_app. eapply perm_trans;
            [apply Permutation_app_tail; exact HpermT0 | apply Permutation_app_comm]. }
        assert (Hpermtr_d : Permutation (inputs_of (tau_d ++ trace_curr)) (inputs_of (tr ++ tau_d))).
        { rewrite !inputs_of_app. eapply perm_trans; [apply Permutation_app_comm|].
          apply Permutation_app_tail. exact Hpermtr. }
        assert (Hallow_n : allowed well_formed (inputs_of (tau_d ++ trace_curr))).
        { eapply allowed_perm;
            [ symmetry; exact Hpermtr_d
            | apply (node_inputs_allowed Hgood (T0 ++ t_demon) gs_demon HreachD HallowD
                       n np ns_d (tr ++ tau_d) Hp Hg_d)]. }
        specialize (Hcan' Hallow_n).
        assert (Hproj_d : (exists o', equiv o' o /\ In o' (outputs_of (tau_d ++ trace_curr))) ->
                  exists go, equiv_g go (o, n) /\ In go (outputs_of (t_demon ++ t))).
        { intros (o' & Heqo' & Hout_sd). rewrite outputs_of_app in Hout_sd.
          apply in_app_or in Hout_sd as [Ho_taud | Ho_curr].
          - exists (o', n). split; [split; [reflexivity | exact Heqo']|].
            apply outputs_of_in_app. left.
            apply (Hpres_d o' (eq_trans (output_visible_equiv n o' o Heqo') Hvis) Ho_taud).
          - destruct (Hout_proj (ex_intro _ o' (conj Heqo' Ho_curr))) as (go & Hgo & Hingo).
            exists go. split; [exact Hgo|]. apply outputs_of_in_app. right. exact Hingo. }
        destruct Hcan' as [Hmid_left | (s'' & outs & Hns_step & Hmidset_at)].
        { left.
          apply (IH (ns_d, tau_d ++ trace_curr) Hmid_left gs_demon (t_demon ++ t)).
          - exists (T0 ++ t_demon). split; [exact HreachD|]. split; [exact HallowD | exact HpermD].
          - exists (tr ++ tau_d). split; [exact Hg_d | exact Hpermtr_d].
          - exact Hproj_d. }
        right.
        set (gs_next :=
               {| g_nodes := map.put gs_demon.(g_nodes) n (s'', (tr ++ tau_d) ++ [O_event node_lbl outs]);
                  g_messages :=
                    gs_demon.(g_messages) ++
                    flat_map (fun m0 => map (fun n' => (n', m0))
                                            (forward n m0)) outs |}).
        exists gs_next, (map (fun m => (m, n)) (filter (output_visible n) outs)).
        split.
        { eapply gstep_run; [exact Hp | exact Hg_d | exact Hns_step]. }
        assert (Hstep_next : gstep gs_demon
                  (O_event (run n node_lbl) (map (fun m => (m, n)) (filter (output_visible n) outs)))
                  gs_next)
          by (eapply gstep_run; [exact Hp | exact Hg_d | exact Hns_step]).
        apply (IH (s'', O_event node_lbl outs :: tau_d ++ trace_curr) Hmidset_at gs_next
                  (O_event (run n node_lbl) (map (fun m => (m, n)) (filter (output_visible n) outs))
                     :: t_demon ++ t)).
        + exists ((T0 ++ t_demon) ++
                  [O_event (run n node_lbl) (map (fun m => (m, n)) (filter (output_visible n) outs))]).
          split; [eapply star_app; [exact HreachD | econstructor; [exact Hstep_next | constructor]]|].
          split.
          * eapply allowed_perm; [| exact HallowD].
            rewrite Hio_snoc_g. apply Permutation_refl.
          * rewrite Hio_snoc_g. exact HpermD.
        + exists ((tr ++ tau_d) ++ [O_event node_lbl outs]). split; [cbn [snd]; apply map.get_put_same|].
          cbn [snd]. rewrite Hio_snoc_n. exact Hpermtr_d.
        + intros (o' & Heqo' & Hout_sd). cbn [snd] in Hout_sd.
          apply in_app_or in Hout_sd as [Hhead | Hrest].
          * exists (o', n). split; [split; [reflexivity | exact Heqo']|].
            apply in_or_app. left.
            apply In_tag. apply filter_In.
            split; [exact Hhead | rewrite (output_visible_equiv n o' o Heqo'); exact Hvis].
          * destruct (Hproj_d (ex_intro _ o' (conj Heqo' Hrest))) as (go & Hgo & Hingo).
            exists go. split; [exact Hgo|].
            apply in_or_app. right. exact Hingo.
    Qed.
    Lemma force_dominator_equiv :
      Forall2_map node_good p initial_ns ->
      forall on np_o, map.get p on = Some np_o ->
      forall gs_pre TC gsC, star gstep gsC TC gs_pre ->
      inputs_of TC = [] ->
      forall ns_o t_o, map.get gs_pre.(g_nodes) on = Some (ns_o, t_o) ->
      forall TC0, star gstep initial_graph_state TC0 gsC -> allowed well_formed_graph_inputs (inputs_of TC0) ->
      forall TX gsX, star gstep initial_graph_state TX gsX ->
      core_dom_mod gsC gsX ->
      forall t, allowed well_formed_graph_inputs (inputs_of t) ->
      Permutation (inputs_of TX) (inputs_of t) ->
      eventually (will_step gstep well_formed_graph_inputs)
        (fun '(gs', t') =>
           (exists nsS tS, map.get gs'.(g_nodes) on = Some (nsS, tS) /\
              incl_mod equiv (inputs_of t_o) (inputs_of tS)) /\
           (exists T', star gstep initial_graph_state T' gs' /\
                       allowed well_formed_graph_inputs (inputs_of T') /\
                       Permutation (inputs_of T') (inputs_of t')))
        (gsX, t).
    Proof.
      intros Hgood on np_o Hp_o gs_pre TC gsC Hstar.
      assert (Hio_snoc_g : forall (l : list gevent) glbl (o0 : list (message * node_id)),
                inputs_of (l ++ [O_event glbl o0]) = inputs_of l)
        by (intros ll gg oo; rewrite inputs_of_app; cbn [inputs_of flat_map app];
            rewrite ?app_nil_r; reflexivity).
      assert (Hio_snoc_n : forall (l : list IO_event) glbl (o0 : list message),
                inputs_of (l ++ [O_event glbl o0]) = inputs_of l)
        by (intros ll gg oo; rewrite inputs_of_app; cbn [inputs_of flat_map app];
            rewrite ?app_nil_r; reflexivity).
      induction Hstar as [gC | gC e gC1 TC' gpre Hstep Hstar' IH];
        intros Hinp ns_o t_o Hg_o TC0 HC0 HallC0 TX gsX HTX Hdom t Hall_t Hperm.
      - (* gsX already dominates gs_pre = gC *)
        apply eventually_done.
        destruct (proj1 Hdom on np_o ns_o t_o Hp_o Hg_o) as (nsS & tS & HgS & Hincl).
        split.
        + exists nsS, tS. split; [exact HgS | exact Hincl].
        + exists TX. split; [exact HTX | split; [| exact Hperm]].
          eapply allowed_perm; [symmetry; exact Hperm | exact Hall_t].
      - cbn in Hinp. inv_gstep Hstep; subst.
        + cbn in Hinp. discriminate.
        + (* gstep_run ni : force ni to re-emit outsi, dominate gC1 *)
          assert (HallX : allowed well_formed_graph_inputs (inputs_of TX)).
          { eapply allowed_perm; [symmetry; exact Hperm | exact Hall_t]. }
          destruct (proj1 Hdom ni npi nsi ti Hpi Hgi) as (nsXi & tXi & HgXi & Hincli).
          assert (Hcan : forall mu, In mu outsi ->
                    might_output_equiv (node_step npi) equiv nsXi tXi mu).
          { intros mu Hmu.
            apply (node_cap_transfer_equiv Hgood ni npi Hpi TC0 gC nsi ti HC0 HallC0 Hgi
                     TX gsX nsXi tXi HTX HallX HgXi Hincli mu).
            exists [O_event lbli outsi], nsi'. split; [econstructor; [exact Hsi | constructor]|].
            split; [reflexivity|]. apply outputs_of_in_app. left. apply in_or_app. left. exact Hmu. }
          eapply eventually_trans.
          { apply (eventually_carry_dom gC Hgood _ gsX t TX HTX HallX Hperm Hdom
                     (force_emit_list_equiv Hgood outsi ni npi Hpi TX gsX HTX HallX
                        nsXi tXi HgXi Hcan t Hperm)). }
          intros [gsM tM] (((_ & _) & Hfwds) & (TM & HTM & HallM & HpermM & HdomM)).
          refine (IH Hinp ns_o t_o Hg_o
                    (TC0 ++ [O_event (run ni lbli) (map (fun m => (m, ni)) (filter (output_visible ni) outsi))])
                    (star_app _ _ _ _ _ _ HC0 (star_step _ _ _ _ _ _
                       (gstep_run p node_step gC ni npi nsi ti nsi' lbli outsi Hpi Hgi Hsi)
                       (star_refl _ _)))
                    ltac:(rewrite Hio_snoc_g; exact HallC0)
                    TM gsM HTM _ tM ltac:(eapply allowed_perm; [exact HpermM | exact HallM]) HpermM).
          (* core_dom_mod gC1 gsM, where gC1 is the run-successor of gC *)
          split.
          * intros nn npn nsn tn Hpn Hgn. cbn [g_nodes] in Hgn.
            destruct (Nat.eq_dec nn ni) as [->|Hne].
            -- rewrite map.get_put_same in Hgn. injection Hgn as <- <-.
               destruct (proj1 HdomM ni npi nsi ti Hpi Hgi) as (nsB & tB & HgB & HinclB).
               exists nsB, tB. split; [exact HgB|].
               rewrite Hio_snoc_n. exact HinclB.
            -- rewrite map.get_put_diff in Hgn by auto. apply (proj1 HdomM nn npn nsn tn Hpn Hgn).
          * intros nn mm Hin. cbn [g_messages] in Hin. apply in_app_or in Hin as [Hin | Hin].
            -- apply (proj2 HdomM nn mm Hin).
            -- apply in_flat_map in Hin as (mu & Hmu & Hin).
               apply in_map_iff in Hin as (n'' & Heq & Hn''). injection Heq as <- <-.
               destruct (Hfwds mu n'' Hmu Hn'') as [Hq | Hr]; [left | right; exact Hr].
               destruct Hq as (m' & Hin' & Hmm'). exists m'. split; [exact Hin' | exact Hmm'].
        + (* gstep_receive ni mi : deliver a relative of mi to ni, dominate gC1 *)
          assert (HallX : allowed well_formed_graph_inputs (inputs_of TX)).
          { eapply allowed_perm; [symmetry; exact Hperm | exact Hall_t]. }
          destruct (proj1 Hdom ni npi nsi ti Hpi Hgi) as (nsXi & tXi & HgXi & _).
          destruct (reachable_state_initial _ _ HTX ni _ HgXi) as (ns0i & Hns0i).
          assert (Hcm : (exists m', In (ni, m') gsX.(g_messages) /\ equiv mi m') \/
                        node_received_mod gsX ni mi).
          { apply (proj2 Hdom). rewrite Hmsg. apply in_or_app. right. left. reflexivity. }
          (* deliver: in either case ni ends up having received a relative of mi *)
          assert (Hdeliv : eventually (will_step gstep well_formed_graph_inputs)
                    (fun '(gs', _) => node_received_mod gs' ni mi) (gsX, t)).
          { destruct Hcm as [(m' & Hq & Hmm') | Hr].
            - eapply eventually_weaken;
                [apply (force_deliver_equiv TX gsX HTX ni m' npi ns0i Hpi Hns0i
                          (or_introl Hq) t)|].
              intros [gs' t'] (ns & tt & Hg & Hin). exists ns, tt, m'.
              split; [exact Hg | split; [exact Hin | exact Hmm']].
            - apply eventually_done. exact Hr. }
          eapply eventually_trans.
          { apply (eventually_carry_dom gC Hgood _ gsX t TX HTX HallX Hperm Hdom Hdeliv). }
          intros [gsM tM] (Hrcv & (TM & HTM & HallM & HpermM & HdomM)).
          refine (IH Hinp ns_o t_o Hg_o (TC0 ++ [O_event (receive ni mi) []])
                    (star_app _ _ _ _ _ _ HC0 (star_step _ _ _ _ _ _
                       (gstep_receive p node_step gC ni npi nsi ti nsi' mi msa msb Hpi Hgi Hsi Hmsg)
                       (star_refl _ _)))
                    ltac:(rewrite Hio_snoc_g; exact HallC0)
                    TM gsM HTM _ tM ltac:(eapply allowed_perm; [exact HpermM | exact HallM]) HpermM).
          split.
          * intros nn npn nsn tn Hpn Hgn. cbn [g_nodes] in Hgn.
            destruct (Nat.eq_dec nn ni) as [->|Hne].
            -- rewrite map.get_put_same in Hgn. injection Hgn as <- <-.
               destruct (proj1 HdomM ni npi nsi ti Hpi Hgi) as (nsB & tB & HgB & HinclB).
               exists nsB, tB. split; [exact HgB|].
               destruct Hrcv as (nsR & tR & mu' & HgR & Hin_mu' & Hmi_mu').
               assert (tR = tB) by congruence. subst tR.
               intros a Ha. rewrite inputs_of_app in Ha. apply in_app_or in Ha as [Ha | Ha].
               { apply HinclB. exact Ha. }
               cbn in Ha. destruct Ha as [Heq | []]. subst a.
               exists mu'. split; [exact Hin_mu' | exact Hmi_mu'].
            -- rewrite map.get_put_diff in Hgn by auto. apply (proj1 HdomM nn npn nsn tn Hpn Hgn).
          * intros nn mm Hin. cbn [g_messages] in Hin.
            apply (proj2 HdomM nn mm). rewrite Hmsg.
            apply in_app_iff. apply in_app_or in Hin as [H|H]; [left; exact H | right; right; exact H].
    Qed.

    (* A graph state reachable from the initial one. *)
    Definition reachable (g : graph_state) : Prop :=
      exists Tg, star gstep initial_graph_state Tg g.

    Lemma eventually_carry_inv2_wf :
      forall (R : graph_state -> list gevent -> Prop),
        (forall gs tt t_d s_d, R gs tt ->
           star gstep gs t_d s_d -> R s_d (t_d ++ tt)) ->
        (forall gs tt glbl outs gs', R gs tt ->
           gstep gs (O_event glbl outs) gs' -> R gs' (O_event glbl outs :: tt)) ->
        forall (P : graph_state * list gevent -> Prop) gs tt,
          R gs tt ->
          eventually (will_step gstep well_formed_graph_inputs) P (gs, tt) ->
          eventually (will_step gstep well_formed_graph_inputs)
            (fun '(gs', t') => P (gs', t') /\ R gs' t') (gs, tt).
    Proof.
      intros R Hstarp Hostep P gs tt HR Hev.
      remember (gs, tt) as st eqn:Est. revert gs tt HR Est.
      induction Hev as [[s' t'] HP | [s' t'] midset Hcan Hmid IH];
        intros gs tt HR [= -> ->].
      - apply eventually_done. split; [exact HP | exact HR].
      - destruct Hcan as [glbl Hcan].
        apply eventually_step_cps. exists glbl.
        intros gs_d t_d Hstar_d Hallow.
        specialize (Hcan gs_d t_d Hstar_d Hallow).
        destruct Hcan as [Hmid_left | (s'' & outs & Hstep & Hmidset)].
        + left. apply (IH (gs_d, t_d ++ tt) Hmid_left gs_d (t_d ++ tt)
                          (Hstarp _ _ _ _ HR Hstar_d) eq_refl).
        + right. exists s'', outs. split; [exact Hstep|].
          apply (IH _ Hmidset s'' (O_event glbl outs :: t_d ++ tt)); [|reflexivity].
          apply (Hostep _ _ _ _ _ (Hstarp _ _ _ _ HR Hstar_d) Hstep).
    Qed.


    Lemma graph_can_implies_will_equiv :
      Forall2_map node_good p initial_ns ->
      can_implies_will_equiv (graph_step p node_step) equiv_g well_formed_graph_inputs
                             initial_graph_state.
    Proof.
      intros Hgood t gs o Hstar Hall Hcan.
      destruct o as (omsg, on).
      destruct Hcan as (T_a & s_f & Hstar_a & Hinp_a & Hout).
      apply outputs_of_in_app in Hout as [Hout_T | Hout_t].
      2: { apply eventually_done. exists (omsg, on).
           split; [split; [reflexivity | reflexivity] | exact Hout_t]. }
      destruct (find_producing_step _ _ _ Hstar_a Hinp_a omsg on Hout_T)
        as (T_pre & T_post & np_o & ns_o & ns_o' & t_o & outs_o & lbl_o
            & gs_pre & gs_post & Heq_T & Hstar_pre_a & Hstep_prod
            & Hstar_post_a & Hinp_pre & Hp_o & Hg_o & Hns_o & Hino_o & Hvis_o).
      pose proof (star_app _ _ _ _ _ _ Hstar Hstar_pre_a) as Hstar_to_pre.
      assert (Harmed : might_output (node_step np_o) ns_o t_o omsg).
      { exists [O_event lbl_o outs_o], ns_o'. split; [econstructor; [exact Hns_o | constructor]|].
        split; [reflexivity|]. apply outputs_of_in_app. left.
        apply in_or_app. left. exact Hino_o. }
      destruct (reachable_state_initial _ _ Hstar_to_pre on _ Hg_o) as (ns0o & Hns0o).
      (* Carry the modulo output-reflection through the drive. *)
      set (R := fun (g : graph_state) (tt : list gevent) =>
                  reachable g /\
                  (forall ns tn, map.get g.(g_nodes) on = Some (ns, tn) ->
                     (exists o', equiv o' omsg /\ In o' (outputs_of tn)) ->
                     exists go, equiv_g go (omsg, on) /\ In go (outputs_of tt))).
      assert (HR_init : R gs t).
      { split; [exists t; exact Hstar|].
        intros ns tn Hg (o' & Heqo' & Hotn).
        destruct (node_run _ _ Hstar on np_o ns0o ns tn Hp_o Hns0o Hg) as (_ & Hpres).
        exists (o', on). split; [split; [reflexivity | exact Heqo']|].
        apply (Hpres o' (eq_trans (output_visible_equiv on _ _ Heqo') Hvis_o) Hotn). }
      assert (Hstarp : forall g tt t_d s_d, R g tt ->
                star gstep g t_d s_d -> R s_d (t_d ++ tt)).
      { intros g tt t_d s_d [(Tg & HTg) Href] Hs. split.
        - exists (Tg ++ t_d). eapply star_app; eassumption.
        - intros ns tn Hgsd (o' & Heqo' & Hotn).
          destruct (project_node_gen _ _ HTg on np_o ns0o Hp_o Hns0o)
            as (taug & nsg & _ & Hgg & _).
          destruct (node_drive_delta _ _ _ Hs on np_o nsg taug Hp_o Hgg)
            as (nsd & td & Hgd & _ & Hpresd).
          assert (tn = taug ++ td) by congruence. subst tn.
          apply outputs_of_in_app in Hotn as [Ho | Ho].
          + destruct (Href nsg taug Hgg (ex_intro _ o' (conj Heqo' Ho)))
              as (go & Hgo & Hingo).
            exists go. split; [exact Hgo|]. apply outputs_of_in_app. right. exact Hingo.
          + pose proof (Hpresd o' (eq_trans (output_visible_equiv on _ _ Heqo') Hvis_o) Ho)
              as Hgtag.
            exists (o', on). split; [split; [reflexivity | exact Heqo']|].
            apply outputs_of_in_app. left. exact Hgtag. }
      assert (Hostep : forall g tt glbl outs g', R g tt ->
                gstep g (O_event glbl outs) g' -> R g' (O_event glbl outs :: tt)).
      { intros g tt glbl outs g' HR Hstep'.
        apply (Hstarp g tt [O_event glbl outs] g' HR).
        econstructor; [exact Hstep' | constructor]. }
      eapply eventually_trans.
      { apply (eventually_carry_inv2_wf R Hstarp Hostep _ gs t HR_init
                 (force_dominator_equiv Hgood on np_o Hp_o gs_pre T_pre gs Hstar_pre_a Hinp_pre
                    ns_o t_o Hg_o
                    t Hstar Hall t gs Hstar (core_dom_mod_refl gs) t Hall (Permutation_refl _))). }
      intros [gsStar tStar] ((Hprod & (TStar & HTStar & HallStar & HpermStar)) & HRStar).
      destruct Hprod as (nsS & tS & HgS & Hincl).
      assert (HcanS : might_output_equiv (node_step np_o) equiv nsS tS omsg).
      { apply (node_cap_transfer_equiv Hgood on np_o Hp_o
                 _ gs_pre ns_o t_o Hstar_to_pre
                 ltac:(rewrite inputs_of_app, Hinp_pre, app_nil_r; exact Hall) Hg_o
                 _ gsStar nsS tS HTStar HallStar HgS
                 Hincl omsg Harmed). }
      destruct HcanS as (o' & Heqo' & HcanS').
      pose proof (node_will_equiv Hgood on np_o Hp_o TStar gsStar nsS tS HTStar HallStar HgS
                    o' HcanS') as Hwillo.
      apply (drive_node_must_equiv Hgood np_o on omsg Hp_o Hvis_o (nsS, tS)
               (will_output_equiv_weaken _ _ _ _ _ Heqo' Hwillo)
               gsStar tStar
               (ex_intro _ TStar (conj HTStar (conj HallStar HpermStar)))
               (ex_intro _ tS (conj HgS (Permutation_refl _)))
               (proj2 HRStar nsS tS HgS)).
    Qed.
  End graph.

End __.

Definition translate_event {L M M'} (t : M' -> M) (ev : IO_event L M') : IO_event L M :=
  match ev with
  | I_event m' => I_event (t m')
  | O_event l ms' => O_event l (map t ms')
  end.

Definition translate_step {NS L M M'} (t : M' -> M)
  (step : NS -> IO_event L M -> NS -> Prop)
  : NS -> IO_event L M' -> NS -> Prop :=
  fun ns ev ns' => step ns (translate_event t ev) ns'.
