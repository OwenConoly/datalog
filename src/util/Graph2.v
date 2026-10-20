From coqutil Require Import Semantics.OmniSmallstepCombinators.
From coqutil Require Import Eqb Tactics Tactics.fwd.
From Stdlib Require Import List Permutation Relations.
From Datalog Require Import Smallstep Fin Function List Relations Eqb Tactics.
From Datalog Require Import MessagelessSmallstep.
Import ListNotations.

Section __.
  Context (message label : Type) (num_nodes : nat).
  Abbreviation node := (fin num_nodes).
  Context (forward : node -> node -> message -> bool) (node_state : Type).
  Context (node_step : node -> node_state -> IO_event label message -> node_state -> Prop).
  Abbreviation nevent := (IO_event label message).
  Context (nodes_input_total : forall n, input_total (node_step n)).

  Context (npred_transf : node -> list message -> (list message -> Prop) -> Prop).
  Context (init : node -> node_state).
  Context (safe : node -> list message -> Prop).
  Context (safe_mono : forall n, multiset_monotone_dec (safe n)).
  Context (safe_nothing : forall n, safe n []).

  Definition inputs_of_outputs (outputs : node -> list message) destn :=
    flat_map (fun n => filter (forward n destn) (outputs n)) (fin.all _).

  Definition safe_inputs (n : node) (inps : list message) :=
    exists ojs,
      (forall n', safe n' (ojs n')) /\
        Permutation inps (inputs_of_outputs ojs n).

  Context (safe_preserved :
            forall n t st,
              star (node_step n) (init n) t st ->
              safe_inputs n (flat_map inputs_of t) ->
              safe n (flat_map outputs_of t)).

  Context (npred_transf_sound :
            forall n t P st,
              npred_transf n (flat_map inputs_of t) P ->
              star (node_step n) (init n) t st ->
              eventually (Smallstep.will_step (node_step n) (safe_inputs n)) (fun '(_, t') => P (flat_map outputs_of t')) (st, t)).

  Context (relevant : node -> (list message -> Prop) -> Prop).

  Context (npred_transf_complete :
            forall n t st P,
            star (node_step n) (init n) t st ->
            safe_inputs n (flat_map inputs_of t) ->
            relevant n P ->
            P (flat_map outputs_of t) ->
            npred_transf n (flat_map inputs_of t) P).

  Definition suffices loc (Pjs : node -> list message -> Prop) P :=
    forall ojs,
      (forall n', Pjs n' (ojs n') /\ safe n' (ojs n')) ->
      npred_transf loc (inputs_of_outputs ojs loc) P.

  Context (relevant_preserved :
            forall n ojs P,
              relevant n P ->
              (forall n', safe n' (ojs n')) ->
              npred_transf n (inputs_of_outputs ojs n) P ->
              exists (Pjs : node -> (list message -> Prop)),
                (forall n', relevant n' (Pjs n') /\ Pjs n' (ojs n')) /\
                  suffices n Pjs P).

  Context (npred_transf_mono_inc :
            forall n inps inps' P,
              npred_transf n inps P ->
              safe_inputs n inps' ->
              submultiset inps inps' ->
              npred_transf n inps' P).

  Record graph_node_state :=
    { gns_node_state : node_state;
      gns_trace : list nevent;
      gns_queue : list message }.

  Definition enqueue inps gns :=
    {| gns_node_state := gns.(gns_node_state);
      gns_trace := gns.(gns_trace);
      gns_queue := inps ++ gns.(gns_queue) |}.

  Variant graph_label :=
    | receive (_ : node) (_ : message)
    | run (_ : node) (_ : label).

  Definition graph_state := node -> graph_node_state.

  Definition forward_to (keep : node -> message -> bool) (msgs : list message) (gs : graph_state) : graph_state :=
    fun n => enqueue (filter (keep n) msgs) (gs n).

  Definition gns_run n (ns : graph_node_state) (e : nevent) (ns' : graph_node_state) :=
    exists st',
      node_step n ns.(gns_node_state) e st' /\
        ns' = {| gns_node_state := st';
                gns_trace := e :: ns.(gns_trace);
                gns_queue := ns.(gns_queue) |}.

  Definition gns_receive n (ns : graph_node_state) m ns' :=
    exists ms1 ms2,
      ns.(gns_queue) = ms1 ++ m :: ms2 /\
        gns_run n {| gns_node_state := ns.(gns_node_state);
                    gns_trace := ns.(gns_trace);
                    gns_queue := ms1 ++ ms2 |} (I_event m) ns'.

  Variant graph_step : graph_state -> graph_label -> graph_state -> Prop :=
    | gstep_run n gs ns' lbl outs :
      gns_run n (gs n) (O_event lbl outs) ns' ->
      graph_step gs (run n lbl) (forward_to (forward n) outs (fun_put gs n ns'))
    | gstep_receive gs n m ns' :
      gns_receive n (gs n) m ns' ->
      graph_step gs (receive n m) (fun_put gs n ns').

  Definition outputs_at (gs : graph_state) n := flat_map outputs_of (gs n).(gns_trace).
  Definition inputs_at (gs : graph_state) n := flat_map inputs_of (gs n).(gns_trace).

  Inductive graph_sat : node -> (list message -> Prop) -> Prop :=
  | step_sat loc P Pjs :
    (forall n', graph_sat n' (Pjs n')) ->
    suffices loc Pjs P ->
    graph_sat loc P
  | top_sat loc :
    graph_sat loc (fun _ => True).

  Definition init_graph := fun n =>
    {| gns_node_state := init n;
      gns_trace := [];
      gns_queue := [] |}.

  Lemma messages_conserved_step gs lbl gs' dst :
    (forall dst', Permutation (inputs_of_outputs (outputs_at gs) dst') (inputs_at gs dst' ++ (gs dst').(gns_queue))) ->
    graph_step gs lbl gs' ->
    Permutation (inputs_of_outputs (outputs_at gs') dst) (inputs_at gs' dst ++ (gs' dst).(gns_queue)).
  Proof.
    intros Hcons Hstep. invert Hstep.
    - cbv [gns_run] in *. fwd.
      transitivity (filter (forward n dst) outs ++ inputs_of_outputs (outputs_at gs) dst).
      + apply flat_map_app_at_perm with (a := n).
        * apply fin.all_NoDup.
        * apply fin.all_Full.
        * intros a' ?. cbv [outputs_at forward_to enqueue fun_put]. destr (eqb a' n); cbn; congruence.
        * cbv [outputs_at forward_to enqueue fun_put]. destr (eqb n n); [|congruence].
          cbn. apply filter_app.
      + cbv [inputs_at forward_to enqueue fun_put]. destr (eqb dst n); cbn;
          symmetry; apply perm_ins; symmetry; apply Hcons.
    - cbv [gns_receive gns_run] in *. fwd.
      transitivity (inputs_of_outputs (outputs_at gs) dst).
      + apply Permutation_refl'. apply flat_map_ext. intros k.
        cbv [outputs_at fun_put]. destr (eqb k n); reflexivity.
      + cbv [inputs_at fun_put]. destr (eqb dst n); cbn.
        * rewrite Hcons, Hp0. apply perm_recv.
        * apply Hcons.
  Qed.

  Lemma messages_conserved gs dst :
    (any_step graph_step)^* init_graph gs ->
    Permutation (inputs_of_outputs (outputs_at gs) dst) (inputs_at gs dst ++ (gs dst).(gns_queue)).
  Proof.
    intros H. apply clos_rt1n_rt, clos_rt_rtn1 in H. revert dst. induction H; intros dst.
    - cbv [inputs_of_outputs outputs_at inputs_at init_graph]. cbn.
      rewrite flat_map_all_nil by auto. reflexivity.
    - destruct H as [lbl H]. eapply messages_conserved_step; eassumption.
  Qed.

  Lemma pool_submultiset_step gs lbl gs' dst :
    graph_step gs lbl gs' ->
    submultiset (inputs_at gs dst) (inputs_at gs' dst) /\
      submultiset (inputs_at gs dst ++ (gs dst).(gns_queue)) (inputs_at gs' dst ++ (gs' dst).(gns_queue)).
  Proof.
    intros Hstep. invert Hstep.
    - cbv [gns_run] in *. fwd. cbv [inputs_at forward_to enqueue fun_put]. destr (eqb dst n); cbn;
        split; auto using submultiset_refl, submultiset_app_mid.
    - cbv [gns_receive gns_run] in *. fwd. cbv [inputs_at fun_put].
      destr (eqb dst n); cbn; split; auto using submultiset_refl, submultiset_cons.
      rewrite Hp0. apply submultiset_perm. apply perm_recv.
  Qed.

  Lemma pool_submultiset gs gs' dst :
    (any_step graph_step)^* gs gs' ->
    submultiset (inputs_at gs dst) (inputs_at gs' dst) /\
      submultiset (inputs_at gs dst ++ (gs dst).(gns_queue)) (inputs_at gs' dst ++ (gs' dst).(gns_queue)).
  Proof.
    induction 1.
    - split; apply submultiset_refl.
    - destruct H as [lbl H]. apply pool_submultiset_step with (dst := dst) in H. fwd.
      split; eapply submultiset_trans; eassumption.
  Qed.

  Lemma eventually_received gs dst base owed :
    submultiset base (inputs_at gs dst) ->
    submultiset (base ++ owed) (inputs_at gs dst ++ (gs dst).(gns_queue)) ->
    eventually (will_step graph_step) (fun gs' => submultiset (base ++ owed) (inputs_at gs' dst)) gs.
  Proof.
    revert base gs. induction owed as [|m owed IH]; intros base gs Hbase Howed.
    - apply eventually_done. rewrite app_nil_r. assumption.
    - apply eventually_step with
        (midset := fun gs' => submultiset (base ++ [m]) (inputs_at gs' dst) /\
                              submultiset (base ++ m :: owed) (inputs_at gs' dst ++ (gs' dst).(gns_queue))).
      + exists (receive dst m). intros gs' Hreach.
        apply pool_submultiset with (dst := dst) in Hreach. destruct Hreach as [HR HRQ].
        apply (submultiset_trans _ _ _ Hbase) in HR.
        apply (submultiset_trans _ _ _ Howed) in HRQ.
        destruct (submultiset_snoc_or_in _ _ _ _ _ HR HRQ) as [Hdone|Hq].
        * left. split; assumption.
        * right. apply in_split in Hq. destruct Hq as (ms1 & ms2 & Hq).
          destruct (nodes_input_total dst (gs' dst).(gns_node_state) m) as [st' Hst'].
          eexists. split.
          -- constructor. exists ms1, ms2. split; [exact Hq|]. eexists. split; [exact Hst'|reflexivity].
          -- cbv [inputs_at fun_put]. destr (eqb dst dst); [|congruence]. cbn. split.
             ++ eapply submultiset_perm_l; [apply Permutation_cons_append|].
                apply submultiset_cons_mono. assumption.
             ++ eapply submultiset_perm_r; [apply perm_recv|]. rewrite <- Hq. assumption.
      + intros gs' [].
        replace (base ++ m :: owed) with ((base ++ [m]) ++ owed) in * by (rewrite <- app_assoc; reflexivity).
        auto.
  Qed.

  Lemma drain_queues gs dst :
    eventually (will_step graph_step)
      (fun gs' =>
         submultiset
           (inputs_at gs dst ++ (gs dst).(gns_queue))
           (inputs_at gs' dst))
      gs.
  Proof. apply eventually_received; apply submultiset_refl. Qed.

  Lemma sent_msgs_eventually_received gs dst :
    (any_step graph_step)^* init_graph gs ->
    eventually (will_step graph_step) (fun gs' => submultiset (inputs_of_outputs (outputs_at gs) dst) (inputs_at gs' dst)) gs.
  Proof.
    intros Hreach. eapply eventually_weaken; [apply drain_queues|].
    intros gs' H. eapply submultiset_perm_l; [|exact H].
    symmetry. apply messages_conserved. assumption.
  Qed.

  Lemma inputs_of_outputs_mono ojs ojs' dst :
    (forall n, submultiset (ojs n) (ojs' n)) ->
    submultiset (inputs_of_outputs ojs dst) (inputs_of_outputs ojs' dst).
  Proof. intros H. apply submultiset_flat_map. intros n. apply submultiset_filter, H. Qed.

  Lemma safe_inputs_mono n : multiset_monotone_dec (safe_inputs n).
  Proof.
    intros inps' inps (ojs & Hsafe & Hperm) Hsub.
    apply (submultiset_perm_r _ _ _ Hperm) in Hsub.
    apply submultiset_flat_map_split in Hsub; [ | apply fin.all_NoDup ].
    destruct Hsub as (g & Hg & Hgsub). exists g. split.
    - intros n'. eapply safe_mono; [ apply Hsafe | ].
      eapply submultiset_trans; [ apply Hgsub | apply filter_submultiset ].
    - rewrite Hg. apply Permutation_refl', flat_map_ext_in. intros n' _.
      symmetry. eapply filter_id_submultiset. apply Hgsub.
  Qed.

  Lemma node_steps_of_graph_steps gs gs' n :
    (any_step graph_step)^* gs gs' ->
    exists t, star (node_step n) (gs n).(gns_node_state) t (gs' n).(gns_node_state) /\
              (gs' n).(gns_trace) = t ++ (gs n).(gns_trace).
  Proof.
    intros H. apply clos_rt1n_rt, clos_rt_rtn1 in H. induction H.
    - exists []. split; [ apply star_refl | reflexivity ].
    - destruct IHclos_refl_trans_n1 as (t & Ht & Htr). destruct H as [lbl H]. invert H.
      + cbv [gns_run] in *. fwd. cbv [forward_to enqueue fun_put].
        destr (eqb n n0); cbn; [ | exists t; split; assumption ].
        eexists. split.
        * eauto using star_step.
        * cbn. congruence.
      + cbv [gns_receive gns_run] in *. fwd. cbv [fun_put].
        destr (eqb n n0); cbn; [ | exists t; split; assumption ].
        eexists. split.
        * eauto using star_step.
        * cbn. congruence.
  Qed.

  Lemma node_steps_of_graph_steps_init gs n :
    (any_step graph_step)^* init_graph gs ->
    star (node_step n) (init n) (gs n).(gns_trace) (gs n).(gns_node_state).
  Proof.
    intros H. apply node_steps_of_graph_steps with (n := n) in H. destruct H as (t & Ht & Htr).
    cbn in Htr. rewrite Htr, app_nil_r. exact Ht.
  Qed.

  Lemma graph_is_safe gs n :
    (any_step graph_step)^* init_graph gs ->
    safe n (outputs_at gs n).
  Proof.
    intros H. apply clos_rt1n_rt, clos_rt_rtn1 in H. revert n. induction H; intros n.
    - apply safe_nothing.
    - assert (Hy : (any_step graph_step)^* init_graph y) by (apply clos_rt_rt1n, clos_rtn1_rt; assumption).
      destruct H as [lbl H]. invert H.
      + cbv [gns_run] in *. fwd. cbv [outputs_at forward_to enqueue fun_put].
        destr (eqb n n0); [ | apply IHclos_refl_trans_n1 ].
        eapply safe_preserved; cbn.
        * eauto using star_step, node_steps_of_graph_steps_init.
        * eapply safe_inputs_mono.
          -- exists (outputs_at y). split; [ exact IHclos_refl_trans_n1 | reflexivity ].
          -- eapply submultiset_perm_r; [ | apply submultiset_app_r ].
             symmetry. apply messages_conserved. exact Hy.
      + cbv [gns_receive gns_run] in *. fwd. cbv [outputs_at fun_put].
        destr (eqb n n0); cbn; apply IHclos_refl_trans_n1.
  Qed.

  Lemma graph_inputs_safe gs n :
    (any_step graph_step)^* init_graph gs ->
    safe_inputs n (inputs_at gs n).
  Proof.
    intros H. eapply safe_inputs_mono.
    - exists (outputs_at gs). split; [ eauto using graph_is_safe | reflexivity ].
    - eapply submultiset_perm_r; [ | apply submultiset_app_r ].
      symmetry. apply messages_conserved. assumption.
  Qed.

  Lemma graph_will_step_of_node_will_step gs n P :
    (any_step graph_step)^* init_graph gs ->
    Smallstep.will_step (node_step n) (safe_inputs n) ((gs n).(gns_node_state), (gs n).(gns_trace)) P ->
    will_step graph_step gs (fun gs' => P ((gs' n).(gns_node_state), (gs' n).(gns_trace))).
  Proof.
    intros Hreach (lbl & Hwill). exists (run n lbl). intros gs' Hgs'.
    destruct (node_steps_of_graph_steps _ _ n Hgs') as (t & Ht & Htr).
    destruct (Hwill _ _ Ht) as [HP | (s'' & outs & Hstep & HP)].
    - rewrite <- Htr. apply graph_inputs_safe. eapply crt1n_trans_compose; eassumption.
    - left. rewrite Htr. assumption.
    - right. eexists. split.
      + econstructor. exists s''. split; [ exact Hstep | reflexivity ].
      + cbv [forward_to enqueue fun_put]. destr (eqb n n); [ | congruence ].
        cbn. rewrite Htr. assumption.
  Qed.

  Lemma graph_eventually_of_node_eventually gs n P :
    (any_step graph_step)^* init_graph gs ->
    eventually (Smallstep.will_step (node_step n) (safe_inputs n)) P
      ((gs n).(gns_node_state), (gs n).(gns_trace)) ->
    eventually (will_step graph_step) (fun gs' => P ((gs' n).(gns_node_state), (gs' n).(gns_trace))) gs.
  Proof.
    intros Hreach Hev. remember ((gs n).(gns_node_state), (gs n).(gns_trace)) as st eqn:E.
    revert gs Hreach E. induction Hev; intros gs Hreach E; subst.
    - apply eventually_done. assumption.
    - apply eventually_step with
        (midset := fun gs' => (any_step graph_step)^* init_graph gs' /\
                              midset ((gs' n).(gns_node_state), (gs' n).(gns_trace))).
      + apply will_step_reach. eapply will_step_impl.
        * apply graph_will_step_of_node_will_step; eassumption.
        * intros gs' ? ?. split; eauto using crt1n_trans_compose.
      + intros gs' []. eauto.
  Qed.

  Lemma step_sat_sound Pjs gs dst P :
    (any_step graph_step)^* init_graph gs ->
    (forall src, Pjs src (outputs_at gs src)) ->
    npred_transf dst (inputs_of_outputs (outputs_at gs) dst) P ->
    eventually (will_step graph_step) (fun gs' => P (outputs_at gs' dst)) gs.
  Proof.
    intros Hstep HPjs Htrans.
    eapply eventually_trans.
    { apply eventually_and_reach. apply sent_msgs_eventually_received with (dst := dst). assumption. }
    simpl. intros gs' Hgs'. fwd.
    eapply eventually_weaken.
    { apply eventually_and_reach. apply graph_eventually_of_node_eventually.
      - eauto using crt1n_trans_compose.
      - apply npred_transf_sound.
        2: { apply node_steps_of_graph_steps_init. eauto using crt1n_trans_compose. }
        eapply npred_transf_mono_inc.
        + eassumption.
        + apply graph_inputs_safe. eauto using crt1n_trans_compose.
        + assumption. }
    simpl. intros final Hfinal. fwd. assumption.
  Qed.

  Lemma outputs_at_forward_to keep msgs gs n :
    outputs_at (forward_to keep msgs gs) n = outputs_at gs n.
  Proof. reflexivity. Qed.

  Lemma outputs_at_fun_put gs n ns m :
    outputs_at (fun_put gs n ns) m =
      if eqb m n then flat_map outputs_of ns.(gns_trace) else outputs_at gs m.
  Proof. cbv [outputs_at fun_put]. destr (eqb m n); reflexivity. Qed.

  Lemma outputs_at_mono s lbl s' n :
    graph_step s lbl s' ->
    submultiset (outputs_at s n) (outputs_at s' n).
  Proof.
    intros Hstep. invert Hstep.
    - cbv [gns_run] in *. fwd. cbv [outputs_at forward_to enqueue fun_put].
      destr (eqb n n0); cbn; auto using submultiset_refl, submultiset_app_l.
    - cbv [gns_receive gns_run] in *. fwd. cbv [outputs_at fun_put].
      destr (eqb n n0); cbn; apply submultiset_refl.
  Qed.

  Lemma graph_sat_sound loc P :
    graph_sat loc P ->
    eventually (will_step graph_step) (fun gs => P (outputs_at gs loc)) init_graph.
  Proof.
    induction 1.
    - eapply eventually_trans.
      + apply eventually_and_reach.
        eapply eventually_will_step_Forall with
          (Ps := map (fun n' => fun gs => exists os, Pjs n' os /\ submultiset os (outputs_at gs n')) (fin.all _)) .
        -- apply Forall_map, Forall_forall. intros n _. cbv [ev_stable]. intros. fwd.
           eexists. split; [eassumption|]. eapply submultiset_trans; [eassumption|].
           eapply outputs_at_mono. eassumption.
        -- apply Forall_map, Forall_forall. intros n _. eapply eventually_weaken.
           { apply H0. }
           simpl. intros. eauto using submultiset_refl.
      + simpl. intros gs Hgs. fwd. apply Forall_map in Hgsp1. rewrite fin.Forall_all in Hgsp1.
        eapply step_sat_sound with (Pjs := fun _ _ => _).
        { assumption. }
        { exact Hgsp1. }
        cbv [suffices] in H1. apply fin.choice in Hgsp1. destruct Hgsp1 as [ojs Hojs].
        eapply npred_transf_mono_inc.
        -- apply H1. intros n'. specialize (Hojs n'). fwd. split; [eassumption|].
           eapply safe_mono; [|eassumption]. apply graph_is_safe. assumption.
        -- cbv [safe_inputs]. eexists. split; [|reflexivity]. intros. apply graph_is_safe. assumption.
        -- apply inputs_of_outputs_mono. intros n. specialize (Hojs n). fwd. assumption.
    - apply eventually_done. constructor.
  Qed.

  Lemma step_sat_complete gs gs' P dst :
    (any_step graph_step)^* init_graph gs ->
    relevant dst P ->
    any_step graph_step gs gs' ->
    P (outputs_at gs' dst) ->
    outputs_at gs' dst = outputs_at gs dst \/
      exists Pjs,
        (forall n, relevant n (Pjs n) /\ Pjs n (outputs_at gs n)) /\
          suffices dst Pjs P.
  Proof.
    intros Hreach Hrel Hstep HP. cbv [any_step] in Hstep. fwd. invert Hstep.
    - cbv [gns_run] in H. fwd. rewrite outputs_at_forward_to in HP |- *. cbv [fun_put outputs_at] in HP |- *.
      destr (eqb dst n); [|left; reflexivity]. simpl in HP |- *. right.
      pose proof node_steps_of_graph_steps as H''. especialize H''; eauto. fwd.
      pose proof npred_transf_complete as H'. especialize H'.
      { eapply star_step. 2: eassumption. simpl in H''p0. eassumption. }
      { admit. }
      { eassumption. }
      { rewrite H''p1 in HP. simpl. simpl in HP. rewrite app_nil_r in HP. exact HP. }
      simpl in H'. apply relevant_preserved.
      + assumption.
      + intros. apply graph_is_safe. assumption.
      + eapply relevant_preser
        pose proof node_steapply node_steps_of_graph_steps.
    - left. cbv [fun_put]. cbv [outputs_at]. cbv [gns_receive] in H. fwd.
      cbv [gns_run] in Hp1. simpl in Hp1. fwd. destr (eqb dst n); reflexivity.
  Qed.

  Lemma graph_sat_complete P dst t gs :
    relevant dst P ->
    star (graph_step) init_graph t gs ->
    P (outputs_at gs dst) ->
    graph_sat dst P.
  Proof. Admitted.
End __.
