From coqutil Require Import Semantics.OmniSmallstepCombinators.
From coqutil Require Import Eqb Tactics Tactics.fwd.
From Stdlib Require Import List Permutation Relations.
From Datalog Require Import Smallstep FinTypeclass Function List Relations Eqb Tactics IOGraph.
Import ListNotations.

Section __.
  Context {message label : Type} {node : nodeT}.
  Context {node_eqb : Eqb node} {node_eqb_ok : Eqb_ok node_eqb} {node_fin : Fin.Fin node}.
  Context (forward : source -> destn -> message -> bool) {node_state : Type}.
  Context (node_step : node -> node_state -> IO_event label message -> node_state -> Prop).
  Abbreviation nevent := (IO_event label message).
  Context (nodes_input_total : forall n, input_total (node_step n)).

  Context {claim : Type} (interp_claim : source -> claim -> list message -> Prop).
  Context (interp_claim_mono : forall n c, multiset_monotone_inc (interp_claim n c)).
  Context (npred_transf : node -> list message -> claim -> Prop).
  Context (init : node -> node_state).
  Context (safe : source -> list message -> Prop).
  Context (safe_mono : forall n, multiset_monotone_dec (safe n)).
  Context (safe_nothing : forall n, safe n []).

  Definition inputs_of_outputs (outputs : source -> list message) destn :=
    flat_map (fun n => filter (forward n destn) (outputs n)) (Fin.all _).

  (*TODO can we just have d of type node?*)
  Definition safe_inputs (d : destn) (inps : list message) :=
    exists ojs,
      (forall n', safe n' (ojs n')) /\
        Permutation inps (inputs_of_outputs ojs d).

  Context (safe_preserved :
            forall n t st,
              star (node_step n) (init n) t st ->
              safe_inputs (node_destn n) (flat_map inputs_of t) ->
              safe (node_source n) (flat_map outputs_of t)).

  Context (npred_transf_sound :
            forall n t P st,
              npred_transf n (flat_map inputs_of t) P ->
              safe_inputs (node_destn n) (flat_map inputs_of t) ->
              star (node_step n) (init n) t st ->
              eventually (will_step (node_step n) (safe_inputs (node_destn n))) (fun '(_, t') => interp_claim (node_source n) P (flat_map outputs_of t')) (st, t)).

  Context (npred_transf_complete :
            forall n t st P,
            star (node_step n) (init n) t st ->
            safe_inputs (node_destn n) (flat_map inputs_of t) ->
            interp_claim (node_source n) P (flat_map outputs_of t) ->
            npred_transf n (flat_map inputs_of t) P).

  Definition suffices loc (Pjs : source -> claim) P :=
    forall ojs,
      (forall n', interp_claim n' (Pjs n') (ojs n') /\ safe n' (ojs n')) ->
      npred_transf loc (inputs_of_outputs ojs (node_destn loc)) P.

  Definition decomposes ojs d (Q : list message -> Prop) :=
    exists (Pjs : source -> claim),
      (forall n', interp_claim n' (Pjs n') (ojs n')) /\
        forall ojs',
          (forall n', interp_claim n' (Pjs n') (ojs' n') /\ safe n' (ojs' n')) ->
          Q (inputs_of_outputs ojs' d).

  Context (preconditions_decompose :
            forall n ojs P,
              (forall n', safe n' (ojs n')) ->
              npred_transf n (inputs_of_outputs ojs (node_destn n)) P ->
              decomposes ojs (node_destn n) (fun inps => npred_transf n inps P)).

  Context (npred_transf_mono_inc :
            forall n inps inps' P,
              npred_transf n inps P ->
              safe_inputs (node_destn n) inps' ->
              submultiset inps inps' ->
              npred_transf n inps' P).

  Record graph_node_state :=
    { gns_node_state : node_state;
      gns_trace : list nevent;
      gns_queue : list message }.

  Definition enqueue inps (gns : graph_node_state) : graph_node_state :=
    {| gns_node_state := gns.(gns_node_state);
      gns_trace := gns.(gns_trace);
      gns_queue := inps ++ gns.(gns_queue) |}.

  Variant graph_label :=
    | receive (_ : node) (_ : message)
    | run (_ : node) (_ : label)
    | emit (_ : message).

  Record graph_state :=
    { graph_nodes : node -> graph_node_state;
      graph_output_queue : list message }.

  Definition put_node (gs : graph_state) n ns' :=
    {| graph_nodes := fun_put gs.(graph_nodes) n ns';
      graph_output_queue := gs.(graph_output_queue) |}.

  Definition forward_to (keep : destn -> message -> bool) (msgs : list message) (gs : graph_state) : graph_state :=
    {| graph_nodes := fun n => enqueue (filter (keep (node_destn n)) msgs) (gs.(graph_nodes) n);
      graph_output_queue := filter (keep output_destn) msgs ++ gs.(graph_output_queue) |}.

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

  Variant graph_step : graph_state -> IO_event graph_label message -> graph_state -> Prop :=
    | gstep_input gs m :
      graph_step gs (I_event m) (forward_to (forward input_source) [m] gs)
    | gstep_run n gs ns' lbl outs :
      gns_run n (gs.(graph_nodes) n) (O_event lbl outs) ns' ->
      graph_step gs (O_event (run n lbl) []) (forward_to (forward (node_source n)) outs (put_node gs n ns'))
    | gstep_receive gs n m ns' :
      gns_receive n (gs.(graph_nodes) n) m ns' ->
      graph_step gs (O_event (receive n m) []) (put_node gs n ns')
    | gstep_output gs q1 m q2 :
      gs.(graph_output_queue) = q1 ++ m :: q2 ->
      graph_step gs (O_event (emit m) [m])
                 {| graph_nodes := gs.(graph_nodes);
                   graph_output_queue := q1 ++ q2 |}.

  Definition outputs_at (gs : graph_state) (t : list (IO_event graph_label message)) (n : source) :=
    match n with
    | input_source => flat_map inputs_of t
    | node_source n' => flat_map outputs_of (gs.(graph_nodes) n').(gns_trace)
    end.

  Definition inputs_at (gs : graph_state) (t : list (IO_event graph_label message)) n :=
    match n with
    | output_destn => flat_map outputs_of t
    | node_destn n' => flat_map inputs_of (gs.(graph_nodes) n').(gns_trace)
    end.

  Definition queue_at (gs : graph_state) d :=
    match d with
    | output_destn => gs.(graph_output_queue)
    | node_destn n => (gs.(graph_nodes) n).(gns_queue)
    end.

  Inductive graph_sat (inputs : list message) : source -> claim -> Prop :=
  | step_sat loc P Pjs :
    (forall n', graph_sat _ n' (Pjs n')) ->
    suffices loc Pjs P ->
    graph_sat _ (node_source loc) P
  | init_sat loc P :
    interp_claim (node_source loc) P [] ->
    graph_sat _ (node_source loc) P
  | input_sat P :
    interp_claim input_source P inputs ->
    graph_sat _ input_source P.

  Definition init_gns n : graph_node_state :=
    {| gns_node_state := init n;
      gns_trace := [];
      gns_queue := [] |}.

  Definition init_graph_state : graph_state :=
    {| graph_nodes := init_gns; graph_output_queue := [] |}.

  Lemma outputs_at_forward_to keep msgs gs t n :
    outputs_at (forward_to keep msgs gs) t n = outputs_at gs t n.
  Proof. destruct n; reflexivity. Qed.

  Lemma outputs_at_put_node gs t n ns m :
    outputs_at (put_node gs n ns) t m =
      if eqb m (node_source n) then flat_map outputs_of ns.(gns_trace) else outputs_at gs t m.
  Proof.
    cbv [outputs_at put_node fun_put]. destr (eqb m (node_source n)); cbn [graph_nodes].
    - rewrite_true (eqb n n) by reflexivity. reflexivity.
    - destruct m as [m|]; [ | reflexivity ]. rewrite_false (eqb m n) by congruence. reflexivity.
  Qed.

  Lemma messages_conserved_step gs t e gs' d :
    (forall d', Permutation (inputs_of_outputs (outputs_at gs t) d') (inputs_at gs t d' ++ queue_at gs d')) ->
    graph_step gs e gs' ->
    Permutation (inputs_of_outputs (outputs_at gs' (e :: t)) d) (inputs_at gs' (e :: t) d ++ queue_at gs' d).
  Proof.
    intros Hcons Hstep. invert Hstep.
    - transitivity (filter (forward input_source d) [m] ++ inputs_of_outputs (outputs_at gs t) d).
      + apply flat_map_app_at_perm with (a := input_source).
        * apply Fin.all_NoDup.
        * apply Fin.all_Full.
        * intros [a'|] ?; [ reflexivity | congruence ].
        * apply (filter_app _ [m]).
      + cbv [inputs_at queue_at forward_to enqueue]. destruct d; cbn;
          symmetry; apply perm_ins; symmetry; apply Hcons.
    - cbv [gns_run] in *. fwd.
      transitivity (filter (forward (node_source n) d) outs ++ inputs_of_outputs (outputs_at gs t) d).
      + apply flat_map_app_at_perm with (a := node_source n).
        * apply Fin.all_NoDup.
        * apply Fin.all_Full.
        * intros a' ?. cbv beta. rewrite outputs_at_forward_to, outputs_at_put_node.
          rewrite_false (eqb a' (node_source n)) by assumption. destruct a'; reflexivity.
        * cbv beta. rewrite outputs_at_forward_to, outputs_at_put_node.
          rewrite_true (eqb (node_source n) (node_source n)) by reflexivity.
          apply filter_app.
      + cbv [inputs_at queue_at forward_to enqueue put_node fun_put]. cbn [graph_nodes graph_output_queue].
        destruct d as [dst|].
        * destr (eqb dst n); cbn; symmetry; apply perm_ins; symmetry; apply Hcons.
        * cbn. symmetry. apply perm_ins. symmetry. apply Hcons.
    - cbv [gns_receive gns_run] in *. fwd.
      transitivity (inputs_of_outputs (outputs_at gs t) d).
      + apply Permutation_of_eq, flat_map_ext. intros k.
        rewrite outputs_at_put_node. destr (eqb k (node_source n)); [ reflexivity | destruct k; reflexivity ].
      + rewrite Hcons. cbv [inputs_at queue_at put_node fun_put]. cbn [graph_nodes graph_output_queue].
        destruct d as [dst|]; [ | reflexivity ].
        destr (eqb dst n); cbn.
        * rewrite Hp0. apply perm_recv.
        * reflexivity.
    - transitivity (inputs_of_outputs (outputs_at gs t) d); [ reflexivity | ].
      rewrite Hcons. destruct d as [dst|]; [ reflexivity | ].
      cbv [inputs_at queue_at]. cbn. rewrite H. apply perm_recv.
  Qed.

  Lemma messages_conserved gs t d :
    star graph_step init_graph_state t gs ->
    Permutation (inputs_of_outputs (outputs_at gs t) d) (inputs_at gs t d ++ queue_at gs d).
  Proof.
    intros H. revert d. induction H; intros d.
    - cbv [inputs_of_outputs]. rewrite flat_map_all_nil by (intros []; reflexivity). destruct d; reflexivity.
    - eapply messages_conserved_step; eassumption.
  Qed.

  Lemma pool_submultiset_step gs t e gs' d :
    graph_step gs e gs' ->
    submultiset (inputs_at gs t d) (inputs_at gs' (e :: t) d) /\
      submultiset (inputs_at gs t d ++ queue_at gs d) (inputs_at gs' (e :: t) d ++ queue_at gs' d).
  Proof.
    intros Hstep. invert Hstep.
    - cbv [inputs_at queue_at forward_to enqueue]. destruct d; cbn;
        split; auto using submultiset_refl, submultiset_app_mid.
    - cbv [gns_run] in *. fwd. cbv [inputs_at queue_at forward_to enqueue put_node fun_put].
      cbn [graph_nodes graph_output_queue]. destruct d as [dst|].
      + destr (eqb dst n); cbn; split; auto using submultiset_refl, submultiset_app_mid.
      + cbn. split; auto using submultiset_refl, submultiset_app_mid.
    - cbv [gns_receive gns_run] in *. fwd. cbv [inputs_at queue_at put_node fun_put].
      cbn [graph_nodes graph_output_queue]. destruct d as [dst|]; [ | split; apply submultiset_refl ].
      destr (eqb dst n); cbn; split; auto using submultiset_refl, submultiset_cons.
      rewrite Hp0. apply submultiset_perm. apply perm_recv.
    - destruct d as [dst|]; [ split; apply submultiset_refl | ].
      cbv [inputs_at queue_at]. cbn. split; [ apply submultiset_cons | ].
      rewrite H. apply submultiset_perm. apply perm_recv.
  Qed.

  Lemma pool_submultiset gs t t' gs' d :
    star graph_step gs t' gs' ->
    submultiset (inputs_at gs t d) (inputs_at gs' (t' ++ t) d) /\
      submultiset (inputs_at gs t d ++ queue_at gs d) (inputs_at gs' (t' ++ t) d ++ queue_at gs' d).
  Proof.
    induction 1.
    - split; apply submultiset_refl.
    - apply pool_submultiset_step with (t := t0 ++ t) (d := d) in H0. fwd.
      split; eapply submultiset_trans; eassumption.
  Qed.

  Lemma eventually_received gs t d base owed :
    submultiset base (inputs_at gs t d) ->
    submultiset (base ++ owed) (inputs_at gs t d ++ queue_at gs d) ->
    eventually (will_step graph_step (safe input_source))
      (fun '(gs', t') => submultiset (base ++ owed) (inputs_at gs' t' d)) (gs, t).
  Proof.
    revert base gs t. induction owed as [|m owed IH]; intros base gs t Hbase Howed.
    - apply eventually_done. rewrite app_nil_r. assumption.
    - apply eventually_step with
        (midset := fun '(gs', t') =>
                     submultiset (base ++ [m]) (inputs_at gs' t' d) /\
                       submultiset (base ++ m :: owed) (inputs_at gs' t' d ++ queue_at gs' d)).
      + exists (match d with node_destn dst => receive dst m | output_destn => emit m end).
        intros gs' t' Hreach _.
        apply pool_submultiset with (t := t) (d := d) in Hreach. destruct Hreach as [HR HRQ].
        apply (submultiset_trans _ _ _ Hbase) in HR.
        apply (submultiset_trans _ _ _ Howed) in HRQ.
        destruct (submultiset_snoc_or_in _ _ _ _ _ HR HRQ) as [Hdone|Hq].
        * left. split; assumption.
        * right. apply in_split in Hq. destruct Hq as (ms1 & ms2 & Hq). destruct d as [dst|].
          -- destruct (nodes_input_total dst (gs'.(graph_nodes) dst).(gns_node_state) m) as [st' Hst'].
             do 2 eexists. split.
             ++ constructor. exists ms1, ms2. split; [exact Hq|]. eexists. split; [exact Hst'|reflexivity].
             ++ cbv [inputs_at queue_at put_node fun_put]. cbn [graph_nodes]. simpl.
                rewrite_true (eqb dst dst) by reflexivity. split.
                ** eapply submultiset_perm_l; [apply Permutation_cons_append|].
                   apply submultiset_cons_mono. assumption.
                ** eapply submultiset_perm_r; [apply perm_recv|]. rewrite <- Hq. assumption.
          -- do 2 eexists. split.
             ++ constructor. exact Hq.
             ++ cbv [inputs_at queue_at]. cbn. split.
                ** eapply submultiset_perm_l; [apply Permutation_cons_append|].
                   apply submultiset_cons_mono. assumption.
                ** eapply submultiset_perm_r; [apply perm_recv|]. rewrite <- Hq. assumption.
      + intros [gs' t'] [].
        replace (base ++ m :: owed) with ((base ++ [m]) ++ owed) in * by (rewrite <- app_assoc; reflexivity).
        auto.
  Qed.

  Lemma drain_queues gs t d :
    eventually (will_step graph_step (safe input_source))
      (fun '(gs', t') => submultiset (inputs_at gs t d ++ queue_at gs d) (inputs_at gs' t' d))
      (gs, t).
  Proof. apply eventually_received; apply submultiset_refl. Qed.

  Lemma sent_msgs_eventually_received gs t d :
    star graph_step init_graph_state t gs ->
    eventually (will_step graph_step (safe input_source))
      (fun '(gs', t') => submultiset (inputs_of_outputs (outputs_at gs t) d) (inputs_at gs' t' d))
      (gs, t).
  Proof.
    intros Hreach. eapply eventually_weaken; [apply drain_queues|].
    intros [gs' t'] H. eapply submultiset_perm_l; [|exact H].
    symmetry. apply messages_conserved. assumption.
  Qed.

  Lemma inputs_of_outputs_mono ojs ojs' dst :
    (forall n, submultiset (ojs n) (ojs' n)) ->
    submultiset (inputs_of_outputs ojs dst) (inputs_of_outputs ojs' dst).
  Proof. intros H. apply submultiset_flat_map. intros n. apply submultiset_filter, H. Qed.

  Lemma In_inputs_of_outputs ojs dst m :
    In m (inputs_of_outputs ojs dst) <-> exists n, In m (ojs n) /\ forward n dst m = true.
  Proof.
    cbv [inputs_of_outputs]. rewrite in_flat_map. split.
    - intros (n & _ & Hin). apply filter_In in Hin. eauto.
    - intros (n & Hin & Hfw). exists n. split; [ apply Fin.all_Full | apply filter_In; auto ].
  Qed.

  Lemma safe_inputs_mono d : multiset_monotone_dec (safe_inputs d).
  Proof.
    intros inps' inps (ojs & Hsafe & Hperm) Hsub.
    apply (submultiset_perm_r _ _ _ Hperm) in Hsub.
    apply submultiset_flat_map_split in Hsub; [ | apply Fin.all_NoDup ].
    destruct Hsub as (g & Hg & Hgsub). exists g. split.
    - intros n'. eapply safe_mono; [ apply Hsafe | ].
      eapply submultiset_trans; [ apply Hgsub | apply filter_submultiset ].
    - rewrite Hg. apply Permutation_of_eq, flat_map_ext_in. intros n' _.
      symmetry. eapply filter_id_submultiset. apply Hgsub.
  Qed.

  Lemma node_steps_of_graph_steps gs t gs' n :
    star graph_step gs t gs' ->
    exists tn, star (node_step n) (gs.(graph_nodes) n).(gns_node_state) tn (gs'.(graph_nodes) n).(gns_node_state) /\
               (gs'.(graph_nodes) n).(gns_trace) = tn ++ (gs.(graph_nodes) n).(gns_trace).
  Proof.
    induction 1.
    - exists []. split; [ apply star_refl | reflexivity ].
    - destruct IHstar as (tn & Htn & Htr). invert H0.
      + exists tn. split; assumption.
      + cbv [gns_run] in *. fwd. cbv [forward_to enqueue put_node fun_put]. cbn [graph_nodes].
        destr (eqb n n0); cbn; [ | exists tn; split; assumption ].
        eexists. split.
        * eauto using star_step.
        * cbn. congruence.
      + cbv [gns_receive gns_run] in *. fwd. cbv [put_node fun_put]. cbn [graph_nodes].
        destr (eqb n n0); cbn; [ | exists tn; split; assumption ].
        eexists. split.
        * eauto using star_step.
        * cbn. congruence.
      + exists tn. split; assumption.
  Qed.

  Lemma node_steps_of_graph_steps_init gs t n :
    star graph_step init_graph_state t gs ->
    star (node_step n) (init n) (gs.(graph_nodes) n).(gns_trace) (gs.(graph_nodes) n).(gns_node_state).
  Proof.
    intros H. apply node_steps_of_graph_steps with (n := n) in H. destruct H as (tn & Htn & Htr).
    cbn in Htr. rewrite Htr, app_nil_r. exact Htn.
  Qed.

  Lemma graph_is_safe gs t s :
    star graph_step init_graph_state t gs ->
    safe input_source (flat_map inputs_of t) ->
    safe s (outputs_at gs t s).
  Proof.
    intros H. revert s. induction H; intros s Hinp.
    - destruct s; apply safe_nothing.
    - assert (Hinp' : safe input_source (flat_map inputs_of t0)).
      { eapply safe_mono; [ exact Hinp | apply submultiset_app_l ]. }
      invert H0.
      + destruct s; [ apply IHstar, Hinp' | assumption ].
      + cbv [gns_run] in *. fwd. rewrite outputs_at_forward_to, outputs_at_put_node.
        destr (eqb s (node_source n)); [ | destruct s; apply IHstar, Hinp' ].
        eapply safe_preserved; cbn.
        * eauto using star_step, node_steps_of_graph_steps_init.
        * eapply safe_inputs_mono.
          -- exists (outputs_at s' t0). split; [ intros; apply IHstar, Hinp' | reflexivity ].
          -- eapply submultiset_perm_r; [ | apply submultiset_app_r ].
             symmetry. apply messages_conserved. assumption.
      + cbv [gns_receive gns_run] in *. fwd. rewrite outputs_at_put_node.
        destr (eqb s (node_source n)); [ apply IHstar, Hinp' | destruct s; apply IHstar, Hinp' ].
      + destruct s; apply IHstar, Hinp'.
  Qed.

  Lemma graph_inputs_safe gs t d :
    star graph_step init_graph_state t gs ->
    safe input_source (flat_map inputs_of t) ->
    safe_inputs d (inputs_at gs t d).
  Proof.
    intros H Hinp. eapply safe_inputs_mono.
    - exists (outputs_at gs t). split; [ eauto using graph_is_safe | reflexivity ].
    - eapply submultiset_perm_r; [ | apply submultiset_app_r ].
      symmetry. apply messages_conserved. assumption.
  Qed.

  Lemma graph_will_step_of_node_will_step gs t n P :
    star graph_step init_graph_state t gs ->
    will_step (node_step n) (safe_inputs (node_destn n))
      ((gs.(graph_nodes) n).(gns_node_state), (gs.(graph_nodes) n).(gns_trace)) P ->
    will_step graph_step (safe input_source) (gs, t)
      (fun '(gs', _) => P ((gs'.(graph_nodes) n).(gns_node_state), (gs'.(graph_nodes) n).(gns_trace))).
  Proof.
    intros Hreach (lbl & Hwill). exists (run n lbl). intros gs' t' Hgs' Hsafe.
    destruct (node_steps_of_graph_steps _ _ _ n Hgs') as (tn & Htn & Htr).
    destruct (Hwill _ _ Htn) as [HP | (s'' & outs & Hstep & HP)].
    - rewrite <- Htr. apply (graph_inputs_safe _ (t' ++ t) (node_destn n)).
      + eapply star_app; eassumption.
      + assumption.
    - left. cbv beta iota. rewrite Htr. assumption.
    - right. do 2 eexists. split.
      + econstructor. exists s''. split; [ exact Hstep | reflexivity ].
      + cbv [forward_to enqueue put_node fun_put]. cbn [graph_nodes].
        rewrite_true (eqb n n) by reflexivity. cbn. rewrite Htr. assumption.
  Qed.

  Lemma graph_eventually_of_node_eventually gs t n P :
    star graph_step init_graph_state t gs ->
    eventually (will_step (node_step n) (safe_inputs (node_destn n))) P
      ((gs.(graph_nodes) n).(gns_node_state), (gs.(graph_nodes) n).(gns_trace)) ->
    eventually (will_step graph_step (safe input_source))
      (fun '(gs', _) => P ((gs'.(graph_nodes) n).(gns_node_state), (gs'.(graph_nodes) n).(gns_trace))) (gs, t).
  Proof.
    intros Hreach Hev. remember ((gs.(graph_nodes) n).(gns_node_state), (gs.(graph_nodes) n).(gns_trace)) as st eqn:E.
    revert gs t Hreach E. induction Hev; intros gs t Hreach E; subst.
    - apply eventually_done. assumption.
    - apply eventually_step with
        (midset := fun '(gs', t') =>
                     star graph_step init_graph_state t' gs' /\
                       midset ((gs'.(graph_nodes) n).(gns_node_state), (gs'.(graph_nodes) n).(gns_trace))).
      + apply will_step_reach. eapply will_step_impl.
        * apply graph_will_step_of_node_will_step; eassumption.
        * intros [gs' t'] Hm Hr. cbv [reachable] in Hr. fwd. split.
          -- eapply star_app; eassumption.
          -- exact Hm.
      + intros [gs' t'] []. eauto.
  Qed.

  Lemma step_sat_sound gs t dst P :
    star graph_step init_graph_state t gs ->
    safe input_source (flat_map inputs_of t) ->
    npred_transf dst (inputs_of_outputs (outputs_at gs t) (node_destn dst)) P ->
    eventually (will_step graph_step (safe input_source))
      (fun '(gs', t') => interp_claim (node_source dst) P (outputs_at gs' t' (node_source dst))) (gs, t).
  Proof.
    intros Hreach Hsafe Htrans.
    eapply eventually_trans.
    { apply eventually_will_step_annotate. apply sent_msgs_eventually_received with (d := node_destn dst). assumption. }
    intros [gs' t'] ((tr & Hstar & -> & Hsafe') & Hrecv).
    eapply eventually_weaken.
    { apply graph_eventually_of_node_eventually.
      - eapply star_app; eassumption.
      - apply npred_transf_sound.
        + eapply npred_transf_mono_inc.
          * eassumption.
          * apply (graph_inputs_safe _ (tr ++ t) (node_destn dst)).
            -- eapply star_app; eassumption.
            -- auto.
          * assumption.
        + apply (graph_inputs_safe _ (tr ++ t) (node_destn dst)).
          * eapply star_app; eassumption.
          * auto.
        + apply node_steps_of_graph_steps_init with (t := tr ++ t). eapply star_app; eassumption. }
    intros [gs'' t''] HP. exact HP.
  Qed.

  Lemma outputs_at_mono s t e s' n :
    graph_step s e s' ->
    submultiset (outputs_at s t n) (outputs_at s' (e :: t) n).
  Proof.
    intros Hstep. invert Hstep.
    - destruct n; [ apply submultiset_refl | apply submultiset_cons ].
    - cbv [gns_run] in *. fwd. rewrite outputs_at_forward_to, outputs_at_put_node.
      destr (eqb n (node_source n0)); [ apply submultiset_app_l | destruct n; apply submultiset_refl ].
    - cbv [gns_receive gns_run] in *. fwd. rewrite outputs_at_put_node.
      destr (eqb n (node_source n0)); [ apply submultiset_refl | destruct n; apply submultiset_refl ].
    - destruct n; apply submultiset_refl.
  Qed.

  Lemma graph_sat_sound gs t loc P :
    star graph_step init_graph_state t gs ->
    safe input_source (flat_map inputs_of t) ->
    graph_sat (flat_map inputs_of t) loc P ->
    eventually (will_step graph_step (safe input_source))
      (fun '(gs', t') => interp_claim loc P (outputs_at gs' t' loc)) (gs, t).
  Proof.
    intros Hreach Hsafe. induction 1.
    - eapply eventually_trans.
      + apply eventually_will_step_annotate.
        eapply eventually_will_step_Forall with
          (Ps := map (fun n' '(gs', t') => interp_claim n' (Pjs n') (outputs_at gs' t' n')) (Fin.all _)).
        -- apply Forall_map, Forall_forall. intros n _ s s' e t0 HP Hstep.
           eapply interp_claim_mono; [ exact HP | ]. eapply outputs_at_mono. eassumption.
        -- apply Forall_map, Forall_forall. intros n _. apply H0.
      + intros [gs' t'] ((tr & Hstar & -> & Hsafe') & Hgs).
        apply Forall_map in Hgs. rewrite Fin.Forall_all in Hgs.
        apply step_sat_sound.
        * eapply star_app; eassumption.
        * auto.
        * apply H1. intros n'. split; [ apply Hgs | ].
          apply graph_is_safe; [ eapply star_app; eassumption | auto ].
    - apply eventually_done. eapply interp_claim_mono; [ eassumption | apply submultiset_nil_l ].
    - apply eventually_done. assumption.
  Qed.

  Lemma step_sat_complete gs t e gs' dst P :
    star graph_step init_graph_state t gs ->
    safe input_source (flat_map inputs_of t) ->
    graph_step gs e gs' ->
    interp_claim (node_source dst) P (outputs_at gs' (e :: t) (node_source dst)) ->
    outputs_at gs' (e :: t) (node_source dst) = outputs_at gs t (node_source dst) \/
      exists Pjs,
        (forall n, interp_claim n (Pjs n) (outputs_at gs t n)) /\
          suffices dst Pjs P.
  Proof.
    intros Hreach Hsafe Hstep HP. invert Hstep.
    - left. reflexivity.
    - cbv [gns_run] in H. fwd. rewrite outputs_at_forward_to, outputs_at_put_node in *.
      destr (eqb (node_source dst) (node_source n)); [ invert E | left; reflexivity ].
      right. apply preconditions_decompose.
      + intros. apply graph_is_safe; assumption.
      + eapply npred_transf_mono_inc.
        * apply npred_transf_complete with (st := st').
          -- eapply star_step; [ eapply node_steps_of_graph_steps_init; eassumption | eassumption ].
          -- apply (graph_inputs_safe _ t (node_destn n)); assumption.
          -- exact HP.
        * exists (outputs_at gs t). split; [ | reflexivity ]. intros. apply graph_is_safe; assumption.
        * eapply submultiset_perm_r; [ | apply submultiset_app_r ].
          symmetry. apply messages_conserved. assumption.
    - left. cbv [gns_receive gns_run] in H. fwd. rewrite outputs_at_put_node.
      destr (eqb (node_source dst) (node_source n)); [ invert E | ]; reflexivity.
    - left. reflexivity.
  Qed.

  Lemma graph_sat_mono inps inps' s P :
    graph_sat inps s P ->
    submultiset inps inps' ->
    graph_sat inps' s P.
  Proof.
    intros Hsat Hsub. induction Hsat.
    - eapply step_sat; eassumption.
    - apply init_sat. assumption.
    - apply input_sat. eapply interp_claim_mono; eassumption.
  Qed.

  Lemma graph_sat_complete gs t dst P :
    star graph_step init_graph_state t gs ->
    safe input_source (flat_map inputs_of t) ->
    interp_claim dst P (outputs_at gs t dst) ->
    graph_sat (flat_map inputs_of t) dst P.
  Proof.
    intros Hreach. revert dst P. induction Hreach; intros dst P Hsafe HP.
    - destruct dst; [ apply init_sat | apply input_sat ]; assumption.
    - assert (Hsafe' : safe input_source (flat_map inputs_of t0)).
      { eapply safe_mono; [ exact Hsafe | apply submultiset_app_l ]. }
      destruct dst as [n|]; [ | apply input_sat; assumption ].
      eapply graph_sat_mono; [ | apply submultiset_app_l ].
      destruct (step_sat_complete _ _ _ _ _ _ Hreach Hsafe' H HP) as [Heq | (Pjs & HPjs & Hsuff)].
      + apply IHHreach; [ assumption | ]. rewrite <- Heq. assumption.
      + eapply step_sat; [ | eassumption ]. intros n'. apply IHHreach; [ assumption | apply HPjs ].
  Qed.

  (*TODO this is basically suffices with npred_transf := fun P x => P x or sth*)
  Definition output_sat inputs P :=
    exists Pjs,
      (forall n, graph_sat inputs n (Pjs n)) /\
        forall ojs,
          (forall n, interp_claim n (Pjs n) (ojs n) /\ safe n (ojs n)) ->
          P (inputs_of_outputs ojs output_destn).

  (*TODO this is basically preconditions_decompose with npred_transf := fun P x => P x or sth *)
  Definition admissible P :=
    (forall x y, P x -> Permutation x y -> P y) /\
      forall ojs,
        (forall n, safe n (ojs n)) ->
        P (inputs_of_outputs ojs output_destn) ->
        decomposes ojs output_destn P.

  Lemma output_sat_sound t gs P :
    star graph_step init_graph_state t gs ->
    safe input_source (flat_map inputs_of t) ->
    output_sat (flat_map inputs_of t) P ->
    eventually (will_step graph_step (safe input_source)) (fun '(_, t') => P (flat_map outputs_of t')) (gs, t).
  Proof.
    intros Hinit Hsafe H. cbv [output_sat] in H. fwd.
    eapply eventually_trans.
    - (*conjunction over all nodes..*)

  Lemma output_sat_complete t gs P :
    star graph_step init_graph_state t gs ->
    safe input_source (flat_map inputs_of t) ->
    admissible P ->
    P (flat_map outputs_of t) ->
    output_sat (flat_map inputs_of t) P.
  Proof. Admitted.

End __.
Arguments graph_node_state : clear implicits.
Arguments graph_label : clear implicits.
Arguments graph_state : clear implicits.
