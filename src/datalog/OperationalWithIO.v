From Stdlib Require Import List PeanoNat.
From Datalog Require Import Datalog Node Operational Smallstep List.
From coqutil Require Import Map.Interface Datatypes.List.
Import ListNotations.

Section __.
  Context {rel : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.
  Context (is_input : rel -> bool).
  Context (p : prog).
  Context (Hmeta_rules : meta_rules_valid (rules_of p)).
  Context (Hp_input : Forall (good_non_meta_rule is_input) p.(non_meta_rules)).
  Context (Hp_meta_input : Forall (good_meta_rule_inputs is_input) p.(meta_rules)).
  Context (Hfin : meta_facts_finite p).
  Context (Hlen : 0 < length p.(non_meta_rules)).

  Local Notation IO_event := (Smallstep.IO_event unit dfact).

  Inductive step : state -> IO_event -> state -> Prop :=
  | step_comp s1 s2 :
    comp_step is_input p s1 s2 ->
    step s1 (O_event tt []) s2
  | step_input s f :
    step s (I_event f) (map (add_waiting_fact f) s)
  | step_output s R args :
    knows_dfact s (normal_dfact R args) ->
    step s (O_event tt [normal_dfact R args]) s.

  Definition empty_rule_state : Operational.node_state :=
    {| known_facts := []; waiting_facts := []; sent_facts := [] |}.

  Definition initial : state := repeat empty_rule_state (length p.(non_meta_rules)).

  Local Notation R_senders := (Operational.R_senders is_input p).
  Local Notation rules_of := (Operational.rules_of p).
  Local Notation knows_datalog_fact := (Node.knows_datalog_fact R_senders).
  Local Notation good_input_facts := (Operational.good_input_facts is_input).
  Local Notation state_correct := (Operational.state_correct is_input p).
  Local Notation state_complete := (Operational.state_complete is_input p).
  Local Notation sane_state := (Operational.sane_state is_input p).
  Local Notation meta_facts_correct := (Operational.meta_facts_correct is_input p).
  Local Notation meta_facts_ok := (Operational.meta_facts_ok is_input p).
  Local Notation has_derived_datalog_fact := (Operational.has_derived_datalog_fact is_input p).

  Definition INV (inputs : list dfact) (s : state) : Prop :=
    sane_state inputs s /\ meta_facts_correct s /\ meta_facts_ok s /\ state_correct inputs s.

  Definition load (l : list dfact) (s : state) : state :=
    fold_right (fun f s' => map (add_waiting_fact f) s') s l.

  Lemma load_star (l : list dfact) (s : state) :
    star step s (map I_event l) (load l s).
  Proof.
    induction l as [|f l IH]; [apply star_refl|].
    cbn [map load fold_right]. eapply star_step; [exact IH | apply step_input].
  Qed.

  Lemma comp_lift (s s' : state) :
    (comp_step is_input p)^* s s' ->
    exists t, star step s t s' /\ inputs_of t = [] /\ outputs_of t = [].
  Proof.
    intros H. induction H as [ | s0 s1 s2 Hstep Hrest IH].
    - exists []. split; [apply star_refl | split; reflexivity].
    - destruct IH as (t & Hstar & Hin & Hout).
      exists (t ++ [O_event tt []]). split.
      + eapply star_app; [apply star_one; apply step_comp; exact Hstep | exact Hstar].
      + rewrite inputs_of_app, outputs_of_app, Hin, Hout. split; reflexivity.
  Qed.

  Lemma output_decomp (t : list IO_event) (s ns : state) (m : dfact) :
    star step s t ns ->
    In m (outputs_of t) ->
    exists tpre spost,
      star step s tpre spost /\ knows_dfact spost m /\ incl (inputs_of tpre) (inputs_of t).
  Proof.
    intros Hstar. induction Hstar as [ | t0 s' e s'' Hstar IH Hstep]; intros Hin.
    - destruct Hin.
    - cbn [outputs_of flat_map] in Hin. rewrite in_app_iff in Hin.
      destruct Hin as [Hin_e | Hin_t0].
      + destruct Hstep as [s1 s2 Hc | s0 f | s0 R args Hk]; cbn in Hin_e.
        * destruct Hin_e.
        * destruct Hin_e.
        * destruct Hin_e as [<- | []].
          exists t0, s0. split; [exact Hstar|]. split; [exact Hk|].
          cbn [inputs_of flat_map]. apply incl_refl.
      + destruct (IH Hin_t0) as (tpre & spost & Hs & Hk & Hincl).
        exists tpre, spost. split; [exact Hs|]. split; [exact Hk|].
        apply incl_appr. exact Hincl.
  Qed.

  Lemma sane_state_initial (inputs : list dfact) :
    good_input_facts inputs -> sane_state inputs initial.
  Admitted.

  Lemma Forall3_map_mid {A B B' C} (g : B -> B') (Q : A -> B' -> C -> Prop)
    (l : list A) (m : list B) (k : list C) :
    Forall3 (fun a b c => Q a (g b) c) l m k -> Forall3 Q l (map g m) k.
  Proof. intros H. induction H; cbn; constructor; assumption. Qed.

  Lemma Forall3_repeat_seq {A} (Q : A -> node_state -> nat -> Prop)
    (l : list A) (x : node_state) (start : nat) :
    (forall a n, Q a x n) -> Forall3 Q l (repeat x (length l)) (seq start (length l)).
  Proof.
    intros HQ. revert start. induction l as [|a l IH]; intros start; cbn; constructor.
    - apply HQ.
    - apply IH.
  Qed.

  Lemma mfc_initial : meta_facts_correct initial.
  Proof.
    unfold meta_facts_correct, initial. rewrite repeat_length.
    apply Forall3_repeat_seq. intros a n R mf_args num Hin. destruct Hin.
  Qed.

  Lemma mfok_initial : meta_facts_ok initial.
  Proof.
    unfold meta_facts_ok, initial. rewrite repeat_length.
    apply Forall3_repeat_seq. intros a n mf_rel mf_args num Hin. destruct Hin.
  Qed.

  Lemma knows_dfact_initial (g : dfact) : ~ knows_dfact initial g.
  Proof.
    unfold knows_dfact, initial. intros H. apply Exists_exists in H.
    destruct H as (rs & Hin & Hrhd). apply repeat_spec in Hin. subst rs.
    destruct Hrhd as [[] | []].
  Qed.

  Lemma sc_initial (inputs : list dfact) : state_correct inputs initial.
  Proof.
    intros f (Hderiv & _). exfalso. destruct f as [R args | R args set].
    - eapply knows_dfact_initial; exact Hderiv.
    - cbn in Hderiv. destruct (is_input R).
      + destruct Hderiv as (num & Hk). eapply knows_dfact_initial; exact Hk.
      + specialize (Hderiv 0 Hlen). destruct Hderiv as (num & Hk).
        eapply knows_dfact_initial; exact Hk.
  Qed.

  Lemma add_input_sane (inputs : list dfact) (f : dfact) (s : state) :
    good_input_facts inputs -> In f inputs -> sane_state inputs s ->
    sane_state inputs (map (add_waiting_fact f) s).
  Admitted.

  Lemma add_wf_mfc (f : dfact) (s : state) :
    meta_facts_correct s -> meta_facts_correct (map (add_waiting_fact f) s).
  Proof.
    unfold meta_facts_correct. rewrite length_map. intros H.
    apply Forall3_map_mid. exact H.
  Qed.

  Lemma add_wf_mfok (f : dfact) (s : state) :
    meta_facts_ok s -> meta_facts_ok (map (add_waiting_fact f) s).
  Proof.
    unfold meta_facts_ok. rewrite length_map. intros H.
    apply Forall3_map_mid. exact H.
  Qed.

  Lemma add_input_sc (inputs : list dfact) (f : dfact) (s : state) :
    good_input_facts inputs -> In f inputs -> sane_state inputs s -> state_correct inputs s ->
    state_correct inputs (map (add_waiting_fact f) s).
  Admitted.

  Lemma INV_initial (inputs : list dfact) :
    good_input_facts inputs -> INV inputs initial.
  Proof.
    intros Hg. unfold INV.
    split; [apply sane_state_initial; exact Hg|].
    split; [apply mfc_initial|]. split; [apply mfok_initial|]. apply sc_initial.
  Qed.

  Lemma step_preserves_INV (inputs : list dfact) (s1 : state) (e : IO_event) (s2 : state) :
    good_input_facts inputs ->
    (forall f, e = I_event f -> In f inputs) ->
    step s1 e s2 ->
    INV inputs s1 -> INV inputs s2.
  Proof.
    intros Hg Hef Hstep (Hs & Hmfc & Hmfok & Hsc).
    destruct Hstep as [a b Hc | a f | a R args Hk]; unfold INV.
    - split; [eapply step_preserves_sane; eauto|].
      split; [eapply step_preserves_mfs_correct; eauto|].
      split; [eapply step_preserves_meta_facts_ok; eauto|].
      eapply comp_steps_sound; try eassumption.
      eapply Relation_Operators.rt1n_trans; [exact Hc | apply Relation_Operators.rt1n_refl].
    - assert (Hf : In f inputs) by (apply Hef; reflexivity).
      split; [apply add_input_sane; auto|].
      split; [apply add_wf_mfc; auto|].
      split; [apply add_wf_mfok; auto|].
      apply add_input_sc; auto.
    - split; [exact Hs|]. split; [exact Hmfc|]. split; [exact Hmfok|]. exact Hsc.
  Qed.

  Lemma star_INV (inputs : list dfact) (t : list IO_event) (s : state) :
    good_input_facts inputs ->
    star step initial t s ->
    (forall f, In (I_event f) t -> In f inputs) ->
    INV inputs s.
  Proof.
    intros Hg Hstar. induction Hstar as [ | t0 s' e s'' Hstar IH Hstep]; intros Hef.
    - apply INV_initial; exact Hg.
    - eapply step_preserves_INV with (s1 := s') (e := e).
      + exact Hg.
      + intros f Heq. apply Hef. subst e. left. reflexivity.
      + exact Hstep.
      + apply IH. intros f Hf. apply Hef. right. exact Hf.
  Qed.

  Lemma In_I_inputs_of (f : dfact) (t : list IO_event) :
    In (I_event f) t -> In f (inputs_of t).
  Proof.
    intros Hf. unfold inputs_of. apply in_flat_map.
    exists (I_event f). split; [exact Hf | left; reflexivity].
  Qed.

  Theorem produces_sound (inputs : list dfact) (R : rel) (args : list T) :
    good_input_facts inputs ->
    produces step initial inputs (normal_dfact R args) ->
    prog_impl rules_of (knows_datalog_fact inputs) (normal_fact R args).
  Proof.
    intros Hg (t & ns & Hstar & Hinp & Hout).
    destruct (output_decomp _ _ _ _ Hstar Hout) as (tpre & spost & Hspre & Hk & Hincl).
    assert (Hef : forall f, In (I_event f) tpre -> In f inputs).
    { intros f Hf. rewrite <- Hinp. apply Hincl. apply In_I_inputs_of. exact Hf. }
    pose proof (star_INV inputs tpre spost Hg Hspre Hef) as (Hs & Hmfc & Hmfok & Hsc).
    apply Hsc. split; [exact Hk | exact I].
  Qed.

  Theorem produces_complete (inputs : list dfact) (R : rel) (args : list T) :
    good_input_facts inputs ->
    prog_impl rules_of (knows_datalog_fact inputs) (normal_fact R args) ->
    produces step initial inputs (normal_dfact R args).
  Proof.
    intros Hg Hprog.
    pose proof (load_star inputs initial) as Hload.
    assert (Hinp0 : forall f, In (I_event f) (map I_event inputs : list IO_event) -> In f inputs).
    { intros f Hf. apply in_map_iff in Hf. destruct Hf as (x & Heq & Hin).
      inversion Heq. subst. exact Hin. }
    pose proof (star_INV inputs _ _ Hg Hload Hinp0)
      as (Hs & Hmfc & Hmfok & Hsc).
    assert (Hcompl : state_complete inputs (load inputs initial))
      by (apply comp_step_complete; assumption).
    destruct (Hcompl (normal_fact R args) Hprog) as (s' & Hcomp & Hderiv).
    destruct (comp_lift _ _ Hcomp) as (tc & Htc & Htcin & Htcout).
    exists (O_event tt [normal_dfact R args] :: tc ++ map I_event inputs), s'.
    split; [| split].
    - eapply star_step.
      + eapply star_app; [exact Hload | exact Htc].
      + apply step_output. exact Hderiv.
    - replace (inputs_of (O_event tt [normal_dfact R args] :: tc ++ map I_event inputs))
        with (inputs_of (tc ++ map I_event inputs)) by reflexivity.
      rewrite inputs_of_app, Htcin, inputs_of_map_I_event. reflexivity.
    - replace (outputs_of (O_event tt [normal_dfact R args] :: tc ++ map I_event inputs))
        with (normal_dfact R args :: outputs_of (tc ++ map I_event inputs)) by reflexivity.
      apply in_eq.
  Qed.
End __.
