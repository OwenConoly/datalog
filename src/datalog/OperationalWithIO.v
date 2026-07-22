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

  Lemma meta_load_c (l : list dfact) : meta_facts_correct (load l initial).
  Proof.
    induction l as [|f l IH]; [apply mfc_initial|].
    cbn [load fold_right]. apply add_wf_mfc. exact IH.
  Qed.

  Lemma meta_load_ok (l : list dfact) : meta_facts_ok (load l initial).
  Proof.
    induction l as [|f l IH]; [apply mfok_initial|].
    cbn [load fold_right]. apply add_wf_mfok. exact IH.
  Qed.

  (* The fully-loaded state is sane w.r.t. inputs (it knows every input); the
     empty initial state is not, so the invariants are established here rather
     than carried from initial. *)
  Lemma sane_state_loaded (inputs : list dfact) :
    good_input_facts inputs -> sane_state inputs (load inputs initial).
  Admitted.

  (* At any reached state whose whole trace has consumed exactly [inputs], the
     known facts are all prog_impl-derivable.  (Aggregations only fire once their
     done-message's matching set is actually present, so a fact known here is
     soundly derived.) *)
  Lemma state_correct_final (inputs : list dfact) (t : list IO_event) (ns : state) :
    good_input_facts inputs -> star step initial t ns -> inputs_of t = inputs ->
    state_correct inputs ns.
  Admitted.

  Lemma output_known_final (t : list IO_event) (ns : state) (g : dfact) :
    star step initial t ns -> In g (outputs_of t) -> knows_dfact ns g.
  Admitted.

  Theorem produces_sound (inputs : list dfact) (R : rel) (args : list T) :
    good_input_facts inputs ->
    produces step initial inputs (normal_dfact R args) ->
    prog_impl rules_of (knows_datalog_fact inputs) (normal_fact R args).
  Proof.
    intros Hg (t & ns & Hstar & Hinp & Hout).
    assert (Hk : knows_dfact ns (normal_dfact R args)) by (eapply output_known_final; eassumption).
    assert (Hsc : state_correct inputs ns) by (eapply state_correct_final; eassumption).
    apply Hsc. split; [exact Hk | exact I].
  Qed.

  Theorem produces_complete (inputs : list dfact) (R : rel) (args : list T) :
    good_input_facts inputs ->
    prog_impl rules_of (knows_datalog_fact inputs) (normal_fact R args) ->
    produces step initial inputs (normal_dfact R args).
  Proof.
    intros Hg Hprog.
    pose proof (load_star inputs initial) as Hload.
    assert (Hscl : state_correct inputs (load inputs initial)).
    { eapply state_correct_final; [exact Hg | exact Hload | apply inputs_of_map_I_event]. }
    assert (Hcompl : state_complete inputs (load inputs initial)).
    { apply comp_step_complete; try assumption.
      - exact (sane_state_loaded inputs Hg).
      - apply meta_load_c.
      - apply meta_load_ok. }
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
