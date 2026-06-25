From Stdlib Require Import List.
From Datalog Require Import Datalog Operational Smallstep.
From coqutil Require Import Map.Interface.
Import ListNotations.

Section __.
  Context {rel : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map exprvar T}.
  Context (is_input : rel -> bool).
  Context (R_senders : rel -> list nat).
  Context (p : prog).

  Variant io_label :=
    | L_learn (n : nat) (f : dfact)   (* rule [n] received (learned) fact [f] *)
    | L_fire (n : nat) (f : dfact)    (* rule [n] derived and broadcast fact [f] *)
    | L_output (f : dfact).           (* emit the known fact [f] *)

  Definition learn_fact_at_rule_f (f : dfact) (s1 s2 : node_state) : Prop :=
    exists l1 l2,
      s2.(known_facts) = f :: s1.(known_facts) /\
      s1.(waiting_facts) = l1 ++ f :: l2 /\
      s2.(waiting_facts) = l1 ++ l2 /\
      s2.(sent_facts) = s1.(sent_facts).

  Lemma learn_fact_at_rule_iff s1 s2 :
    learn_fact_at_rule s1 s2 <-> exists f, learn_fact_at_rule_f f s1 s2.
  Proof.
    unfold learn_fact_at_rule, learn_fact_at_rule_f. split.
    - intros (l1 & x & l2 & H). exists x, l1, l2. exact H.
    - intros (f & l1 & l2 & H). exists l1, f, l2. exact H.
  Qed.

  Inductive comp_step_with_label : state -> io_label -> state -> Prop :=
  | cwl_learn n f s1 s2 :
    stepWithLabel (fun k rs rs' => k = n /\ learn_fact_at_rule_f f rs rs')
                  (seq 0 (length s1)) s1 s2 ->
    comp_step_with_label s1 (L_learn n f) s2
  | cwl_fire n f s1 s2 :
    stepWithLabel (fun '(r, k) rs rs' => k = n /\ fire_at_rule is_input R_senders p r k rs rs' f)
                  (combine p.(non_meta_rules) (seq 0 (length s1))) s1 s2 ->
    comp_step_with_label s1 (L_fire n f) (map (add_waiting_fact f) s2).

  Lemma comp_step_with_label_iff s1 s2 :
    comp_step is_input R_senders p s1 s2 <->
    exists lbl, comp_step_with_label s1 lbl s2.
  Proof.
    split.
    - intros Hcs. inversion Hcs as [sa sb Hone | nf sa sb Hswl]; subst.
      + destruct Hone as (l1 & x & y & l2 & -> & -> & Hlfar).
        apply learn_fact_at_rule_iff in Hlfar as (f & Hlf).
        exists (L_learn (length l1) f). apply cwl_learn.
        apply stepWithLabel_seq_intro. split; [reflexivity | exact Hlf].
      + destruct Hswl as (la & (r0 & k0) & x & y & lb & Hc & Hsm & Hbody).
        exists (L_fire k0 nf). apply cwl_fire. unfold stepWithLabel.
        exists la, (r0, k0), x, y, lb.
        split; [exact Hc | split; [exact Hsm | split; [reflexivity | exact Hbody]]].
    - intros (lbl & Hcwl). destruct lbl as [n f | n f | f].
      + inversion Hcwl; subst.
        match goal with H : stepWithLabel _ _ _ _ |- _ =>
          apply stepWithLabel_seq_elim in H as (l1 & x & y & l2 & k & -> & -> & (_ & Hlf)) end.
        apply learn_fact. exists l1, x, y, l2.
        split; [reflexivity | split; [reflexivity |]].
        apply learn_fact_at_rule_iff. exists f. exact Hlf.
      + inversion Hcwl; subst. apply fire_rule.
        match goal with H : stepWithLabel _ _ _ _ |- _ =>
          destruct H as (la & (r0 & k0) & x & y & lb & Hc & Hsm & (_ & Hbody)) end.
        unfold stepWithLabel. exists la, (r0, k0), x, y, lb.
        split; [exact Hc | split; [exact Hsm | exact Hbody]].
      + inversion Hcwl.
  Qed.

  Local Notation IO_event := (Smallstep.IO_event io_label dfact).

  Inductive step : state -> IO_event -> state -> Prop :=
  | step_comp s1 lbl s2 :
    comp_step_with_label s1 lbl s2 ->
    step s1 (O_event lbl []) s2
  | step_input s f :
    step s (I_event f) (map (add_waiting_fact f) s)
  | step_output s f :
    knows_dfact s f ->
    step s (O_event (L_output f) [f]) s.

  Definition allowed : list dfact -> Prop := good_input_facts is_input.

  Definition empty_node_state : node_state :=
    {| known_facts := []; waiting_facts := []; sent_facts := [] |}.

  Definition initial : state := repeat empty_node_state (length p.(non_meta_rules)).

  Lemma step_input_total : input_total step.
  Proof. intros s m. eexists. apply step_input. Qed.


End __.
