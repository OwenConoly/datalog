From coqutil Require Import Semantics.OmniSmallstepCombinators.

Section EventuallyInd.
  Context [State : Type] (step : State -> (State -> Prop) -> Prop).
  Context (step_weaken :
             forall s (P Q : State -> Prop),
               (forall x, P x -> Q x) -> step s P -> step s Q).

  Check eventually_ind.
  Lemma eventually_ind' (P Q : State -> Prop)
    (Hdone : forall s, P s -> Q s)
    (Hstep : forall s, step s (fun s' => eventually step P s' /\ Q s') -> Q s) :
    forall s, eventually step P s -> Q s.
  Proof.
    intros s He. induction He as [s HP | s midset Hms Hrec IH].
    - exact (Hdone _ HP).
    - apply Hstep. eapply step_weaken; [| exact Hms].
      intros x Hx. split; [exact (Hrec x Hx) | exact (IH x Hx)].
  Qed.
End EventuallyInd.
