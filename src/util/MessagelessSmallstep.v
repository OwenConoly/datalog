From Datalog Require Import Relations.

Section step.
  Context {state label : Type}.
  Context (step : state -> label -> state -> Prop).

  Definition any_step s s' := exists lbl, step s lbl s'.

  Definition will_step s (P : state -> Prop) : Prop :=
    exists lbl,
    forall s',
      any_step^* s s' ->
      P s' \/ exists s'', step s' lbl s'' /\ P s''.
End step.
