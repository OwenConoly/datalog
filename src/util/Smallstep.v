(*worth comparing to https://compcert.org/doc/html/compcert.common.Smallstep.html*)
From Stdlib Require Import List.
Import ListNotations.
Section __.
  Context {state event : Type} (trace := list event)
          (step : state -> event -> state -> Prop).
Inductive star : state -> trace -> state -> Prop :=
| star_refl s :
  star s [] s
| star_step s e s' t0 s'' :
  step s e s' ->
  star s' t0 s'' ->
  star s (e :: t0) s''.
End __.

Section __.
  Context {state event : Type}.
  Context (step : state -> event -> state -> Prop).
  Context (guaranteed : list event -> event -> Prop).

  (*the angel can step to the postcondition regardless of the demon's actions*)
  Definition can_step '(s, t) (P : state * list event -> Prop) : Prop :=
    forall s' t',
      star step s t' s' ->
      exists s'' e,
        guaranteed (t' ++ t) e /\
          step s' e s'' /\
          P (s'', e :: t' ++ t).
End __.
