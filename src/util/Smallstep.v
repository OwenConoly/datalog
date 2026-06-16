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
