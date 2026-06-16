(*worth comparing to https://compcert.org/doc/html/compcert.common.Smallstep.html*)
From Stdlib Require Import List.
Import ListNotations.
Section __.
  Context {state event : Type} (trace := list event)
          (step : state -> list event -> state -> Prop).
Inductive star : state -> trace -> state -> Prop :=
| star_refl s :
  star s [] s
| star_step s es s' t0 s'' :
  step s es s' ->
  star s' t0 s'' ->
  star s (es ++ t0) s''.
End __.
