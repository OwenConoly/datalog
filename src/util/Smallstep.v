(*worth comparing to https://compcert.org/doc/html/compcert.common.Smallstep.html*)
From Stdlib Require Import List.
Import ListNotations.
Section __.
  Context {state event : Type} (trace := list event) (step : state -> option event -> state -> Prop).
  Search (option _ -> list _ -> list _).
  Definition option_cons {T} (a : option T) (l : list T) :=
    match a with
    | Some b => b :: l
    | None => l
    end.
Inductive star : state -> trace -> state -> Prop :=
| star_refl s :
  star s [] s
| star_step s e s' t0 s'' t :
  step s e s' ->
  star s' t0 s'' ->
  t = option_cons e t0 ->
  star s t s''.
End __.
