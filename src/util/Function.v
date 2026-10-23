From coqutil Require Import Eqb.

Definition fun_put {A B} {eqbA : Eqb A} (f : A -> B) (a : A) (b : B) : A -> B :=
  fun x => if eqb x a then b else f x.
