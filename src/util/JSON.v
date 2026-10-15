From JSON Require Import Encode.
From Stdlib Require Import List String.
From coqutil Require Import Map.Interface.
Import ListNotations.
Local Open Scope string_scope.

#[export] Instance JEncode__pair {A B} `{JEncode A} `{JEncode B} : JEncode (A * B) :=
  fun '(a, b) => JSON__Array [encode a; encode b].

#[export] Instance JEncode__sum {A B} `{JEncode A} `{JEncode B} : JEncode (A + B) :=
  fun ab =>
  match ab with
  | inl a => JSON__Object [("inl", encode a)]
  | inr b => JSON__Object [("inr", encode b)]
  end.

#[export] Instance JEncode__map {K V} {M : map.map K V} `{JEncode K} `{JEncode V} : JEncode M :=
  fun m => encode (map.tuples m).
