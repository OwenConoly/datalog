(*https://inria.hal.science/hal-01966714/document*)
From Stdlib Require Import RelationClasses.

Module quot.
  (*putting proofs and non-proofs together, since i don't intend to do any computation here?*)
  Class quot {T : Type} {equiv : T -> T -> Prop} := {
      t : Type;
      repr : t -> T;
      pi : T -> t;
      reprK : forall x : t, pi (repr x) = x;
      equiv_correct : forall x y, equiv x y <-> pi x = pi y;
    }.
  Arguments quot : clear implicits.
End quot. Abbreviation quot := quot.quot.

Notation "T / equiv" := (@quot.t T equiv) : type_scope.
