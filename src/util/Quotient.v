(*https://inria.hal.science/hal-01966714/document*)
From Stdlib Require Import RelationClasses Morphisms.

Module quot.
  (*putting proofs and non-proofs together, since i don't intend to do any computation here?*)
  Class quot {T : Type} {equiv : T -> T -> Prop} := {
      t : Type;
      repr : t -> T;
      pi : T -> t;
      reprK : forall x : t, pi (repr x) = x;
      equiv_correct : forall x y, equiv x y <-> pi x = pi y;
    }.
  #[global] Hint Mode quot + + : typeclass_instances.
  #[local] Hint Mode quot - - : typeclass_instances.
  Arguments quot : clear implicits.
  Arguments t _ _ {_}.

  Section __.
    Context {T} {equiv : T -> T -> Prop} {q : quot T equiv}.

    Lemma equiv_eq (x y : t T equiv) :
      equiv (repr x) (repr y) ->
      x = y.
    Proof.
      intros. rewrite <- (reprK x), <- (reprK y).
      apply equiv_correct. assumption.
    Qed.
  End __.
End quot. Abbreviation quot := quot.quot.

Notation "T / equiv" := (@quot.t T equiv) : type_scope.
