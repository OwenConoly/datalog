From Stdlib Require Import List.
From Datalog.Util Require Import List.
Import ListNotations.

(*see also [fset] in Map.v.  maybe i will respect some convention where Prop-ish definitions have capital letters, and computable things have lowercase letters?  (like List.forallb vs List.Forall..?) *)

Module Mfset.
  Section one.
    Context {T : Type}.

    Definition Mfset := list (T * Prop).

    Definition union (X Y : Mfset) := X ++ Y.
    Definition filter P (X : Mfset) := map (fun '(x, Q) => (x, Q /\ P x)) X.
    Definition count (X : Mfset) x n := Existsn (fun '(x', Q) => x = x' /\ Q) n X.
    Definition has (X : Mfset) x := Exists (fun '(x', Q) => x = x' /\ Q) X.
    Definition of_list (l : list T) : Mfset := map (fun x => (x, True)) l.

    Fixpoint fold {A : Type} (f : A -> T -> A) (X : Mfset) (a : A) : A -> Prop :=
      match X with
      | (x, Q) :: X' => fun a' =>
                        Q /\ fold f X' (f a x) a' \/
                          ~Q /\ fold f X' a a'
      | [] => eq a
      end.

    Fixpoint dedup (X : Mfset) :=
      match X with
      | (x, Q) :: X' => (x, Q /\ ~has X' x) :: dedup X'
      | [] => []
      end.
  End one.
  Arguments Mfset : clear implicits.

  Section two.
    Context {A B : Type}.

    Definition map (f : A -> B) : Mfset A -> Mfset B := map (fun '(x, Q) => (f x, Q)).
  End two.
End Mfset. Abbreviation Mfset := Mfset.Mfset.
