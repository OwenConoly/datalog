From Datalog.Util Require Import List.
From coqutil Require Import Datatypes.List Tactics.fwd.
From Stdlib Require Import List.

Module fset.
  Class impl {T : Type} :=
    { rep : Type;
      P : T -> bool;
      to_list : rep -> list T;
      of_list : list T -> rep;
    }.
  Arguments impl : clear implicits.
  #[global] Hint Mode impl + : typeclass_instances.
  #[local] Hint Mode impl - : typeclass_instances.
  Class ok {T} {impl : impl T} := {
      ext : forall s1 s2, same_set (to_list s1) (to_list s2) -> s1 = s2;
      to_list_of_list : forall s, same_set (to_list (of_list s)) (filter P s);
      of_list_to_list : forall s, of_list (to_list s) = s;
    }.
  Arguments ok {_} _.

  Class impl_with {T} (P : T -> bool) := { _impl : impl T }.
  #[global] Instance fset_with_inst {T} {i : impl T} : impl_with i.(P) := { _impl := _ }.

  Section __.
    Context {T} {impl : impl T} {ok : ok impl}.

    Definition has s x := In x (to_list s).

    Lemma has_ext s1 s2 :
      (forall x, P x = true ->
            (has s1 x <-> has s2 x)) ->
      s1 = s2.
    Proof.
      intros H. apply ext. cbv [same_set].
      intros x. rewrite <- of_list_to_list with (s := s1).
      rewrite <- of_list_to_list with (s := s2).
      do 2 rewrite to_list_of_list. do 2 rewrite filter_In. split; intros; fwd.
      - cbv [has] in H. rewrite <- H by assumption. auto.
      - cbv [has] in H. rewrite H by assumption. auto.
    Qed.
  End __.
End fset.

Definition fset T P {impl : fset.impl_with P} : Type := @fset.rep T impl.(fset._impl).
