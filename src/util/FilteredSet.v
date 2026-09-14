From Datalog.Util Require Import List.
From coqutil Require Import Datatypes.List Tactics.fwd.
From Stdlib Require Import List.

Module fset.
  Class impl {T : Type} :=
    { rep : Type;
      to_list : rep -> list T;
      of_list : list T -> rep;
    }.
  #[global] Hint Mode impl + : typeclass_instances.
  #[local] Hint Mode impl - : typeclass_instances.
  Arguments impl : clear implicits.

  Class ok {T P} {impl : impl T} := {
      ext : forall s1 s2, same_set (to_list s1) (to_list s2) -> s1 = s2;
      to_list_of_list : forall s, same_set (to_list (of_list s)) (filter P s);
      of_list_to_list : forall s, of_list (to_list s) = s;
    }.
  #[global] Hint Mode ok + - + : typeclass_instances.
  Arguments ok {_} _ _.

  Class impls {T} := { impl_with : (T -> bool) -> impl T }.
  #[global] Hint Mode impls + : typeclass_instances.
  #[local] Hint Mode impls - : typeclass_instances.
  Arguments impls : clear implicits.

  Class oks {T} {impls : impls T} := { ok_with : forall P, ok P (impl_with P) }.
  #[global] Hint Mode oks + + : typeclass_instances.
  Arguments oks {_} _.
  #[global] Existing Instance fset.ok_with.

  Section __.
    Context {T P} {impl : impl T} {ok : ok P impl}.

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
Definition fset T {impls : fset.impls T} P : Type := @fset.rep T (fset.impl_with P).
