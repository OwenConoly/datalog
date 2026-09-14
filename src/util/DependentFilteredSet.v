From Datalog.Util Require Import List.
From coqutil Require Import Datatypes.List Tactics.fwd.
From Stdlib Require Import List.

Module sfset.
  Class impl {T U : Type} {P : T -> U -> bool} :=
    { rep : Type;
      to_pair : rep -> T * list U;
      of_pair : T * list U -> rep;
    }.
  Arguments impl {_ _} _.
  #[global] Hint Mode impl + + + : typeclass_instances.
  #[local] Hint Mode impl - - - : typeclass_instances.

  Class ok {T U} {P : T -> U -> bool} {impl : impl P} := {
      ext : forall s1 s2,
        fst (to_pair s1) = fst (to_pair s2) ->
        same_set (snd (to_pair s1)) (snd (to_pair s2)) ->
        s1 = s2;
      to_pair_of_pair_fst : forall s, fst (to_pair (of_pair s)) = fst s;
      to_pair_of_pair_snd : forall s, same_set (snd (to_pair (of_pair s))) (filter (P (fst s)) (snd s));
      of_list_to_list : forall s, of_pair (to_pair s) = s;
    }.
  Arguments ok {_ _ _} _.

  Section __.
    Context {T U} {P : T -> U -> bool} {impl : impl P} {ok : ok impl}.

    Definition has s x := In x (to_pair s).

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

Definition fset T P {impl : fset.impl T P} : Type := @fset.rep T P _.
