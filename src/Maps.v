(*TODO probably arbitrary key and value types*)
(*probably i should get rid of this and use somebody else's implementation of maps?
  - FRAP fmaps are no good, since i can't iterate over them
  - coqutil maps are probably a good option, but obviously a pain to work with
    compared to functions
 *)

From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Coq Require Import ZArith.Zdiv.
From Coq Require Import ZArith.Int.
From Coq Require Import ZArith.Znat.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.

Import ListNotations.
Require Import ContextsAgree.

From Coq Require Import Arith.PeanoNat. Import Nat. Check S.
Import Datatypes. Check S.

Definition var : Set := string + nat.

Definition var_eqb (x y : var) : bool :=
  match x, y with
  | inl x, inl y => x =? y
  | inr x, inr y => Nat.eqb x y
  | _, _ => false
  end.
Lemma var_eqb_refl x :
  var_eqb x x = true.
Proof.
  destruct x; simpl.
  - apply String.eqb_refl.
  - apply Nat.eqb_refl.
Qed.

Lemma var_eqb_eq x y :
  var_eqb x y = true ->
  x = y.
Proof.
  cbv [var_eqb]. intros H. destruct x, y; try congruence; f_equal.
  - apply String.eqb_eq in H. auto.
  - apply Nat.eqb_eq in H. auto.
Qed.

Section Map.
Context {fn : Type}.

Definition map_empty : var -> option fn := fun _ => None.

Definition map_cons (x : var) (y : option fn) (m : var -> option fn) :=
  fun v => if var_eqb x v then y else m v.

Definition removemany (vs : list var) (s : var -> option fn) :=
  fold_right (fun v s => map_cons v None s) s vs.

Definition putmany (vs : list var) (s : var -> option fn) : var -> option fn. Admitted.
End Map.

