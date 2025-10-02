From Stdlib Require Import Lists.List.
From ATL Require Import FrapWithoutSets Tactics.

Ltac specialize' H :=
  let hyp := fresh "hyp" in
  eassert _ as hyp;
  [clear H|specialize (H hyp); clear hyp].  

Ltac invert_list_stuff :=
  match goal with
  | H : Forall2 _ (cons _ _) _ |- _ => invert H
  | H : Forall2 _ _ (cons _ _) |- _ => invert H
  | H : Forall2 _ nil _ |- _ => invert H
  | H : Forall2 _ _ nil |- _ => invert H
  | H : Exists _ nil |- _ => invert H
  | H : Exists _ (cons _ nil) |- _ => invert H
  end.
