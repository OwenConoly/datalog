From Stdlib Require Import Lists.List.
From ATL Require Import FrapWithoutSets Tactics.

Ltac specialize' H :=
  let hyp := fresh "hyp" in
  eassert _ as hyp;
  [clear H|specialize (H hyp); clear hyp].  

Ltac destruct_option_map_Some :=
  match goal with
  | H: option_map ?f ?x = Some ?y |- _ =>
      destruct x eqn:?E; [cbn [option_map] in H; invert H|discriminate H]
  end.

Ltac invert_list_stuff :=
  repeat match goal with
  | H : Forall2 _ (cons _ _) _ |- _ => invert H
  | H : Forall2 _ _ (cons _ _) |- _ => invert H
  | H : Forall2 _ nil _ |- _ => invert H
  | H : Forall2 _ _ nil |- _ => invert H
  | H : Exists _ nil |- _ => invert H
  | H : Exists _ (cons _ nil) |- _ => invert H
  | _ => destruct_option_map_Some
  end.
