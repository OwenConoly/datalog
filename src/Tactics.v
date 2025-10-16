From Stdlib Require Import Lists.List.
From ATL Require Import FrapWithoutSets Tactics.

Ltac specialize' H :=
  let hyp := fresh "hyp" in
  eassert _ as hyp;
  [clear H|specialize (H hyp); clear hyp].  

Ltac epose_dep H :=
  repeat lazymatch type of H with
  | ?A -> ?B => fail
  | forall _, _ => epose proof (H _) as H
  end.
