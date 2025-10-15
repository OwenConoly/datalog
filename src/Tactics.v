From Stdlib Require Import Lists.List.
From ATL Require Import FrapWithoutSets Tactics.

Ltac specialize' H :=
  let hyp := fresh "hyp" in
  eassert _ as hyp;
  [clear H|specialize (H hyp); clear hyp].  
