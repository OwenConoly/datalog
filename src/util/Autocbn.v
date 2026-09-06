(*https://github.com/mit-plv/fiat-crypto/blob/master/src/Util/Tactics/DestructHyps.v ?*)
From coqutil Require Import Ltac2.
Ltac2 mutable to_cbn () : Std.reference list := [].

Ltac2 x () := cbn [Nat.succ].
Print Ltac2 x.
(*should be the same flags passed by cbn [refs]*)
Ltac2 default_redflags_of (refs : Std.reference list) :=
  { Std.rStrength := Std.Norm;
    Std.rBeta := true;
    Std.rMatch := true;
    Std.rFix := true;
    Std.rCofix := true;
    Std.rZeta := true;
    Std.rDelta := false;
    Std.rConst := refs }.

(*as in https://rocq-prover.org/doc/v8.15/stdlib/Ltac2.Notations.html*)
Ltac2 Notation "cbn_list" cl(opt(clause)) :=
  fun s => Std.cbn (default_redflags_of s) (default_on_concl cl).
Ltac2 Check default_on_concl.
Print Ltac2 Type Std.clause.
Ltac2 y () := cbn in *.
Print Ltac2 y.

Ltac2 autocbn0 () := Std.cbn (default_redflags_of (to_cbn ())) { Std.on_hyps := None; Std.on_concl := Std.AllOccurrences }.

Ltac2 Notation autocbn := autocbn0 ().
Ltac autocbn := ltac2:(autocbn).

Ltac2 Set to_cbn as prev := fun _ => reference:(fst) :: reference:(snd) :: prev ().

Goal forall x : nat * nat, fst x = 5.
  autocbn.
  intros [? ?]. autocbn.
Abort.
