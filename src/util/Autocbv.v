From coqutil Require Import Ltac2.
Ltac2 mutable to_cbv () : Std.reference list := [].

Ltac2 cbv_redflags_of (refs : Std.reference list) :=
  { Std.rStrength := Std.Norm;
    Std.rBeta := true;
    Std.rMatch := true;
    Std.rFix := true;
    Std.rCofix := true;
    Std.rZeta := true;
    Std.rDelta := false;
    Std.rConst := refs }.

Ltac2 autocbv1 () := Std.cbv (cbv_redflags_of (to_cbv ())) { Std.on_hyps := None; Std.on_concl := Std.AllOccurrences }.

Ltac2 autocbv0 () := Control.enter (fun () => autocbv1 ()).

Ltac2 Notation autocbv := autocbv0 ().
Ltac autocbv := ltac2:(autocbv).
