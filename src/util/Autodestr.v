(*https://github.com/mit-plv/fiat-crypto/blob/master/src/Util/Tactics/DestructHyps.v ?*)
From coqutil Require Import Ltac2.
Ltac2 mutable to_destruct () : constr list := [].
Ltac2 Set to_destruct as old_to_destruct := fun _ => constr:(prod nat nat) :: old_to_destruct ().

Ltac2 Check destruct0.
Print Std.induction_clause.
Ltac2 y () := destruct z, w.
Print Ltac2 y.
Ltac2 simple_induction_clause (id : ident) : Std.induction_clause :=
  { Std.indcl_arg := Std.ElimOnIdent id;
    Std.indcl_eqn := None;
    Std.indcl_as := None;
    Std.indcl_in := None; }.

Ltac2 simple_destruct (ids : ident list) :=
  destruct0 false (List.map simple_induction_clause ids) (fun _ => None).

Ltac2 Check Control.hyps.
Ltac2 Check List.exist.
Ltac2 matching_hyps (ts : constr list) :=
  List.filter (fun (_, _, t) => List.exist (Constr.equal t) ts) (Control.hyps ()).

Ltac2 matching_hyp_ids ts :=
  List.map (fun (name, _, _) => name) (matching_hyps ts).

Ltac2 destruct_matching_hyps ts :=
  simple_destruct (matching_hyp_ids ts).

Ltac2 autodestr0 () := destruct_matching_hyps (to_destruct ()).

Ltac2 Notation autodestr := autodestr0 ().
Ltac2 Eval matching_hyp_ids (to_destruct ()).

Goal forall x : nat * nat, nat.
  Ltac2 Eval matching_hyp_ids (to_destruct ()).
  intros.
  Ltac2 Eval matching_hyp_ids (to_destruct ()).
  Ltac2 Eval Control.hyps ().
  autodestr.
