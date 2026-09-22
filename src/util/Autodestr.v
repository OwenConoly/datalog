(*https://github.com/mit-plv/fiat-crypto/blob/master/src/Util/Tactics/DestructHyps.v ?*)
From Datalog Require Import Ltac2.
Ltac2 mutable to_destruct () : (constr -> bool) list := [].

Ltac2 Check Pattern.matches.
Ltac2 Eval Pattern.matches pat:(?x) constr:(nat).
Ltac2 pattern_pred p c := boolify (fun _ => Pattern.matches p c).

Ltac2 Set to_destruct as to_destruct' := fun _ => pattern_pred pat:(prod _ _) :: to_destruct' ().

Ltac2 y () := destruct z, w.
Print Ltac2 y.
Ltac2 simple_induction_clause (id : ident) : Std.induction_clause :=
  { Std.indcl_arg := Std.ElimOnIdent id;
    Std.indcl_eqn := None;
    Std.indcl_as := None;
    Std.indcl_in := None; }.

Ltac2 simple_destruct (ids : ident list) :=
  match ids with
  | [] => ()
  | _ :: _ => destruct0 false (List.map simple_induction_clause ids) (fun _ => None)
  end.

Ltac2 matching_hyps (ts : (constr -> bool) list) :=
  List.filter (fun (_, _, t) => List.exist (fun test => test t) ts) (Control.hyps ()).

(*[destruct] cannot clear a section variable, so it would case-analyse the goal
  and leave the variable in place, and [simp] would fire on it forever*)
Ltac2 matching_hyp_ids ts :=
  List.filter (fun id => Bool.neg (is_section_var id))
    (List.map (fun (name, _, _) => name) (matching_hyps ts)).

Ltac2 destruct_matching_hyps ts :=
  simple_destruct (matching_hyp_ids ts).

Ltac2 autodestr0 () := Control.enter (fun () => destruct_matching_hyps (to_destruct ())).

Ltac2 Notation autodestr := autodestr0 ().
Ltac autodestr := ltac2:(autodestr).
Goal forall x : nat * nat, nat.
  autodestr.
  intros.
  autodestr.
Abort.

Section SectionVar.
  Context (p : nat * nat).
  Goal fst p = fst p.
    repeat (progress autodestr).
  Abort.
End SectionVar.
