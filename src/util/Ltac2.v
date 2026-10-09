From coqutil Require Export Ltac2.
Ltac2 boolify (tac : unit -> 'a) : bool :=
  match Control.case tac with
  | Err _ => false
  | Val (_, _) => true
  end.

Ltac2 is_section_var (id : ident) : bool :=
  match Env.get [id] with
  | Some (Std.VarRef _) => true
  | _ => false
  end.
