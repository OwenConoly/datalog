From coqutil Require Export Ltac2.
Ltac2 boolify (tac : unit -> 'a) : bool :=
  match Control.case tac with
  | Err _ => false
  | Val (_, _) => true
  end.
