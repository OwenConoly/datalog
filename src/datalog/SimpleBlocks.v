From Datalog Require Import Datalog Blocks List.
From Stdlib Require Import List.
Check blocks_prog.

Module simple_args.
  Section __.
    Context `{params : datalog_params}.
    Variant simple_args :=
      | normal (nf : list value)
      | meta (pattern : list value_pattern).
  End __.
End simple_args. Notation simple_args := simple_args.simple_args.

Module simple.
  Section __.
    Context `{params : datalog_params}.
    Context {lvar : Type}.
    Fixpoint interp_blocks_prog (e : blocks_prog (lvar := lvar) (simple_args -> Prop)) : simple_args -> Prop :=
      match e with
      | LetIn x f =>
          interp_blocks_prog (f (interp_blocks_prog x))
      | Block ret inputs p =>
          fun args =>
            program.interp p
              (fun f =>
                 match f with
                 | .normal nf => R' nf
                 |
                 Exists (fun '(R, R') => input R = fact.rel f /\ R' (fact.args_of f)) inputs)
              (fact.of_args (local ret) args)
      end.
