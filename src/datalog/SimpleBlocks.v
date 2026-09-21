From Datalog Require Import Datalog Blocks List Pftree.
From Stdlib Require Import List.



Print block_rel.
Print program.interp. Print program.interp_step.
P c hs ->
  forall hs,

Module sargs.
  Section __.
    Context `{params : datalog_params}.
    Variant sargs :=
      | normal (nf : list value)
      | meta (mf_args : meta_args)
      | done_with (p : list value_pattern).
  End __.
End sargs. Abbreviation sargs := sargs.sargs.

Module sfact.
  Section __.
    Context `{params : datalog_params} {lrel : lrelT}.
    Remove Hints _rel : typeclass_instances.

    Variant sfact {var} :=
      | normal (nf : normal_fact (relt := block_rel var))
      | meta (mf : meta_fact (_rel := block_rel var))
      | done_with (p : fact_pattern (relt := block_rel var)).
  End __.
  Arguments sfact {_ _ _ _} _.
End sfact. Abbreviation sfact := sfact.sfact.

Module srule.
  Section __.
    Context `{params : datalog_params} {lrel : lrelT}.
    Remove Hints _rel : typeclass_instances.
    Context {var : Type}.

    Inductive interp_step (sblock : block_program var) (f : sfact var) :=
    | rstep :

Module sblocks.
  Section __.
    Context `{params : datalog_params}. Print blocks_prog.
    Context `{lvar : lrelT}.
    Fixpoint interp_blocks_prog (e : blocks_prog (simple_args -> Prop)) : simple_args -> Prop :=
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
