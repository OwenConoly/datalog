From Datalog Require Import Datalog Blocks List Pftree Map.
From Stdlib Require Import List.

Module sblocks.
  Section __.
    Context `{params : datalog_params}.
    Context `{lvar : lrelT}.
    Definition inp_holds f :=
      match f with
      | fact.normal {| normal_fact.rel := block_rel.input R; normal_fact.args := args |} =>
          R (fact_args.normal args)
      | fact.meta {| meta_fact.pattern := {| fact_pattern.rel := block_rel.input R;
                                            fact_pattern.args := mf_args |};
                    meta_fact.set := st |} =>
          exists mf,
          R mf /\
            forall args,
              Forall2 value_pattern.matches mf_args args ->
              R (fact_args.normal args) <-> fset.contains st args
      | _ => False
      end.

    Print meta_rule.interp.

    Definition finiteness interp mr c hyps :=
      Forall
      meta_rule.pattern_interp mr pat (map meta_fact.pattern hyps) ->
      exists st,
        {|

    Fixpoint interp (p : blocks_prog (fact_args -> Prop)) :=
      match p with
      | LetIn x f => interp (f (interp x))
      | Block ret p =>
          (forall f,
  End __.
End sblocks.
