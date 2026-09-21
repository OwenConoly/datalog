From Datalog Require Import Datalog Blocks List Pftree Map.
From Stdlib Require Import List.

Module result.
  Section __. Context `{params : datalog_params}.
  Record result :=
    { normals : list value -> Prop;
      done_pats : list value_pattern -> Prop }.
  End __.
End result. Abbreviation result := result.result.

Section __. Context `{params : datalog_params}.
  Definition closed mr P :=
    forall pat hyps,
      meta_rule.pattern_interp mr pat (map meta_fact.pattern hyps) ->
      Forall P hyps ->
      exists st,
        P (meta_fact.mk pat st).

  Definition closed' mrs P :=
    Forall (fun mr => closed mr P) mrs.
End __.

Module sblocks.
  Section __.
    Context `{params : datalog_params}.
    Context `{lvar : lrelT}.
    Definition inp_holds f :=
      match f with
      | fact.normal {| normal_fact.rel := block_rel.input R; normal_fact.args := args |} =>
          R.(result.normals) args
      | fact.meta {| meta_fact.pattern := {| fact_pattern.rel := block_rel.input R;
                                            fact_pattern.args := mf_args |};
                    meta_fact.set := st |} =>
          R.(result.done_pats) mf_args /\
            forall args,
              Forall2 value_pattern.matches mf_args args ->
              R.(result.normals) args <-> fset.contains st args
      | _ => False
      end.

    (*TODO in which places should this replace interp_blocks_prog?  almost everywhere?*)
    Print interp_blocks_prog.
    Fixpoint interp (p : blocks_prog result) :=
      match p with
      | LetIn x f => interp (f (interp x))
      | Block ret p =>
          {| result.normals :=
              fun args => program.interp p inp_holds
                         (fact.normal
                            {| normal_fact.rel := block_rel.local ret;
                              normal_fact.args := args |});
            result.done_pats :=
              fun pat =>
                closed' p.(program.meta_rules) (fun mf => program.interp p inp_holds (fact.meta mf)) ->
                exists st,
                  program.interp p inp_holds
                    (fact.meta
                       (meta_fact.mk
                          {| fact_pattern.rel := block_rel.local ret;
                            fact_pattern.args := pat |}
                          st))
            |}
      end.
  End __.
End sblocks.
