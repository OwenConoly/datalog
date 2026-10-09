From Datalog Require Import Datalog Blocks List Pftree Map.
From Stdlib Require Import List.

Module blocks_prog.
  Import blocks_prog.
  Section __.
    Context `{params : datalog_params}.
    Context `{lvar : lrelT}.

    Definition inp_pat_holds pat :=
      match pat.(fact_pattern.rel) with
      | block_rel.local _ => False
      | block_rel.input r => r.(result.done) pat.(fact_pattern.args)
      end.

    Fixpoint simple_interp (p : blocks_prog result) :=
      match p with
      | LetIn x f => simple_interp (f (simple_interp x))
      | Block ret p =>
          {| result.normal :=
              fun nf_args =>
                program.interp p inp_holds (fact.normal {| normal_fact.rel := block_rel.local ret; normal_fact.args := nf_args |});
            result.done :=
              fun mf_args =>
                pftree (fun c hs => Exists (fun mr => meta_rule.pattern_interp mr c hs) p.(program.meta_rules))
                  inp_pat_holds
                  {| fact_pattern.rel := block_rel.local ret; fact_pattern.args := mf_args |}
          |}
      end.
  End __.
End blocks_prog.
