From Datalog Require Import Datalog Blocks List Pftree.
From Stdlib Require Import List.

Section __.
  Context `{params : datalog_params}.

  (*add some arbitrary extensions Ps?  local because not used now*)
  #[local] Definition interp_step_with_extensions Ps p c hyps :=
    program.interp_step p c hyps \/ Exists (fun P => P c hyps) Ps.
End __.

Module fprog.
  Section __.
    Definition foo := tt.
  End __.
End fprog.
