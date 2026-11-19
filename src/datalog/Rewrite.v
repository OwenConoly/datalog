From Datalog Require Import Datalog List.
From Stdlib Require Import List.
From coqutil Require Import Eqb.
Import ListNotations.

Module impl_rule.
  Section __.
    Context `{params : datalog_params}.
    Record impl_rule :=
      { concls : list clause;
        hyps : list clause; }.
  End __.
End impl_rule. Abbreviation impl_rule := impl_rule.impl_rule.

Module prog.
  Section __.
    Context `{params : datalog_params}.
    Record prog :=
      { inputs : list rel;
        rules : list impl_rule;
        outputs : list rel; }.
  End __.
End prog. Abbreviation prog := prog.prog.

Module rewrite.
  Section __.
    Context `{params : datalog_params}.
    Variant rewrite :=
      | dead_elim (R : rel)
      | headless_elim
      | dup_elim (R : rel) (idxs : list nat)
      | shard (R : rel) (idx : nat)
      | inline (R : rel) (*had better only be concluded in one place*).

    Definition do_dead_elim (R : rel) (r : impl_rule) : list impl_rule :=
      [{| impl_rule.concls := filter (fun c => eqb c.(clause.rel) R) r.(impl_rule.concls);
         impl_rule.hyps := r.(impl_rule.hyps) |}].

    Definition do_headless_elim (r : impl_rule) : list impl_rule :=
      if is_nil r.(impl_rule.concls) then [] else [r].

    Definition do_dup_elim (R : rel) (idxs : list nat) (r : impl_rule) : list impl_rule. Admitted.

    Definition do_shard (R : rel) (idx : nat)

    Definition interp (r : rewrite) (r : rule) :=
      match
  End __.



Section __.
  Context
