From Datalog Require Import Datalog List Eqb.
From Stdlib Require Import List.
From coqutil Require Import Eqb.
Import ListNotations.

Module impl_rule.
  Section __.
    Context `{params : datalog_params}.
    Record impl_rule := mk
      { concls : list clause;
        hyps : list clause; }.
  End __.
End impl_rule. Abbreviation impl_rule := impl_rule.impl_rule.

Module prog.
  Section __.
    Context `{params : datalog_params}.
    Record prog := mk
      { inputs : list rel;
        rules : list impl_rule;
        outputs : list rel; }.
  End __.
End prog. Abbreviation prog := prog.prog.

Module srel.
  Variant srel : relT :=
    | eq
    | named (id : nat).

  Scheme Boolean Equality for srel.
  #[export] Instance eqb : Eqb srel := srel_beq.
  #[export] Instance eqb_ok : Eqb_ok eqb. Proof. eqb_ok. Qed.
End srel. Export (hints) srel. Abbreviation srel := srel.srel.

#[local] Existing Instance srel.

Module rewrite.
  Section __.
    Context `{params : datalog_params (_rel := srel) (rel_eqb := _) (rel_eqb_ok := _)}.
    Variant rewrite :=
      | dead_elim (R : rel)
      | headless_elim
      | dup_elim (R : rel) (idxs : list nat)
      | shard (R : rel) (idx : nat)
      | inline (concl : clause) (hyps : list clause) (*the relation had better only be concluded in this place*)
      | subst_eqs.

    Definition do_dead_elim (R : rel) (r : impl_rule) : list impl_rule :=
      [{| impl_rule.concls := filter (fun c => eqb c.(clause.rel) R) r.(impl_rule.concls);
         impl_rule.hyps := r.(impl_rule.hyps) |}].

    Definition do_headless_elim (r : impl_rule) : list impl_rule :=
      if is_nil r.(impl_rule.concls) then [] else [r].

    Definition do_dup_elim (R : rel) (idxs : list nat) (r : impl_rule) : list impl_rule. Admitted.

    Definition do_inline_hyp (inline_concl : clause) (inline_hyps : list clause) (hyp : clause) : list (clause (exprvar := (exprvar + exprvar)%type)) :=
      let marked_hyp := clause_varmap inr hyp in
      if eqb hyp.(clause.rel) inline_concl.(clause.rel) then
        let marked_inline_concl := clause_varmap inl inline_concl in
        let marked_inline_hyps := map (clause_varmap inl) inline_hyps in
        let eq_hyps := map2 (fun e1 e2 => {| clause.rel := srel.eq; clause.args := [e1; e2] |})
                         marked_hyp.(clause.args) marked_inline_concl.(clause.args) in
        marked_inline_hyps ++ eq_hyps
      else [marked_hyp].

    Definition do_inline (inline_concl : clause) (inline_hyps : list clause)

    Definition do_shard (R : rel) (idx : nat)

    Definition interp (r : rewrite) (r : rule) :=
      match
  End __.



Section __.
  Context
