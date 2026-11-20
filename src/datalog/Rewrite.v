From Stdlib Require Import List.
From coqutil Require Import Eqb Datatypes.List Map.Interface Map.Properties.
From Datalog Require Import Datalog List Eqb Default FancyNotations Map MapInstances RelMap.
Import ListNotations.

Module impl_rule.
  Section __.
    Context `{params : datalog_params}.
    Record impl_rule := mk
      { concls : list clause;
        hyps : list clause; }.

    Definition all_exprvars r :=
      flat_map clause.vars r.(concls) ++ flat_map clause.vars r.(hyps).
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

Section NattifyExprvars.
  Context `{params : datalog_params}.

  Definition exprvar_table (r : impl_rule) : list exprvar :=
    dedup (impl_rule.all_exprvars r).

  Definition encode_rel (table : list exprvar) (v : exprvar) : nat :=
    unwrap_or (length table) (index_of v table).

  Definition nattify_rule_exprvars (r : impl_rule) :=
    let tbl := exprvar_table r in
    {| impl_rule.concls := map (clause_varmap (encode_rel tbl)) r.(impl_rule.concls);
      impl_rule.hyps := map (clause_varmap (encode_rel tbl)) r.(impl_rule.hyps) |}.
End NattifyExprvars.

#[local] Existing Instance srel.

#[local] Instance nat_var : exprvarT := nat.
#[global] Typeclasses Transparent nat_var.

Module arith.
  Inductive arith :=
  | var : nat -> arith
  | plus : arith -> arith -> arith
  | const : nat -> arith.
  Arguments arith : clear implicits.

  Fixpoint interp (substn : nat -> nat) (e : arith) :=
    match e with
    | var v => substn v
    | plus e1 e2 => interp substn e1 + interp substn e2
    | const c => c
    end.

  Fixpoint vars (e : arith) :=
    match e with
    | var v => [v]
    | plus a b => vars a ++ vars b
    | const _ => []
    end.
End arith. Abbreviation arith := arith.arith.

Module rewrite.
  Section __.
    Context `{params : datalog_params (_rel := srel) (rel_eqb := _) (rel_eqb_ok := _)
                         (_exprvar := nat_var) (var_eqb := _) (var_eqb_ok := _)}.
    Context {map_expr_arith : map.map expr arith} {map_expr_nat : map.map expr nat}.

    Variant rewrite :=
      | dead_elim (R : rel)
      | headless_elim
      | dup_elim (R : rel) (idxs : list nat)
      | shard (num_shards : nat) (idxs : rel -> list nat)
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

    Definition do_inline (inline_concl : clause) (inline_hyps : list clause) (r : impl_rule) : list (impl_rule (_exprvar := (exprvar + exprvar)%type)) :=
      [{| impl_rule.concls := map (clause_varmap inr)
                               (filter (fun c => negb (eqb c.(clause.rel) inline_concl.(clause.rel))) r.(impl_rule.concls));
        impl_rule.hyps := flat_map (do_inline_hyp inline_concl inline_hyps) r.(impl_rule.hyps); |}].

    Definition get_shard_pat (idxs : rel -> list nat) (*which argument of this relation to shard*) (r : impl_rule) : partial_map expr(*which argument *) arith(*goes to which shard*) :=
      let args :=
        flat_map
          (fun c =>
             filter_map
               (fun '(i, arg) => if inb i (idxs c.(clause.rel)) then Some arg else None)
               (enumerate O c.(clause.args)))
          (r.(impl_rule.concls) ++ r.(impl_rule.hyps)) in
      let args := dedup args in
      map.of_list (map (fun '(i, arg) => (arg, arith.var i)) (enumerate O args)).

    (*TODO*)
    Definition optimize_shard_pat (pat : partial_map expr arith) := pat.

    Definition vars_of_pat (pat : partial_map expr arith) : list nat :=
      dedup (flat_map arith.vars (values pat)).

    Definition substns (pat : partial_map expr arith) (num_shards : nat) : list (partial_map expr nat) :=
      let vs := vars_of_pat pat in
      let substns := cartesian_prod (repeat (seq O num_shards) (length vs)) in
      map (fun substn => map.map_values (arith.interp (get_or_default (map.of_list (combine vs substn)))) pat) substns.

    Definition new_relname (idxs : rel -> list nat) (shard_pat : partial_map expr nat) (c : clause) :=
      let rel_idxs :=
        filter_map
          (fun '(i, arg) => if inb i (idxs c.(clause.rel)) then Some (get_or_default shard_pat arg) else None)
          (enumerate O c.(clause.args)) in
      (c.(clause.rel), rel_idxs).

    Definition index_rel_of_clause (idxs : rel -> list nat) (shard_pat : partial_map expr nat) (c : clause) :=
      {| clause.rel := new_relname idxs shard_pat c;
        clause.args := c.(clause.args) |}.

    Definition index_rels_of_rule (idxs : rel -> list nat) (shard_pat : partial_map expr nat) (r : impl_rule) :=
      {| impl_rule.concls := map (index_rel_of_clause idxs shard_pat) r.(impl_rule.concls);
        impl_rule.hyps := map (index_rel_of_clause idxs shard_pat) r.(impl_rule.hyps); |}.

    Definition apply_shard_pat (idxs : rel -> list nat) (num_shards : nat) (pat : partial_map expr arith) (r : impl_rule) : list (impl_rule (_rel := (rel * list nat)%type)) :=
      map (fun shard_pat => index_rels_of_rule idxs shard_pat r) (substns pat num_shards).

    Definition do_shard num_shards idxs r :=
      let shard_pat := get_shard_pat idxs r in
      let shard_pat := optimize_shard_pat shard_pat in
      apply_shard_pat idxs num_shards shard_pat r.

    Definition interp (rewr : rewrite) : impl_rule -> list impl_rule :=
      match rewr with
      | dead_elim R => do_dead_elim R
      | headless_elim => do_headless_elim
      | dup_elim R idxs => fun _ => [] (*TODO*)
      | shard num_shards idxs => fun _ => [] (*TODO*)
      | inline concl hyps => fun r => map nattify_rule_exprvars (do_inline concl hyps r)
      | subst_eqs => fun _ => []
      end.

    Definition apply (rewr : rewrite) : list impl_rule -> list impl_rule := flat_map (interp rewr).

    Definition apply_list := fold_left (fun p rewr => apply rewr p).
  End __.
End rewrite. Abbreviation rewrite := rewrite.rewrite.

Module examples.
  Module fn.
    Variant fn : fnT :=
      | add
      | mod.

    Scheme Boolean Equality for fn.
    #[export] Instance eqb : Eqb fn := fn_beq.
    #[export] Instance eqb_ok : Eqb_ok eqb. Proof. eqb_ok. Qed.
  End fn. Export (hints) fn. Abbreviation fn := fn.fn.
  #[local] Existing Instance fn.
  #[local] Instance no_agg : aggregatorT := Empty_set.
  #[local] Instance expr_map T : map.map expr T := assoc_list_map.map T.

  Declare Custom Entry impl_rule.
  Notation "impl_rule:( r )" := r (r custom impl_rule, format "'impl_rule:(' r ')'").
  Notation "cs :- hs" := {| impl_rule.concls := cs; impl_rule.hyps := hs |}
    (in custom impl_rule at level 1, cs custom datalog_clause_list, hs custom datalog_clause_list).

  Declare Custom Entry impl_rule_list.
  Notation "impl_rules:( rs )" := rs (rs custom impl_rule_list, format "'impl_rules:(' rs ')'").
  Notation "[ ]" := nil (in custom impl_rule_list, format "[ ]").
  Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..)
    (in custom impl_rule_list, x custom impl_rule, y custom impl_rule).

  Definition edge := srel.named 0.
  Definition path2 := srel.named 1.
  Definition path4 := srel.named 2.

  Definition inline_example : prog :=
    {| prog.inputs := [edge];
      prog.rules :=
        impl_rules:(
                      [ [ {path2}(#0, #2, {fn.add}(#3, #4)) ] :- [ {edge}(#0, #1, #3); {edge}(#1, #2, #4) ];
                        [ {path4}(#0, #2, {fn.add}(#3, #4)) ] :- [ {path2}(#0, #1, #3); {path2}(#1, #2, #4) ] ]);
      prog.outputs := [path4] |}.

  Definition the_inline := rewrite.apply_list [rewrite.inline datalog_clause:({path2}(#0, #2, {fn.add}(#3, #4))) [datalog_clause:({edge}(#0, #1, #3)); datalog_clause:({edge}(#1, #2, #4))]; rewrite.headless_elim].

  Example use_the_inline :
    the_inline inline_example.(prog.rules) =
      impl_rules:([[{path4}(#0, #5, {fn.add}(#1, #7))]
                     :- [{edge}(#4, #2, #8); {edge}(#2, #6, #9); {srel.eq}(#0, #4);
                         {srel.eq}(#3, #6); {srel.eq}(#1, {fn.add}(#8, #9)); {edge}(#4, #2, #8);
                         {edge}(#2, #6, #9); {srel.eq}(#3, #4); {srel.eq}(#5, #6);
                         {srel.eq}(#7, {fn.add}(#8, #9))]]).
  Proof. reflexivity. Abort.

  Definition shard_example : impl_rule :=
    impl_rule:([ {path2}(#0, #2, {fn.add}(#3, #4)) ] :- [ {edge}(#0, #1, #3); {edge}(#1, #2, #4) ]).

  Definition shard_example_idxs := fun R => if eqb R edge then [0; 1] else [].

  Example use_shard :
    rewrite.do_shard 2 shard_example_idxs shard_example =
      impl_rules:([[{(path2, [])}(#0, #2, {fn.add}(#3, #4))]
                     :- [{(edge, [0; 0])}(#0, #1, #3); {(edge, [0; 0])}(#1, #2, #4)];
                   [{(path2, [])}(#0, #2, {fn.add}(#3, #4))]
                     :- [{(edge, [1; 0])}(#0, #1, #3); {(edge, [0; 0])}(#1, #2, #4)];
                   [{(path2, [])}(#0, #2, {fn.add}(#3, #4))]
                     :- [{(edge, [0; 1])}(#0, #1, #3); {(edge, [1; 0])}(#1, #2, #4)];
                   [{(path2, [])}(#0, #2, {fn.add}(#3, #4))]
                     :- [{(edge, [1; 1])}(#0, #1, #3); {(edge, [1; 0])}(#1, #2, #4)];
                   [{(path2, [])}(#0, #2, {fn.add}(#3, #4))]
                     :- [{(edge, [0; 0])}(#0, #1, #3); {(edge, [0; 1])}(#1, #2, #4)];
                   [{(path2, [])}(#0, #2, {fn.add}(#3, #4))]
                     :- [{(edge, [1; 0])}(#0, #1, #3); {(edge, [0; 1])}(#1, #2, #4)];
                   [{(path2, [])}(#0, #2, {fn.add}(#3, #4))]
                     :- [{(edge, [0; 1])}(#0, #1, #3); {(edge, [1; 1])}(#1, #2, #4)];
                   [{(path2, [])}(#0, #2, {fn.add}(#3, #4))]
                     :- [{(edge, [1; 1])}(#0, #1, #3); {(edge, [1; 1])}(#1, #2, #4)]]).
  Proof. reflexivity. Abort.

End examples.
