From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Datalog Require Import Map List Datalog Node Smallstep Multiset.
From coqutil Require Import Map.Interface Map.Properties Tactics Tactics.fwd Datatypes.List Datatypes.Option.

Import ListNotations.

Module low_node.
Module set_fact.
  Section __.
    Context `{params : datalog_params}.

    Variant set_fact :=
    | contains (vals : list value)
    | agg (agg : aggregator) (result : value)
    | merge (agg : aggregator) (result : value)
    | count_received (num : nat)
    | count_sent (num : nat).

  End __.
End set_fact. Abbreviation set_fact := set_fact.set_fact.

Module state.
  Section __.
    Context `{params : datalog_params}.

    Record state :=
      { received : list normal_fact;
        known : list normal_fact; (*a superset of [received].  why store it redundantly?  to preserve ordering.*)
        sent : list normal_fact; }.

    Definition empty := {| received := []; known := []; sent := [] |}.
  End __.
End state. Abbreviation state := state.state.

Module set_query.
  Section __.
    Context `{params : datalog_params}.

    (*TODO which should be expr, which should be exprvar*)
    (*query on a set of tuples*)
    Variant set_query :=
      (*is this tuple in the set?*)
      | contains (vals : list expr)
      (*does aggregating over the set yield [result]? *)
      | agg (agg : aggregator) (result : exprvar)
      (*does merging over the set yield [result]?
        unlike aggregating, there may (or may not) be duplicates.*)
      | merge (agg : aggregator) (result : exprvar)
      (*is [num] the number of messages in this set that we have received?*)
      | count_received (num : exprvar)
      (*is [num] the number of messages in this set that we have sent?*)
      | count_sent (num : exprvar).

    Variant interp (ctx : context) : set_query -> set_fact -> Prop :=
      | interp_contains es vs :
        Forall2 (expr.interp ctx) es vs ->
        interp _ (contains es) (set_fact.contains vs)
      | interp_agg a v r :
        map.get ctx v = Some r ->
        interp _ (agg a v) (set_fact.agg a r)
      | interp_merge a v r :
        map.get ctx v = Some r ->
        interp _ (merge a v) (set_fact.merge a r)
      | interp_count_received v n :
        map.get ctx v = Some n ->
        interp _ (count_received v) (set_fact.count_received (get_nat n))
      | interp_count_sent v n :
        map.get ctx v = Some n ->
        interp _ (count_sent v) (set_fact.count_sent (get_nat n)).

  End __.
End set_query. Abbreviation set_query := set_query.set_query.

Definition select {A} (bs : list bool) (l : list A) :=
  filter_map (fun '(b, x) => if (b : bool) then Some x else None) (combine bs l).

Definition select_not {A} (bs : list bool) (l : list A) :=
  filter_map (fun '(b, x) => if negb b then Some x else None) (combine bs l).

Module hyp_fact_key.
  Section __.
    Context `{params : datalog_params}.

    Record hyp_fact_key :=
      { rel : rel;
        mask : list bool;
        args : list value; }.

    Definition matches (f : hyp_fact_key) (nf : normal_fact) :=
      f.(rel) = nf.(normal_fact.rel) /\
        f.(args) = select f.(mask) nf.(normal_fact.args).

  End __.
End hyp_fact_key. Abbreviation hyp_fact_key := hyp_fact_key.hyp_fact_key.

Module hyp_clause_key.
  Section __.
    Context `{params : datalog_params}.

    Record hyp_clause_key :=
      { rel : rel;
        mask : list bool; (*bit mask---which arguments constitute the key?*)
        args : list expr; (*length should be equal to the number of ones in mask*) }.

    Definition interp (ctx : context) (c : hyp_clause_key) (k : hyp_fact_key) :=
      c.(rel) = k.(hyp_fact_key.rel) /\
        c.(mask) = k.(hyp_fact_key.mask) /\
        Forall2 (expr.interp ctx) c.(args) k.(hyp_fact_key.args).

  End __.
End hyp_clause_key. Abbreviation hyp_clause_key := hyp_clause_key.hyp_clause_key.

Module hyp_fact.
  Section __.
    Context `{params : datalog_params}.

    Record hyp_fact :=
      { key : hyp_fact_key;
        val_fact : set_fact }.

    Definition values (k : hyp_fact_key) (nfs : list normal_fact) : Mfset (list value) :=
      Mfset.map
        (fun nf => select_not k.(hyp_fact_key.mask) nf.(normal_fact.args))
        (Mfset.filter
           (hyp_fact_key.matches k)
           (Mfset.of_list nfs)).

    (*i haven't thought very much about how the semantics should handle an aggregation operation that doesn't induce a function of multisets (or a merge operation that don't induce a function of sets).
      the current semantics are probably unreasonable in this case.
     *)
    Definition known_by (s : state) (f : hyp_fact) :=
      match f.(val_fact) with
      | set_fact.contains val =>
          Mfset.has (values f.(key) s.(state.known)) val
      | set_fact.agg agg result =>
          (*Mfset of things like [[index, val_to_aggregate]] *)
          let elts := Mfset.dedup (values f.(key) s.(state.known)) in
          (*Mfset of things like [val_to_aggregate]*)
          let vals := Mfset.filter_map (fun x => hd_error (tl x)) elts in
          Mfset.fold (agg_bop agg) vals (agg_id agg) result
      | set_fact.merge agg result =>
          (*Mfset of things like [val_to_aggregate]*)
          let elts := values f.(key) s.(state.known) in
          let vals := Mfset.filter_map hd_error elts in
          Mfset.fold (agg_bop agg) vals (agg_id agg) result
      | set_fact.count_received num =>
          Mfset.size (values f.(key) s.(state.received)) num
      | set_fact.count_sent num =>
          Mfset.size (values f.(key) s.(state.sent)) num
      end.

  End __.
End hyp_fact. Abbreviation hyp_fact := hyp_fact.hyp_fact.

Module hyp_clause.
  Section __.
    Context `{params : datalog_params}.

    Record hyp_clause :=
      { key : hyp_clause_key;
        val_query : set_query; (*query on the set resulting from partial application of the relation to [key]*) }.

    Definition interp (ctx : context) (c : hyp_clause) (f : hyp_fact) :=
      hyp_clause_key.interp ctx c.(key) f.(hyp_fact.key) /\
        set_query.interp ctx c.(val_query) f.(hyp_fact.val_fact).
  End __.
End hyp_clause. Abbreviation hyp_clause := hyp_clause.hyp_clause.

Module rule.
  Section __.
    Context `{params : datalog_params}.

    Record rule :=
      { concls : list clause;
        hyps : list hyp_clause; }.

    (*Example: R(x, y) :- S(x, y)*)
    Example example (R S : rel) (x y : exprvar) : rule :=
      {| concls :=
          [{| clause.rel := R;
             clause.args := [expr.var x; expr.var y] |}];
        hyps :=
          [{| hyp_clause.key :=
               {| hyp_clause_key.rel := S;
                 hyp_clause_key.mask := [true; true];
                 hyp_clause_key.args := [expr.var x; expr.var y] |};
             hyp_clause.val_query := set_query.contains []; |}] |}.

    Definition interp r nf hyps' :=
      exists ctx,
        Exists (fun c => clause.interp ctx c nf) r.(concls) /\
          Forall2 (hyp_clause.interp ctx) r.(hyps) hyps'.
  End __.
End rule. Abbreviation rule := rule.rule.

Section step.
  Context `{params : datalog_params}.

  Definition can_deduce (p : list rule) (s : state) nf :=
      exists hyps,
        Exists (fun r => rule.interp r nf hyps) p /\
          Forall (hyp_fact.known_by s) hyps.

  (*TODO do not output everything*)
  (*TODO spec node does not forward to itself, but this one does.  what to do about that?*)
  Variant step p : state -> IO_event unit normal_fact -> state -> Prop :=
    | deduce_step ns new_facts old_facts :
      is_list_set (can_deduce p ns) (new_facts ++ old_facts) ->
      incl old_facts ns.(state.known) ->
      step _ ns (O_event tt new_facts)
           {| state.sent := new_facts ++ ns.(state.sent);
             state.known := new_facts ++ ns.(state.known);
             state.received := ns.(state.received); |}
    | input_step ns input :
      step _ ns (I_event input)
           {| state.sent := ns.(state.sent);
             state.known := input :: ns.(state.known);
             state.received := input :: ns.(state.received); |}.


















    (*on the high level, eventually <-> maybe.
      prove: HL eventually -> LL eventually -> LL maybe -> HL maybe.
     *)

    (*i think there are two pieces to saying that node_step and spec_node_step behave the same.
      first i want to prove that node_step steps to outputting some fact iff spec_node_step does.
      this is a safety property of node_step (assuming the safety property holds for spec_node_step).
      then i want to prove that stepsTo P holds iff spec_stepsTo P holds.
      this is a liveness property (assuming the liveness property holds for spec_node_step).
     *)
End step.

End low_node.

Section compile.
  Context `{params : datalog_params} {sender_label : sender_labelT}.
  Context (R_senders : rel -> list sender_label).
  Context (value_to_nat : value -> nat) (nat_to_value : nat -> value). (*value_to_nat should be injective, or something?*)
  Context (label_to_value : sender_label -> value).

  (*Note on the two bitmasks in play once we lower meta-clauses:
    - the [to_keep] bitmask in [lrel] constructors has length = length of the
      spec-level [meta_clause_args].  It distinguishes views (i.e., it is part
      of the lowered rel name) and encodes which positions of the original args
      are wildcards vs specified.
    - the [mask] bitmask in [hyp_clause_key]/[hyp_fact_key] operates over the
      impl-side positions, i.e., has length = number of [Some]s in the
      [meta_clause_args] = arity of the lowered rel.  It splits those positions
      into key vs value.
    These are not the same bitmask. *)
  Variant lrel :=
    | normal_rel (rel_name : rel)
    | done_receiving_from (rel_name : rel) (to_keep : list bool)
    (*above is like below, except it comes with two extra arguments:
      which source did we receive it from, and how many did we receive*)
    | done_receiving_rel (rel_name : rel) (to_keep : list bool)
    | done_sending_rel (rel_name : rel) (to_keep : list bool).

  Definition lvar : Type := exprvar + nat.

  Context (num_args : rel -> nat).
  Context {lcontext : map.map lvar value}.

  Definition lower_clause_hyp (c : clause) : low_node.hyp_clause (_rel := lrel) (_exprvar := lvar) :=
    {| low_node.hyp_clause.key :=
        {| low_node.hyp_clause_key.rel := normal_rel c.(clause.rel);
          low_node.hyp_clause_key.mask := map (fun _ => true) c.(clause.args);
          low_node.hyp_clause_key.args := map (expr_varmap inl) c.(clause.args) |};
      low_node.hyp_clause.val_query := low_node.set_query.contains [] |}.

  Definition lower_clause_concl (c : clause) : clause (relt := lrel) (exprvar := lvar) :=
    {| clause.rel := normal_rel c.(clause.rel);
      clause.args := map (expr_varmap inl) c.(clause.args) |}.

  Definition lower_clause_pattern_concl (c : clause_pattern) : clause (relt := lrel) (exprvar := lvar) :=
    let es := map expr_pattern.expr_of c.(clause_pattern.args) in
    {| clause.rel := done_sending_rel c.(clause_pattern.rel) (map is_Some es);
      clause.args := map (expr_varmap inl) (keep_Some es); |}.

  Definition lower_clause_pattern_hyp (c : clause_pattern) : low_node.hyp_clause (_rel := lrel) (_exprvar := lvar) :=
    let es := map expr_pattern.expr_of c.(clause_pattern.args) in
    {| low_node.hyp_clause.key :=
        {| low_node.hyp_clause_key.rel := done_receiving_rel c.(clause_pattern.rel) (map is_Some es);
          low_node.hyp_clause_key.mask := map (fun _ => true) (keep_Some es);
          low_node.hyp_clause_key.args := map (expr_varmap inl) (keep_Some es) |};
      low_node.hyp_clause.val_query := low_node.set_query.contains [] |}.
  Axiom count : aggregator.

  Definition lower_rule (r : rule) : list (low_node.rule (_rel := lrel) (_exprvar := lvar)) :=
    match r with
    | rule.impl concls hyps =>
        [{| low_node.rule.concls := map lower_clause_concl concls;
           low_node.rule.hyps := map lower_clause_hyp hyps |}]
    | rule.agg target_rel agg source_rel =>
        (*source_rel(_, _, 2, ... 9) concl_rel(_, 2, ..., 9),
          assuming source_rel is 10-ary.*)
        let n := num_args source_rel in
        [{| low_node.rule.concls :=
             [{| clause.rel := normal_rel target_rel;
                (*inr 0 = aggregate result, inr 1..n-2 = the carried-through args*)
                clause.args := map expr.var (map inr (seq O (n - 1))); |}];
           low_node.rule.hyps :=
             [{| low_node.hyp_clause.key :=
                  {| low_node.hyp_clause_key.rel := done_receiving_rel
                                                      source_rel
                                                      (false :: false :: repeat true (n - 2));
                    low_node.hyp_clause_key.mask := repeat true (n - 2);
                    low_node.hyp_clause_key.args := map expr.var (map inr (seq 1 (n - 2))) |};
                low_node.hyp_clause.val_query := low_node.set_query.contains [] |};
              {| low_node.hyp_clause.key :=
                  {| low_node.hyp_clause_key.rel := normal_rel source_rel;
                    low_node.hyp_clause_key.mask := false :: false :: repeat true (n - 2);
                    low_node.hyp_clause_key.args := map expr.var (map inr (seq 1 (n - 2))) |};
                low_node.hyp_clause.val_query := low_node.set_query.agg agg (inr O) |}];
         |}]
    (* target_rel(val, c, d) :- done_receiving(source_rel, [2, 3])(c, d),
                                agg(source_rel, [2, 3])(c, d) = val
     *)
    end.

  (*R(_, x) :- G(x, x) =>
    done_sending(R, [1])(x, num_sent) :- done_receiving(G, [0, 1])(x, x)

done_receiving(G, [0, 1])(x, x) :- received*builtin*(G)(x, x)(num_rec),
                           expected(G, [0, 1])(x, x)(N) *N is number of friends from which we expect to receive G-messages*
   *)
  Definition lower_meta_rule (mr : meta_rule) : low_node.rule (_rel := lrel) (_exprvar := lvar) :=
    {| low_node.rule.concls := map lower_clause_pattern_concl mr.(meta_rule.concls);
      low_node.rule.hyps := map lower_clause_pattern_hyp mr.(meta_rule.hyps) |}.

  Definition lower_prog (p : program) : list (low_node.rule (_rel := lrel) (_exprvar := lvar)) :=
    flat_map lower_rule p.(program.rules) ++ map lower_meta_rule p.(program.meta_rules).

  Definition lower_message (f : node.message) : normal_fact (relt := lrel) :=
    match f with
    | node.message.normal nf =>
        {| normal_fact.rel := normal_rel nf.(normal_fact.rel); normal_fact.args := nf.(normal_fact.args) |}
    | node.message.done_with pat src count =>
        let vals := map value_pattern.value_of pat.(fact_pattern.args) in
        {| normal_fact.rel := done_receiving_from pat.(fact_pattern.rel) (map is_Some vals);
          normal_fact.args := label_to_value src :: nat_to_value count :: keep_Some vals |}
    end.

  Definition hyp_fact_of (f : normal_fact (relt := lrel)) : low_node.hyp_fact (_rel := lrel) :=
    {| low_node.hyp_fact.key :=
        {| low_node.hyp_fact_key.rel := f.(normal_fact.rel);
          low_node.hyp_fact_key.mask := map (fun _ => true) f.(normal_fact.args);
          low_node.hyp_fact_key.args := f.(normal_fact.args) |};
      low_node.hyp_fact.val_fact := low_node.set_fact.contains [] |}.

  Lemma compiler_correct p name :
    steps_corresp_sound (node.allowed_inputs R_senders)
      (node.step R_senders p name) node.init
      (translate_step lower_message (low_node.step (lower_prog p))) low_node.state.empty /\
    steps_corresp_sound (node.allowed_inputs R_senders)
      (translate_step lower_message (low_node.step (lower_prog p))) low_node.state.empty
      (node.step R_senders p name) node.init.
  Proof. Abort.

  Definition spec_knows_fact (ns : node.state) f :=
    In f ns.(node.state.known).

  Definition knows_fact ns f :=
    low_node.hyp_fact.known_by ns (hyp_fact_of f).

  (* Lemma sim_step (sp : spec_node_prog) G bss ts bs t P : *)
  (*   (forall f, spec_knows_fact bss f -> knows_fact bs (lower_dfact f)) -> *)
  (*   spec_node_step' sp G (bss, ts) P -> *)
  (*   node_step' (lower_prog sp) (map lower_dfact G) (bs, t) *)
  (*     (fun '(bs', t') => *)
  (*        exists bss' ts', *)
  (*          P (bss', ts') /\ *)
  (*            (forall f, spec_knows_fact bss' f -> *)
  (*                  knows_fact bs' (lower_dfact f))). *)
  (* Proof. Abort. *)

  (* Lemma lower_rule_complete bss bs ts t (sp : spec_node_prog) P G : *)
  (*   (forall f, spec_knows_fact bss f -> knows_fact bs (lower_dfact f)) -> *)
  (*   spec_stepsTo sp G P (bss, ts) -> *)
  (*   stepsTo (lower_prog sp) (map lower_dfact G) *)
  (*     (fun '(bs, _) => exists bss' ts', *)
  (*          P (bss', ts') /\ *)
  (*            forall f, *)
  (*              spec_knows_fact bss' f -> *)
  (*              knows_fact bs (lower_dfact f)) *)
  (*     (bs, t). *)
  (* Proof. Abort. *)
End compile.
