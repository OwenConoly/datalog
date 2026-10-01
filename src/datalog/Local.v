From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.

From Datalog Require Import Map List Datalog Node Smallstep.

From coqutil Require Import Map.Interface Map.Properties Tactics Tactics.fwd Datatypes.List Datatypes.Option.

Import ListNotations.

Section __.
  Section impl.
    Context `{params : datalog_params}.
    Context {agg_map : map.map aggregator value}.

    Inductive query_val_set :=
    | is_member (vals : list expr)
    | agg (agg : aggregator) (result : exprvar)
    | merge (agg : aggregator) (result : exprvar)
    | count_received (num : exprvar)
    | count_sent (num : exprvar).



    Record hyp_rel :=
      { hr_rel : rel;
        hr_idxs : idx_struct }.

    Record hyp_clause_key :=
      { hc_rel : hyp_rel;
        hc_key_args : list expr; }.

    Record hyp_clause :=
      { hc_key : hyp_clause_key;
        hc_val : hyp_clause_val }.

    Record local_rule :=
      { local_rule_concls : list clause;
        local_rule_hyps : list hyp_clause }.

    (*Example: R(x, y) :- S(x, y)*)
    Example example_local_rule (R S : rel) (x y : exprvar) : local_rule :=
      {| local_rule_concls :=
          [{| clause.rel := R;
              clause.args := [expr.var x; expr.var y] |}];
         local_rule_hyps :=
          [{| hc_key :=
                {| hc_rel := {| hr_rel := S;
                                hr_idxs := {| key_idxs := [true; true];
                                              value_idxs := [false; false] |} |};
                   hc_key_args := [expr.var x; expr.var y] |};
              hc_val := value_clause [] |}] |}.

    Record node_prog :=
      { n_relviews : rel_views;
        n_rules : list local_rule }.

    Record val_data :=
      { msgs_received : nat;
        msgs_sent : nat;
        aggs : agg_map;
        values : value_set }.

    Inductive hyp_fact_val :=
    | value_fact (vals : list value)
    | agg_fact (agg : aggregator) (num : value)
    | received_fact (num : nat)
    | sent_fact (num : nat).

    Record hyp_fact_key :=
      { hf_rel : hyp_rel;
        hf_key_args : list value; }.

    Record hyp_fact :=
      { hf_key : hyp_fact_key;
        hf_val : hyp_fact_val }.

    Context {node_rels : map.map hyp_fact_key val_data}.

    Definition node_state := node_rels.

    Definition empty_node_state : node_state := map.empty.

    Definition knows_hyp_fact (s : node_state) (f : hyp_fact) :=
      match map.get s f.(hf_key) with
      | Some inp_data =>
          match f.(hf_val) with
          | value_fact output =>
              map.get inp_data.(values) output = Some tt
          | agg_fact agg val =>
              map.get inp_data.(aggs) agg = Some val
          | received_fact val =>
              inp_data.(msgs_received) = val
          | sent_fact val =>
              inp_data.(msgs_sent) = val
          end
      | None => False
      end.

    Definition interp_hyp_clause_key ctx clk fk :=
      clk.(hc_rel) = fk.(hf_rel) /\
        Forall2 (expr.interp ctx) clk.(hc_key_args) fk.(hf_key_args).

    Definition interp_hyp_clause_val ctx clv fv :=
      match clv, fv with
      | value_clause es, value_fact es' =>
          Forall2 (expr.interp ctx) es es'
      | agg_clause a v, agg_fact a' v' =>
          a = a' /\ map.get ctx v = Some v'
      | received_clause v, received_fact v' =>
          option_map get_nat (map.get ctx v) = Some v'
      | sent_clause v, sent_fact v' =>
          option_map get_nat (map.get ctx v) = Some v'
      | _, _ => False
      end.

    Definition interp_hyp_clause (ctx : context) (cl : hyp_clause) (f : hyp_fact) :=
      interp_hyp_clause_key ctx cl.(hc_key) f.(hf_key) /\
        interp_hyp_clause_val ctx cl.(hc_val) f.(hf_val).

    (*hyp_facts are deducible from history of receiving and sending basic_hyp_facts*)
    Record basic_hyp_fact :=
      { bhf_key : hyp_fact_key;
        bhf_value : list value }.

    Definition default_val_data (as_ : list aggregator) : val_data :=
      {| msgs_received := 0;
        msgs_sent := 0;
        aggs := map.of_list (map (fun a => (a, agg_id a)) as_);
        values := map.empty; |}.

    Definition agg_ops_of (p : node_prog) (k : hyp_fact_key) : list aggregator :=
      match map.get p.(n_relviews) k.(hf_rel).(hr_rel) with
      | Some idxs =>
          match map.get idxs k.(hf_rel).(hr_idxs) with
          | Some vi => vi.(agg_ops)
          | None => []
          end
      | None => []
      end.

    Definition receive_fact (p : node_prog) (s : node_state) (f : basic_hyp_fact) :=
      mupd_total (default_val_data (agg_ops_of p f.(bhf_key)))
                 (fun val_data =>
                    {| msgs_received := S val_data.(msgs_received);
                      msgs_sent := val_data.(msgs_sent);
                      (*Dedup by the full [bhf_value] tuple before folding into the
                        aggregators.  We need this because we want to support things
                        like sums over sets (non-set-monotone): receiving the same
                        (i, x) twice should not double-count x in the sum.*)
                      aggs := match map.get val_data.(values) f.(bhf_value) with
                              | Some tt =>
                                  val_data.(aggs)
                              | None =>
                                  map_values' (value' := value)
                                    (fun agg v =>
                                       match f.(bhf_value) with
                                       | [i; x] =>
                                           agg_bop agg v x
                                       | _ => v
                                       end)
                                    val_data.(aggs)
                              end;
                      values := map.put val_data.(values) f.(bhf_value) tt; |})
                 s f.(bhf_key).

    Definition send_fact (p : node_prog) (s : node_state) (f : basic_hyp_fact) :=
      mupd_total (default_val_data (agg_ops_of p f.(bhf_key)))
                 (fun val_data =>
                    {| msgs_received := val_data.(msgs_received);
                      msgs_sent := S val_data.(msgs_sent);
                      aggs := val_data.(aggs);
                      values := val_data.(values); |})
                 s f.(bhf_key).

    Definition lrule_impl (s : node_state) (r : local_rule) (concl : normal_fact) (hyps : list hyp_fact) :=
      exists ctx,
        Exists (fun c => clause.interp ctx c concl) r.(local_rule_concls) /\
          Forall2 (interp_hyp_clause ctx) r.(local_rule_hyps) hyps.

    Definition lcan_deduce_fact (p : node_prog) (s : node_state) concl :=
      exists r hyps,
        In r p.(n_rules) /\
          lrule_impl s r concl hyps /\
          Forall (knows_hyp_fact s) hyps.

    Definition select {A} (bs : list bool) (l : list A) :=
      map snd (filter (fun '(b, _) => b) (combine bs l)).

    Definition locally_forward (p : node_prog) (f : normal_fact) : list basic_hyp_fact :=
      match map.get p.(n_relviews) f.(normal_fact.rel) with
      | Some vs =>
          map (fun '(idx_str, vals_info) =>
                 {| bhf_key :=
                     {| hf_rel := {| hr_rel := f.(normal_fact.rel);
                                    hr_idxs := idx_str; |};
                       hf_key_args := select idx_str.(key_idxs) f.(normal_fact.args) |};
                   bhf_value := select idx_str.(value_idxs) f.(normal_fact.args) |})
            (map.tuples vs)
      | None => []
      end.

    Variant node_step p : node_state -> IO_event unit normal_fact -> node_state -> Prop :=
    | node_deduce_step ns facts :
      is_list_set (lcan_deduce_fact p ns) facts ->
      node_step _ ns (O_event (deduce_label facts) facts)
        (fold_left (send_fact p) (flat_map (locally_forward p) facts) ns)
    | node_input_step ns input :
      node_step _ ns (I_event input)
        (fold_left (receive_fact p) (locally_forward p input) ns).

    (*on the high level, eventually <-> maybe.
      prove: HL eventually -> LL eventually -> LL maybe -> HL maybe.
     *)

    (*i think there are two pieces to saying that node_step and spec_node_step behave the same.
      first i want to prove that node_step steps to outputting some fact iff spec_node_step does.
      this is a safety property of node_step (assuming the safety property holds for spec_node_step).
      then i want to prove that stepsTo P holds iff spec_stepsTo P holds.
      this is a liveness property (assuming the liveness property holds for spec_node_step).
     *)
  End impl.
  Arguments hyp_clause _ _ {_ _}.
  Arguments local_rule _ _ {_ _}.
  Arguments hyp_fact _ {_ _}.
  Arguments hyp_fact_key _ {_}.
  Arguments node_prog _ _ {_ _ _ _}.

  Context `{params : datalog_params} {sender_label : sender_labelT}.
  Context (R_senders : rel -> list sender_label).
  Context (value_to_nat : value -> nat) (nat_to_value : nat -> value). (*bijection..*)
  Context (label_to_value : sender_label -> value).

  (*Note on the two bitmasks in play once we lower meta-clauses:
    - the [to_keep] bitmask in [lrel] constructors has length = length of the
      spec-level [meta_clause_args].  It distinguishes views (i.e., it is part
      of the lowered rel name) and encodes which positions of the original args
      are wildcards vs specified.
    - the [key_idxs]/[value_idxs] bitmasks in [idx_struct] (carried inside
      [hyp_clause]/[hyp_fact]) operate over the impl-side positions, i.e., have
      length = number of [Some]s in the [meta_clause_args] = arity of the
      lowered rel.  They split those positions into key vs value.
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

  Definition lower_clause_hyp (c : clause) : hyp_clause lrel lvar :=
    {| hc_key :=
        {| hc_rel := {| hr_rel := normal_rel c.(clause.rel);
                       hr_idxs := {| key_idxs := map (fun _ => true) c.(clause.args);
                                    value_idxs := map (fun _ => false) c.(clause.args); |}; |};
          hc_key_args := map (expr_varmap inl) c.(clause.args) |};
      hc_val := value_clause []; |}.

  Definition lower_clause_concl (c : clause) : clause (relt := lrel) (exprvar := lvar) :=
    {| clause.rel := normal_rel c.(clause.rel);
      clause.args := map (expr_varmap inl) c.(clause.args) |}.

  Definition lower_clause_pattern_concl (c : clause_pattern) : clause (relt := lrel) (exprvar := lvar) :=
    let es := map expr_pattern.expr_of c.(clause_pattern.args) in
    {| clause.rel := done_sending_rel c.(clause_pattern.rel) (map is_Some es);
      clause.args := map (expr_varmap inl) (keep_Some es); |}.

  Definition lower_clause_pattern_hyp (c : clause_pattern) : hyp_clause lrel lvar :=
    let es := map expr_pattern.expr_of c.(clause_pattern.args) in
    {| hc_key :=
        {| hc_rel := {| hr_rel := done_receiving_rel c.(clause_pattern.rel) (map is_Some es);
                       hr_idxs := {| key_idxs := map (fun _ => true) (keep_Some es);
                                    value_idxs := map (fun _ => false) (keep_Some es); |} |};
          hc_key_args := map (expr_varmap inl) (keep_Some es); |};
      hc_val := value_clause [] |}.
  Axiom count : aggregator.

  Definition lower_rule (r : rule) : list (local_rule lrel lvar) :=
    match r with
    | rule.impl concls hyps =>
        [{| local_rule_concls := map lower_clause_concl concls;
           local_rule_hyps := map lower_clause_hyp hyps |}]
    | rule.agg target_rel agg source_rel =>
        (*source_rel(_, _, 2, ... 9) concl_rel(_, 2, ..., 9),
          assuming source_rel is 10-ary.*)
        let n := num_args source_rel in
        [{| local_rule_concls :=
             [{| clause.rel := normal_rel target_rel;
                (*inr 0 = aggregate result, inr 1..n-2 = the carried-through args*)
                clause.args := map expr.var (map inr (seq O (n - 1))); |}];
           local_rule_hyps :=
             [{| hc_key := {| hc_rel := {| hr_rel := done_receiving_rel
                                                       source_rel
                                                       (false :: false :: repeat true (n - 2));
                                          hr_idxs := {| key_idxs := repeat true (n - 2);
                                                       value_idxs := repeat false (n - 2); |} |};
                             hc_key_args := map expr.var (map inr (seq 1 (n - 2))) |};
                hc_val := value_clause []; |};
              {| hc_key := {| hc_rel := {| hr_rel := normal_rel source_rel;
                                          hr_idxs := {| key_idxs := false :: false :: repeat true (n - 2);
                                                       value_idxs := true :: true :: repeat false (n - 2); |} |};
                             hc_key_args := map expr.var (map inr (seq 1 (n - 2))) |};
                hc_val := agg_clause agg (inr O) |}];
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
  Definition lower_meta_rule (mr : meta_rule) : local_rule lrel lvar :=
    {| local_rule_concls := map lower_clause_pattern_concl mr.(meta_rule.concls);
      local_rule_hyps := map lower_clause_pattern_hyp mr.(meta_rule.hyps) |}.

  Context {agg_map : map.map aggregator value}
    {idx_structs_info : map.map idx_struct values_info}
    {rel_views : map.map lrel idx_structs_info}
    {rels_data : map.map (hyp_fact_key lrel) val_data}
    {lcontext : map.map lvar value}.

  Definition lower_prog (p : program) : node_prog lrel lvar :=
    {| n_relviews := map.empty;
      n_rules := flat_map lower_rule p.(program.rules) ++ map lower_meta_rule p.(program.meta_rules) |}.

  Definition lower_message (f : node.message) : normal_fact (relt := lrel) :=
    match f with
    | node.message.normal nf =>
        {| normal_fact.rel := normal_rel nf.(normal_fact.rel); normal_fact.args := nf.(normal_fact.args) |}
    | node.message.done_with pat src count =>
        let vals := map value_pattern.value_of pat.(fact_pattern.args) in
        {| normal_fact.rel := done_receiving_from pat.(fact_pattern.rel) (map is_Some vals);
          normal_fact.args := label_to_value src :: nat_to_value count :: keep_Some vals |}
    end.

  Definition hyp_fact_of (f : normal_fact (relt := lrel)) : hyp_fact lrel :=
    {| hf_key := {| hf_rel := {| hr_rel := f.(normal_fact.rel);
                                hr_idxs := {| key_idxs := map (fun _ => true) f.(normal_fact.args);
                                             value_idxs := map (fun _ => false) f.(normal_fact.args); |} |};
                   hf_key_args := f.(normal_fact.args) |};
      hf_val := value_fact [] |}.

  Lemma compiler_correct p name :
    steps_corresp_sound (node.allowed_inputs R_senders)
      (node.step R_senders p name) node.init
      (translate_step lower_message (node_step (lower_prog p))) empty_node_state /\
    steps_corresp_sound (node.allowed_inputs R_senders)
      (translate_step lower_message (node_step (lower_prog p))) empty_node_state
      (node.step R_senders p name) node.init.
  Proof. Abort.

  Definition spec_knows_fact (ns : node.state) f :=
    In f ns.(node.state.known).

  Definition knows_fact ns f :=
    knows_hyp_fact ns (hyp_fact_of f).

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
End __.
