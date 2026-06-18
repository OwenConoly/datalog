From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import Classical_Prop.
From Stdlib Require Import Relations.Relation_Operators Relations.Operators_Properties.

From Datalog Require Import Permutation Map Tactics Fp List Dag Datalog Interpreter Operational Smallstep Graph.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List Datatypes.Option Sorting.OrderToPermutation.

From coqutil Require Import Semantics.OmniSmallstepCombinators.

Import ListNotations.

Section __.
  Context {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context `{sig : signature fn aggregator T}.
  Context {T_eqb : T -> T -> bool}.
  Context {value_set : map.map (list T) unit}.
  Context {agg_to_T : map.map aggregator T}.
  Context (T_to_nat : T -> nat) (nat_to_T : nat -> T). (*bijection..*)

  Section impl.
    Context {rel : relT} {exprvar : exprvarT}.
    Context {context : map.map exprvar T}.

    (*for each relation, store a list of index structures---that is, key-value pairs, with information about what to store about each key.*)
    (*both lists have length n, where *)
    Record idx_struct :=
      { key_idxs : list bool;
        value_idxs : list bool; }.

    Record values_info :=
      { track_sent : bool;
        track_received : bool;
        agg_ops : list aggregator; }.

    Context {idx_structs_info : map.map idx_struct values_info}.
    Context {rel_views : map.map rel idx_structs_info}.

    Inductive hyp_clause_val :=
    | value_clause (value : list expr)
    | agg_clause (agg : aggregator) (num : exprvar)
    | received_clause (num : exprvar)
    | sent_clause (num : exprvar).

    Record hyp_rel :=
      { hr_rel : rel;
        hr_idxs : idx_struct }.

    Record hyp_clause_key :=
      { hc_rel : hyp_rel;
        hc_key_args : list expr; }.

    Record hyp_clause :=
      { hc_key : hyp_clause_key;
        hc_val : hyp_clause_val }.

    Record concl_clause :=
      { cc_rel : rel;
        cc_args : list expr }.

    Record local_rule :=
      { local_rule_concls : list concl_clause;
        local_rule_hyps : list hyp_clause }.

    (*Example: R(x, y) :- S(x, y)*)
    Example example_local_rule (R S : rel) (x y : exprvar) : local_rule :=
      {| local_rule_concls :=
          [{| cc_rel := R;
              cc_args := [var_expr x; var_expr y] |}];
         local_rule_hyps :=
          [{| hc_key :=
                {| hc_rel := {| hr_rel := S;
                                hr_idxs := {| key_idxs := [true; true];
                                              value_idxs := [false; false] |} |};
                   hc_key_args := [var_expr x; var_expr y] |};
              hc_val := value_clause [] |}] |}.

    Record node_prog :=
      { n_relviews : rel_views;
        n_rules : list local_rule }.

    Record val_data :=
      { msgs_received : nat;
        msgs_sent : nat;
        aggs : agg_to_T;
        values : value_set }.

    Inductive hyp_fact_val :=
    | value_fact (value : list T)
    | agg_fact (agg : aggregator) (num : T)
    | received_fact (num : nat)
    | sent_fact (num : nat).

    Record hyp_fact_key :=
      { hf_rel : hyp_rel;
        hf_key_args : list T; }.

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
        Forall2 (interp_expr ctx) clk.(hc_key_args) fk.(hf_key_args).

    Definition interp_hyp_clause_val ctx clv fv :=
      match clv, fv with
      | value_clause es, value_fact es' =>
          Forall2 (interp_expr ctx) es es'
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

    Record concl_fact :=
      { cf_rel : rel;
        cf_args : list T }.

    (*hyp_facts are deducible from history of receiving and sending basic_hyp_facts*)
    Record basic_hyp_fact :=
      { bhf_key : hyp_fact_key;
        bhf_value : list T }.

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
      mupd (default_val_data (agg_ops_of p f.(bhf_key))) s f.(bhf_key)
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
                                  map_values' (value' := T)
                                    (fun agg v =>
                                       match f.(bhf_value) with
                                       | [i; x] =>
                                           agg_bop agg v x
                                       | _ => v
                                       end)
                                    val_data.(aggs)
                              end;
                      values := map.put val_data.(values) f.(bhf_value) tt; |}).

    Definition send_fact (p : node_prog) (s : node_state) (f : basic_hyp_fact) :=
      mupd (default_val_data (agg_ops_of p f.(bhf_key))) s f.(bhf_key)
                 (fun val_data =>
                    {| msgs_received := val_data.(msgs_received);
                      msgs_sent := S val_data.(msgs_sent);
                      aggs := val_data.(aggs);
                      values := val_data.(values); |}).

    Definition interp_concl_clause ctx c f :=
      c.(cc_rel) = f.(cf_rel) /\
        Forall2 (interp_expr ctx) c.(cc_args) f.(cf_args).

    Definition lrule_impl (s : node_state) (r : local_rule) (concl : concl_fact) (hyps : list hyp_fact) :=
      exists ctx,
        Exists (fun c => interp_concl_clause ctx c concl) r.(local_rule_concls) /\
          Forall2 (interp_hyp_clause ctx) r.(local_rule_hyps) hyps.

    Definition lcan_deduce_fact (p : node_prog) (s : node_state) concl :=
      exists r hyps,
        In r p.(n_rules) /\
          lrule_impl s r concl hyps /\
          Forall (knows_hyp_fact s) hyps.

    Definition select {A} (bs : list bool) (l : list A) :=
      map snd (filter (fun '(b, _) => b) (combine bs l)).

    Definition locally_forward (p : node_prog) (f : concl_fact) : list basic_hyp_fact :=
      match map.get p.(n_relviews) f.(cf_rel) with
      | Some vs =>
          map (fun '(idx_str, vals_info) =>
                 {| bhf_key :=
                     {| hf_rel := {| hr_rel := f.(cf_rel);
                                    hr_idxs := idx_str; |};
                       hf_key_args := select idx_str.(key_idxs) f.(cf_args) |};
                   bhf_value := select idx_str.(value_idxs) f.(cf_args) |})
            (map.tuples vs)
      | None => []
      end.

    Record big_state :=
      { bs_node : node_state;
        bs_queue : list concl_fact;
      }.

    Definition empty_big_state :=
      {| bs_node := empty_node_state;
        bs_queue := [] |}.

    Inductive node_step p : big_state -> IO_event concl_fact -> big_state -> Prop :=
    | node_dequeue_step bs input rest :
      bs.(bs_queue) = input :: rest ->
      node_step _ bs (O_event [])
                {| bs_node := fold_left (receive_fact p) (locally_forward p input) bs.(bs_node);
                  bs_queue := rest; |}
    | node_deduce_step bs facts :
      is_list_set (lcan_deduce_fact p bs.(bs_node)) facts ->
      node_step _ bs (O_event facts)
                {| bs_node := fold_left (send_fact p) (flat_map (locally_forward p) facts) bs.(bs_node);
                  bs_queue := bs.(bs_queue) ++ facts; |}
    | node_input_step bs input :
      node_step _ bs (I_event input)
                     {| bs_node := bs.(bs_node);
                       bs_queue := bs.(bs_queue) ++ [input] |}.

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
  Arguments hyp_clause : clear implicits.
  Arguments concl_clause : clear implicits.
  Arguments hyp_fact : clear implicits.
  Arguments node_prog _ _ {_ _}.

  Context {rel : relT} {exprvar : exprvarT}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.
  Context (is_input : rel -> bool).
  Context (senders : rel -> list nat).
  Section spec.
    Local Notation can_deduce_fact := (can_deduce_fact is_input senders).
    Local Notation ok_to_deduce_fact := (ok_to_deduce_fact is_input senders).

    Record spec_node_state :=
      { known_facts : list dfact;
        sent_facts : list dfact }.

    Definition empty_spec_state :=
      {| known_facts := []; sent_facts := [] |}.

    Record spec_node_prog :=
      { spec_node_rules : list rule;
        spec_node_label : nat }.

    Definition new_facts (p : spec_node_prog) (ss : spec_node_state) f :=
      Exists
        (fun r => can_deduce_fact r p.(spec_node_label) ss.(known_facts) ss.(sent_facts) f)
        p.(spec_node_rules) /\
        Forall
          (fun r => ok_to_deduce_fact r ss.(known_facts) f)
          p.(spec_node_rules).

    Definition spec_input_fact ss f :=
      {| known_facts := f :: ss.(known_facts);
        sent_facts := ss.(sent_facts) |}.

    Definition spec_output_fact ss f :=
      {| known_facts := ss.(known_facts);
        sent_facts := f :: ss.(sent_facts) |}.

    (*"big" because it contains the node, plus a bunch of other stuff...*)
    Record big_spec_state :=
      { bss_spec_node : spec_node_state;
        bss_queue : list dfact;
      }.

    Definition empty_big_spec_state :=
      {| bss_spec_node := empty_spec_state;
        bss_queue := [] |}.

    Inductive spec_node_step p : big_spec_state -> IO_event dfact -> big_spec_state -> Prop :=
    | spec_node_dequeue_step bss input rest :
      bss.(bss_queue) = input :: rest ->
      spec_node_step _ bss (O_event [])
                     {| bss_spec_node := spec_input_fact bss.(bss_spec_node) input;
                       bss_queue := rest; |}
    | spec_node_deduce_step bss output :
      new_facts p bss.(bss_spec_node) output ->
      spec_node_step _ bss (O_event [output])
                     {| bss_spec_node := spec_output_fact bss.(bss_spec_node) output;
                       bss_queue := bss.(bss_queue) ++ [output]; |}
    | spec_node_input_step bss input :
      spec_node_step _ bss (I_event input)
                     {| bss_spec_node := bss.(bss_spec_node);
                       bss_queue := bss.(bss_queue) ++ [input] |}.
  End spec.

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
        {| hc_rel := {| hr_rel := normal_rel c.(Datalog.clause_rel);
                       hr_idxs := {| key_idxs := map (fun _ => true) c.(Datalog.clause_args);
                                    value_idxs := map (fun _ => false) c.(Datalog.clause_args); |}; |};
          hc_key_args := map (expr_varmap inl) c.(Datalog.clause_args) |};
      hc_val := value_clause []; |}.

  Definition lower_clause_concl (c : clause) : concl_clause lrel lvar :=
    {| cc_rel := normal_rel c.(Datalog.clause_rel);
      cc_args := map (expr_varmap inl) c.(Datalog.clause_args) |}.

  Definition lower_meta_clause_concl (c : meta_clause) : concl_clause lrel lvar :=
    {| cc_rel := done_sending_rel
                   c.(Datalog.meta_clause_rel)
                       (map is_Some c.(Datalog.meta_clause_args));
      cc_args := map (expr_varmap inl) (keep_Some c.(Datalog.meta_clause_args)); |}.

  Definition lower_meta_clause_hyp (c : meta_clause) : hyp_clause lrel lvar :=
    {| hc_key :=
        {| hc_rel := {| hr_rel := done_receiving_rel
                                    c.(Datalog.meta_clause_rel)
                                        (map is_Some c.(Datalog.meta_clause_args));
                       hr_idxs := {| key_idxs := map (fun _ => true) (keep_Some c.(Datalog.meta_clause_args));
                                    value_idxs := map (fun _ => false) (keep_Some c.(Datalog.meta_clause_args)); |} |};
          hc_key_args := map (expr_varmap inl) (keep_Some c.(Datalog.meta_clause_args)); |};
      hc_val := value_clause [] |}.
  Axiom count : aggregator.

  Definition lower_rule (r : rule) : list (@local_rule lrel lvar) :=
    match r with
    | normal_rule concls hyps =>
        [{| local_rule_concls := map lower_clause_concl concls;
           local_rule_hyps := map lower_clause_hyp hyps |}]
    | meta_rule concls hyps =>
        [{| local_rule_concls := map lower_meta_clause_concl concls;
           local_rule_hyps := map lower_meta_clause_hyp hyps |}]
    (*R(_, x) :- G(x, x) =>
      done_sending(R, [1])(x, num_sent) :- done_receiving(G, [0, 1])(x, x)

done_receiving(G, [0, 1])(x, x) :- received*builtin*(G)(x, x)(num_rec),
                           expected(G, [0, 1])(x, x)(N) *N is number of friends from which we expect to receive G-messages*
     *)
    | agg_rule target_rel agg source_rel =>
        (*source_rel(_, _, 2, ... 9) concl_rel(_, 2, ..., 9),
          assuming source_rel is 10-ary.*)
        let n := num_args source_rel in
        [{| local_rule_concls :=
             [{| cc_rel := normal_rel target_rel;
                (*inr 0 = aggregate result, inr 1..n-2 = the carried-through args*)
                cc_args := map var_expr (map inr (seq O (n - 1))); |}];
           local_rule_hyps :=
             [{| hc_key := {| hc_rel := {| hr_rel := done_receiving_rel
                                                       source_rel
                                                       (false :: false :: repeat true (n - 2));
                                          hr_idxs := {| key_idxs := repeat true (n - 2);
                                                       value_idxs := repeat false (n - 2); |} |};
                             hc_key_args := map var_expr (map inr (seq 1 (n - 2))) |};
                hc_val := value_clause []; |};
              {| hc_key := {| hc_rel := {| hr_rel := normal_rel source_rel;
                                          hr_idxs := {| key_idxs := false :: false :: repeat true (n - 2);
                                                       value_idxs := true :: true :: repeat false (n - 2); |} |};
                             hc_key_args := map var_expr (map inr (seq 1 (n - 2))) |};
                hc_val := agg_clause agg (inr O) |}];
         |}]
    (* target_rel(val, c, d) :- done_receiving(source_rel, [2, 3])(c, d),
                                agg(source_rel, [2, 3])(c, d) = val
     *)
    end.

  Context {idx_structs_info : map.map idx_struct values_info}
    {rel_views : map.map lrel idx_structs_info}
    {rels_data : map.map (@hyp_fact_key lrel) val_data}
    {lcontext : map.map lvar T}.

  Definition lower_prog (sp : spec_node_prog) : node_prog lrel lvar :=
    {| n_relviews := map.empty;
      n_rules := flat_map lower_rule sp.(spec_node_rules) |}.

  Definition lower_dfact (f : dfact) : @concl_fact lrel :=
    match f with
    | normal_dfact R args =>
        {| cf_rel := normal_rel R; cf_args := args |}
    | meta_dfact R args source num =>
        {| cf_rel := done_receiving_from R (map is_Some args);
          cf_args :=
            let tl := nat_to_T num :: keep_Some args in
            match source with
            | None => tl
            | Some node_name => nat_to_T node_name :: tl
            end
        |}
    end.

  Definition hyp_fact_of (f : @concl_fact lrel) : hyp_fact lrel :=
    {| hf_key := {| hf_rel := {| hr_rel := f.(cf_rel);
                                hr_idxs := {| key_idxs := map (fun _ => true) f.(cf_args);
                                             value_idxs := map (fun _ => false) f.(cf_args); |} |};
                   hf_key_args := f.(cf_args) |};
      hf_val := value_fact [] |}.

  Axiom (A : list dfact -> Prop).
  Lemma compiler_correct p :
    nodes_equiv A (spec_node_step p) empty_big_spec_state
                  (translate_step lower_dfact (node_step (lower_prog p))) empty_big_state.
  Proof. Abort.

  Definition spec_knows_fact bss f :=
    In f (bss.(bss_spec_node).(known_facts)) \/ In f bss.(bss_queue).

  Definition knows_fact bs f :=
    knows_hyp_fact bs.(bs_node) (hyp_fact_of f) \/
      In f bs.(bs_queue).

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
