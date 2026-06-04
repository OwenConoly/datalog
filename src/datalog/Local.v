From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import Classical_Prop.
From Stdlib Require Import Relations.Relation_Operators Relations.Operators_Properties.

From Datalog Require Import Permutation Map Tactics Fp List Dag Datalog Interpreter Operational.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List Datatypes.Option Sorting.OrderToPermutation.

Import ListNotations.

Section __.
  Context {rel lrel var fn aggregator T : Type}.
  Context `{sig : signature fn aggregator T}.
  Context {T_eqb : T -> T -> bool}.
  Context {context : map.map var T} {context_ok : map.ok context}.
  Context (num_args : rel -> nat).

  Local Notation clause := (clause rel var fn).
  Local Notation meta_clause := (meta_clause rel var fn).
  Local Notation fact := (fact rel T).
  Local Notation expr := (expr var fn).
  Local Notation rule := (rule rel var fn aggregator).
  Local Notation non_meta_rule := (non_meta_rule rel var fn aggregator).
  Local Notation dfact := (dfact rel T).
  Local Notation prog := (prog rel var fn aggregator).

  Implicit Types known_facts sent_facts waiting_facts input_facts inputs : list dfact.
  Implicit Types nf result : dfact.
  Implicit Types mf_rel : rel.
  Implicit Types mf_args : list (option T).
  Implicit Types nf_args : list T.

  Context (is_input : rel -> bool).
  Context (senders : rel -> list nat).
  Local Notation can_deduce_fact := (can_deduce_fact is_input senders).
  Local Notation ok_to_deduce_fact := (ok_to_deduce_fact is_input senders).

  Record spec_node_state :=
    { known_facts : list dfact;
      sent_facts : list dfact }.

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

  Record local_rel_info :=
    { num_inputs : nat;
      num_outputs : nat;
      track_sent : bool;
      track_received : bool;
      agg_ops : list aggregator; }.

  Context {local_rels_info : map.map lrel local_rel_info} {local_rels_info_ok : map.ok local_rels_info}.

  Inductive hyp_clause_val :=
  | outputs_clause (outputs : list expr)
  | agg_clause (agg : aggregator) (num : var)
  | received_clause (num : var)
  | sent_clause (num : var).

  Record hyp_clause_key :=
    { clause_rel : lrel;
      clause_inputs : list expr }.

  Record hyp_clause : Type :=
    { hc_key : hyp_clause_key;
      hc_val : hyp_clause_val }.

  Inductive hyp_fact_val :=
  | outputs_fact (outputs : list T)
  | agg_fact (agg : aggregator) (num : T)
  | received_fact (num : nat)
  | sent_fact (num : nat).

  Record fact_key :=
    { fact_rel : lrel;
      fact_inputs : list T }.

  Record hyp_fact : Type :=
    { hf_key : fact_key;
      hf_val : hyp_fact_val }.

  Record concl_clause :=
    { cc_rel : rel;
      cc_args : list expr }.

  Record local_rule :=
    { local_rule_concls : list concl_clause;
      local_rule_hyps : list hyp_clause }.

  Record corresponding_lrel :=
    { corresp_lrel : lrel;
      corresp_inputs : list nat;
      corresp_outputs : list nat;
    }.

  Context {rel_to_lrel : map.map rel (list corresponding_lrel)} {rel_to_lrel_ok : map.ok rel_to_lrel}.

  Record node_prog :=
    { local_forwarding_table : rel_to_lrel;
      local_rels : local_rels_info;
      rules : list local_rule }.

  Context {outputs_set : map.map (list T) unit}.
  Context {agg_to_T : map.map aggregator T}.

  Record val_data :=
    { msgs_received : nat;
      msgs_sent : nat;
      aggs : agg_to_T;
      outputs : outputs_set }.

  Context {map_factkey_valdata : map.map fact_key val_data}.

  Definition node_state :=
    map_factkey_valdata.

  Definition knows_hyp_fact (s : node_state) (f : hyp_fact) :=
    match map.get s f.(hf_key) with
    | Some inp_data =>
        match f.(hf_val) with
        | outputs_fact output =>
            map.get inp_data.(outputs) output = Some tt
        | agg_fact agg val =>
            map.get inp_data.(aggs) agg = Some val
        | received_fact val =>
            inp_data.(msgs_received) = val
        | sent_fact val =>
            inp_data.(msgs_sent) = val
        end
    | None => False
    end.

  Definition interp_clause_key ctx clk fk :=
    clk.(clause_rel) = fk.(fact_rel) /\
      Forall2 (interp_expr ctx) clk.(clause_inputs) fk.(fact_inputs).

  Definition interp_hyp_clause_val ctx clv fv :=
    match clv, fv with
    | outputs_clause es, outputs_fact es' =>
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
    interp_clause_key ctx cl.(hc_key) f.(hf_key) /\
      interp_hyp_clause_val ctx cl.(hc_val) f.(hf_val).

  Record concl_fact :=
    { cf_rel : rel;
      cf_args : list T }.

  Record local_fact :=
    { lf_key : fact_key;
      lf_value : list T }.

  (*TODO mupd should take as argument a default value, and it should be used here.*)

  Definition receive_fact (s : node_state) (f : local_fact) :=
    mupd s f.(lf_key)
      (fun val_data =>
         {| msgs_received := S val_data.(msgs_received);
           msgs_sent := val_data.(msgs_sent);
           aggs := match map.get val_data.(outputs) f.(lf_value) with
                   | Some tt =>
                       val_data.(aggs)
                   | None =>
                       map_values' (value' := T)
                         (fun agg v =>
                            match f.(lf_value) with
                            | [i; x] =>
                                agg_bop agg v x
                            | _ => v
                            end)
                         val_data.(aggs)
                   end;
           outputs := map.put val_data.(outputs) f.(lf_value) tt; |}).

  Definition send_fact (s : node_state) (f : local_fact) :=
    mupd s f.(lf_key)
      (fun val_data =>
         {| msgs_received := val_data.(msgs_received);
           msgs_sent := S val_data.(msgs_sent);
           aggs := val_data.(aggs);
           outputs := val_data.(outputs); |}).

  Definition interp_concl_clause ctx c f :=
    c.(cc_rel) = f.(cf_rel) /\
      Forall2 (interp_expr ctx) c.(cc_args) f.(cf_args).

  Definition lrule_impl (s : node_state) (r : local_rule) (concl : concl_fact) (hyps : list hyp_fact) :=
    exists ctx,
      Exists (fun c => interp_concl_clause ctx c concl) r.(local_rule_concls) /\
        Forall2 (interp_hyp_clause ctx) r.(local_rule_hyps) hyps.

  Definition lcan_deduce_fact (p : node_prog) (s : node_state) concl :=
    exists r hyps,
      In r p.(rules) /\
        lrule_impl s r concl hyps /\
        Forall (knows_hyp_fact s) hyps.

  Definition locally_forward (p : node_prog) (f : concl_fact) : list local_fact :=
    match map.get p.(local_forwarding_table) f.(cf_rel) with
    | Some clrels =>
        map (fun clrel =>
               {| lf_key :=
                   {| fact_rel := clrel.(corresp_lrel);
                     fact_inputs := apply_permutation clrel.(corresp_inputs) f.(cf_args) |};
                 lf_value := apply_permutation clrel.(corresp_outputs) f.(cf_args) |})
            clrels
    | None => []
    end.
End __.
Arguments concl_clause : clear implicits.
Arguments hyp_clause : clear implicits.
Arguments local_rule : clear implicits.
Arguments hyp_clause_key : clear implicits.
Arguments concl_fact : clear implicits.

  Fail Definition step (event : input_or_output) (s1 s2 : node_state) : Prop. Fail Admitted.
  (*theorem : for any sequence of input_or_output events, node state and spec state can deduce same facts.*)

Fail Definition learns_facts (p : node_prog) (s : node_state) new_facts :=
    forall f,
      In f new_facts <-> can_deduce_fact p s f.

Section __.
  Context {rel var fn aggregator T : Type}.
  Context `{sig : signature fn aggregator T}.
  Context {T_eqb : T -> T -> bool}.
  Context {context : map.map var T} {context_ok : map.ok context}.
  Context (num_args : rel -> nat).

  Local Notation clause := (clause rel var fn).
  Local Notation meta_clause := (meta_clause rel var fn).
  Local Notation fact := (fact rel T).
  Local Notation rule := (rule rel var fn aggregator).
  Local Notation non_meta_rule := (non_meta_rule rel var fn aggregator).
  Local Notation dfact := (dfact rel T).
  Local Notation prog := (prog rel var fn aggregator).

  Implicit Types known_facts sent_facts waiting_facts input_facts inputs : list dfact.
  Implicit Types nf result : dfact.
  Implicit Types mf_rel : rel.
  Implicit Types mf_args : list (option T).
  Implicit Types nf_args : list T.

  Variant low_rel :=
    | normal_rel (rel_name : rel)
    | done_receiving_from (rel_name : rel) (to_keep : list bool)
    (*above is like below, except it comes with two extra arguments:
      which source did we receive it from, and how many did we receive*)
    | done_receiving_rel (rel_name : rel) (to_keep : list bool)
    | done_sending_rel (rel_name : rel) (to_keep : list bool).

  Variant lrel :=
    | normal_lrel (rel_name : rel) (rel_inputs : list bool)
    | done_receiving_lrel (rel_name : rel) (to_keep : list bool)
    | done_sending_lrel (rel_name : rel) (to_keep : list bool).
  Definition lvar : Type := var + nat.
  Local Notation concl_clause := (concl_clause low_rel lvar fn).
  Local Notation hyp_clause := (hyp_clause lrel lvar fn aggregator).
  Local Notation local_rule := (local_rule low_rel lrel lvar fn aggregator).
  Local Notation clause_key := (hyp_clause_key lrel lvar fn).
  Local Notation expr := (Datalog.expr lvar fn).
  Local Notation concl_fact := (concl_fact low_rel T).

  Definition lower_clause_hyp (c : clause) : hyp_clause :=
    {| hc_key :=
        {| clause_rel :=
            normal_lrel c.(Datalog.clause_rel)
                           (map (fun _ => true) c.(Datalog.clause_args));
          clause_inputs := map (expr_varmap inl) c.(Datalog.clause_args) |};
      hc_val := outputs_clause []; |}.
  Definition lower_clause_concl (c : clause) : concl_clause :=
    {| cc_rel := normal_rel c.(Datalog.clause_rel);
      cc_args := map (expr_varmap inl) c.(Datalog.clause_args) |}.
  Definition lower_meta_clause_concl (c : meta_clause) : concl_clause :=
    {| cc_rel := done_sending_rel
                   c.(Datalog.meta_clause_rel)
                       (map is_Some c.(Datalog.meta_clause_args));
      cc_args := map (expr_varmap inl) (keep_Some c.(Datalog.meta_clause_args)); |}.
  Definition lower_meta_clause_hyp (c : meta_clause) : hyp_clause :=
    {| hc_key :=
        {| clause_rel := done_receiving_lrel
                           c.(Datalog.meta_clause_rel)
                               (map is_Some c.(Datalog.meta_clause_args));
          clause_inputs := map (expr_varmap inl) (keep_Some c.(Datalog.meta_clause_args)); |};
      hc_val := outputs_clause [] |}.
  Axiom count : aggregator.

  Print Local.concl_clause. Print clause_key. Print Local.hyp_clause_val.
  Print Local.local_rule.
  Definition lower_rule (r : rule) : list local_rule :=
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
        (*source_rel(_, _, 2, ... 9) concl_rel(_, 2, ..., 9)
          assume source_rel is 10-ary.*)
        let n := num_args source_rel in
        [{| local_rule_concls :=
             [{| cc_rel := normal_rel target_rel;
                cc_args := map var_expr (map inr (seq O (n - 1))); |}];
           local_rule_hyps :=
             [{| hc_key := {| clause_rel := done_receiving_lrel
                                              source_rel
                                              (false :: false :: repeat true (n - 2));
                             clause_inputs := map var_expr (map inr (seq 1 (n - 2))) |};
                hc_val := outputs_clause []; |};
              {| hc_key := {| clause_rel := normal_lrel
                                              source_rel
                                              (false :: false :: repeat true 8);
                             clause_inputs := map var_expr (map inr (seq 1 8)) |};
                hc_val := agg_clause agg (inr O) |}];
         |}]
    (* target_rel(val, c, d) :- done_receiving(source_rel, [2, 3])(c, d),
                                agg(source_rel, [2, 3])(c, d) = val
     *)
    end.

  Definition lower_dfact (f : dfact) : concl_fact :=
    match f with
    | normal_dfact R args =>
        {| cf_rel := normal_rel R; cf_args := args |}
    | meta_dfact R args source num =>
        {| cf_rel := done_receiving_from R (map is_Some args);
          cf_args := keep_Some args |}
    end.

  Fail Definition hyp_fact_of (f : concl_fact) : hyp_fact.

  Fail Definition corresp (p : node_prog) (ss : spec_node_state) (s : node_state) :=
    forall f,
      (forall outs,
          knows_hyp_fact s (hyp_fact_of (lower_dfact f)) <->
            In f ss.(known_facts)).
