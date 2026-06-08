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
  Context {fn aggregator T : Type}.
  Context `{sig : signature fn aggregator T}.
  Context {T_eqb : T -> T -> bool}.
  Context {value_set : map.map (list T) unit}.
  Context {agg_to_T : map.map aggregator T}.
  Context (T_to_nat : T -> nat) (nat_to_T : nat -> T). (*bijection..*)

  Section impl.
    Context {rel var : Type}.
    Context {context : map.map var T} {context_ok : map.ok context}.
    Local Notation expr := (expr var fn).

    (*for each relation, store a list of index structures---that is, key-value pairs, with information about what to store about each key.*)
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
    | agg_clause (agg : aggregator) (num : var)
    | received_clause (num : var)
    | sent_clause (num : var).

    Record hyp_rel :=
      { hr_rel : rel;
        hr_idxs : idx_struct }.

    Record hyp_clause_key :=
      { hc_rel : hyp_rel;
        hc_key_args : list expr; }.

    Record hyp_clause :=
      { hc_key : hyp_clause_key;
        hc_val : hyp_clause_val }.

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

    Record concl_clause :=
      { cc_rel : rel;
        cc_args : list expr }.

    Record local_rule :=
      { local_rule_concls : list concl_clause;
        local_rule_hyps : list hyp_clause }.

    Record node_prog :=
      { n_relviews : rel_views;
        n_rules : list local_rule }.

    Record val_data :=
      { msgs_received : nat;
        msgs_sent : nat;
        aggs : agg_to_T;
        values : value_set }.

    Context {rels_data : map.map hyp_fact_key val_data}.

    Definition node_state := rels_data.

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
      { blf_key : hyp_fact_key;
        blf_value : list T }.

    (*TODO mupd should take as argument a default value, and it should be used here.*)

    Definition receive_fact (s : node_state) (f : basic_hyp_fact) :=
      mupd s f.(blf_key)
                 (fun val_data =>
                    {| msgs_received := S val_data.(msgs_received);
                      msgs_sent := val_data.(msgs_sent);
                      aggs := match map.get val_data.(values) f.(blf_value) with
                              | Some tt =>
                                  val_data.(aggs)
                              | None =>
                                  map_values' (value' := T)
                                    (fun agg v =>
                                       match f.(blf_value) with
                                       | [i; x] =>
                                           agg_bop agg v x
                                       | _ => v
                                       end)
                                    val_data.(aggs)
                              end;
                      values := map.put val_data.(values) f.(blf_value) tt; |}).

    Definition send_fact (s : node_state) (f : basic_hyp_fact) :=
      mupd s f.(blf_key)
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

    Fail Fail Definition idxs_satisfying {A} test (l : list A) :=
      map fst (filter (fun '(x, _) => test x) (combine l (seq O (length l)))).
    Definition select {A} (bs : list bool) (l : list A) :=
      map snd (filter (fun '(b, _) => b) (combine bs l)).
    Definition locally_forward (p : node_prog) (f : concl_fact) : list basic_hyp_fact :=
      match map.get p.(n_relviews) f.(cf_rel) with
      | Some vs =>
          map (fun '(idx_str, vals_info) =>
                 {| blf_key :=
                     {| hf_rel := {| hr_rel := f.(cf_rel);
                                    hr_idxs := idx_str; |};
                       hf_key_args := select idx_str.(key_idxs) f.(cf_args) |};
                   blf_value := select idx_str.(value_idxs) f.(cf_args) |})
            (map.tuples vs)
      | None => []
      end.
  End impl.
  Arguments hyp_clause : clear implicits.
  Arguments concl_clause : clear implicits.
  Arguments hyp_fact : clear implicits.
  Arguments node_prog : clear implicits.


  Context (rel var : Type).
  Context {context : map.map var T} {context_ok : map.ok context}.
  Context (is_input : rel -> bool).
  Context (senders : rel -> list nat).
  Section spec.
    Local Notation dfact := (dfact rel T).
    Local Notation rule := (rule rel var fn aggregator).
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

    Definition
    Definition spec_node_step ss ss' :=
      exists facts,
        Forall (new_facts p ss) facts /\
          ss' = fold_left (spec_
  End spec.

  Variant lrel :=
    | normal_rel (rel_name : rel)
    | done_receiving_from (rel_name : rel) (to_keep : list bool)
    (*above is like below, except it comes with two extra arguments:
      which source did we receive it from, and how many did we receive*)
    | done_receiving_rel (rel_name : rel) (to_keep : list bool)
    | done_sending_rel (rel_name : rel) (to_keep : list bool).

  Definition lvar : Type := var + nat.


(* Arguments concl_clause : clear implicits. *)
(* Arguments hyp_clause : clear implicits. *)
(* Arguments local_rule : clear implicits. *)
(* Arguments hyp_clause_key : clear implicits. *)
(* Arguments concl_fact : clear implicits. *)

  Fail Definition step (event : input_or_output) (s1 s2 : node_state) : Prop. Fail Admitted.
  (*theorem : for any sequence of input_or_output events, node state and spec state can deduce same facts.*)

Fail Definition learns_facts (p : node_prog) (s : node_state) new_facts :=
    forall f,
      In f new_facts <-> can_deduce_fact p s f.

  Context (num_args : rel -> nat).

  Local Notation clause := (clause rel var fn).
  Local Notation hyp_clause0 := (hyp_clause lrel lvar).
  Local Notation meta_clause := (meta_clause rel var fn).
  (* Local Notation fact := (fact rel T). *)
  Local Notation rule := (rule rel var fn aggregator).
  (* Local Notation non_meta_rule := (non_meta_rule rel var fn aggregator). *)
  Local Notation dfact := (dfact rel T).
  (* Local Notation prog := (prog rel var fn aggregator). *)
  (* Local Notation node_prog := (node_prog rel var fn aggregator). *)

  (* Implicit Types known_facts sent_facts waiting_facts input_facts inputs : list dfact. *)
  (* Implicit Types nf result : dfact. *)
  (* Implicit Types mf_rel : rel. *)
  (* Implicit Types mf_args : list (option T). *)
  (* Implicit Types nf_args : list T. *)

  (* Local Notation concl_clause := (concl_clause lrel lvar fn). *)
  (* Local Notation local_rule := (local_rule lrel lvar fn aggregator). *)
  (* Local Notation clause_key := (hyp_clause_key lrel lvar fn). *)
  (* Local Notation expr := (Datalog.expr lvar fn). *)
  (* Local Notation concl_fact := (concl_fact lrel T). *)
  (* Local Notation hyp_fact := (hyp_fact lrel aggregator T). *)

  Definition lower_clause_hyp (c : clause) : hyp_clause lrel lvar :=
    {| hc_key :=
        {| hc_rel := {| hr_rel := normal_rel c.(Datalog.clause_rel);
                       hr_idxs := {| key_idxs := map (fun _ => true) c.(Datalog.clause_args);
                                    value_idxs := []; |}; |};
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
                       hr_idxs := {| key_idxs := map is_Some c.(Datalog.meta_clause_args);
                                    value_idxs := []; |} |};
          hc_key_args := map (expr_varmap inl) (keep_Some c.(Datalog.meta_clause_args)); |};
      hc_val := value_clause [] |}.
  Axiom count : aggregator.

  Print concl_clause. Print hyp_clause_val.
  Print local_rule.
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
        (*source_rel(_, _, 2, ... 9) concl_rel(_, 2, ..., 9),
          assuming source_rel is 10-ary.*)
        let n := num_args source_rel in
        [{| local_rule_concls :=
             [{| cc_rel := normal_rel target_rel;
                cc_args := map var_expr (map inr (seq O (n - 1))); |}];
           local_rule_hyps :=
             [{| hc_key := {| hc_rel := {| hr_rel := done_receiving_rel
                                                       source_rel
                                                       (false :: false :: repeat true (n - 2));
                                          hr_idxs := {| key_idxs := repeat true (n - 2);
                                                       value_idxs := []; |} |};
                             hc_key_args := map var_expr (map inr (seq 1 (n - 2))) |};
                hc_val := value_clause []; |};
              {| hc_key := {| hc_rel := {| hr_rel := normal_rel source_rel;
                                          hr_idxs := {| key_idxs := false :: false :: repeat true 8;
                                                       value_idxs := []; |} |};
                             hc_key_args := map var_expr (map inr (seq 1 n)) |};
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
          cf_args :=
            let tl := nat_to_T num :: keep_Some args in
            match source with
            | None => tl
            | Some node_name => nat_to_T node_name :: tl
            end
        |}
    end.

  Definition hyp_fact_of (f : concl_fact) : hyp_fact lrel :=
    {| hf_key := {| hf_rel := {| hr_rel := f.(cf_rel);
                                hr_idxs := {| key_idxs := map (fun _ => true) f.(cf_args);
                                             value_idxs := []; |} |};
                   hf_key_args := f.(cf_args) |};
      hf_val := value_fact [] |}.

  Context {idx_structs_info : map.map idx_struct values_info}
    {rel_views : map.map lrel idx_structs_info}
    {rels_data : map.map (@hyp_fact_key lrel) val_data}.
  Local Notation node_prog0 := (node_prog lrel lvar idx_structs_info rel_views).
  Local Notation knows_hyp_fact0 := (knows_hyp_fact (rels_data := rels_data)).
  Definition corresp (p : node_prog0) (ss : spec_node_state) (s : node_state) :=
    forall f,
      knows_hyp_fact0 s (hyp_fact_of (lower_dfact f)) <->
        In f ss.(known_facts).

  Print receive_fact.
  Lemma receive_fact f :
    correspreceive_fact

End __.
