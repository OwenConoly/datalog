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

  Record spec_node_state :=
    { known_facts : list dfact;
      sent_facts : list dfact }.

  Definition spec_node_prog :=
    list rule.

  Definition spec_node_step (p : list rule) : spec_node_state -> spec_node_state -> Prop. Admitted.

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

  Record clause_key :=
    { clause_rel : lrel;
      clause_inputs : list expr }.

  Definition hyp_clause : Type :=
    clause_key * hyp_clause_val.

  Inductive hyp_fact_val :=
  | outputs_fact (outputs : list T)
  | agg_fact (agg : aggregator) (num : T)
  | received_fact (num : nat)
  | sent_fact (num : nat).

  Record fact_key :=
    { fact_rel : lrel;
      fact_inputs : list T }.

  Definition hyp_fact : Type :=
    fact_key * hyp_fact_val.

  Definition concl_clause : Type :=
    clause_key * list expr.

  Record local_rule :=
    { local_rule_concls : list concl_clause;
      local_rule_hyps : list hyp_clause }.

  Record rel_corresp :=
    { the_rel : rel;
      indices : list nat }.

  Context {lrel_to_rel_corresp : map.map lrel rel_corresp} {lrel_to_rel_ok : map.ok lrel_to_rel_corresp}.

  Record node_prog :=
    {
      (*we could have separate relname correspondences for input facts and output
        facts, but i don't see any reason to do that for now.*)
      rel_corresps : lrel_to_rel_corresp;
      local_rels : local_rels_info;
      rules : list local_rule }.

  Context {outputs_set : map.map (list T) unit}.
  Context {agg_to_T : map.map aggregator T}.

  Record inputs_data :=
    { msgs_received : nat;
      msgs_sent : nat;
      aggs : agg_to_T;
      outputs : outputs_set }.

  Context {inputs_to_data : map.map (list T) inputs_data}.
  Context {lrel_to_all_inputs_data : map.map lrel inputs_to_data}.

  Definition node_state :=
    lrel_to_all_inputs_data.

  Definition inputs_data_of (s : node_state) (k : fact_key) : option inputs_data :=
    match map.get s k.(fact_rel) with
    | Some inp_datas => map.get inp_datas k.(fact_inputs)
    | None => None
    end.

  Definition knows_hyp_fact (s : node_state) (f : hyp_fact) :=
    let (k, v) := f in
    match inputs_data_of s k with
    | Some inp_data =>
        match v with
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
    let (clk, clv) := cl in
    let (fk, fv) := f in
    interp_clause_key ctx clk fk /\ interp_hyp_clause_val ctx clv fv.

  Definition receive_fact (s : node_state) (R : lrel) (inps outs : list T) :=
    mupd s R (fun all_inps =>
                mupd all_inps inps
                  (fun inp_data =>
                     {| msgs_received := S inp_data.(msgs_received);
                       msgs_sent := inp_data.(msgs_sent);
                       aggs := match map.get inp_data.(outputs) outs with
                               | Some tt =>
                                   inp_data.(aggs)
                               | None =>
                                   map_values' (value' := T)
                                     (fun agg v =>
                                        match outs with
                                        | [i; x] =>
                                            agg_bop agg v x
                                        | _ => v
                                        end)
                                     inp_data.(aggs)
                               end;
                       outputs := map.put inp_data.(outputs) outs tt; |})).

  Definition send_fact (s : node_state) (R : lrel) (inps outs : list T) :=
    mupd s R (fun all_inps =>
                mupd all_inps inps
                  (fun inp_data =>
                     {| msgs_received := inp_data.(msgs_received);
                       msgs_sent := S inp_data.(msgs_sent);
                       aggs := inp_data.(aggs) ;
                       outputs := inp_data.(outputs); |})).

  Definition concl_fact : Type :=
    fact_key * list T.

  Definition interp_concl_clause ctx c f :=
    let '(ck, cv) := c in
    let '(fk, fv) := f in
    interp_clause_key ctx ck fk /\ Forall2 (interp_expr ctx) cv fv.

  Definition lrule_impl (s : node_state) (r : local_rule) (concl : concl_fact) (hyps : list hyp_fact) :=
    exists ctx,
      Exists (fun c => interp_concl_clause ctx c concl) r.(local_rule_concls) /\
        Forall2 (interp_hyp_clause ctx) r.(local_rule_hyps) hyps.

  Definition can_deduce_fact (p : node_prog) (s : node_state) concl :=
    exists r hyps,
      In r p.(rules) /\
        lrule_impl s r concl hyps /\
        Forall (knows_hyp_fact s) hyps.

  Definition localize_one (p : node_prog) (R : lrel) (args : list T) : option concl_fact :=
    match map.get p.(local_rels) R with
    | Some rinfo =>
        Some ({| fact_rel := R;
                fact_inputs := firstn rinfo.(num_inputs) args |},
            skipn rinfo.(num_inputs) args)
    | None => None
    end.

  Definition localize (p : node_prog) (f : dfact) : option (list concl_fact) :=
    match f with
    | normal_dfact R args =>
        option_all (map (fun '(lR, rc) =>
                           let args' := apply_permutation rc.(indices) args in
                           localize_one p lR args')
                      (map.tuples p.(rel_corresps)))
    | meta_dfact _ _ _ _ => None
    end.

  Definition globalize (p : node_prog) (f : concl_fact) : option dfact :=
    let (fk, fv) := f in
    match map.get p.(rel_corresps) fk.(fact_rel) with
    | Some rc =>
        Some (normal_dfact rc.(the_rel) (apply_permutation (invert_permutation rc.(indices)) (fk.(fact_inputs) ++ fv)))
    | _ =>
        None
    end.

  Fail Definition corresp (p : node_prog) (ss : spec_node_state) (s : node_state) :=
    forall fk,
      (forall outs,
          knows_hyp_fact s (fk, outputs_fact outs) <-> In (globalize p (fk, outs)) ss.(known_facts)).



  Fail Definition step (event : input_or_output) (s1 s2 : node_state) : Prop. Fail Admitted.
  (*theorem : for any sequence of input_or_output events, node state and spec state can deduce same facts.*)

  Definition learns_facts (p : node_prog) (s : node_state) new_facts :=
    forall f,
      In f new_facts <-> can_deduce_fact p s f.

End __.
Arguments concl_clause : clear implicits.
Arguments hyp_clause : clear implicits.
Arguments local_rule : clear implicits.
Arguments clause_key : clear implicits.

Section __.
  Context {rel var fn aggregator T : Type}.
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

  Variant lrel :=
    | normal_rel (rel_name : rel) (rel_inputs : list bool)
    | done_receiving_rel (rel_name : rel) (rel_inputs : list bool)
    | done_sending_rel (rel_name : rel) (rel_inputs : list bool).
  Definition lvar : Type := var + nat.
  Local Notation concl_clause := (concl_clause lrel lvar fn).
  Local Notation hyp_clause := (hyp_clause lrel lvar fn aggregator).
  Local Notation local_rule := (local_rule lrel lvar fn aggregator).
  Local Notation clause_key := (clause_key lrel lvar fn).
  Definition lower_clause (c : clause) : clause_key :=
    {| clause_rel := normal_rel c.(Datalog.clause_rel)
                                    (map (fun _ => true) c.(Datalog.clause_args));
      clause_inputs := map (expr_varmap inl) c.(Datalog.clause_args)
    |}.
  Search (option _ -> bool). About is_Some. About keep_Some. Check meta_clause_varmap.
  Definition lower_meta_clause_concl (c : meta_clause) : concl_clause :=
    ({| clause_rel := done_sending_rel
                        c.(Datalog.meta_clause_rel)
                            (map is_Some c.(Datalog.meta_clause_args));
       clause_inputs := map (expr_varmap inl) (keep_Some c.(Datalog.meta_clause_args));
     |},
      []).
  Print hyp_clause_val.
  Definition lower_meta_clause_hyp (c : meta_clause) : hyp_clause :=
    ({| clause_rel := done_receiving_rel
                        c.(Datalog.meta_clause_rel)
                            (map is_Some c.(Datalog.meta_clause_args));
       clause_inputs := map (expr_varmap inl) (keep_Some c.(Datalog.meta_clause_args));
     |},
      outputs_clause []).
  Axiom count : aggregator.
  Print Operational.dfact.

  Print Local.concl_clause. Print clause_key. Print Local.hyp_clause_val.
  Definition lower_rule (r : rule) : list local_rule :=
    match r with
    | normal_rule concls hyps =>
        [{| local_rule_concls := map (fun x => (lower_clause x, [])) concls;
           local_rule_hyps := map (fun x => (lower_clause x, outputs_clause [])) hyps |}]
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
        [{| local_rule_concls :=
             [({| clause_rel := normal_rel target_rel (repeat true 9);
                 clause_inputs := map var_expr (map inr (seq O 9)); |},
                [])];
           local_rule_hyps :=
             [({| clause_rel := done_receiving_rel
                                  source_rel
                                  (false :: false :: repeat true 8);
                 clause_inputs := map var_expr (map inr (seq 1 8)) |}, outputs_clause []);
              ({| clause_rel := normal_rel
                                  source_rel
                                  (false :: false :: repeat true 8);
                 clause_inputs := map var_expr (map inr (seq 1 8)) |},
                agg_clause agg (inr O))];
         |}]
    (* target_rel(val, c, d) :- done_receiving(source_rel, [2, 3])(c, d),
                                agg(source_rel, [2, 3])(c, d) = val
     *)
    end.
