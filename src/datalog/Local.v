From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import Classical_Prop.
From Stdlib Require Import Relations.Relation_Operators Relations.Operators_Properties.

From Datalog Require Import Map Tactics Fp List Dag Datalog Operational Interpreter.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List Datatypes.Option.

Import ListNotations.

Section __.
  Context {rel lrel var fn aggregator T : Type}.
  Context `{sig : signature fn aggregator T}.
  Context {T_eqb : T -> T -> bool}.
  Context {context : map.map var T} {context_ok : map.ok context}.
  Context {lrel_to_rel : map.map lrel rel} {lrel_to_rel_ok : map.ok lrel_to_rel}.
  Context {rel_to_lrel : map.map rel lrel} {rel_to_lrel_ok : map.ok rel_to_lrel}.

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
  Implicit Types p : prog.
  Implicit Types r : non_meta_rule.
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

  (* Definition lower_rule (r : rule) := *)
  (*   (*for each relation, find necessary index structures.. *)
  (*     then, compile each rule.*) *)
  (*   match r with *)
  (*   | *)

  Record node_prog :=
    { output_corresp : lrel_to_rel;
      input_corresp : rel_to_lrel;
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

  (*TODO add these to signature or sometihng*)
  Axiom interp_agg_bin : T -> T -> T.
  Axiom get_nat : T -> nat.
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
                                   map.map_values
                                     (fun v =>
                                        match outs with
                                        | [i; x] =>
                                            interp_agg_bin v x
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



  Definition node_comp_step (p : node_prog) (s1 s2 : node_state) : Prop :=
    forall f,
