From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.

From coqutil Require Import Map.Interface Eqb Datatypes.List.

From Datalog Require Import Datalog RelMap List.

Import ListNotations.

Section NattifyRel.
  Context {rel : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.
  Context {rel_eqb : Eqb rel} {rel_eqb_ok : Eqb_ok rel_eqb}.
  Context (input_rels : list rel).

  Definition rel_table (p : list rule) : list rel :=
    dedup (flat_map all_rels p ++ input_rels).

  Definition encode_rel (p : list rule) (R : rel) : nat :=
    index_of R (rel_table p).

  Definition nattify_rel_prog (p : list rule) :=
    map (map_rule_rels (encode_rel p)) p.

  Definition nattify_rel_fact (p : list rule) (f : fact) :=
    map_fact (encode_rel p) f.

  Theorem nattify_rel_correct p Q f0 :
    (forall f, Q f -> In (rel_of f) input_rels) ->
    prog_impl p Q f0 <->
    prog_impl (nattify_rel_prog p)
      (fun fn => exists g, fn = nattify_rel_fact p g /\ Q g)
      (nattify_rel_fact p f0).
  Proof.
  Admitted.
End NattifyRel.
