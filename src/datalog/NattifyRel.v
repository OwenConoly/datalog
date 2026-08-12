From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.

From coqutil Require Import Map.Interface Eqb Datatypes.List.

From Datalog Require Import Datalog RelMap List Default.

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
    unwrap_or (length (rel_table p)) (index_of R (rel_table p)).

  Definition nattify_rel_prog (p : list rule) :=
    map (map_rule_rels (encode_rel p)) p.

  Definition nattify_rel_fact (p : list rule) (f : fact) :=
    map_fact (encode_rel p) f.

  Lemma rels_of_prog_in_table p :
    incl (flat_map all_rels p) (rel_table p).
  Proof. intros R HR. cbv [rel_table]. apply dedup_In. apply in_or_app. auto. Qed.

  (* nattify_rel_fact is injective on facts whose relation is in the table *)
  Lemma nattify_rel_fact_inj p a b :
    In (rel_of a) (rel_table p) ->
    nattify_rel_fact p a = nattify_rel_fact p b -> a = b.
  Proof.
    intros Hatab Heq. cbv [nattify_rel_fact] in Heq.
    apply (map_fact_inj_g (encode_rel p) a b); [|exact Heq].
    intros Henc. cbv [encode_rel] in Henc.
    apply index_of_unwrap_inj with (l := rel_table p); [exact Hatab | exact Henc].
  Qed.

  Theorem nattify_rel_correct p Q f0 :
    (forall f, Q f -> In (rel_of f) input_rels) ->
    prog_impl p Q f0 <->
    prog_impl (nattify_rel_prog p)
      (fun fn => exists g, fn = nattify_rel_fact p g /\ Q g)
      (nattify_rel_fact p f0).
  Proof.
    intros HQin.
    assert (forall f, Q f -> In (rel_of f) (rel_table p)) as HQtab.
    { intros f Hf. cbv [rel_table]. apply dedup_In. apply in_or_app. right.
      apply HQin. exact Hf. }
    cbv [nattify_rel_prog nattify_rel_fact].
    apply prog_impl_map_rule_rels_iff_inj.
    - cbv [encode_rel]. apply index_of_inj_on. apply rels_of_prog_in_table.
    - cbv [encode_rel]. apply index_of_inj_on_cons. apply rels_of_prog_in_table.
    - intros f1 f2 Heq. cbv [fact_equiv] in Heq.
      split; intros HQ.
      + apply nattify_rel_fact_inj in Heq; subst; auto.
      + symmetry in Heq. apply nattify_rel_fact_inj in Heq; subst; auto.
  Qed.
End NattifyRel.
