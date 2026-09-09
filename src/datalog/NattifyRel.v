From Stdlib Require Import Lists.List.

From coqutil Require Import Eqb.

From Datalog Require Import Datalog RelMap List Default.

Import ListNotations.

Section NattifyRel.
  Context `{params : datalog_params}.
  Context {rel_eqb : Eqb rel} {rel_eqb_ok : Eqb_ok rel_eqb}.
  Context (input_rels : list rel).

  Definition rel_table (p : program) : list rel :=
    dedup (program.all_rels p ++ input_rels).

  Definition encode_rel (p : program) (R : rel) : nat :=
    unwrap_or (length (rel_table p)) (index_of R (rel_table p)).

  Definition nattify_rel_prog (p : program) :=
    map_program (encode_rel p) p.

  Definition nattify_rel_fact (p : program) (fct : fact) :=
    map_fact (encode_rel p) fct.

  Lemma prog_rels_in_table p R :
    In R (program.all_rels p) -> In R (rel_table p).
  Proof. intros. cbv [rel_table]. apply dedup_In. apply in_or_app. auto. Qed.

  (* nattify_rel_fact is injective on facts whose relation is in the table *)
  Lemma nattify_rel_fact_inj p a b :
    In (fact.rel a) (rel_table p) ->
    nattify_rel_fact p a = nattify_rel_fact p b ->
    a = b.
  Proof.
    intros Ha Heq. apply (fact_equiv_eq (encode_rel p)); [|exact Heq].
    intros Henc. eapply index_of_unwrap_inj; eassumption.
  Qed.

  Theorem nattify_rel_correct p Q fct :
    (forall g, Q g -> In (fact.rel g) input_rels) ->
    program.interp p Q fct <->
      program.interp (nattify_rel_prog p)
        (fun fct' => exists g, fct' = nattify_rel_fact p g /\ Q g)
        (nattify_rel_fact p fct).
  Proof.
    intros HQin.
    assert (HQtab : forall g, Q g -> In (fact.rel g) (rel_table p)).
    { intros g Hg. cbv [rel_table]. apply dedup_In. apply in_or_app. auto. }
    apply interp_map_iff_inj.
    - cbv [encode_rel]. apply index_of_inj_on_cons. exact (prog_rels_in_table p).
    - intros f1 f2 Heq. split; intros HQf.
      + replace f2 with f1; [assumption|]. apply (nattify_rel_fact_inj p); auto.
      + replace f1 with f2; [assumption|].
        apply (nattify_rel_fact_inj p); [auto | symmetry; exact Heq].
  Qed.
End NattifyRel.
