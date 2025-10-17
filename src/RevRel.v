From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Permutation.


From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics.

From Datalog Require Import Datalog Map Tactics Fp List Dag Interpreter.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List.

Import ListNotations.

Section __.
  Context {rel var fn aggregator T : Type}.
  Context `{sig : signature fn aggregator T} `{query_sig : query_signature rel}.
  Context {context : map.map var T} {context_ok : map.ok context}.
  Context {var_eqb : var -> var -> bool} {var_eqb_spec :  forall x0 y0 : var, BoolSpec (x0 = y0) (x0 <> y0) (var_eqb x0 y0)}.

  Local Notation expr := (expr var fn).
  Local Notation rule := (rule rel var fn aggregator).
  Local Notation fact := (fact rel var fn).
  Local Notation agg_expr := (agg_expr rel var fn aggregator).

  Implicit Type r : rule.
  Implicit Type f : fact.
  Implicit Type ctx : context.
  Implicit Type aexpr : agg_expr.

  Definition rev_fact_rels f :=
    {| fact_R := f.(fact_R); fact_args := rev f.(fact_args) |}.
    
  Definition rev_aexpr_rels aexpr :=
    {| agg_agg := aexpr.(agg_agg);
      agg_i := aexpr.(agg_i);
      agg_vs := aexpr.(agg_vs);
      agg_s := aexpr.(agg_s);
      agg_body := aexpr.(agg_body);
      agg_hyps := map rev_fact_rels aexpr.(agg_hyps) |}.
  
  Definition rev_rule_rels r :=
    {| rule_concls := map rev_fact_rels r.(rule_concls);
      rule_hyps := map rev_fact_rels r.(rule_hyps);
      rule_agg := option_map (fun '(res, aexpr) => (res, rev_aexpr_rels aexpr)) r.(rule_agg) |}.

  Definition rev_prog_rels := map rev_rule_rels.

  Definition rev_fact'_rels (f' : rel * list T) := (fst f', rev (snd f')).

  Lemma rev_fact_correct ctx f fct' :
    interp_fact ctx f fct' ->
    interp_fact ctx (rev_fact_rels f) (rev_fact'_rels fct').
  Proof.
    invert 1. constructor. simpl. apply Forall2_rev. assumption.
  Qed.
  
  Lemma rev_aexpr_correct ctx aexpr res hyps :
    interp_agg_expr ctx aexpr res hyps ->
    interp_agg_expr ctx (rev_aexpr_rels aexpr) res (map (map rev_fact'_rels) hyps).
  Proof.
    intros H. invert H. cbv [rev_aexpr_rels]. simpl. econstructor; eauto.
    apply Forall3_map3. eapply Forall3_impl; [|eassumption]. simpl. clear.
    intros. fwd. do 2 eexists. intuition eauto. rewrite <- Forall2_map_l.
    rewrite <- Forall2_map_r. eapply Forall2_impl; [|eassumption].
    intros. apply rev_fact_correct. assumption.
  Qed.

  Lemma rev_rule_correct' r c hyps ahyps :
    rule_impl' r c hyps ahyps ->
    rule_impl' (rev_rule_rels r) (rev_fact'_rels c) (map rev_fact'_rels hyps) (map (map rev_fact'_rels) ahyps).
  Proof.
    intros H. invert H. invert H0.
    - simpl. eapply mk_rule_impl'; eauto.
      + simpl. rewrite <- H4. constructor.
      + simpl. apply Exists_map. eapply Exists_impl; [|eassumption].
        simpl. intros. apply rev_fact_correct. eassumption.
      + simpl. rewrite <- Forall2_map_l, <- Forall2_map_r.
        eapply Forall2_impl; [|eassumption]. intros. apply rev_fact_correct; eassumption.
    - simpl. eapply mk_rule_impl'; eauto.
      + simpl. rewrite <- H. econstructor.
        -- reflexivity.
        -- apply rev_aexpr_correct. eassumption.
      + simpl. apply Exists_map. eapply Exists_impl; [|eassumption].
        simpl. intros. apply rev_fact_correct. eassumption.
      + simpl. rewrite <- Forall2_map_l, <- Forall2_map_r.
        eapply Forall2_impl; [|eassumption]. intros. apply rev_fact_correct; eassumption.
  Qed.

  Lemma rev_rule_correct r c hyps :
    rule_impl r c hyps ->
    rule_impl (rev_rule_rels r) (rev_fact'_rels c) (map rev_fact'_rels hyps).
  Proof.
    cbv [rule_impl]. intros. fwd. do 2 eexists.
    intuition eauto using rev_rule_correct'.
    rewrite map_app. rewrite concat_map. reflexivity.
  Qed.

  Lemma rev_correct' p c :
    prog_impl_fact p c ->
    prog_impl_fact (rev_prog_rels p) (rev_fact'_rels c).
  Proof.
    induction 1. econstructor.
    { apply Exists_map. eapply Exists_impl; [|eassumption]. simpl. intros r Hr.
      apply rev_rule_correct. eassumption. }
    apply Forall_map. eapply Forall_impl; [|eassumption]. simpl.
    intros ? H'. exact H'.
  Qed.

  Ltac t :=
    repeat match goal with
           | _ => reflexivity || apply rev_involutive
           | _ => rewrite map_map
           | _ => erewrite map_ext; [apply map_id|]
           | _ => progress (cbv [rev_aexpr_rels rev_fact_rels rev_prog_rels rev_rule_rels]; simpl; intros; fwd)
           | _ => destruct_one_match || destruct_one_match_hyp
           | |- _ = ?a => is_var a;
                        match type of a with
                        | rule => destr a
                        | fact => destr a
                        | option _ => destr a
                        | agg_expr => destr a
                        end
           | _ => f_equal
           end.

  Lemma rev_prog_rels_involutive p :
    rev_prog_rels (rev_prog_rels p) = p.
  Proof. t. Qed.

  Lemma rev_fact'_rels_involutive c : rev_fact'_rels (rev_fact'_rels c) = c.
  Proof.
    destruct c. cbv [rev_fact'_rels]. simpl. rewrite rev_involutive. reflexivity.
  Qed.

  Lemma rev_correct p c :
    prog_impl_fact p c <-> prog_impl_fact (rev_prog_rels p) (rev_fact'_rels c).
  Proof.
    split; [apply rev_correct'|]. intros H.
    apply rev_correct' in H.
    rewrite rev_prog_rels_involutive, rev_fact'_rels_involutive in H.
    assumption.
  Qed.

  Lemma rev_dag' p :
    incl (rel_graph (rev_prog_rels p)) (rel_graph p).
  Proof.
    cbv [rel_graph]. Search incl flat_map. cbv [rev_prog_rels]. rewrite flat_map_map.
    apply incl_flat_map_strong; auto with incl. intros r.
    cbv [edges_of_rule]. simpl. rewrite flat_map_map.
    apply incl_flat_map_strong; auto with incl.
    intros f x H. rewrite in_map_iff in *. fwd. rewrite in_app_iff in *. simpl.
    exists (rev_fact_rels x0). simpl. split; [reflexivity|]. apply in_app_iff.
    destruct Hp1 as [Hp1|Hp1].
    - left. cbv [rule_agg_hyps] in *. simpl in *.
      destruct r.(rule_agg) as [(?&?)|]; simpl in *.
      + rewrite in_map_iff in *. fwd. t. rewrite rev_involutive. destruct x. assumption.
      + assumption.
    - rewrite in_map_iff in Hp1. t. rewrite rev_involutive. destruct x; simpl; auto.
  Qed.

  Lemma rev_dag p :
    dag' (rel_graph p) ->
    dag' (rel_graph (rev_prog_rels p)).
  Proof. eauto using rev_dag', dag'_incl. Qed.
End __.
