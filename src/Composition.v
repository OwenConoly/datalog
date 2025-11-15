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

From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics.
From Lower Require Import ATLDeep.

From Datalog Require Import QueryableToRunnable Datalog Map Tactics Fp List Dag Interpreter ZeroLowerBounds ATLUtils.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List.

From Datalog Require Import ATLToDatalog.

Import ListNotations.

Existing Instance ATLToDatalog.ATLSig.
Existing Instance ATLToDatalog.query_sig.
Section __.
  Context {context : map.map var obj} {context_ok : map.ok context}.
  Context {str_nat : map.map string nat} {str_nat_ok : map.ok str_nat}.
  Context {var_eqb : var -> var -> bool} {var_eqb_spec :  forall x0 y0 : var, BoolSpec (x0 = y0) (x0 <> y0) (var_eqb x0 y0)}.
  Context {valuation' : map.map Var.var Z} {valuation'_ok : map.ok valuation'}.

  Local Notation expr := (expr var fn).
  Local Notation rule := (rule rel var fn aggregator).
  Local Notation fact := (fact rel var fn).
  Local Notation agg_expr := (agg_expr rel var fn aggregator).

  Implicit Type r : rule.
  Implicit Type f : fact.
  Implicit Type ctx : context.
  Implicit Type aexpr : agg_expr.

  Definition composed_lower e out := make_good (lower e out).

  (*this theorem only says things about closed terms, which doesn't seem very useful*)
  (*it's modeled after the top-level ATL -> C theorem, which apparently has the same restriction?*)
  Lemma composed_lower_complete e out res sz :
    eval_expr $0 $0 $0 e res ->
    size_of e sz ->
    vars_good [] e ->
    gen_lbs_zero e ->
    forall idxs val,
      result_lookup_Z' idxs res val ->
      prog_impl_implication (composed_lower e out)
        (fun x => x = ((str_rel out, false), map Zobj idxs))
        ((str_rel out, true), Robj (toR val) :: map Zobj idxs).
  Proof.
    intros. pose proof lower_correct as H'.
    specialize (H' out _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) _ _ ltac:(eassumption)).
    eapply prog_impl_implication_weaken_hyp.
    - apply source_impl_target.
      + apply good_index_lower.
      + apply lower_goodish. auto.
      + eapply prog_impl_fact_prog_impl_implication with (Q := fun _ => False); [eassumption|].
        auto.
    - simpl. intros. destruct y as [[? ?] ?]. destruct b; [contradiction|].
      invert H4. reflexivity.
  Qed.
End __.


From Examples Require Import Blur Matmul.
From Inferpad Require Import Reify.

Derive matmul_reified in True as matmul_equiv.
Proof.
  assert (forall A B C m1 m2, matmul A B C m1 m2 = matmul A B C m1 m2).
  { cbv [matmul]. intros.
    match goal with
    | |- ?prog = _ => 
        let ast := reify prog in idtac prog;
                                 enough (matmul_reified = ast) by reflexivity
    end.
    subst matmul_reified. simpl. reflexivity. }
  constructor.
Qed.
Print matmul_reified.
Check @composed_lower.
From coqutil Require Import Map.SortedListString.
Check composed_lower. Check map.
Definition str_nat := map nat.
Check @composed_lower str_nat.
Compute (@composed_lower str_nat matmul_reified "output").
