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
From Lower Require Import ATLDeep.

From Datalog Require Import QueryableToRunnable RevRel Datalog Map Tactics Fp List Dag Interpreter.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List.

From Datalog Require Import ATLToDatalog.

Import ListNotations.

Existing Instance ATLToDatalog.ATLSig.
Existing Instance ATLToDatalog.query_sig.
Section __.
  Context {context : map.map var obj} {context_ok : map.ok context}.
  Context {str_nat : map.map string nat} {str_nat_ok : map.ok str_nat}.
  Context {var_eqb : var -> var -> bool} {var_eqb_spec :  forall x0 y0 : var, BoolSpec (x0 = y0) (x0 <> y0) (var_eqb x0 y0)}.

  Local Notation expr := (expr var fn).
  Local Notation rule := (rule rel var fn aggregator).
  Local Notation fact := (fact rel var fn).
  Local Notation agg_expr := (agg_expr rel var fn aggregator).

  Implicit Type r : rule.
  Implicit Type f : fact.
  Implicit Type ctx : context.
  Implicit Type aexpr : agg_expr.

  Print lower.
  
  Definition composed_lower e out :=
    rev_prog_rels (make_good (rev_prog_rels (lower e out))).
  (*TODO correcness proof*)

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
