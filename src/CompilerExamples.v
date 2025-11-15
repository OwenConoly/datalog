From Datalog Require Import Composition.
From Stdlib Require Import String.
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
From coqutil Require Import Map.SortedListString.
Definition str_nat := map nat.
Definition datalog_matmul := Eval compute in 
    (@composed_lower str_nat matmul_reified "output").
Print datalog_matmul.
