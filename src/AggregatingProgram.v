From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From coqutil Require Import Map.Interface Map.Properties Map.Solver.
From Datalog Require Import List Datalog (* FancyNotations *) .
Import ListNotations.

Section __.
Variant bop := sum | prod.
Variant type := val | set.
Let rel : Type := nat.
Let rule := rule rel nat bop bop.

Definition bop_id o :=
  match o with
  | sum => O
  | prod => 1
  end.

(*to make nontrivial use of some meta-rule features, should have prod and proj or something, maybe subset-satisfying-prop*)
Inductive Sexpr {var} : type -> Type :=
| Var : forall t, var t -> Sexpr t
| bop_over_vals : bop -> Sexpr val -> Sexpr val -> Sexpr val
| empty : Sexpr set
| singleton : Sexpr val -> Sexpr set
(* | union : Sexpr set -> Sexpr set -> Sexpr set *)
| intersection : Sexpr set -> Sexpr set -> Sexpr set
| let_in t1 t2 : Sexpr t1 -> (var t1 -> Sexpr t2) -> Sexpr t2
| bop_over_set : bop -> Sexpr set -> Sexpr val.
Arguments Sexpr : clear implicits.

Fixpoint compile_Sexpr (name : nat) (out : rel) {t} (e : Sexpr (fun _ => nat) t) : nat * list rule :=
  match e with
  | Var t x => (name,
                [normal_rule
                   [{| clause_R := (out, normal); clause_args := [var_expr O] |}]
                   [{| clause_R := (x, normal); clause_args := [var_expr O] |}]])
  | bop_over_vals o x y =>
      let x' := name in
      let (name1, p1) := compile_Sexpr (S name) x' x in
      let y' := name1 in
      let (name2, p2) := compile_Sexpr (S name1) y' y in
      (name2,
        normal_rule
          [{| clause_R := (out, normal); clause_args := [fun_expr o [var_expr O; var_expr (S O)]] |}]
          [{| clause_R := (x', normal); clause_args := [var_expr O] |};
           {| clause_R := (y', normal); clause_args := [var_expr (S O)] |}]
          :: p1 ++ p2)
  | empty => (name, [])
  | singleton x => (*we happen to represent sets in the same format as elements*)
      compile_Sexpr name out x
  | intersection x y =>
      let x' := name in
      let (name1, p1) := compile_Sexpr (S name) x' x in
      let y' := name1 in
      let (name2, p2) := compile_Sexpr (S name1) y' y in
      (name2,
        normal_rule
          [{| clause_R := (out, normal); clause_args := [var_expr O] |}]
          [{| clause_R := (x', normal); clause_args := [var_expr O] |};
           {| clause_R := (y', normal); clause_args := [var_expr O] |}]
          :: p1 ++ p2)
  | let_in t1 t2 x y =>
      let x' := name in
      let (name1, p1) := compile_Sexpr (S name) x' x in
      let (name2, p2) := compile_Sexpr (S name1) out (y x') in
      (name2, p1 ++ p2)
  | bop_over_set o x =>
      let x' := name in
      let (name1, p1) := compile_Sexpr (S name) x' x in
      (name1, agg_rule out o x' :: p1)
  end.

Definition interp_type t : Type :=
  match t with
  | val => nat
  | set => nat -> Prop
  end.

Definition interp_bop o x y :=
  match o with
  | sum => x + y
  | prod => x * y
  end.

Inductive interp_Sexpr : forall {t}, Sexpr interp_type t -> interp_type t -> Prop :=
| interp_Var t x :
  interp_Sexpr (Var t x) x
| interp_bop_over_vals o x y x' y' :
  interp_Sexpr x x' ->
  interp_Sexpr y y' ->
  interp_Sexpr (bop_over_vals o x y) (interp_bop o x' y')
| interp_empty :
  interp_Sexpr empty (fun _ => False)
| interp_singleton x x' :
  interp_Sexpr x x' ->
  interp_Sexpr (singleton x) (eq x')
(* | interp_union s1 s2 s1' s2' : *)
(*   interp_Sexpr s1 s1' -> *)
(*   interp_Sexpr s2 s2' -> *)
(*   interp_Sexpr (union s1 s2) (fun x => s1' x \/ s2' x) *)
| interp_intersection s1 s2 s1' s2' :
  interp_Sexpr s1 s1' ->
  interp_Sexpr s2 s2' ->
  interp_Sexpr (intersection s1 s2) (fun x => s1' x /\ s2' x)
| interp_let_in t1 t2 x y x' y' :
  interp_Sexpr x x' ->
  interp_Sexpr (y x') y' ->
  interp_Sexpr (let_in t1 t2 x y) y'
| interp_bop_over_set o (x : Sexpr _ set) x' l :
  interp_Sexpr x x' ->
  is_list_set x' l ->
  interp_Sexpr (bop_over_set o x) (fold_right (interp_bop o) (bop_id o) l).

Inductive Sexpr_with_args {var} : type -> Type :=
| with_args_nil t : Sexpr var t -> Sexpr_with_args t
| with_args_cons t : var t -> Sexpr_with_args t.
Arguments Sexpr_with_args : clear implicits.
