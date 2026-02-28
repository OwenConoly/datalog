From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From coqutil Require Import Map.Interface Map.Properties Map.Solver Datatypes.List.
From Datalog Require Import List Datalog (* FancyNotations *) .
Import ListNotations.

Section __.
Variant bop := sum | prod.
Variant type := val | set.
Let rel : Type := nat.
Variant obj0 :=
  | natobj' (_ : nat).
Variant obj :=
  | primitive (_ : obj0)
  (* | setobj (_ : nat -> Prop) *)
  (* | listsetobj (_ : list nat -> Prop) *)
  | setobj (_ : nat -> Prop)
  | factset (_ : rel * list obj0 -> Prop)
  | blank
  | iter.
Context (context : map.map nat obj).
Definition natobj x := primitive (natobj' x).
Let fact : Type := fact rel obj.
Variant fn :=
  | fn_lit (o : obj)
  | fn_bop (o : bop)
  | fn_fun (f : list (rel * list obj0 -> Prop) -> rel * list obj0 -> Prop).
Let rule := rule rel nat fn bop.
Let expr := expr nat fn.

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

Definition lit x : expr := fun_expr (fn_lit x) [].

Definition union : list expr -> expr :=
  fun_expr (fn_fun (fun args x => Exists (fun P => P x) args)).

Print signature.

Definition interp_bop o x y :=
  match o with
  | sum => x + y
  | prod => x * y
  end.
Print fn. Print option_all.
Definition interp_fn (f : fn) (args : list obj) : option obj :=
  match f with
  | fn_lit x => Some x
  | fn_bop o =>
      match args with
      | [primitive (natobj' x); primitive (natobj' y)] => Some (natobj (interp_bop o x y))
      | _ => None
      end
  | fn_fun g =>
      match option_all (map (fun x =>
                               match x with
                               | factset f => Some f
                               | _ => None
                               end) args)
      with
      | Some args' => Some (factset (g args'))
      | None => None
      end
  end.
Print signature. Print obj.
Definition get_set (s : obj) :=
  match s with
  | primitive _ => None
  | setobj P => Some (fun x =>
                       match x with
                       | primitive (natobj' x0) => P x0
                       | _ => False
                       end)
  | factset fs => None
  | blank => None
  | iter => None
  end.

Check fold_right.
Definition extract_nat (x : obj) :=
  match x with
  | primitive (natobj' x0) => Some x0
  | _ => None
  end.

Definition interp_agg o (i_xis : list (obj * obj)) :=
  match option_all (map extract_nat (map snd i_xis)) with
  | Some xis => natobj (fold_right (interp_bop o) (bop_id o) xis)
  | None => natobj O
  end.

Instance Sig : signature fn bop obj :=
  { interp_fun := interp_fn ;
    get_set := get_set;
    blank := blank;
    interp_agg := interp_agg }.

Definition closure (p : list rule) : list expr -> expr :=
  fun_expr (fn_fun (fun args x => prog_impl_implication (sig := Sig) p
                                 (fun y => exists y',
                                      Exists (fun P => P y') args /\
                                        y = {| fact_R := (fst y', normal);
                                              fact_args := map primitive (snd y') |})
                                 {| fact_R := (fst x, normal); fact_args := map primitive (snd x) |})).

Definition bare_rule : Type := (rel * list expr) * list (rel * list expr).

Definition is_blank (e : expr) :=
  match e with
  | fun_expr (fn_lit blank) [] => true
  | _ => false
  end.

(* Definition meta_rule_of (p : list rule) (r : bare_rule) := *)
(*   let (concl, hyps) := r in *)

Fixpoint compile_Sexpr (name : nat) (out : rel) {t} (e : Sexpr (fun _ => nat) t) : nat * list rule :=
  match e with
  | Var t x => (name,
                [normal_rule
                   [{| clause_R := (out, normal); clause_args := [var_expr O] |}]
                   [{| clause_R := (x, normal); clause_args := [var_expr O] |}];
                 normal_rule
                   [{| clause_R := (out, meta); clause_args := [var_expr O; lit blank] |}]
                   [{| clause_R := (x, meta); clause_args := [var_expr O; lit blank] |}]
                ])
  | bop_over_vals o x y =>
      let x' := name in
      let (name1, p1) := compile_Sexpr (S name) x' x in
      let y' := name1 in
      let (name2, p2) := compile_Sexpr (S name1) y' y in
      (name2,
        normal_rule
          [{| clause_R := (out, normal); clause_args := [fun_expr (fn_bop o) [var_expr O; var_expr (S O)]] |}]
          [{| clause_R := (x', normal); clause_args := [var_expr O] |};
           {| clause_R := (y', normal); clause_args := [var_expr (S O)] |}]
          :: normal_rule
          [{| clause_R := (out, meta); clause_args := [union; lit blank]|}]
          [{| clause_R := (x', meta); clause_args := [var_expr O; lit blank]|};
           {| clause_R := (y', meta); clause_args := [var_expr (S O); lit blank]|}]
          :: p1 ++ p2)
  | empty => (name, [normal_rule
                      [{| clause_R := (out, meta); clause_args := [fun_expr (fn_lit (listsetobj (fun _ => False))) []; fun_expr (fn_lit blank) []] |}]
                      []])
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
