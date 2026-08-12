From Stdlib Require Import QArith.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Stdlib Require Import ZArith.Zdiv.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.

From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics Common.
From Lower Require Import Zexpr Bexpr Sexpr Array Result ListMisc
  Meshgrid ContextsAgree ATLDeep Range.
From Datalog Require Import Datalog Dag Map List Tactics (*Interpreter QueryableToRunnable*) (*ATLUtils*) (*ZeroLowerBounds*) Blocks.
From Inferpad Require Import ATLPhoas TensorToResult.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Map.OfFunc Tactics.fwd Tactics.destr Tactics Decidable Datatypes.List.

Import Datatypes.
Import ListNotations.

(*source language syntax*)
Print pATLexpr.
(*source language semantics*)
Print result_of_pATLexpr.
(*some property that valid source programs should probably (?) have*)
Print sound_sizeof.

Fixpoint sizeof_prop {var n} (sizeof_var : var tZ -> option Z) (e : pATLexpr var n) (sz : list nat) : Prop :=
  let sizeof_prop := fun {n} => @sizeof_prop var n sizeof_var in
  match e with
  | Gen lo hi body =>
      exists lo' hi' sz',
      sizeof_pZexpr sizeof_var lo = Some lo' /\
        sizeof_pZexpr sizeof_var hi = Some hi' /\
        let n := Z.to_nat (hi' - lo') in
        sz = n :: sz' /\ 0 < n /\ forall x, sizeof_prop (body x) sz'
  | Sum lo hi body =>
      forall x, sizeof_prop (body x) sz
  | Guard p body =>
      sizeof_prop body sz
  | Lbind e1 e2 =>
      exists sz',
      sizeof_prop e1 sz' /\ forall x, sizeof_prop (e2 x) sz
  | Concat x y =>
      exists nx ny sz',
      sizeof_prop x (nx :: sz') /\ sizeof_prop y (ny :: sz') /\ sz = (nx + ny :: sz')
  | Flatten e =>
      exists a b sz',
      sizeof_prop e (a :: b :: sz') /\ sz = a * b :: sz'
  | Split k e =>
      exists a sz' k',
      sizeof_prop e (a :: sz') /\
        sizeof_pZexpr sizeof_var k = Some k' /\
        0 < Z.to_nat k' /\
        sz = a //n (Z.to_nat k') :: Z.to_nat k' :: sz'
  | Transpose e =>
      exists a b sz',
      sizeof_prop e (a :: b :: sz') /\ sz = b :: a :: sz'
  | Truncr n e | Truncl n e =>
                   exists m sz' n',
                   sizeof_prop e (m :: sz') /\
                     sizeof_pZexpr sizeof_var n = Some n' /\
                     Z.to_nat n' < m /\ sz = m - Z.to_nat n' :: sz'
  | Padr n e =>
      exists m sz' n',
      sizeof_prop e (m :: sz') /\
        sizeof_pZexpr sizeof_var n = Some n' /\
        sz = m + Z.to_nat n' :: sz'
  | Padl n e =>
      exists m sz' n',
      sizeof_prop e (m :: sz') /\
        sizeof_pZexpr sizeof_var n = Some n' /\
        sz = (Z.to_nat n' + m :: sz')
  | @Var _ n _ => sz = [] /\ n = O
  | @Get _ n v idxs =>
      length idxs = n /\ sz = [] /\
        match v with
        | Var _ => True
        | _ => False
        end
  | SBop _ x y =>
      sz = [] /\ sizeof_prop x [] /\ sizeof_prop y []
  | SIZR _ => sz = []
  end.

(*target language syntax*)
Print blocks_prog.
(*target language semantics*)
Print interp_blocks_prog.

(*example source program*)
(* GEN [i < 10] (IZR i) *)
Check IZR. (*the inclusion Z -> R*)
Definition example_pATLexpr {var} : pATLexpr var 1 :=
  Gen (ZZ_of_nat 0) (ZZ_of_nat 10)
    (fun i => SIZR (ZVar i)).
(*TODO fill these in*)
#[local] Instance lvar : lvarT := nat.
#[local] Instance exprvar : exprvarT := nat.

(* should i be seperating these definitions into more variants like in the previous compiler?
cause everything in the language is purely defined as fn, so maybe it wouldn't work, but
having every fn term be uner the fn variant might be messy when it comes to interpreting them with return variables?? *)
Variant fn : fnT :=
  fn_Add | fn_Sub | fn_Divf | fn_Divc | fn_Mul | fn_Mod | fn_Z0 | fn_Pos | fn_Neg | fn_Nat | fn_Opp
  | fn_Lit (x : Z) | fn_Lt | fn_Le | fn_And | fn_Not | fn_Div | fn_Get | fn_Eq.

#[local] Existing Instance fn.

Axiom (aggregator : aggregatorT).
Goal aggregatorT. Fail typeclasses eauto. Abort.
#[local] Existing Instance aggregator.

Definition var_of (var : Type) (t : type) : Type :=
  match t with
  | tZ => nat (*or exprvar, or something countably infinite...*)
  | tB => unit (*shouldn't matter what is here?*)
  | tensor_n n => var * nat (* this is what you meant by redefining var_of to tag with the depth right? *)
  end.

Section __.
Context {str_nat : map.map string nat} {str_nat_ok : map.ok str_nat}.

Definition ZBop_to_fn (op : Zbop) : fn :=
  match op with
  | ZTimes => fn_Mul
  | ZPlus => fn_Add
  | ZDivf => fn_Divf
  | ZDivc => fn_Divc
  | ZMinus => fn_Sub
  | ZMod => fn_Mod
end.

Inductive pZexpr' {var : Type} : Type :=
  | ZBop : Zbop -> pZexpr' -> pZexpr' -> pZexpr'
  | ZVar : var -> pZexpr'
  | ZLit : Z -> pZexpr'
  | Zopp : pZexpr' -> pZexpr'.
Arguments pZexpr' : clear implicits.


Fixpoint lower_pZexpr' (e : pZexpr' nat) : expr :=
  match e with
  | ZBop op x y => fun_expr (ZBop_to_fn op) [lower_pZexpr' x; lower_pZexpr' y]
  | ZVar x => var_expr x
  | ZLit p => fun_expr (fn_Lit p) []
  | Zopp x => fun_expr fn_Opp [lower_pZexpr' x]
end.

Inductive pATL_Sexpr' {var : type -> Type} : Type :=
| Get : forall n : nat, var (tensor_n n) -> list (pZexpr' (var tZ)) -> pATL_Sexpr'
| SBop : Sbop -> pATL_Sexpr' -> pATL_Sexpr' -> pATL_Sexpr'
| SLit : Z -> pATL_Sexpr'.
Arguments pATL_Sexpr' : clear implicits.


Definition sbop_to_fn (o : Sbop) : fn :=
  match o with
  | Mul => fn_Mul
  | Add => fn_Add
  | Div => fn_Div
  | Sub => fn_Sub
end.

(*
Gen_{i = 0}^{i = 10}
     Let x := i in
     x * x
*)
Fixpoint lower_pSexpr' {var} (idxs0 : list exprvar) (next_varname : exprvar) (e : pATL_Sexpr' (var_of var)) :
    expr (*value of expr*) *
    list clause (*hypotheses*) *
    exprvar (*next varname*) *
    list (lvar * var) :=
  match e with
  (* when i tried to update Get with your suggestion to vr, it wouldn't take jus var, so then i made it a var of tensor_n, and then
  that required a for all n : nat, and so now get has an extra variable (??) of n?? *)
  | Get n (var, depth) idxs =>
  (* i feel like this actually should work?? the value part might be wrong, but i basically just copied the defintion from your compiler, and then updated
  it to fit the new types, so i think that the hypotheses part is right?? *)
    (var_expr next_varname,
            [{| clause_rel := local next_varname; clause_args := var_expr ( next_varname) :: map var_expr (firstn depth idxs0) ++ map lower_pZexpr' idxs |}],
            S next_varname,
            [( next_varname, var)])
  | SBop o x y =>
    let '(e1, hyps1, next_varname, correspondences1) := lower_pSexpr' idxs0 next_varname x in
    let '(e2, hyps2, next_varname, correspondences2) := lower_pSexpr' idxs0 next_varname y in
    (fun_expr (sbop_to_fn o) [e1; e2], (hyps1 ++ hyps2)%list, next_varname, correspondences1 ++ correspondences2)
  | SLit x => (fun_expr (fn_Lit x) [], [], next_varname, [])
end.

(* this is to lower a pZexpr to a pZexpr' *)
Fixpoint lower_pZexpr {var : Type} (e : pZexpr var) : pZexpr' var :=
  match e with
  | ATLPhoas.ZBop op x y => ZBop op (lower_pZexpr x) (lower_pZexpr y)
  | ATLPhoas.ZVar x => ZVar x
  | ATLPhoas.ZZ0 => ZLit 0
  | ATLPhoas.ZZpos p => ZLit (Z.pos p)
  | ATLPhoas.ZZneg p => ZLit (Z.neg p)
  | ATLPhoas.ZZ_of_nat n => ZLit (Z.of_nat n)
  | ATLPhoas.ZZopp x => Zopp (lower_pZexpr x)
end.

Fixpoint stringvar_ZLit {var} (e : pZexpr var) : Z :=
  match e with
  | ATLPhoas.ZBop o x y => interp_Zbop o (stringvar_ZLit x) (stringvar_ZLit y)
  | ATLPhoas.ZVar _ => Z0
  | ATLPhoas.ZZ0 => 0%Z
  | ATLPhoas.ZZpos p => (Zpos p)
  | ATLPhoas.ZZneg p => (Zneg p)
  | ATLPhoas.ZZ_of_nat n => (Z.of_nat n)
  | ATLPhoas.ZZopp x => (stringvar_ZLit x)
  end.

Fixpoint stringvar_S {var} {n} (e : pATLexpr var n) : pATL_Sexpr' var :=
  match e with
  | ATLPhoas.SBop o x y =>
    let x' := stringvar_S x in
    let y' := stringvar_S y in
    SBop o x' y'
  | ATLPhoas.SIZR x => SLit (stringvar_ZLit x)
  | ATLPhoas.Get x idxs =>
    match x with
      | Var y => Get _ y (map lower_pZexpr idxs)
      | _ => SLit 0
      end
  | _ => SLit 0
  end.

Inductive pBexpr' {var : Type} : Type :=
	| BAnd : pBexpr' -> pBexpr' -> pBexpr'
  | BBop : Bbop -> pZexpr' var -> pZexpr' var -> pBexpr'.
Arguments pBexpr' : clear implicits.


Fixpoint lower_pBexpr {var} (e : pBexpr (var)) : pBexpr' (var) :=
  match e with
  | ATLPhoas.BAnd x y => BAnd (lower_pBexpr x) (lower_pBexpr y)
  | ATLPhoas.BBop b x y => BBop b (lower_pZexpr x) (lower_pZexpr y)
end.

Fixpoint lower_pBexpr' (e : pBexpr' nat) : expr :=
  match e with
  | BAnd x y => fun_expr fn_And [lower_pBexpr' x; lower_pBexpr' y]
  | BBop o x y =>
    match o with
    | BLt => fun_expr fn_Lt [lower_pZexpr' x; lower_pZexpr' y]
    | BLe => fun_expr fn_Le [lower_pZexpr' x; lower_pZexpr' y]
    | BEq => fun_expr fn_Eq [lower_pZexpr' x; lower_pZexpr' y]
    end
end.


Inductive pATLexpr' { var : type -> Type } : nat -> Type :=
  | Gen : forall n : nat,
          pZexpr' (var tZ) ->
          pZexpr' (var tZ) ->
          (var tZ -> pATLexpr' n) -> pATLexpr' (ATLPhoas.S n)
  | Sum : forall n : nat,
          pZexpr' (var tZ) ->
          pZexpr' (var tZ) -> (var tZ -> pATLexpr' n) -> pATLexpr' n
  | Guard : forall n : nat,
            pBexpr' (var tZ) -> pATLexpr' n -> pATLexpr' n
  | Lbind : forall n m : nat,
            pATLexpr' n ->
            (var (tensor_n n) -> pATLexpr' m) -> pATLexpr' m
  | Concat : forall n : nat,
             pATLexpr' (ATLPhoas.S n) ->
             pATLexpr' (ATLPhoas.S n) -> pATLexpr' (ATLPhoas.S n)
  | Flatten : forall n : nat,
              pATLexpr' (ATLPhoas.S (ATLPhoas.S n)) ->
              pATLexpr' (ATLPhoas.S n)
  | Split : forall n : nat,
            pZexpr' (var tZ) ->
            pATLexpr' (ATLPhoas.S n) ->
            pATLexpr' (ATLPhoas.S (ATLPhoas.S n))
  | Transpose : forall n : nat,
                pATLexpr' (ATLPhoas.S (ATLPhoas.S n)) ->
                pATLexpr' (ATLPhoas.S (ATLPhoas.S n))
  | Truncr : forall n : nat,
             pZexpr' (var tZ) ->
             pATLexpr' (ATLPhoas.S n) -> pATLexpr' (ATLPhoas.S n)
  | Truncl : forall n : nat,
             pZexpr' (var tZ) ->
             pATLexpr' (ATLPhoas.S n) -> pATLexpr' (ATLPhoas.S n)
  | Padr : forall {n : nat},
           pZexpr' (var tZ) ->
           pATLexpr' (ATLPhoas.S n) -> pATLexpr' (ATLPhoas.S n)
  | Padl : forall {n : nat},
           pZexpr' (var tZ) ->
           pATLexpr' (ATLPhoas.S n) -> pATLexpr' (ATLPhoas.S n)
  | Scalar : pATL_Sexpr' var -> pATLexpr' 0
  .

Arguments pATLexpr' : clear implicits.


Fixpoint create_garbage (var : type -> Type) (n : nat) : pATLexpr' (var) n :=
  match n with
  | 0 => Scalar (SLit 0)
  | S n' => Gen _ (ZLit Z0) (ZLit Z0) (fun t => create_garbage var n')
end.

(* i tried fixing this, but like i don't know, its just messy and maybe something is wrong?? *)
Fixpoint lower_pATLexpr {var n} (e : pATLexpr (var) n) : pATLexpr' (var) n :=
  match e with
  | ATLPhoas.Gen lo hi body => Gen _ (lower_pZexpr lo) (lower_pZexpr hi) (fun x => (lower_pATLexpr (body x)))
  | ATLPhoas.Sum lo hi body => Sum _ (lower_pZexpr lo) (lower_pZexpr hi) (fun x => (lower_pATLexpr (body x)))
  | ATLPhoas.Guard b e1 => Guard _ (lower_pBexpr b) (lower_pATLexpr e1)
  | ATLPhoas.Lbind x f => Lbind _ _ (lower_pATLexpr x) (fun x => (lower_pATLexpr (f x)))
  | ATLPhoas.Concat x y => Concat _ (lower_pATLexpr x) (lower_pATLexpr y)
  | ATLPhoas.Flatten x => Flatten _ (lower_pATLexpr x)
  | ATLPhoas.Split k x => Split _ (lower_pZexpr k) (lower_pATLexpr x)
  | ATLPhoas.Transpose x => Transpose _ (lower_pATLexpr x)
  | ATLPhoas.Truncr k x => Truncr _ (lower_pZexpr k) (lower_pATLexpr x)
  | ATLPhoas.Truncl k x => Truncl _ (lower_pZexpr k) (lower_pATLexpr x)
  | ATLPhoas.Padr k x => Padr (lower_pZexpr k) (lower_pATLexpr x)
  | ATLPhoas.Padl k x => Padl (lower_pZexpr k) (lower_pATLexpr x)
  | ATLPhoas.Var x => create_garbage _ _
  | ATLPhoas.Get _ _ | ATLPhoas.SBop _ _ _ | ATLPhoas.SIZR _ => Scalar (stringvar_S e)
end.

(* wrote this to translate a Zexpr into it's numerical value for some of the match cases with lower_pATLexpr' *)
Fixpoint eval_pZexpr'_total { var : Type } (e : pZexpr' var) : option Z :=
  match e with
  | ZBop o x y =>
    match eval_pZexpr'_total x, eval_pZexpr'_total y with
    | Some x', Some y' =>
      match o with
      | ZTimes => Some (x' * y')%Z
      | ZPlus => Some (x' + y')%Z
      | ZDivf => Some (Z.div x' y')
      | ZDivc => Some (Z.quot x' y')
      | ZMinus => Some (x' - y')%Z
      | ZMod => Some (Z.modulo x' y')
      end
    | _, _ => None
    end
  | ZVar x => None
  | ZLit x => Some x
  | Zopp x => option_map Z.opp (eval_pZexpr'_total x)
end.

(* var name explanation: f = function, e = expression, z = pZexpr', s = pSexpr' *)
Fixpoint get_block_size {var n} (e : pATLexpr' (var_of var) n) : list nat :=
  match e with
  | Gen n lo hi f =>
    match eval_pZexpr'_total hi, eval_pZexpr'_total lo with
    | Some hi', Some lo' => (Z.to_nat hi') - (Z.to_nat lo') :: get_block_size (f 0)
    | _, _ => [] (*garbage because this shouldn't happen*)
  end
  | Sum n lo hi f => get_block_size (f 0)
  | Guard n b e => get_block_size e
  | Lbind n m e f => get_block_size e
  | Concat n e1 e2 =>
    match get_block_size e1, get_block_size e2 with
    | x1 :: rest1, x2 :: rest2 => x1 + x2 :: rest1
    | _, _ => []
  end
  | Flatten n e =>
    match get_block_size e with
    | a :: b :: rest => a * b :: rest
    | _ => []
  end
  | Split n z e =>
    match eval_pZexpr'_total z with
    | Some z' =>
      let '(zVal) := (Z.to_nat z') in
      match get_block_size e with
      | x :: rest => (x / zVal) :: zVal :: rest
      | _ => []
      end
    | _ => []
  end
  | Transpose n e =>
    match get_block_size e with
    | a :: b :: rest => b :: a :: rest
    | _ => []
  end
  | Truncr n z e =>
    match eval_pZexpr'_total z with
      | Some z' =>
        let '(zVal) := (Z.to_nat z') in
        match get_block_size e with
        | x :: rest => (x - zVal) :: rest
        | _ => []
        end
      | _ => []
    end
  | Truncl n z e =>
    match eval_pZexpr'_total z with
      | Some z' =>
        let '(zVal) := (Z.to_nat z') in
        match get_block_size e with
        | x :: rest => (x - zVal) :: rest
        | _ => []
        end
      | _ => []
    end
  | Padr z e =>
    match eval_pZexpr'_total z with
      | Some z' =>
        let '(zVal) := (Z.to_nat z') in
        match get_block_size e with
        | x :: rest => (x + zVal) :: rest
        | _ => []
        end
      | _ => []
    end
  | Padl z e =>
    match eval_pZexpr'_total z with
      | Some z' =>
        let '(zVal) := (Z.to_nat z') in
        match get_block_size e with
        | x :: rest => (x + zVal) :: rest
        | _ => []
        end
      | _ => []
    end
  | Scalar s => 1 :: []
end.


Fixpoint lower_pATLexpr' {var n} (e : pATLexpr' (var_of var) n) (idxs : list exprvar) (true_rel : var) : blocks_prog var :=
  match e with
  | Gen n lo hi body =>
    lower_pATLexpr' (body (length idxs)) (idxs ++ [length idxs]) true_rel
  | Sum n lo hi body => Block 0 [] []
  | Guard n b body =>
    let dimvars := (seq O (length (get_block_size body))) in
    let x := length (get_block_size body) in
      LetIn (lower_pATLexpr' body idxs true_rel) (fun val =>
      Block 0 [(0, val); (1, true_rel)]
      [normal_rule
      [{| clause_rel := local 0;
          clause_args := var_expr x ::
                          map var_expr idxs ++
                          map var_expr dimvars |}]
      [{| clause_rel := input 0;
          clause_args := var_expr x ::
                          map var_expr idxs ++
                          map var_expr dimvars|};
        {| clause_rel := input 1; clause_args := [lower_pBexpr' b] |}];
      normal_rule
      [{| clause_rel := local 0;
          clause_args := fun_expr (fn_Lit 0) [] ::
                                   map var_expr idxs ++
                                   map var_expr dimvars |}]
      [{| clause_rel := input 1;
          clause_args := [fun_expr fn_Not [lower_pBexpr' b]] |}]])
  | Lbind n m x f =>
    LetIn (lower_pATLexpr' x idxs true_rel) (fun val =>
      lower_pATLexpr' (f (val, (length idxs))) idxs true_rel)
  | Concat n e1 e2 =>
  (* using n instead of size of e1 here because e1 no longer has a size*)
      let dimvars := seq O (length (get_block_size e1) - 1) in
      let dimvarO := length (get_block_size e1) - 1 in
      let x := length (get_block_size e1) in
      (* using 0 and 1 here for pragmatic reasons *)
      let aux1 := 1 in
      let aux2 := S aux1 in
      let out := S aux2 in
      let len1 := Z.of_nat match get_block_size e1 with
                    | [] => 0
                    | n :: _ => n
                    end in
      LetIn (lower_pATLexpr' e1 idxs true_rel) (fun val1 =>
        LetIn (lower_pATLexpr' e2 idxs true_rel) (fun val2 =>
          Block out [(aux1, val1); (aux2, val2); (0, true_rel)]
          [normal_rule
          (* i feel like this might work now : i added in the true_rel statemetns, and also it returns the out, so maybe it works???? *)
          [{| clause_rel := local out; clause_args := var_expr x :: map var_expr idxs ++ map var_expr (dimvarO :: dimvars) |}]
          [{| clause_rel := input aux1; clause_args := var_expr x :: map var_expr idxs ++ map var_expr (dimvarO :: dimvars) |};
          {| clause_rel := input 0; clause_args := [fun_expr fn_Lt [var_expr dimvarO; fun_expr (fn_Lit len1) []]] |}];
          normal_rule
          [{| clause_rel := local out; clause_args := var_expr x :: map var_expr idxs ++ map var_expr (dimvarO :: dimvars) |}]
          [{| clause_rel := input aux2; clause_args := var_expr x :: map var_expr idxs ++ fun_expr fn_Add [] :: map var_expr dimvars |};
          {| clause_rel := input 0; clause_args := [fun_expr fn_Le [fun_expr (fn_Lit len1) []; var_expr dimvarO]] |}]]))
  | Flatten n e =>
  (* using n instead of e here because you can't get length from e anymore *)
    let dimvars := (seq O (length (get_block_size e) - 2)) in
      let dimvarO := (length (get_block_size e) - 2) in
      let x := (length (get_block_size e) - 1) in
      (* same as x but i feel like the match statement doesn't work here *)
      let len2 := Z.of_nat match get_block_size e with
                    | _ :: di :: _ => di
                    | _ => 0
                    end in
      let aux := 0 in
      (* out is probably redundant here but it's just to show that there needs to be some number for the clause_rel of the rule *)
      let out := S aux in
      LetIn (lower_pATLexpr' e idxs true_rel) (fun val =>
      Block out [(aux, val)]
      [normal_rule
      [{| clause_rel := local out; clause_args :=
                                 var_expr x ::
                                   map var_expr idxs ++
                                   var_expr dimvarO ::
                                   map var_expr dimvars|}]
      [{| clause_rel := input aux; clause_args := var_expr x ::
                                            map var_expr idxs ++
                                            fun_expr fn_Divf
                                            [var_expr dimvarO;
                                             fun_expr (fn_Lit len2) []] ::
                                            fun_expr fn_Mod
                                            [var_expr dimvarO;
                                             fun_expr (fn_Lit len2) []] ::
                                            map var_expr dimvars |}]])
  | Split n k e =>
    let dimvars := (seq O (length (get_block_size e) - 1)) in
    let dimvar1 := (length (get_block_size e) - 1) in
    let dimvar2 := length (get_block_size e) in
    let x := (S (length (get_block_size e))) in
    let k' := Z.of_nat (Z.to_nat (
      match eval_pZexpr'_total k with
      | Some kz => kz
      | None => 0 end)) in
    (* this is an issue because there's no way to get the len currently *)
    let len := Z.of_nat match get_block_size e with
                    | d :: _ => d
                    | _ => 0
                    end in
    let aux := 1 in
    let out := S aux in
    let pad_start := (len mod k')%Z in
    (* i had to put the facts for the first rule's hypotheses' hypothesis in let statements because there were weird errors with brackets *)
    let eq_check := fun_expr fn_Eq [var_expr dimvar1; fun_expr (fn_Lit (len / k')) []] in
    let le_check := fun_expr fn_Le [fun_expr (fn_Lit pad_start) []; var_expr dimvar2] in
    let bound_check := fun_expr fn_Not [fun_expr fn_And [eq_check; le_check]] in
    LetIn (lower_pATLexpr' e idxs true_rel) (fun val =>
      Block out [(aux, val); (0, true_rel)]
      [normal_rule [{| clause_rel := local out;
                        clause_args := var_expr x ::
                                   (map var_expr idxs ++
                                   (var_expr dimvar1 ::
                                   (var_expr dimvar2 ::
                                   map var_expr dimvars)))|}]
                  [ {| clause_rel := input aux;
                        clause_args := var_expr x ::
                                  (map var_expr idxs ++
                                  (fun_expr fn_Add
                                  [fun_expr fn_Mul
                                      [var_expr dimvar1;
                                      fun_expr (fn_Lit k') []];
                                    var_expr dimvar2] ::
                                  map var_expr dimvars)) |};
                        {| clause_rel := input 0; clause_args := [bound_check] |} ];
      normal_rule [ {| clause_rel := local out;
                    clause_args := fun_expr (fn_Lit 0) [] ::
                                   map var_expr idxs ++
                                   fun_expr (fn_Lit (len / k')) [] ::
                                   var_expr dimvar1 ::
                                   map var_expr dimvars|}]
                  [{| clause_rel := input 0;
                    clause_args := [fun_expr fn_Le
                                             [fun_expr (fn_Lit pad_start) [];
                                              var_expr dimvar1]] |}]])
  | Transpose n x =>
    let dimvars := (seq O (length (get_block_size x) - 2)) in
      let dimvar1 := (length (get_block_size x) - 1) in
      let dimvar2 := length (get_block_size x) in
      let Sn := (S (length (get_block_size x))) in
      let out := 1 in
        LetIn (lower_pATLexpr' x idxs true_rel)
        (fun val => Block out [(0, val)]
          [normal_rule
          [{| clause_rel := local out; clause_args := [var_expr Sn] ++ map var_expr idxs
                    ++ [var_expr dimvar2] ++ [var_expr dimvar1] ++ map var_expr dimvars |}]
          [{| clause_rel := input 0; clause_args := [var_expr Sn] ++ map var_expr idxs
                    ++ [var_expr dimvar1] ++ [var_expr dimvar2] ++ map var_expr dimvars |}]])
  | Truncr n k x => lower_pATLexpr' x idxs true_rel
  | Truncl m k e =>
    let dimvars := (seq O (length (get_block_size e) - 1)) in
    let dimvar1 := (length (get_block_size e) - 1) in
    (* placeholder *)
    let x := length (get_block_size e) in
    let k' :=   Z.of_nat (Z.to_nat (
      match eval_pZexpr'_total k with
      | Some kz => kz
      | None => 0 end)) in
    let aux := 0 in
    let out := S aux in
    LetIn (lower_pATLexpr' e idxs true_rel) (fun val =>
      (* not sure what numbers to use for block's name + values here*)
      Block out [(aux, val)]
      [normal_rule
      [{| clause_rel := local out; clause_args :=
                                 var_expr x ::
                                   map var_expr idxs ++
                                   var_expr dimvar1 ::
                                   map var_expr dimvars|}]
      [{| clause_rel := input aux; clause_args :=
                              var_expr x ::
                                 map var_expr idxs ++
                                 fun_expr fn_Add
                                 [fun_expr (fn_Lit k') [];
                                  var_expr dimvar1] ::
                                 map var_expr dimvars  |}]])
  | Padr k e =>
    let dimvars := seq O (length (get_block_size e) - 1) in
    let dimvar1 := length (get_block_size e) - 1 in
    let x := length (get_block_size e) in
    let k' := Z.of_nat (Z.to_nat (
      match eval_pZexpr'_total k with
      | Some kz => kz
      | None => 0 end)) in
    let aux := 0 in
    let out := S aux in
    let len := Z.of_nat match get_block_size e with
                    | d :: _ => d
                    | _ => 0
                    end in
    LetIn (lower_pATLexpr' e idxs true_rel) (fun val =>
      Block out [(aux, val); (2, true_rel)]
      [normal_rule
      [{| clause_rel := local out;
          clause_args := var_expr x ::
                    map var_expr idxs ++
                    var_expr dimvar1 ::
                    map var_expr dimvars |}]
      [{| clause_rel := input aux;
          clause_args := var_expr x ::
                          map var_expr idxs ++
                          var_expr dimvar1 ::
                          map var_expr dimvars|};
        {| clause_rel := input 2;
          clause_args := [fun_expr fn_Lt
                            [var_expr dimvar1;
                              fun_expr (fn_Lit len) []]] |}];
      normal_rule
      [{| clause_rel := local out;
          clause_args := fun_expr (fn_Lit 0) [] ::
                            map var_expr idxs ++
                            var_expr dimvar1 ::
                            map var_expr dimvars |}]
      [{| clause_rel := input 2;
          clause_args := [fun_expr fn_Le
                            [fun_expr (fn_Lit len) [];
                              var_expr dimvar1]] |}]])
  | Padl k e =>
    let dimvars := seq O (length (get_block_size e) - 1) in
    let dimvar1 := length (get_block_size e) - 1 in
    let x := length (get_block_size e) in
    let k' := Z.of_nat (Z.to_nat (
      match eval_pZexpr'_total k with
      | Some kz => kz
      | None => 0 end)) in
    let aux := 0 in
    let out := S aux in
    LetIn (lower_pATLexpr' e idxs true_rel) (fun val =>
    Block out [(aux, val); (2, true_rel)]
    [normal_rule
    [{| clause_rel := local out;
      clause_args := var_expr x ::
                      map var_expr idxs ++
                      var_expr dimvar1 ::
                      map var_expr dimvars|}]
    [{| clause_rel := input aux;
      clause_args := var_expr x ::
                    map var_expr idxs ++
                    fun_expr fn_Sub
                    [var_expr dimvar1;
                    fun_expr (fn_Lit k') []] ::
                    map var_expr dimvars |};
      {| clause_rel := input 2;
      clause_args := [fun_expr fn_Le
                      [fun_expr (fn_Lit k') [];
                      var_expr dimvar1]] |}];
    normal_rule
    [{| clause_rel := local out;
    clause_args := fun_expr (fn_Lit 0) [] ::
                    map var_expr idxs ++
                    var_expr dimvar1 ::
                    map var_expr dimvars |}]
    [{| clause_rel := input 2;
    clause_args := [fun_expr fn_Lt
                    [var_expr dimvar1;
                    fun_expr (fn_Lit k') []]] |}]])
  | Scalar x =>
    let '(value, hyps, next_varname, correspondences) := (lower_pSexpr' idxs 0 x) in
      Block next_varname correspondences
          [normal_rule [{| clause_rel := local next_varname; clause_args := [value] |}] hyps]
  end.

Definition lower_main {var n} (e : pATLexpr (var_of var) n) (true_rel : var): blocks_prog var :=
  let '(e') := lower_pATLexpr e in
  lower_pATLexpr' e' [] true_rel.

(* end of compiler, this stuff should go in ATLToDatalog semantics, but that isn't working *)

Fixpoint dim_n (n : nat) : Set :=
  match n with
  | O => R
  | S n' => list (dim_n n')
  end.


Definition interp_type t : Type :=
  match t with
  | tZ => Z
  | tB => bool
  | tensor_n n => dim_n n
  end.

Definition interp_type_tagged t : Type :=
  match t with
  | tZ => tagged_Z
  | tB => bool
  | tensor_n n => dim_n n
  end.



Fixpoint interp_pZexpr' (e : pZexpr' tagged_Z) : Z :=
  match e with
  | ZBop o x y => interp_Zbop o (interp_pZexpr' x) (interp_pZexpr' y)
  | ZVar x => x
  | ZLit x => x
  | Zopp x => - interp_pZexpr' x
end.

Fixpoint interp_pBexpr' (e : pBexpr' tagged_Z) : bool :=
  match e with
  | BAnd a b => interp_pBexpr' a && interp_pBexpr' b
  | BBop o x y => interp_Bbop o (interp_pZexpr' x) (interp_pZexpr' y)
end.

Fixpoint interp_pSexpr' (e : pATL_Sexpr' interp_type_tagged) : R :=
  match e with
  | Get n x idxs => get_R x (map interp_pZexpr' idxs)
  | SBop o x y => interp_Sbop o (interp_pSexpr' x) (interp_pSexpr' y)
  | SLit z => IZR z
end.

Fixpoint interp_pATLexpr' {n} (e : pATLexpr' interp_type_tagged n) : interp_type (tensor_n n) :=
  match e with
  | Gen n lo hi body =>
      genr (interp_pZexpr' lo) (interp_pZexpr' hi) (fun x => interp_pATLexpr' (body (itervarZ x)))
  | Sum n0 lo hi body =>
      sumr (interp_pZexpr' lo) (interp_pZexpr' hi) (fun x => interp_pATLexpr' (body (itervarZ x)))
  | Guard n b e1 => iverson (interp_pBexpr' b) (interp_pATLexpr' e1)
  | Lbind n m x f => let_binding (interp_pATLexpr' x) (fun x0 => interp_pATLexpr' (f x0))
  | Concat n x y => (*ATL.concat (interp_pATLexpr' x) (interp_pATLexpr' y) *)
  @ATL.concat (interp_type (tensor_n n)) (dim_n_TensorElem n) (interp_pATLexpr' x) (interp_pATLexpr' y)
  | Flatten n x => Common.flatten (interp_pATLexpr' x)
  | Split n k x => Tile (interp_pATLexpr' x) (interp_pZexpr' k)
  | Transpose n x => transpose (interp_pATLexpr' x)
  | Truncr n k x => Common.Truncr (interp_pZexpr' k) (interp_pATLexpr' x)
  | Truncl n k x => Common.Truncl (interp_pZexpr' k) (interp_pATLexpr' x)
  | Padl k x => Common.Padl (interp_pZexpr' k) (interp_pATLexpr' x)
  | Padr k x => Common.Padr (interp_pZexpr' k) (interp_pATLexpr' x)
  | Scalar x => interp_pSexpr' x
  end.

Lemma pZexpr'_works : forall z, interp_pZexpr' (lower_pZexpr z) = interp_pZexpr z.
Proof.
  intros z.
  induction z as
  [ z1 z2 IHz1 z3 IHz2 (* ZBop *)
  | v                   (* ZVar *)
  |                       (* ZZ0 *)
  | p                     (* ZZpos *)
  | p                     (* ZZneg *)
  | n                     (* ZZ_of_nat *)
  | z IHz ].              (* ZZopp *)
  - simpl. rewrite IHz1. rewrite IHz2. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IHz. reflexivity.
Qed.

Lemma pBexpr'_works : forall b, interp_pBexpr' (lower_pBexpr b) = interp_pBexpr b.
Proof.
 intros b.
 induction b as
 [ b1 IHb1 b2 IHb2 (* band *)
 | b p p0 (* bbop *)].
 - simpl. rewrite IHb1. rewrite IHb2. reflexivity.
 - simpl. rewrite !pZexpr'_works. reflexivity.
Qed.

Definition sizeof_var (v : tagged_Z) : option Z := Some (untag_Z v).

Definition dummy_tensor (n : nat) : dim_n n :=
  match n with
  | O => 0%R
  | S n' => []
  end.

Definition dummy (t : type) : interp_type_tagged t :=
  match t with
  | tZ => itervarZ 0
  | tB => true
  | tensor_n n => dummy_tensor n
  end.

Lemma stringvar_S_works (e : pATLexpr interp_type_tagged 0) sz :
  sizeof_prop sizeof_var e sz -> sz = [] ->
  interp_pSexpr' (stringvar_S e) = interp_pATLexpr e.
Proof.
Admitted. (* still have to write this *)


Theorem semantics_work : forall {n} (e : pATLexpr interp_type_tagged n) (sz : list nat),
      sizeof_prop sizeof_var e sz ->
      interp_pATLexpr' (lower_pATLexpr e) = interp_pATLexpr e.
Proof.
  intros n e.
  induction e as
  [ n p p0 p1 H                    (* Gen *)
  | n p p0 p1 H                    (* Sum *)
  | n p e IH                       (* Guard *)
  | n m e1 IH1 f IH2               (* Lbind *)
  | n e1 IH1 e2 IH2                (* Concat *)
  | n e IH                         (* Flatten *)
  | n p e IH                       (* Split *)
  | n e IH                         (* Transpose *)
  | n p e IH                       (* Truncr *)
  | n p e IH                       (* Truncl *)
  | n p e IH                       (* Padr *)
  | n p e IH                       (* Padl *)
  | n v                            (* Var *)
  | n e IH l                       (* Get *)
  | s e1 IH1 e2 IH2                (* SBop *)
  | p ].                           (* SIZR *)
  - intros sz szH. simpl. rewrite !pZexpr'_works.
    f_equal. apply functional_extensionality.
    intros x. inversion szH.
    destruct H0 as [hi' [sz' [Hlo [Hhi [Hsz [Hpos Hbody]]]]]].
    rewrite (H (itervarZ x) sz').
    + reflexivity.
    + apply Hbody.
  - intros sz szH. simpl. rewrite !pZexpr'_works.
    f_equal. apply functional_extensionality.
    intros x. rewrite (H (itervarZ x) sz).
    + reflexivity.
    + apply szH.
  - intros sz szH. simpl. rewrite !pBexpr'_works.
    f_equal. apply (IH sz). exact szH.
  - intros sz szH. simpl in szH.
    destruct szH as [sz' [Hsz1 Hsz2]]. 
    simpl. f_equal.
    + apply (IH1 sz'). apply Hsz1.
    + apply functional_extensionality. intros x. 
      rewrite (IH2 x sz).
      * reflexivity.
      * apply Hsz2.
  - intros sz szH. simpl. 
    destruct szH as [nx [ny [sz' [Hx [Hy Hsz]]]]].
    f_equal.
    + apply (IH1 (nx :: sz')). apply Hx.
    + apply (IH2 (ny :: sz')). apply Hy.
  - intros sz szH. simpl.
    f_equal. 
    destruct szH as [a [b [sz' [He Hsz]]]].
    apply (IH (a :: b :: sz')). apply He.
  - intros sz szH. simpl.
    destruct szH as [a [sz' [k' [He [Hpos Hsz]]]]].
    f_equal.
    + apply (IH (a :: sz')). apply He.
    + apply pZexpr'_works.
  - intros sz szH. simpl.
    destruct szH as [a [b [sz' [He Hsz]]]].
    f_equal. apply (IH (a :: b :: sz')). apply He.
  - intros sz szH. simpl.
    destruct szH as [m [sz' [n' [He [Hn [Hlt Hsz]]]]]].
    f_equal.
    + apply pZexpr'_works.
    + apply (IH (m :: sz')). apply He.
  - intros sz szH. simpl.
    destruct szH as [m [sz' [n' [He [Hn [Hlt Hsz]]]]]].
    f_equal.
    + apply pZexpr'_works.
    + apply (IH (m :: sz')).  apply He.
  - intros sz szH. simpl.
    destruct szH as [m [sz' [n' [He [Hn Hsz]]]]].
    f_equal.
    + apply pZexpr'_works.
    + apply (IH (m :: sz')). apply He.
  - intros sz szH. simpl.
    destruct szH as [m [sz' [n' [He [Hn Hsz]]]]].
    f_equal.
    + apply pZexpr'_works.
    + apply (IH (m :: sz')). apply He.
  - intros sz szH. simpl.
    destruct szH as [Hsz Hn].
    subst n. simpl. admit.
  - intros sz szH.
    destruct szH as [Hlen [Hsz Hv]].
    destruct e eqn:Ee; simpl in Hv; try contradiction.
    simpl. rewrite map_map. f_equal.
    apply map_ext. intros a. apply pZexpr'_works.
  - intros sz szH.
    destruct szH as [Hsz [Hx Hy]].
    simpl. f_equal.
    + apply (stringvar_S_works e1 []).
      * apply Hx. 
      * reflexivity.
    + apply (stringvar_S_works e2 []).
      * apply Hy.
      * reflexivity.
  - intros sz szH.
    simpl. f_equal. admit.
Admitted.
