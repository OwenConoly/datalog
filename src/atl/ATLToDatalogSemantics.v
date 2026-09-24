From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Program.Equality.

From ATL Require Import ATL Div Common.

From Datalog Require Import Datalog Tactics Blocks.
From Inferpad Require Import ATLPhoas TensorToResult.

From coqutil Require Import Map.Interface Map.Properties Tactics.


Import ListNotations.

Fixpoint pZexpr_no_vars {var} (e : pZexpr var) : Prop :=
  match e with
  | ZBop _ x y => pZexpr_no_vars x /\ pZexpr_no_vars y
  | ZVar _ => False
  | ZZ0 | ZZpos _ | ZZneg _ | ZZ_of_nat _ => True
  | ZZopp x => pZexpr_no_vars x
  end.


Fixpoint stringvar_S_ok {var} (e : pATLexpr var 0) : Prop :=
  match e with
  | ATLPhoas.SBop _ x y => stringvar_S_ok x /\ stringvar_S_ok y
  | ATLPhoas.SIZR _ => True
  | ATLPhoas.Get _ _ => True
  | _ => False
  end.

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
    sz = [] /\ sizeof_prop x [] /\ sizeof_prop y [] /\
    stringvar_S_ok x /\ stringvar_S_ok y
  | SIZR x => sz = [] /\ pZexpr_no_vars x
  end.


(* should i be seperating these definitions into more variants like in the previous compiler?
cause everything in the language is purely defined as fn, so maybe it wouldn't work, but
having every fn term be uner the fn variant might be messy when it comes to interpreting them with return variables?? *)
Variant fn : fnT :=
  fn_Add | fn_Sub | fn_Divf | fn_Divc | fn_Mul | fn_Mod | fn_Nat | fn_Opp
  | fn_Lit (x : Z) | fn_Lt | fn_Le | fn_And | fn_Not | fn_Div | fn_Eq.

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
  | ZBop op x y => expr.app (ZBop_to_fn op) [lower_pZexpr' x; lower_pZexpr' y]
  | ZVar x => expr.var x
  | ZLit p => expr.app (fn_Lit p) []
  | Zopp x => expr.app fn_Opp [lower_pZexpr' x]
end.

Inductive pATL_Sexpr' {var : type -> Type} : Type :=
| Get : forall n : nat, var (tensor_n n) -> list (pZexpr' (var tZ)) -> pATL_Sexpr'
| SBop : Sbop -> pATL_Sexpr' -> pATL_Sexpr' -> pATL_Sexpr'
| SLit : Z -> pATL_Sexpr'.
Arguments pATL_Sexpr' : clear implicits.

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
  | ATLPhoas.ZZopp x => (- stringvar_ZLit x)%Z
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
  | Var : forall n : nat, var (tensor_n n) -> pATLexpr' n
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
  | ATLPhoas.Var x => Var _ x
  | ATLPhoas.Get _ _ | ATLPhoas.SBop _ _ _ | ATLPhoas.SIZR _ => Scalar (stringvar_S e)
end.
