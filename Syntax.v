From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Coq Require Import ZArith.Zdiv.
From Coq Require Import ZArith.Int.
From Coq Require Import ZArith.Znat.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.

Set Warnings "-deprecate-hint-without-locality,-deprecated".
Import ListNotations.

From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics.
From Lower Require Import Zexpr Bexpr Array Range Sexpr Result ListMisc
  Meshgrid VarGeneration Injective Constant InterpretReindexer
  WellFormedEnvironment.

Require Import ATLDeep.
Open Scope string_scope.

Section __.
Context (rel: Type) (var: Type) (fn: Type).
(*constants are 0-ary functions*)

Inductive expr :=
| fun_expr (f : fn) (args : list expr)
| var_expr (v : var).

Record fact :=
  { fact_R : rel; fact_args : list expr }.

Record rule :=
  { rule_hyps: list fact; rule_concl: fact }.

Fixpoint subst_in_expr (s : var -> option expr) (e : expr) :=
  match e with
  | fun_expr f args => fun_expr f (map (subst_in_expr s) args)
  | var_expr v => match s v with
                 | Some e => e
                 | None => var_expr v
                 end
  end.

Definition subst_in_fact (s : var -> option expr) (f : fact) : fact :=
  Build_fact f.(fact_R) (map (subst_in_expr s) f.(fact_args)).

Definition subst_in_rule (s : var -> option expr) (r : rule) : rule :=
  Build_rule (map (subst_in_fact s) r.(rule_hyps)) (subst_in_fact s r.(rule_concl)).

Fixpoint appears_in_expr (v : var) (e : expr) :=
  match e with
  | fun_expr _ args => fold_left (fun acc arg => acc \/ appears_in_expr v arg) args False
  | var_expr v0 => v0 = v
  end.

Definition appears_in_fact (v : var) (f : fact) :=
  Exists (appears_in_expr v) f.(fact_args).

Definition good_rule (r : rule) :=
  forall v, appears_in_fact v r.(rule_concl) ->
       Exists (appears_in_fact v) r.(rule_hyps).

Definition good_prog (p : list rule) := Forall good_rule p.

Inductive prog_impl_fact (p : list rule) : fact -> Prop :=
| impl_step f : Exists
                  (fun r => exists s,
                       let r' := subst_in_rule s r in
                       r'.(rule_concl) = f /\
                         exists s', Forall (prog_impl_fact p) (map (subst_in_fact s') r'.(rule_hyps)))
                  p ->
                prog_impl_fact p f.
End __.
Arguments Build_rule {_ _ _}.
Arguments Build_fact {_ _ _}.
Arguments fun_expr {_ _}.
Arguments var_expr {_ _}.

(*p is target*)
(*f is reindexer*)
(*asn is StoreType += or =*)
(*sh is shape of something?*)
Print Zexpr.
(*just like Zexpr but no ZVar*)
Variant Zfn : Set :=
  fn_ZPlus | fn_ZMinus | fn_ZTimes | fn_ZDivf | fn_ZDivc | fn_ZMod | fn_ZLit (x : Z).
Print Sstmt.
(*just like Sstmt but no SVar, SGet*)
Variant Rfn : Set :=
  fn_SMul | fn_SAdd | fn_SDiv | fn_SSub | fn_SLit (x : R).
Variant tfn : Set :=
  fn_Z (_ : Zfn) | fn_R (_ : Rfn).
Definition rel : Set := string.
(*inl s is string representing indexing variable (e.g. i, j), which came directly from source program
  inr n is nat (that i generated) representing value in some intermediate thing
 *)
Definition var : Set := string + nat.
Definition trule := rule rel var tfn.
Print rule. Print flat_map. Check Gen.
Search list Z. Search zrange. Print Zexpr. Print lowerS.
Print lower. Check Scalar. Print lowerS.

Search Sstmt. Print eval_Sstmt. Print context. Print fmap. Check Build_rule. Check Build_fact.

Print Zexpr. Print expr.
Fixpoint lower_idx (idx: Zexpr) : expr var tfn :=
  match idx with
  (*copy-pasted monstrosity*)
  | ZPlus x y => fun_expr (fn_Z fn_ZPlus) [lower_idx x; lower_idx y]
  | ZMinus x y => fun_expr (fn_Z fn_ZMinus) [lower_idx x; lower_idx y]
  | ZTimes x y => fun_expr (fn_Z fn_ZTimes) [lower_idx x; lower_idx y]
  | ZDivf x y => fun_expr (fn_Z fn_ZDivf) [lower_idx x; lower_idx y]
  | ZDivc x y => fun_expr (fn_Z fn_ZMod) [lower_idx x; lower_idx y]
  | ZMod x y => fun_expr (fn_Z fn_ZMod) [lower_idx x; lower_idx y]
  | ZLit x => fun_expr (fn_Z (fn_ZLit x)) []
  | ZVar x => var_expr (inl x)
  end.

Check lowerS.
Print Sexpr.
Fixpoint lower_Sexpr (next_varname : nat) (e : Sexpr) :
  expr var tfn (*value of expr*) *
    list (fact rel var tfn) (*hypotheses*) *
    nat (*next varname *) :=
  match e with
  | Var x => (var_expr (inr next_varname),
              [{| fact_R := x; fact_args := [] |}],
              succ next_varname)
  | Get x idxs => (var_expr (inr next_varname),
                   [{| fact_R := x; fact_args := map lower_idx idxs |}],
                   succ next_varname)
  (*copy-pasted monstrosity*)
  | Mul x y => let '(e1, hyps1, next_varname) := lower_Sexpr next_varname x in
              let '(e2, hyps2, next_varname) := lower_Sexpr next_varname y in
              (fun_expr (fn_R fn_SMul) [e1; e2],
                (hyps1 ++ hyps2)%list,
                next_varname)
  | Div x y => let '(e1, hyps1, next_varname) := lower_Sexpr next_varname x in
              let '(e2, hyps2, next_varname) := lower_Sexpr next_varname y in
              (fun_expr (fn_R fn_SDiv) [e1; e2],
                (hyps1 ++ hyps2)%list,
                next_varname)
  | Add x y => let '(e1, hyps1, next_varname) := lower_Sexpr next_varname x in
              let '(e2, hyps2, next_varname) := lower_Sexpr next_varname y in
              (fun_expr (fn_R fn_SAdd) [e1; e2],
                (hyps1 ++ hyps2)%list,
                next_varname)
  | Sub x y => let '(e1, hyps1, next_varname) := lower_Sexpr next_varname x in
              let '(e2, hyps2, next_varname) := lower_Sexpr next_varname y in
              (fun_expr (fn_R fn_SSub) [e1; e2],
                (hyps1 ++ hyps2)%list,
                next_varname)
  | Lit x => (fun_expr (fn_R (fn_SLit x)) [], [], next_varname)
  end.

Print rule. Print fact.
Fixpoint lower
  (e : ATLexpr)
  (out: rel)
  (*this list is backwards compared to the other lowering alg*)
  (*also, i don't use the bounds at all (yet)*)
  (idxs_bds : list (Zexpr * Zexpr))
  : list trule :=
  match e with
  | Gen i lo hi body =>
      lower body out ((ZMinus (ZVar i) lo, ZMinus hi lo) :: idxs_bds)
  | Scalar s =>
      let '(val, hyps, _) := lower_Sexpr O s in
      [{| rule_hyps := hyps; rule_concl := {| fact_R := out; fact_args := val :: (map lower_idx (map fst idxs_bds)) |} |}]
  | _ => nil end.
      For i lo hi
          (lower body  p asn sh)
  | Sum i lo hi body =>
      For i lo hi
          (lower body f p Reduce sh)
  | Guard b body =>
      If b (lower body f p asn sh)
  | Lbind x e1 e2 =>
    match sizeof e1 with
    | [] =>
        Seq (AllocS x)
            (Seq (lower e1 (fun l => l) x Assign sh)
                 (Seq (lower e2 f p asn (sh $+ (x,sizeof e1)))
                      (DeallocS x)))
    | _ =>
      Seq (AllocV x (flat_sizeof e1))
          (Seq (lower e1 (fun l => l) x Assign sh)
               (Seq (lower e2 f p asn (sh $+ (x,sizeof e1)))
                    (Free x)))
    end
  | Concat x y =>
    let xlen := match sizeof x with
                | n::_ => n
                | _ => ZLit 0
                end in 
    let ylen := match sizeof y with
                | n::_ => n
                | _ => ZLit 0
                end in   
    Seq (lower x (fun l =>
                    f (match l with
                     | (v,d)::xs =>
                         ((v,ZPlus d ylen)::xs)
                     | _ => l
                     end)) p asn sh)
        (lower y (fun l => f (match l with
                          | (v,d)::xs => ((ZPlus v xlen,ZPlus d xlen)::xs)
                          | _ => l
                          end)) p asn sh)
  | Transpose e =>
    lower e (fun l => f (match l with
                         | (v,d)::(vi,di)::xs => (vi,di)::(v,d)::xs
                         | _ => l
                         end)) p asn sh
  | Split k e =>
    lower e (fun l => f (match l with
                         | (v,d)::xs => (ZDivf v k,ZDivc d k)::(ZMod v k,k)::xs
                         | _ => l
                         end)) p asn sh
  | Flatten e =>
    lower e (fun l => f (match l with
                         | (v,d)::(vi,di)::xs =>
                           (ZPlus (ZTimes v di) vi,ZTimes d di)::xs
                         | _ => l
                         end)) p asn sh          
p  | Truncr n e =>
    lower e (fun l => f (match l with
                         | (v,d)::xs =>
                           (v,ZMinus d n)::xs
                         | _ => l
                         end)) p asn sh
  | Truncl n e =>
    lower e (fun l => f (match l with
                         | (v,d)::xs =>
                             (ZMinus v n,
                               ZMinus d n)::xs
                         | _ => l
                         end)) p asn sh
  | Padr n e =>
    lower e (fun l => f (match l with
                         | (v,d)::xs =>
                           (v,ZPlus d n)::xs
                         | _ => l
                         end)) p asn sh
  | Padl n e =>
    lower e (fun l => f (match l with
                         | (v,d)::xs =>
                           (ZPlus v n,ZPlus d n)::xs
                         | _ => l
                         end)) p asn sh
  end.
