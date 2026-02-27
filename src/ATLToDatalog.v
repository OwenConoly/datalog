From Stdlib Require Import QArith.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Stdlib Require Import ZArith.Zdiv.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.

Import ListNotations.
From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics.
From Lower Require Import Zexpr Bexpr Sexpr Array Result ListMisc
  Meshgrid ContextsAgree ATLDeep Range.

From Datalog Require Import Datalog Dag Map List Tactics (*Interpreter QueryableToRunnable*) ATLUtils ZeroLowerBounds.
From coqutil Require Import Map.Interface Map.Properties Map.Solver Map.OfFunc Tactics.fwd Tactics.destr Tactics Decidable Datatypes.List.

Import Datatypes.

Open Scope list_scope.
Open Scope nat_scope.

Definition var : Type := string + nat.

Variant obj : Set :=
  Bobj : bool -> obj | Zobj : Z -> obj | Robj : R -> obj | Setobj (min : Z) (max : Z).

(*just like Bexpr, except i added blit*)
Variant Bfn : Set :=
  fn_BAnd | fn_BLt | fn_BLe | fn_BEq | fn_BLit (_ : bool) | fn_BNot.

Definition interp_Bfn (f : Bfn) (l : list obj) : option bool :=
  match f, l with
  | fn_BAnd, [Bobj x; Bobj y] => Some (x && y)
  | fn_BLt, [Zobj x; Zobj y] => Some (x <? y)
  | fn_BLe, [Zobj x; Zobj y] => Some (x <=? y)
  | fn_BEq, [Zobj x; Zobj y] => Some (x =? y)
  | fn_BLit b, [] => Some b
  | fn_BNot, [Bobj b] => Some (negb b)
  | _, _ => None
  end%Z.

(*just like Zexpr but no ZVar*)
Variant Zfn : Set :=
  fn_ZPlus | fn_ZMinus | fn_ZTimes | fn_ZDivf | fn_ZDivc | fn_ZMod | fn_Zmax(*i added this to make writing the compiler convenient*) | fn_ZLit (x : Z) | fn_ZRange.

Definition interp_Zfn (f : Zfn) (l : list obj) : option obj :=
  match f, l with
  | fn_ZPlus, [Zobj x; Zobj y] => Some (Zobj (x + y))
  | fn_ZMinus, [Zobj x; Zobj y] => Some (Zobj (x - y))
  | fn_ZTimes, [Zobj x; Zobj y] => Some (Zobj (x * y))
  | fn_ZDivf, [Zobj x; Zobj y] => Some (Zobj (x / y))
  | fn_ZDivc, [Zobj x; Zobj y] => Some (Zobj (x // y))
  | fn_ZMod, [Zobj x; Zobj y] => Some (Zobj (x mod y))
  | fn_Zmax, [Zobj x; Zobj y] => Some (Zobj (Z.max x y))
  | fn_ZLit x, [] => Some (Zobj x)
  | fn_ZRange, [Zobj x; Zobj y] => Some (Setobj x y)
  | _, _ => None
  end%Z.

(*just like Sstmt but no SVar, SGet*)
Variant Rfn : Set :=
  fn_SMul | fn_SAdd | fn_SDiv | fn_SSub | fn_SLit (x : Q).

Definition interp_Rfn (f : Rfn) (l : list obj) : option R :=
  match f, l with
  | fn_SMul, [Robj x; Robj y] => Some (x * y)
  | fn_SAdd, [Robj x; Robj y] => Some (x + y)
  | fn_SDiv, [Robj x; Robj y] => Some (x / y)
  | fn_SSub, [Robj x; Robj y] => Some (x - y)
  | fn_SLit x, [] => Some (Q2R x)
  | _, _ => None
  end%R.

Variant fn : Set :=
  fn_B (_ : Bfn) | fn_Z (_ : Zfn) | fn_R (_ : Rfn).

Variant rel : Set :=
  | str_rel (s : string)
  | nat_rel (n : nat)
  | true_rel (*unary, true if arg is true*).

Variant aggregator : Set :=
| sum.

Definition var_eqb (x y : var) : bool :=
  match x, y with
  | inl x, inl y => (x =? y)%string
  | inr x, inr y => x =? y
  | _, _ => false
  end.

Lemma var_eqb_spec x y : BoolSpec (x = y) (x <> y) (var_eqb x y).
Proof.
  destruct x, y; simpl; try (constructor; congruence).
  - destr (s =? s0)%string; constructor; congruence.
  - destr (n =? n0); constructor; congruence.
Qed.

Definition sum_objs (objs : list (obj * obj)) :=
  match option_all (map
                      (fun '(i, x) => match x with
                                   | Robj y => Some y
                                   | _ => None
                                   end)
                      objs)
  with
  | Some vals => Robj (fold_right Rplus 0%R vals)
  | None => Zobj 0 (*garbage*)
  end.

Section __.
  Let interp_fun f l :=
        match f with
        | fn_B f => option_map Bobj (interp_Bfn f l)
        | fn_Z f => interp_Zfn f l
        | fn_R f => option_map Robj (interp_Rfn f l)
        end.
  Let get_set x :=
        match x with
        | Bobj _ => None
        | Zobj _ => None
        | Robj _ => None
        | Setobj min max =>
            Some (fun y =>
                    match y with
                    | Zobj z => (min <= z < max)%Z
                    | _ => False
                    end)
        end.
  Let interp_agg a xs :=
        match a with
        | sum => sum_objs xs
        end.
  Instance ATLSig : signature fn aggregator obj :=
    { interp_fun := interp_fun ;
      get_set := get_set;
      interp_agg := interp_agg }.
End __.

#[local] Existing Instance ATLSig.
Existing Instance var_eqb_spec.
Instance str_eqb_spec : EqDecider String.eqb := String.eqb_spec.
Section __.
Context {valuation' : map.map Var.var Z} {valuation'_ok : map.ok valuation'}.
Context {context : map.map var obj} {context_ok : map.ok context}.
Context {str_nat : map.map string nat} {str_nat_ok : map.ok str_nat}.
Context {str_Zexpr : map.map string Zexpr} {str_Zexpr_ok : map.ok str_Zexpr}.
Local Notation rule := (rule rel var fn aggregator).
Local Notation fact := (fact rel obj).
Local Notation expr := (expr var fn).
Implicit Type ctx : context.

Fixpoint lower_idx (idx: Zexpr) : expr :=
  match idx with
  (*copy-pasted monstrosity*)
  | ZPlus x y => fun_expr (fn_Z fn_ZPlus) [lower_idx x; lower_idx y]
  | ZMinus x y => fun_expr (fn_Z fn_ZMinus) [lower_idx x; lower_idx y]
  | ZTimes x y => fun_expr (fn_Z fn_ZTimes) [lower_idx x; lower_idx y]
  | ZDivf x y => fun_expr (fn_Z fn_ZDivf) [lower_idx x; lower_idx y]
  | ZDivc x y => fun_expr (fn_Z fn_ZDivc) [lower_idx x; lower_idx y]
  | ZMod x y => fun_expr (fn_Z fn_ZMod) [lower_idx x; lower_idx y]
  | ZLit x => fun_expr (fn_Z (fn_ZLit x)) []
  | ZVar x => var_expr (inl x)
  end.

Fixpoint lower_guard (g: Bexpr) : expr :=
  match g with
  | Bexpr.And x y => fun_expr (fn_B fn_BAnd) [lower_guard x; lower_guard y]
  | Bexpr.Lt x y => fun_expr (fn_B fn_BLt) [lower_idx x; lower_idx y]
  | Bexpr.Le x y => fun_expr (fn_B fn_BLe) [lower_idx x; lower_idx y]
  | Bexpr.Eq x y => fun_expr (fn_B fn_BEq) [lower_idx x; lower_idx y]
  end.

Fixpoint vars_of_Bexpr (b : Bexpr) : list string :=
  match b with
  | Bexpr.And x y => vars_of_Bexpr x ++/ vars_of_Bexpr y
  | Bexpr.Lt x y | Bexpr.Le x y | Bexpr.Eq x y => vars_of_Zexpr x ++/ vars_of_Zexpr y
  end.

Print Sexpr. About Add. Print Add.
Fixpoint idx_vars_of_Sexpr (s : Sexpr) : list string :=
  match s with
  | Get _ idxs => flat_map vars_of_Zexpr idxs
  | Mul s1 s2 | Add s1 s2 | Div s1 s2 | Sub s1 s2 =>
                                          idx_vars_of_Sexpr s1 ++ idx_vars_of_Sexpr s2
  | Lit _ => []
  end.

Fixpoint lower_Sexpr (idxs0 : list string) (def_depth : str_nat) (next_varname : nat) (e : Sexpr) :
  expr (*value of expr*) *
    list (clause rel var fn) (*hypotheses*) *
    nat (*next varname *) :=
  match e with
  | Get x idxs' =>
      match map.get def_depth x with
      | None => (fun_expr (fn_Z (fn_ZLit 0)) [], nil, O) (*garbage*)
      | Some n =>
          (var_expr (inr next_varname),
            [{| clause_R := (str_rel x, normal); clause_args := var_expr (inr next_varname) :: map var_expr (map inl (firstn n idxs0)) ++ map lower_idx idxs' |}],
            S next_varname)
      end
  (*copy-pasted monstrosity*)
  | Mul x y => let '(e1, hyps1, next_varname) := lower_Sexpr idxs0 def_depth next_varname x in
              let '(e2, hyps2, next_varname) := lower_Sexpr idxs0 def_depth next_varname y in
              (fun_expr (fn_R fn_SMul) [e1; e2],
                (hyps1 ++ hyps2)%list,
                next_varname)
  | Div x y => let '(e1, hyps1, next_varname) := lower_Sexpr idxs0 def_depth next_varname x in
              let '(e2, hyps2, next_varname) := lower_Sexpr idxs0 def_depth next_varname y in
              (fun_expr (fn_R fn_SDiv) [e1; e2],
                (hyps1 ++ hyps2)%list,
                next_varname)
  | Add x y => let '(e1, hyps1, next_varname) := lower_Sexpr idxs0 def_depth next_varname x in
              let '(e2, hyps2, next_varname) := lower_Sexpr idxs0 def_depth next_varname y in
              (fun_expr (fn_R fn_SAdd) [e1; e2],
                (hyps1 ++ hyps2)%list,
                next_varname)
  | Sub x y => let '(e1, hyps1, next_varname) := lower_Sexpr idxs0 def_depth next_varname x in
              let '(e2, hyps2, next_varname) := lower_Sexpr idxs0 def_depth next_varname y in
              (fun_expr (fn_R fn_SSub) [e1; e2],
                (hyps1 ++ hyps2)%list,
                next_varname)
  | Lit x => (fun_expr (fn_R (fn_SLit x)) [], [], next_varname)
  end.

(*we want to ignore bounds.  to avoid generating wrong answers, then, due to ignoring bounds, we have two options.
  1. don't actually ignore bounds.  before outputting something, check that it's in bounds.  (this sounds terrible and inefficient)
  2. before using something, check---if necessary---that it's in bounds.  (this sounds much less bad, since we usually won't need to do a check).
 *)

(*this is horribly long and repetitive; it should be a fixpoint*)
Inductive vars_good : list string -> ATLexpr -> Prop :=
| vg_Gen i lo hi body idxs :
  incl (vars_of_Zexpr lo) idxs ->
  incl (vars_of_Zexpr hi) idxs ->
  vars_good (idxs ++ [i]) body ->
  vars_good idxs (Gen i lo hi body)
| vg_Sum i lo hi body idxs :
  incl (vars_of_Zexpr lo) idxs ->
  incl (vars_of_Zexpr hi) idxs ->
  vars_good (idxs ++ [i]) body ->
  vars_good idxs (Sum i lo hi body)
| vg_Guard b body idxs :
  incl (vars_of_Bexpr b) idxs ->
  vars_good idxs body ->
  vars_good idxs (Guard b body)
| vg_Lbind x e1 e2 idxs :
  ~ x \in referenced_vars e1 ->
  referenced_vars e1 \cap vars_of e2 = constant [] ->
  ~ x \in vars_of e1 /\ ~ x \in vars_of e2 ->
  vars_of e1 \cap vars_of e2 = constant [] ->
  vars_good idxs e1 ->
  vars_good idxs e2 ->
  vars_good idxs (Lbind x e1 e2)
(*TODO: this one isn't actually reasonable to expect of a source program;
  I'll have to write some name generation pass to make sure it holds*)
| vg_Concat e1 e2 idxs :
  vars_of e1 \cap vars_of e2 = constant [] ->
  vars_of e1 \cap referenced_vars e2 = constant [] ->
  (*note: it would probably make sense to include the symmetric condition,
    vars_of e2 \cap referenced_vars e1 = constant [],
    but i don't need it for anything and am lazy*)
  vars_good idxs e1 ->
  vars_good idxs e2 ->
  vars_good idxs (Concat e1 e2)
| vg_Transpose e idxs :
  vars_good idxs e ->
  vars_good idxs (Transpose e)
| vg_Flatten e idxs :
  vars_good idxs e ->
  vars_good idxs (Flatten e)
| vg_Split k e idxs :
  vars_good idxs e ->
  vars_good idxs (Split k e)
| vg_Truncr k e idxs :
  vars_good idxs e ->
  vars_good idxs (Truncr k e)
| vg_Truncl k e idxs :
  vars_good idxs e ->
  vars_good idxs (Truncl k e)
| vg_Padl k e idxs :
  vars_good idxs e ->
  vars_good idxs (Padl k e)
| vg_Padr k e idxs :
  vars_good idxs e ->
  vars_good idxs (Padr k e)
| vg_Scalar s idxs :
  incl (idx_vars_of_Sexpr s) idxs ->
  vars_good idxs (Scalar s).

Fixpoint lower_rec
  (e : ATLexpr)
  (out: rel)
  (name: nat)
  (idxs : list string)
  (def_depth : str_nat)
  : nat (*next unused name*) * list rule :=
  match e with
  | Gen i lo hi body =>
      lower_rec body out name (idxs ++ [i]) def_depth
  | Sum i lo hi body =>
      let dimvars := map inr (seq O (length (sizeof body))) in
      let x := length (sizeof body) in
      let i' := Datatypes.S x in
      let y := Datatypes.S i' in
      let aux := name in
      let aux' := S aux in
      let (name', rules) := lower_rec body (nat_rel aux) (S aux') (idxs ++ [i]) def_depth in
      (name',
        rules ++
          [agg_rule out sum (nat_rel aux');
           normal_rule
             [{| clause_R := (nat_rel aux', normal);
                clause_args :=
                  var_expr (inr i') ::
                    var_expr (inr x) ::
                    map var_expr (map inl idxs) ++
                    map var_expr dimvars |}]
             [{| clause_R := (nat_rel aux, normal);
                clause_args :=
                  var_expr (inr x) ::
                    map var_expr (map inl idxs) ++
                    var_expr (inr i') ::
                    map var_expr dimvars |}] ] )
  | Guard b body =>
      let dimvars := map inr (seq O (length (sizeof body))) in
      let x := length (sizeof body) in
      let aux := name in
      let (name', rules) := lower_rec body (nat_rel aux) (S aux) idxs def_depth in
      (name',
        rules ++
          [normal_rule
             [{| clause_R := (out, normal);
                clause_args :=
                  var_expr (inr x) ::
                    map var_expr (map inl idxs) ++
                    map var_expr dimvars |}]
             [{| clause_R := (nat_rel aux, normal);
                clause_args :=
                  var_expr (inr x) ::
                    map var_expr (map inl idxs) ++
                    map var_expr dimvars |};
              {| clause_R := (true_rel, normal);
                clause_args := [lower_guard b] |}];
           normal_rule
             [{| clause_R := (out, normal);
                clause_args :=
                  fun_expr (fn_R (fn_SLit 0%Q)) [] ::
                    map var_expr (map inl idxs) ++
                    map var_expr dimvars |}]
             [{| clause_R := (true_rel, normal);
                clause_args := [fun_expr (fn_B fn_BNot) [lower_guard b]] |}] ])
  | Lbind x e1 e2 =>
      let (name', rules1) := lower_rec e1 (str_rel x) name idxs def_depth in
      let (name'', rules2) := lower_rec e2 out name' idxs (map.put def_depth x (length idxs)) in
      (name'', rules1 ++ rules2)
  | Concat e1 e2 =>
      (*should have length (sizeof e1) = length (sizeof e2)*)
      let dimvars := map inr (seq O (length (sizeof e1) - 1)) in
      let dimvarO := inr (length (sizeof e1) - 1) in
      let x := length (sizeof e1) in
      let aux1 := name in
      let aux2 := S name in
      (*TODO think carefully about what is len1 here; what are the variables?*)
      let len1 := match sizeof e1 with
                    | [] => ZLit 0%Z
                    | n :: _ => n
                    end in
      let (name', rules1) := lower_rec e1 (nat_rel aux1) (S aux2) idxs def_depth in
      let (name'', rules2) := lower_rec e2 (nat_rel aux2) name' idxs def_depth in
      (name'',
        rules1 ++ rules2 ++
          [normal_rule
             [{| clause_R := (out, normal);
                clause_args :=
                  var_expr (inr x) ::
                    map var_expr (map inl idxs) ++
                    map var_expr (dimvarO :: dimvars) |}]
             [{| clause_R := (nat_rel aux1, normal);
                clause_args :=
                  var_expr (inr x) ::
                    map var_expr (map inl idxs) ++
                    map var_expr (dimvarO :: dimvars) |};
              {| clause_R := (true_rel, normal);
                clause_args := [fun_expr (fn_B fn_BLt)
                                  [var_expr dimvarO;
                                   lower_idx len1]] |}];
           normal_rule
             [{| clause_R := (out, normal);
                clause_args :=
                  var_expr (inr x) ::
                    map var_expr (map inl idxs) ++
                    var_expr dimvarO ::
                    map var_expr dimvars |}]
             [{| clause_R := (nat_rel aux2, normal);
                clause_args :=
                  var_expr (inr x) ::
                    map var_expr (map inl idxs) ++
                    fun_expr (fn_Z fn_ZMinus)
                    [var_expr dimvarO;
                     lower_idx len1] ::
                    map var_expr dimvars |};
              {| clause_R := (true_rel, normal);
                clause_args := [fun_expr (fn_B fn_BLe)
                                  [lower_idx len1;
                                   var_expr dimvarO]] |}] ])
  | Flatten e =>
      let dimvars := map inr (seq O (length (sizeof e) - 2)) in
      let dimvarO := inr (length (sizeof e) - 2) in
      let x := inr (length (sizeof e) - 1) in
      (*TODO what is len2 here*)
      let len2 :=
        match sizeof e with
          | _ :: di :: _ => di
          | _ => ZLit 0
          end in
      let aux := name in
      let (name', rules) := lower_rec e (nat_rel aux) (S aux) idxs def_depth in
      (name',
        rules ++
          [normal_rule
             [{| clause_R := (out, normal);
                clause_args :=
                  var_expr x ::
                    map var_expr (map inl idxs) ++
                    var_expr dimvarO ::
                    map var_expr dimvars |}]
             [{| clause_R := (nat_rel aux, normal);
                clause_args := var_expr x ::
                                 map var_expr (map inl idxs) ++
                                 fun_expr (fn_Z fn_ZDivf)
                                 [var_expr dimvarO;
                                  lower_idx len2] ::
                                 fun_expr (fn_Z fn_ZMod)
                                 [var_expr dimvarO;
                                  lower_idx len2] ::
                                 map var_expr dimvars |}]])
  | Split k e =>
      let dimvars := map inr (seq O (length (sizeof e) - 1)) in
      let dimvar1 := inr (length (sizeof e) - 1) in
      let dimvar2 := inr (length (sizeof e)) in
      let x := inr (S (length (sizeof e))) in
      (*TODO what is len*)
      let len :=
        match sizeof e with
          | d :: _ => d
          | _ => ZLit 0
          end in
      let aux := name in
      let pad_start := (ZMod len k)%z in
      let (name', rules) := lower_rec e (nat_rel aux) (S aux) idxs def_depth in
      (name',
        rules ++
          [normal_rule
             [{| clause_R := (out, normal);
                clause_args :=
                  var_expr x ::
                    map var_expr (map inl idxs) ++
                    var_expr dimvar1 ::
                    var_expr dimvar2 ::
                    map var_expr dimvars |}]
             [{| clause_R := (nat_rel aux, normal);
                clause_args := var_expr x ::
                                 map var_expr (map inl idxs) ++
                                 fun_expr (fn_Z fn_ZPlus)
                                 [fun_expr (fn_Z fn_ZTimes)
                                    [var_expr dimvar1;
                                     lower_idx k];
                                  var_expr dimvar2] ::
                                 map var_expr dimvars |};
              {| clause_R := (true_rel, normal);
                clause_args := [fun_expr (fn_B fn_BNot)
                                  [fun_expr (fn_B fn_BAnd)
                                     [fun_expr (fn_B fn_BEq)
                                        [var_expr dimvar1;
                                         fun_expr (fn_Z fn_ZDivf)
                                           [lower_idx len; lower_idx k]];
                                      fun_expr (fn_B fn_BLe)
                                        [lower_idx pad_start;
                                         var_expr dimvar2]]]] |}];
           normal_rule
             [{| clause_R := (out, normal);
                clause_args :=
                  fun_expr (fn_R (fn_SLit 0)) [] ::
                    map var_expr (map inl idxs) ++
                    fun_expr (fn_Z fn_ZDivf) [lower_idx len; lower_idx k] ::
                    var_expr dimvar1 ::
                    map var_expr dimvars |}]
             [{| clause_R := (true_rel, normal);
                clause_args := [fun_expr (fn_B fn_BLe)
                                  [lower_idx pad_start;
                                   var_expr dimvar1]] |} ] ])
  | Transpose e =>
      let dimvars := map inr (seq O (length (sizeof e) - 2)) in
      let dimvar1 := inr (length (sizeof e) - 1) in
      let dimvar2 := inr (length (sizeof e)) in
      let x := inr (S (length (sizeof e))) in
      let aux := nat_rel name in
      let (name', rules) := lower_rec e aux (S name) idxs def_depth in
      (name',
        rules ++
          [normal_rule
             [{| clause_R := (out, normal);
                clause_args :=
                  var_expr x ::
                    map var_expr (map inl idxs) ++
                    var_expr dimvar2 ::
                    var_expr dimvar1 ::
                    map var_expr dimvars |}]
             [{| clause_R := (aux, normal);
                clause_args :=
                  var_expr x ::
                    map var_expr (map inl idxs) ++
                    var_expr dimvar1 ::
                    var_expr dimvar2 ::
                    map var_expr dimvars |}] ])
  | Truncr _ e =>
      lower_rec e out name idxs def_depth
  | Truncl k e =>
      let dimvars := map inr (seq O (length (sizeof e) - 1)) in
      let dimvar1 := inr (length (sizeof e) - 1) in
      let x := inr (length (sizeof e)) in
      let aux := nat_rel name in
      let (name', rules) := lower_rec e aux (S name) idxs def_depth in
      (name',
        rules ++
          [normal_rule
             [{| clause_R := (out, normal);
                clause_args :=
                  var_expr x ::
                    map var_expr (map inl idxs) ++
                    var_expr dimvar1 ::
                    map var_expr dimvars |}]
             [{| clause_R := (aux, normal);
                clause_args :=
                  var_expr x ::
                    map var_expr (map inl idxs) ++
                    fun_expr (fn_Z fn_ZPlus)
                    [lower_idx k;
                     var_expr dimvar1] ::
                    map var_expr dimvars |}] ])
  | Padr k e =>
      let dimvars := map inr (seq O (length (sizeof e) - 1)) in
      let dimvar1 := inr (length (sizeof e) - 1) in
      let x := inr (length (sizeof e)) in
      let aux := nat_rel name in
      (*TODO what is len*)
      let len :=
        match sizeof e with
          | d :: _ => d
          | _ => ZLit 0
          end in
      let (name', rules) := lower_rec e aux (S name) idxs def_depth in
      (name',
        rules ++ [normal_rule
                    [{| clause_R := (out, normal);
                       clause_args :=
                         var_expr x ::
                           map var_expr (map inl idxs) ++
                           var_expr dimvar1 ::
                           map var_expr dimvars |}]
                    [{| clause_R := (aux, normal);
                       clause_args :=
                         var_expr x ::
                           map var_expr (map inl idxs) ++
                           var_expr dimvar1 ::
                           map var_expr dimvars |};
                     {| clause_R := (true_rel, normal);
                       clause_args := [fun_expr (fn_B fn_BLt)
                                         [var_expr dimvar1;
                                          lower_idx len]] |}];
                  normal_rule
                    [{| clause_R := (out, normal);
                       clause_args :=
                         fun_expr (fn_R (fn_SLit 0)) [] ::
                           map var_expr (map inl idxs) ++
                           var_expr dimvar1 ::
                           map var_expr dimvars |}]
                    [{| clause_R := (true_rel, normal);
                       clause_args := [fun_expr (fn_B fn_BLe)
                                         [lower_idx len;
                                          var_expr dimvar1]] |}] ])
  | Padl k e =>
      let dimvars := map inr (seq O (length (sizeof e) - 1)) in
      let dimvar1 := inr (length (sizeof e) - 1) in
      let x := inr (length (sizeof e)) in
      let aux := nat_rel name in
      let (name', rules) := lower_rec e aux (S name) idxs def_depth in
      (name',
        rules ++
          [normal_rule
             [{| clause_R := (out, normal);
                clause_args :=
                  var_expr x ::
                    map var_expr (map inl idxs) ++
                    var_expr dimvar1 ::
                    map var_expr dimvars |}]
             [{| clause_R := (aux, normal);
                clause_args :=
                  var_expr x ::
                    map var_expr (map inl idxs) ++
                    fun_expr (fn_Z fn_ZMinus)
                    [var_expr dimvar1;
                     lower_idx k] ::
                    map var_expr dimvars |};
              {| clause_R := (true_rel, normal);
                clause_args := [fun_expr (fn_B fn_BLe)
                                  [lower_idx k;
                                   var_expr dimvar1]] |}];
           normal_rule
             [{| clause_R := (out, normal);
                clause_args :=
                  fun_expr (fn_R (fn_SLit 0)) [] ::
                    map var_expr (map inl idxs) ++
                    var_expr dimvar1 ::
                    map var_expr dimvars |}]
             [{| clause_R := (true_rel, normal);
                clause_args := [fun_expr (fn_B fn_BLt)
                                  [var_expr dimvar1;
                                   lower_idx k]] |}] ])
  | Scalar s =>
      let '(val, hyps, _) := lower_Sexpr idxs def_depth O s in
      (name,
        [normal_rule
           [{| clause_R := (out, normal); clause_args := val :: map var_expr (map inl idxs) |}]
           hyps
      ])
  end.

Definition true_rule : rule :=
  normal_rule
    [{| clause_R := (true_rel, normal);
       clause_args := [fun_expr (fn_B (fn_BLit true)) []] |}]
    [].

Definition lower e out :=
  snd (lower_rec e (str_rel out) O [] map.empty) ++ [true_rule].

(*this is a very (unnecessarily) strong property.  happily, ATL programs are
  very-obviously functional, so they meet it.*)
Definition obviously_non_intersecting (r1 r2 : rule) :=
  forall R idxs hyps1 hyps2 x1 x2,
  rule_impl r1 {| fact_R := R; fact_args := x1 :: idxs |} hyps1 ->
  rule_impl r2 {| fact_R := R; fact_args := x2 :: idxs |} hyps2 ->
  In {| fact_R := (true_rel, normal); fact_args := [Bobj false] |} hyps1 \/
    In {| fact_R := (true_rel, normal); fact_args := [Bobj false] |} hyps2.

Lemma obviously_non_intersecting_comm r1 r2 :
  obviously_non_intersecting r1 r2 ->
  obviously_non_intersecting r2 r1.
Proof.
  cbv [obviously_non_intersecting]. intros.
  specialize (H _ _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
  destruct H; auto.
Qed.

(* Definition pairwise_ni := pairs_satisfy obviously_non_intersecting. *)

(* Inductive pairwise_ni' : list rule -> Prop := *)
(* | pni_nil : pairwise_ni' [] *)
(* | pni_cons r1 p : *)
(*   Forall (obviously_non_intersecting r1) p -> *)
(*   pairwise_ni' p -> *)
(*   pairwise_ni' (r1 :: p). *)

(* Lemma pairwise_ni'_sound p : *)
(*   pairwise_ni' p -> *)
(*   pairwise_ni p. *)
(* Proof. *)
(*   cbv [pairwise_ni pairs_satisfy]. *)
(*   induction 1; simpl; [solve [intuition] |]. intros. *)
(*   rewrite Forall_forall in H. *)
(*   destruct H1, H2; subst; auto using obviously_non_intersecting_comm. *)
(* Qed. *)

(* Lemma pairwise_ni_incl p1 p2 : *)
(*   incl p1 p2 -> *)
(*   pairwise_ni p2 -> *)
(*   pairwise_ni p1. *)
(* Proof. cbv [pairwise_ni pairs_satisfy]. auto. Qed. *)

Definition good_rel name name' (P : string -> Prop) (true_ok : bool) (R : rel) :=
  match R with
  | nat_rel n => name <= n < name'
  | str_rel lbl => P lbl
  | true_rel => if true_ok then True else False
  end.

Definition hyps_of (r : rule) :=
  match r with
  | normal_rule _ rule_hyps => rule_hyps
  | agg_rule _ _ _ => []
  end.

Definition concls_of (r : rule) :=
  match r with
  | normal_rule rule_concls _ => rule_concls
  | agg_rule _ _ _ => []
  end.

Definition good_rule_hyps name name' (P : string -> Prop) (r : rule) :=
  Forall (fun c => good_rel name name' P true (fst c.(clause_R))) (hyps_of r).

Lemma good_rel_weaken P1 P2 R name1 name2 name'1 true_ok name'2 :
  good_rel name1 name'1 P1 true_ok R ->
  name2 <= name1 ->
  name'1 <= name'2 ->
  (forall x, P1 x -> P2 x) ->
  good_rel name2 name'2 P2 true_ok R.
Proof. cbv [good_rel]. destruct R; auto. lia. Qed.

Definition good_rule_or_out out name name' (P : string -> Prop) (r : rule) :=
  Forall (fun c => good_rel name name' P false (fst c.(clause_R)) \/ c.(clause_R) = out) (concls_of r).

Lemma good_rule_weaken P1 P2 name1 name2 name'1 name'2 r :
  good_rule_hyps name1 name'1 P1 r ->
  name2 <= name1 ->
  name'1 <= name'2 ->
  (forall x, P1 x -> P2 x) ->
  good_rule_hyps name2 name'2 P2 r.
Proof.
  cbv [good_rule]. intros. eapply Forall_impl; eauto.
  simpl. eauto using good_rel_weaken.
Qed.

Lemma good_rule_or_out_weaken out name1 name2 name'1 name'2 v r :
  good_rule_or_out out name1 name'1 v r ->
  name2 <= name1 ->
  name'1 <= name'2 ->
  good_rule_or_out out name2 name'2 v r.
Proof.
  cbv [good_rule]. intros. eapply Forall_impl; eauto. simpl.
  cbv [good_rel]. intros a. destruct (fst (clause_R a)); auto. intuition lia.
Qed.

Lemma rule_impl_rel rule_concls rule_hyps f hyps :
  rule_impl (normal_rule rule_concls rule_hyps : rule) f hyps ->
  exists c, In c rule_concls /\ c.(clause_R) = f.(fact_R).
Proof.
  intros H. invert H.
  apply Exists_exists in H2. fwd.
  cbv [interp_clause] in *. fwd. eauto.
Qed.

(* Lemma pairwise_ni_app p1 p2 : *)
(*   pairwise_ni p1 -> *)
(*   pairwise_ni p2 -> *)
(*   diff_rels p1 p2 -> *)
(*   pairwise_ni (p1 ++ p2). *)
(* Proof. *)
(*   cbv [pairwise_ni pairs_satisfy diff_rels]. intros. rewrite in_app_iff in H2, H3. *)
(*   destruct H2, H3; eauto. *)
(*   - cbv [obviously_non_intersecting]. right. intros. subst. *)
(*     apply rule_impl_rel in H4, H5. fwd. exfalso. intuition eauto. *)
(*   - cbv [obviously_non_intersecting]. right. intros. subst. *)
(*     apply rule_impl_rel in H4, H5. fwd. exfalso. intuition eauto. *)
(* Qed. *)

(*
  I need to ensure that index and guard expressions only include variables in scope.
  Otherwise, functionality might not hold.
  Options:
  1. Require eval_expr judgement with appropriate context/valuation/scope v.
     Problem: we lose this invariant when going into loops which execute zero times;
     these could include arbitrary garbage.
  2. Don't actually require this.
     Problem: requires clever "either it's functional or useless" invariant about generated rules, where we say either that it's functional, or it's useless (like an executed-zero-times loop) in the sense that it doesn't affect any "higher-level" (closer to output) code.
     Problem: I'm not actually sure that screwy code with extra variables is guaranteed to not affect higher-level stuff.  Actually it would be kinda nice if it could affect higher-level stuff, because this would give me an excuse for abandoning option 2 (seems like a lot of work) and going with option 3.
     Problem: We would like to say that aggregations expressions are functional as a precondition for compiler-from-datalog correctness; this would require some cleverer "either it's functional or it's useless" precondition about aggregation expressions instead.
  3. Include checks in the compiler to see whether all variables in expressions are in-scope.
     Problem: If option 2 is a possibility, then it's kind of inelegant to have to modify the compiler to make proving things about it easier.  But this is clearly the most practical option.  Actually, having a bunch of meaningless variables floating around is probably
  4. Include checks in the compiler to see whether a loop executes zero times; if so, don't generate any code for it.
     Problem: I find this disgustingly inelegant; it seems to me to be just a coincidence that I have the power to check whether a loop executes zero times, and I don't want to rely on it.  wait actually does const_nonneg_bounds even guarantee this for summations?  i think so because the bounds have to be constant.  which is a weird condition for summations really.  shouldn't need to have that restriction.
     Problem: This would require carrying around an eval_expr hypothesis (as in option 1) in the proof of functionality, which would be a pain.

I choose option 3.  I will modify the compiler accordingly.
I changed my mind; I will do an equivalent slight variation on 3, with the vars_good thing.
 *)

Ltac invert_stuff :=
  match goal with
  | H : rule_impl _ _ _ |- _ => invert1 H
  | H : interp_clause _ _ _ |- _ => cbv [interp_clause] in H; fwd
  | H : interp_expr _ _ _ |- _ => invert1 H
  | _ => invert_list_stuff
  end.

(* This is becoming insane.  I don't technically have to do this, because I could just
   use that bounds are constants... but that still seems wrong somehow, especially for
   summations.  Why should summation bounds have to be constant?*)
Inductive idxs_good : list string -> Prop :=
| idxs_good_nil : idxs_good []
| idxs_good_cons idxs i lo :
  idxs_good idxs ->
  incl (vars_of_Zexpr lo) idxs ->
  idxs_good (idxs ++ [i]).

Lemma map_app_no_dups_incl {B : Type} l1 l2 (f : _ -> B) :
  incl (map f l1 ++ map f l2) (map f (l1 ++/ l2)).
Proof.
  intros x. cbv [app_no_dups]. rewrite map_app. do 2 rewrite in_app_iff.
  intros [H|H]; auto. repeat rewrite in_map_iff in *. fwd.
  destruct (in_bool l1 x0) eqn:E.
  - rewrite in_bool_In in E. eauto.
  - right. exists x0. split; [reflexivity|]. apply filter_In. rewrite E. auto.
Qed.

Lemma lower_idx_keeps_vars e :
  incl (vars_of_expr (lower_idx e)) (map inl (vars_of_Zexpr e)).
Proof.
  induction e; simpl; try rewrite app_nil_r; try rewrite map_app; try apply incl_refl.
  all: eapply incl_tran; [|apply map_app_no_dups_incl].
  all: apply incl_app_app; auto.
Qed.

Lemma lower_guard_keeps_vars e :
  incl (vars_of_expr (lower_guard e)) (map inl (vars_of_Bexpr e)).
Proof.
  induction e; simpl; try rewrite app_nil_r; try rewrite map_app; try apply incl_refl.
  all: eapply incl_tran; [|apply map_app_no_dups_incl].
  all: apply incl_app_app; auto using lower_idx_keeps_vars.
Qed.

Definition out_smaller out name :=
  match out with
  | str_rel _ => True
  | nat_rel n => n < name
  | true_rel => False
  end.

Lemma out_smaller_weaken out name name' :
  out_smaller out name ->
  name <= name' ->
  out_smaller out name'.
Proof. destruct out; simpl; auto; lia. Qed.

Ltac prove_IH_hyp :=
  repeat match goal with
    | H: nat_rel _ = nat_rel _ |- _ => invert H
    end;
  try (intros ?; fwd);
  eassumption ||
    (econstructor; eassumption) ||
    (rewrite map_app; simpl; assumption) ||
    congruence ||
    (simpl; lia) ||
    (eapply out_smaller_weaken; solve [eauto]) ||
    solve[sets] ||
    (match goal with
     | H: ~ (exists _ : _, _) |- False => apply H; try (eexists; split; [|reflexivity]; solve[sets])
     end).

Ltac prove_IH_hyps IH :=
  epose_dep IH;
  match goal with
  | H : lower_rec _ _ _ _ _ = _ |- _ => rewrite H in IH
  end;
  repeat (specialize' IH; [solve[prove_IH_hyp] |]);
  fwd.

Ltac destr_lower :=
  match goal with
  | |- context[lower_rec ?e ?out ?name ?idxs ?depths] =>
      let name' := fresh "name'" in
      let rules := fresh "rules" in
      let E := fresh "E" in
      destruct (lower_rec e out name idxs depths) as (name'&rules) eqn:E
  end.

Ltac prove_good_rule :=
  cbv [good_rule_or_out]; simpl; constructor; [|constructor]; simpl; auto.

Ltac prove_good_rule_hyp := simpl; try lia.

Ltac prove_good_rule_hyps :=
  cbv [good_rule_hyps]; simpl;
  repeat (constructor; [solve[prove_good_rule_hyp] |]); constructor.

Ltac prove_rel_diff :=
  let H := fresh "H" in
  let H2 := fresh "H" in
  intros ? ? ? H ? H2; destruct H2 as [H2|H2]; [|destruct H2];
  subst; simpl; rewrite Forall_forall in *;
  match goal with
  | H': _ |- _ => apply H' in H
  end;
  cbv [good_rule_or_out] in H; rewrite Forall_forall in H;
  specialize (H _ ltac:(eassumption)); cbv [good_rel] in H;
  simpl in *; subst;
  match goal with
  | |- ?x <> ?y => let H' := fresh "H'" in
                intros H'; subst; try (rewrite H' in * );
                destruct x; simpl in *; try congruence
  end; destruct H as [H|H]; prove_IH_hyp.

Ltac prove_rels_diff :=
  (*apply diff_rels_Forall_r*) (*TODO*) idtac; repeat (constructor; [prove_rel_diff|]); try constructor.

Hint Extern 3 (_ \in _) => solve [sets] : autosets.

(* Lemma lower_Sexpr_relnames_good idxs depths n s e hyps n' : *)
(*   lower_Sexpr idxs depths n s = (e, hyps, n') -> *)
(*   Forall (fun f => exists x, x \in vars_of_Sexpr s /\ f.(clause_R) = str_rel x) hyps. *)
(* Proof. *)
(*   revert idxs depths n e hyps n'. induction s; simpl; intros *; *)
(*     repeat destruct_one_match; simpl in *; invert1 1; eauto with autosets. *)
(*   all: apply Forall_app; split; eapply Forall_impl; eauto; simpl; intros; fwd. *)
(*   all: eexists; split; eauto; sets. *)
(* Qed. *)

(* Lemma lower_rec_relnames_good e out name idxs depths name' rules : *)
(*   lower_rec e out name idxs depths = (name', rules) -> *)
(*   name <= name' /\ Forall (good_rule_or_out out name name' (fun str => str \in vars_of e)) rules /\ Forall (good_rule_hyps name name' (fun str => str \in referenced_vars e)) rules. *)
(* Proof. *)
(*   revert out name idxs depths name' rules. *)
(*   induction e; simpl; intros *; repeat destr_lower; intros * H; invert H; *)
(*     try apply IHe in E; try apply IHe1 in E; try apply IHe2 in E0; fwd; auto; *)
(*     (ssplit; [lia| |]); *)
(*     repeat match goal with *)
(*     | |- Forall _ (_ ++ _) => apply Forall_app; split *)
(*     | |- Forall _ (_ :: _) => constructor; [solve [prove_good_rule] || solve[prove_good_rule_hyps] |] *)
(*     | |- Forall _ nil => constructor *)
(*     | H: context[good_rule_or_out] |- Forall (good_rule_or_out _ _ _ _) _ => *)
(*         eapply Forall_impl; [|exact H]; intros; *)
(*         cbv [good_rule_or_out] in * *)
(*     | H: context[good_rule_hyps] |- Forall (good_rule_hyps _ _ _) _ => *)
(*         eapply Forall_impl; [|exact H]; intros; *)
(*         cbv [good_rule_hyps] in *; *)
(*         try match goal with *)
(*           | H: _ |- _ => rewrite Forall_app in H *)
(*           end; fwd *)
(*     | |- Forall _ _ => *)
(*         eapply Forall_impl; [  | eassumption ]; simpl; *)
(*         ((intros ?x [?Hx| ?Hx]; try rewrite Hx) || (intros ?x ?Hx; try rewrite Hx)) *)
(*       | |- _ \/ _ => *)
(*           (right; subst; reflexivity) || *)
(*           (left; simpl; lia) || *)
(*             (left; simpl; solve[sets]) || *)
(*             (left; eapply good_rel_weaken; [eassumption|lia|lia|sets]) *)
(*       | |- good_rel _ _ _ _ _ => eapply good_rel_weaken; [eassumption|lia|lia|sets] *)
(*       | |- In _ (_ ++ _) => apply in_app_iff; eauto *)
(*       end. *)
(*   constructor; [|constructor]. cbv [good_rule_hyps]. simpl. *)
(*   eapply Forall_impl. 2: eauto using lower_Sexpr_relnames_good. simpl. *)
(*   intros * H. fwd. rewrite Hp1. simpl. assumption. *)
(* Qed. *)

(* Lemma lower_functional_rec e out name idxs depths : *)
(*   idxs_good idxs -> *)
(*   vars_good idxs e -> *)
(*   ~ (exists out', out' \in vars_of e /\ out = str_rel out') -> *)
(*   out_smaller out name -> *)
(*   let (name', rules) := lower_rec e out name idxs depths in *)
(*   pairwise_ni rules. *)
(* Proof. *)
(*   revert out name idxs depths. *)
(*   induction e; *)
(*     simpl; intros out name idxs depths Hidxs Hvars_good Hout1 Hout2; invert Hvars_good; *)
(*     repeat destr_lower; *)
(*     try match goal with *)
(*       | H: _ = (_, _), G: _ = (_, _) |- _ => let H' := fresh "H00" in pose proof H as H'; apply lower_rec_relnames_good in H; let G' := fresh "G00" in pose proof G as G'; apply lower_rec_relnames_good in G; destruct H as (?&?&_); destruct G as (?&?&_) *)
(*       | H: _ = (_, _) |- _ => let H' := fresh "H00" in pose proof H as H'; apply lower_rec_relnames_good in H; destruct H as (?&?&_) *)
(*     end; fwd; *)
(*     try (prove_IH_hyps IHe || (prove_IH_hyps IHe1; prove_IH_hyps IHe2)). *)
(*   - auto. *)
(*   - apply pairwise_ni_app; [assumption|..]. *)
(*     + apply pairwise_ni'_sound. repeat constructor. *)
(*     + prove_rels_diff. *)
(*   - apply pairwise_ni_app; auto. *)
(*     + apply pairwise_ni'_sound. constructor. *)
(*       { constructor. *)
(*         { cbv [obviously_non_intersecting]. intros. *)
(*           repeat (invert_stuff; simpl in * ). *)
(*           (*from HA and HB, i want to conclude that ctx and ctx0 agree on idxs*) *)
(*           match goal with *)
(*           | H1: Forall2 _ (_ ++ _) _, H2: Forall2 _ (_ ++ _) _ |- _ => *)
(*               rename H1 into HA; rename H2 into HB *)
(*           end. *)
(*           apply Forall2_app_inv_l in HA, HB. fwd. clear HAp1 HBp1. *)
(*           assert (l1' = l1'0). *)
(*           { apply Forall2_length in HAp0, HBp0. rewrite HBp0 in HAp0. *)
(*             pose proof (invert_app _ _ _ _ ltac:(eassumption) ltac:(eassumption)). *)
(*             fwd. auto. } *)
(*           subst. clear HAp2. *)
(*           assert (Forall (agree_on ctx' ctx'0) (map inl idxs)) as H'. *)
(*           { eapply Forall2_and in HAp0; [|eassumption]. *)
(*             apply Forall2_forget_r in HAp0. rewrite Forall_map in HAp0. *)
(*             eapply Forall_impl; [|eassumption]. simpl. intros a Ha. fwd. *)
(*             invert Hap1. invert Hap2. cbv [agree_on]. eauto using Logic.eq_trans. } *)
(*           rewrite Forall_map in H'. eapply incl_Forall in H'; eauto. *)
(*           rewrite <- Forall_map in H'. *)
(*           eapply incl_Forall in H'. 2: apply lower_guard_keeps_vars. *)
(*           epose proof interp_expr_agree_on as H''. *)
(*           epose proof (H'' _ _ _ _) as H''. *)
(*           specialize' H''. 2: specialize (H'' ltac:(eassumption)). 1: eassumption. *)
(*           epose proof interp_expr_det as H'''. *)
(*           match goal with *)
(*           | H1: _, H2: _ |- _ => specialize (H''' _ _ _ _ H1 H2) *)
(*           end. *)
(*           subst. clear. destruct b; auto. } *)
(*         constructor. } *)
(*       repeat constructor. *)
(*     + prove_rels_diff. *)
(*   - apply pairwise_ni_app; auto. cbv [diff_rels]. *)
(*     intros r1 r2 c1 c2 Hr1 Hr2 Hc1 Hc2. rewrite Forall_forall in *. *)
(*     match goal with *)
(*     | H1: _ , H2: _ |- _ => apply H1 in Hr1; apply H2 in Hr2 *)
(*     end. (*i gues this is quadratic?*) *)
(*     cbv [good_rule_or_out] in Hr1, Hr2. *)
(*     rewrite Forall_forall in Hr1, Hr2. apply Hr1 in Hc1. apply Hr2 in Hc2. *)
(*     clear Hr1 Hr2. move Hout1 at bottom. move Hout2 at bottom. *)
(*     intros H'. rewrite H' in *. clear H'. cbv [out_smaller] in Hout2. *)
(*     destruct Hc1 as [Hc1|Hc1]; destruct Hc2 as [Hc2|Hc2]. *)
(*     + cbv [good_rel] in Hc1, Hc2. destruct (clause_R c2); try congruence. *)
(*       -- sets. *)
(*       -- lia. *)
(*     + subst. destruct (clause_R c2); try congruence. *)
(*       -- simpl in Hc1. apply Hout1. exists s. intuition auto. sets. *)
(*       -- simpl in Hc1. lia. *)
(*     + destruct (clause_R c2); try congruence. simpl in Hc2. invert Hc1. *)
(*       Fail Fail auto. sets. *)
(*     + subst. rewrite Hc1 in *. apply Hout1. eexists. intuition eauto. sets. *)
(*   - apply pairwise_ni_app; [|apply pairwise_ni_app|]; auto. *)
(*     + apply pairwise_ni'_sound. constructor. *)
(*       { constructor. *)
(*         { cbv [obviously_non_intersecting]. intros. subst. *)
(*           repeat (invert_stuff; simpl in * ). *)
(*           (*from HA and HB, i want to conclude that ctx and ctx0 agree on idxs*) *)
(*           match goal with *)
(*           | H1: Forall2 _ (_ ++ _) _, H2: Forall2 _ (_ ++ _) _ |- _ => *)
(*               rename H1 into HA; rename H2 into HB *)
(*           end. *)
(*           apply Forall2_app_inv_l in HA, HB. fwd. *)
(*           assert (l1' = l1'0). *)
(*           { apply Forall2_length in HAp0, HBp0. rewrite HBp0 in HAp0. *)
(*             pose proof (invert_app _ _ _ _ ltac:(eassumption) ltac:(eassumption)). *)
(*             fwd. auto. } *)
(*           subst. clear HAp0 HBp0. apply app_inv_head in HAp2. subst. *)
(*           invert HAp1. invert HBp1. repeat invert_stuff. *)
(*           repeat match goal with *)
(*                  | H: map.get _ _ = Some _ |- _ => rewrite H in * *)
(*                  end. *)
(*           repeat match goal with *)
(*                  | H : Some _ = Some _ |- _ => invert H *)
(*                  end. *)
(*           remember (Z.of_nat _) as blah eqn:Eblah. clear Eblah. *)
(*           match goal with *)
(*           | |- context[(?a <? ?b)%Z] => *)
(*               destr (a <? b)%Z; destr (b <=? a)%Z; auto; lia *)
(*           end. } *)
(*         constructor. } *)
(*       repeat constructor. *)
(*     + prove_rels_diff. *)
(*     + apply diff_rels_app_r. *)
(*       -- cbv [diff_rels]. *)
(*          intros r1 r2 c1 c2 Hr1 Hr2 Hc1 Hc2. rewrite Forall_forall in *. *)
(*          match goal with *)
(*          | H1: _ , H2: _ |- _ => apply H1 in Hr1; apply H2 in Hr2 *)
(*          end. *)
(*          cbv [good_rule_or_out] in Hr1, Hr2. *)
(*          rewrite Forall_forall in Hr1, Hr2. apply Hr1 in Hc1. apply Hr2 in Hc2. *)
(*          clear Hr1 Hr2. move Hout1 at bottom. move Hout2 at bottom. *)
(*          intros H'. rewrite H' in *. clear H'. cbv [out_smaller] in Hout2. *)
(*          destruct Hc1 as [Hc1|Hc1]; destruct Hc2 as [Hc2|Hc2]. *)
(*          ++ cbv [good_rel] in Hc1, Hc2. destruct (clause_R c2); try congruence. *)
(*             --- sets. *)
(*             --- lia. *)
(*          ++ subst. destruct (clause_R c2); try congruence. invert Hc2. simpl in Hc1. lia. *)
(*          ++ rewrite Hc1 in Hc2. simpl in Hc2. lia. *)
(*          ++ rewrite Hc1 in Hc2. invert Hc2. lia. *)
(*       -- prove_rels_diff. *)
(*   - apply pairwise_ni_app; auto. *)
(*     + apply pairwise_ni'_sound. repeat constructor. *)
(*     + prove_rels_diff. *)
(*   - apply pairwise_ni_app; auto. *)
(*     + apply pairwise_ni'_sound. constructor. *)
(*       -- simpl. constructor; [|constructor]. *)
(*          cbv [obviously_non_intersecting]. intros. subst. *)
(*          repeat (invert_stuff; simpl in * ). *)
(*          (*want to conclude that ctxs agree on dimvar1 and dimvar2*) *)
(*          match goal with *)
(*           | H1: Forall2 _ (_ ++ _) _, H2: Forall2 _ (_ ++ _) _ |- _ => *)
(*               rename H1 into HA; rename H2 into HB *)
(*           end. *)
(*           apply Forall2_app_inv_l in HA, HB. fwd. *)
(*          assert (l1' = l1'0). *)
(*          { apply Forall2_length in HAp0, HBp0. rewrite HBp0 in HAp0. *)
(*            pose proof (invert_app _ _ _ _ ltac:(eassumption) ltac:(eassumption)). *)
(*            fwd. auto. } *)
(*          subst. clear HAp0 HBp0. apply app_inv_head in HAp2. subst. *)
(*          repeat (invert_stuff; simpl in * ). *)
(*          remember (match sizeof e with | [] => 0 | _ => _ end) as x eqn:Ex. clear Ex. *)
(*          repeat match goal with *)
(*                 | H: map.get _ _ = Some _ |- _ => rewrite H in * *)
(*                 end. *)
(*          repeat match goal with *)
(*                 | H : Some _ = Some _ |- _ => invert H *)
(*                 end. *)
(*          remember (Z.of_nat x / _)%Z as xx eqn:Exx. remember (Z.of_nat x mod _)%Z as yy eqn:Eyy. *)
(*          clear Exx Eyy. rewrite Z.eqb_refl. destruct (yy <=? _)%Z; auto. *)
(*       -- repeat constructor. *)
(*     + prove_rels_diff. *)
(*   - apply pairwise_ni_app; auto. *)
(*     + apply pairwise_ni'_sound. repeat constructor. *)
(*     + prove_rels_diff. *)
(*   - auto. *)
(*   - apply pairwise_ni_app; auto. *)
(*     + apply pairwise_ni'_sound. repeat constructor. *)
(*     + prove_rels_diff. *)
(*   - apply pairwise_ni_app; auto. *)
(*     + apply pairwise_ni'_sound. constructor. *)
(*       -- simpl. constructor; [|constructor]. *)
(*          cbv [obviously_non_intersecting]. intros. subst. *)
(*          repeat (invert_stuff; simpl in * ). *)
(*          (*want to conclude that ctxs agree on dimvar1 and dimvar2*) *)
(*          match goal with *)
(*           | H1: Forall2 _ (_ ++ _) _, H2: Forall2 _ (_ ++ _) _ |- _ => *)
(*               rename H1 into HA; rename H2 into HB *)
(*           end. *)
(*          apply Forall2_app_inv_l in HA, HB. fwd. *)
(*          assert (l1' = l1'0). *)
(*          { apply Forall2_length in HAp0, HBp0. rewrite HBp0 in HAp0. *)
(*            pose proof (invert_app _ _ _ _ ltac:(eassumption) ltac:(eassumption)). *)
(*            fwd. auto. } *)
(*          subst. clear HAp0 HBp0. apply app_inv_head in HAp2. subst. *)
(*          repeat (invert_stuff; simpl in * ). *)
(*          remember (Z.of_nat match sizeof e with | [] => 0 | _ => _ end) as x eqn:Ex. clear Ex. *)
(*          repeat match goal with *)
(*                 | H: map.get _ _ = Some _ |- _ => rewrite H in * *)
(*                 end. *)
(*          repeat match goal with *)
(*                 | H : Some _ = Some _ |- _ => invert H *)
(*                 end. *)
(*          match goal with *)
(*          | |- context[(?a <? ?b)%Z] => *)
(*              destr (a <? b)%Z; destr (b <=? a)%Z; auto; lia *)
(*          end. *)
(*       -- repeat constructor. *)
(*     + prove_rels_diff. *)
(*   - apply pairwise_ni_app; auto. *)
(*     + apply pairwise_ni'_sound. constructor. *)
(*       -- simpl. constructor; [|constructor]. *)
(*          cbv [obviously_non_intersecting]. intros. subst. *)
(*          repeat (invert_stuff; simpl in * ). *)
(*          (*want to conclude that ctxs agree on dimvar1 and dimvar2*) *)
(*          match goal with *)
(*           | H1: Forall2 _ (_ ++ _) _, H2: Forall2 _ (_ ++ _) _ |- _ => *)
(*               rename H1 into HA; rename H2 into HB *)
(*           end. *)
(*          apply Forall2_app_inv_l in HA, HB. fwd. *)
(*          assert (l1' = l1'0). *)
(*          { apply Forall2_length in HAp0, HBp0. rewrite HBp0 in HAp0. *)
(*            pose proof (invert_app _ _ _ _ ltac:(eassumption) ltac:(eassumption)). *)
(*            fwd. auto. } *)
(*          subst. clear HAp0 HBp0. apply app_inv_head in HAp2. subst. *)
(*          repeat (invert_stuff; simpl in * ). *)
(*          remember (Z.of_nat _) as x eqn:Ex. clear Ex. *)
(*          repeat match goal with *)
(*                 | H: map.get _ _ = Some _ |- _ => rewrite H in * *)
(*                 end. *)
(*          repeat match goal with *)
(*                 | H : Some _ = Some _ |- _ => invert H *)
(*                 end. *)
(*          match goal with *)
(*          | |- context[(?a <? ?b)%Z] => *)
(*              destr (a <? b)%Z; destr (b <=? a)%Z; auto; lia *)
(*          end. *)
(*       -- repeat constructor. *)
(*     + prove_rels_diff. *)
(*   - destruct (lower_Sexpr idxs depths 0 s) as ((val&hyps)&_). *)
(*     apply pairwise_ni'_sound. repeat constructor. *)
(* Qed. *)

(* Lemma good_not_in_snd p name name' P R : *)
(*   ~good_rel name name' P true R -> *)
(*   Forall (good_rule_hyps name name' P) p -> *)
(*   not_in_snd (rel_graph p) R. *)
(* Proof. *)
(*   intros H1 H2. cbv [not_in_snd]. intros H'. apply H1. apply in_map_iff in H'. *)
(*   fwd. rewrite Forall_forall in H2. cbv [rel_graph] in H'p1. *)
(*   rewrite in_flat_map in H'p1. fwd. apply H2 in H'p1p0. cbv [edges_of_rule] in H'p1p1. *)
(*   cbv [good_rule_hyps] in H'p1p0. rewrite in_flat_map in H'p1p1. fwd. *)
(*   rewrite in_map_iff in H'p1p1p1. fwd. rewrite Forall_forall in H'p1p0. apply H'p1p0. *)
(*   assumption. *)
(* Qed. *)

(* Lemma lower_dag_rec e out name idxs depths name' rules idxs0 : *)
(*   vars_good idxs0 e -> (*this is unnecessarily stong*) *)
(*   ~ (exists out', out' \in vars_of e \cup referenced_vars e /\ out = str_rel out') -> *)
(*   out_smaller out name -> *)
(*   lower_rec e out name idxs depths = (name', rules) -> *)
(*   dag (rel_graph rules). *)
(* Proof. *)
(*   revert out name idxs depths name' rules idxs0. *)
(*   induction e; *)
(*     simpl; intros out name idxs depths name' rules idxs0 Hvars_good Hout1 Hout2; *)
(*     invert Hvars_good; *)
(*     repeat destr_lower; intros H; *)
(*     try match goal with *)
(*       | H: _ = (_, _), G: _ = (_, _) |- _ => let H' := fresh "H00" in pose proof H as H'; apply lower_rec_relnames_good in H; let G' := fresh "G00" in pose proof G as G'; apply lower_rec_relnames_good in G; destruct H as (?&?&?); destruct G as (?&?&?) *)
(*       | H: _ = (_, _) |- _ => let H' := fresh "H00" in pose proof H as H'; apply lower_rec_relnames_good in H; destruct H as (?&_&?) *)
(*       end; fwd; *)
(*     try (prove_IH_hyps IHe || (prove_IH_hyps IHe1; prove_IH_hyps IHe2)); *)
(*     cbv [rel_graph] in *; repeat rewrite flat_map_app; simpl; repeat rewrite app_nil_r; simpl. *)
(*   Ltac prove_no_cycles' := *)
(*     repeat match goal with *)
(*       | |- _ => progress (intros; subst; fwd; cbv [good_rel good_rule_hyps]; simpl in * ) *)
(*       | H: context[match ?out with _ => _ end] |- _ => destr out *)
(*       | |- context[match ?out with _ => _ end] => destr out *)
(*       | |- Forall _ (_ :: _) => constructor *)
(*       | |- Forall _ [] => constructor *)
(*       | |- _ => solve [sets] *)
(*       | |- ~_ => intros ? *)
(*       | |- _ /\ _ => split *)
(*       | H: ~_ |- False => apply H; eexists; intuition eauto; [] *)
(*       | H: _ \/ _ |- _ => destruct H; [solve[prove_no_cycles'] |] *)
(*       end. *)
(*   Ltac prove_no_cycles := *)
(*     repeat match goal with *)
(*       | |- _ => eassumption *)
(*       | |- _ => apply dag_cons; repeat rewrite app_nil_r *)
(*       | |- not_in_snd (_ :: _) _ => apply not_in_snd_cons; [prove_no_cycles'|] *)
(*       | |- not_in_snd (_ ++ _) _ => apply not_in_snd_app *)
(*       | |- not_in_snd [] _ => apply not_in_snd_nil *)
(*       | |- not_in_snd _ _ => solve [eapply good_not_in_snd; [|eassumption]; prove_no_cycles'] *)
(*       end. *)
(*   all: prove_no_cycles. *)
(*   all: cycle -1. *)
(*   { cbv [edges_of_rule]. simpl. rewrite app_nil_r. *)
(*     apply lower_Sexpr_relnames_good in E. eapply concl_same_dag. *)
(*     apply Forall_map. eapply Forall_impl; [|eassumption]. simpl. intros. fwd. *)
(*     split; eauto. intros H. subst. apply Hout1. eexists. intuition eauto. sets. } *)
(*   { (*should come from the fact that vars_of e2 \cap referenced_vars e1 is empty*) *)
(*     (*that is, concls of rules1 \cap hyps of rules0 is empty*) *)
(*     clear H11 (*hyps or rules1*) H1 (*concls of rules0*). eapply dag_incl. *)
(*     2: { apply Permutation_incl. apply Permutation.Permutation_app_comm. } *)
(*     apply dag_app; auto. cbv [no_cycles]. apply Forall_map. apply Forall_flat_map. *)
(*     eapply Forall_impl; [|eassumption]. intros r Hr. *)
(*     cbv [good_rule_or_out] in Hr. apply Forall_flat_map. *)
(*     eapply Forall_impl; [|eassumption]. simpl. intros. rewrite <- Forall_map. *)
(*     rewrite map_map. simpl. rewrite map_const. apply Forall_repeat. *)
(*     prove_no_cycles. } *)
(*   { rewrite app_assoc. prove_no_cycles. *)
(*     clear H8 H6. (*arbitrary choice, but works with dag'_app*) *)
(*     apply dag_app; auto. cbv [no_cycles]. apply Forall_map. apply Forall_flat_map. *)
(*     eapply Forall_impl; [|eassumption]. intros r Hr. *)
(*     cbv [good_rule_or_out] in Hr. apply Forall_flat_map. *)
(*     eapply Forall_impl; [|eassumption]. simpl. intros. rewrite <- Forall_map. *)
(*     rewrite map_map. simpl. rewrite map_const. apply Forall_repeat. *)
(*     prove_no_cycles. } *)
(*   Unshelve. (*TODO why*) all: exact "". *)
(* Qed. *)

(* Lemma lower_functional' e out : *)
(*   vars_good [] e -> *)
(*   ~(out \in vars_of e) -> *)
(*   pairwise_ni (lower e out). *)
(* Proof. *)
(*   intros H1 H2. pose proof lower_functional_rec as H'. *)
(*   cbv [lower]. epose_dep H'. destr_lower. rewrite E in H'. *)
(*   simpl. apply lower_rec_relnames_good in E. fwd. apply pairwise_ni_app. *)
(*   - apply H'; simpl; eauto. *)
(*     + constructor. *)
(*     + intros ?. fwd. auto. *)
(*   - apply pairwise_ni'_sound. repeat constructor. *)
(*   - apply diff_rels_Forall_r. constructor; [|constructor]. *)
(*     rewrite Forall_forall in Ep1. intros r1 c1 c2 Hr1 Hc1 Hc2. simpl in Hc2. *)
(*     destruct Hc2; contradiction || subst. simpl. intros ?. apply Ep1 in Hr1. *)
(*     cbv [good_rule_or_out] in Hr1. rewrite Forall_forall in Hr1. apply Hr1 in Hc1. *)
(*     rewrite H in Hc1. destruct Hc1; try congruence. simpl in H0. contradiction. *)
(* Qed. *)

(* Lemma lower_dag e out : *)
(*   vars_good [] e -> *)
(*   ~(out \in vars_of e \cup referenced_vars e) -> *)
(*   dag (rel_graph (lower e out)). *)
(* Proof. *)
(*   intros H1 H2. pose proof lower_dag_rec as H'. *)
(*   cbv [lower]. destr_lower. epose_dep H'. rewrite E in H'. *)
(*   simpl. apply lower_rec_relnames_good in E. fwd. cbv [rel_graph]. rewrite flat_map_app. *)
(*   simpl. rewrite app_nil_r. eapply H'; eauto; prove_no_cycles'. *)
(* Qed. *)

(* Instance query_sig : query_signature rel := *)
(*   { outs R := *)
(*       match R with *)
(*       | str_rel _ => 1 *)
(*       | nat_rel _ => 1 *)
(*       | true_rel => 0 (*why did i choose to make this zero instead of 1?*) *)
(*       end }. *)

(* Ltac t0 tac := *)
(*     repeat match goal with *)
(*       | H: exists _, _ |- _ => destruct H *)
(*       | H: inr _ = inr _ |- _ => invert H *)
(*       | H: (_, _, _) = (_, _, _) |- _ => invert H *)
(*       | H: _ /\ _ |- _ => destruct H *)
(*       | H: Some _ = Some _ |- _ => invert H *)
(*       | H: In _ (map _ _) |- _ => apply in_map_iff in H *)
(*       | H: In _ (seq _ _) |- _ => apply in_seq in H *)
(*       | H: In _ (flat_map _ _) |- _ => apply in_flat_map in H *)
(*       | H: appears_in_rule _ _ |- _ => destruct H as [? | [? | ?] ] *)
(*       | |- _ => progress (intros; cbv [good_agg_expr vars_of_fact] in *; simpl in *; subst) *)
(*       | |- ~_ => intro *)
(*       | H: In _ (vars_of_expr (lower_idx _)) |- _ => apply lower_idx_keeps_vars in H *)
(*       | H: In _ (vars_of_expr (lower_guard _)) |- _ => apply lower_guard_keeps_vars in H *)
(*       | H: In _ ?l, H': incl ?l ?l' |- _ => apply H' in H *)
(*       | |- False \/ _ => right *)
(*       | H: False \/ _ |- _ => destruct H; [contradiction|] *)
(*       | H: in_set_hyps _ [] \/ _ |- _ => destruct H as [H|H]; *)
(*                                       [exfalso; solve[eauto using not_in_set_hyps_nil] |] *)
(*       | H: _ \/ False |- _ => destruct H; [|contradiction] *)
(*       | H: appears_in_agg_expr _ _ |- _ => destruct H as [? | (?&[?|?]) ] *)
(*       | H: _ = _ \/ _ |- _ => destruct H; subst *)
(*       | |- (exists _, inl _ = inr _ /\ _) \/ _ => right *)
(*       | |- _ = _ /\ _ => split; [reflexivity|] *)
(*       | |- _ /\ _ => split *)
(*       | H: In _ (_ ++ _) |- _ => rewrite in_app_iff in H; destruct H *)
(*       | |- _ => congruence || lia *)
(*       | |- _ => destruct_one_match_hyp *)
(*       | |- _ => destruct_one_match *)
(*       | |- In _ (_ ++ _) => apply in_app_iff *)
(*       | |- In _ (map _ _) => apply in_map_iff *)
(*       | |- In _ (flat_map _ _) => apply in_flat_map *)
(*       | |- In _ (seq _ _) => apply in_seq *)
(*       | H: ~_ |- _ => solve [exfalso; apply H; eauto] *)
(*       | |- _ => solve[eauto] *)
(*       | |- _ \/ _ => (left; solve[t0 tac]) || (right; solve [t0 tac]) *)
(*       | |- exists _, _ => eexists; t0 tac; tac *)
(*       end. *)

(* Ltac t := t0 idtac. *)
(* Ltac t' := t0 fail. *)

(* Lemma lower_Sexpr_goodish1 idxs s depths e n hyps n' v : *)
(*   lower_Sexpr idxs depths n s = (e, hyps, n') -> *)
(*   In v (vars_of_expr e) -> *)
(*   In (var_expr v) (flat_map clause_args hyps). *)
(* Proof. *)
(*   revert idxs depths n e hyps n' v. induction s; t'; *)
(*     match goal with *)
(*     | IH: forall _ _ _ _ _ _ _, _ -> _ -> _, H: lower_Sexpr _ _ _ _ = _ |- _ => eapply IH in H; eauto; [] *)
(*   end; t. *)
(* Qed. *)

(* Lemma lower_Sexpr_goodish2 idxs depths n s e hyps n' v : *)
(*   lower_Sexpr idxs depths n s = (e, hyps, n') -> *)
(*   In v (flat_map vars_of_expr (flat_map clause_ins hyps)) -> *)
(*   In v (map inl idxs) \/ In v (map inl (idx_vars_of_Sexpr s)). *)
(* Proof. *)
(*   revert idxs depths n e hyps n' v. induction s; cbv [clause_ins] in *; simpl in *; t'; invert_list_stuff; t. *)
(*   { invert E. left. apply in_firstn in H2. t. } *)
(*   { invert E. left. apply in_firstn in H2. t. } *)
(*   all: match goal with *)
(*     | IH: forall _ _ _ _ _ _ _, _ -> _ -> _, H: lower_Sexpr _ _ _ _ = _ |- _ => eapply IH in H; t; []; destruct H *)
(*   end; t. *)
(* Qed. *)

(* Lemma lower_Sexpr_goodish3 idxs depths n s e hyps n' v : *)
(*   lower_Sexpr idxs depths n s = (e, hyps, n') -> *)
(*   In v (flat_map vars_of_fact hyps) -> *)
(*   In (var_expr v) (flat_map clause_args hyps) \/ (In v (map inl idxs) \/ In v (map inl (idx_vars_of_Sexpr s))). *)
(* Proof. *)
(*   revert idxs depths n e hyps n' v. induction s; t. *)
(*   all: match goal with *)
(*     | IH: forall _ _ _ _ _ _ _, _ -> _ -> _, H: lower_Sexpr _ _ _ _ = _ |- _ => eapply IH in H; t; []; destruct H as [? | [?|?]] *)
(*   end; t. *)
(* Qed. *)

(* Lemma lower_rec_goodish e out name idxs depths : *)
(*   out <> true_rel -> *)
(*   vars_good idxs e -> *)
(*   Forall goodish_rule (snd (lower_rec e out name idxs depths)). *)
(* Proof. *)
(*   revert out name idxs depths. *)
(*   induction e; simpl; intros out name idxs depths Hout Hgood; *)
(*     invert Hgood; repeat destr_lower; simpl. *)
(*   all: try (epose_dep IHe; rewrite E in IHe; specialize (IHe ltac:(congruence) ltac:(assumption))). *)
(*   all: try (epose_dep IHe1; epose_dep IHe2; rewrite E in *; rewrite E0 in *; specialize (IHe1 ltac:(congruence) ltac:(assumption)); specialize (IHe2 ltac:(congruence) ltac:(assumption))). *)
(*   all: repeat rewrite map_app; simpl. *)
(*   all: repeat (apply Forall_app; split; [eauto|]). *)
(*   all: eauto. *)
(*   all: repeat constructor. *)
(*   all: (eexists; split; [reflexivity|]; cbv [clause_ins]; simpl) || idtac "fail". *)
(*   Ltac prove_letin_ok := *)
(*     intro; fwd; *)
(*     try congruence; *)
(*     repeat match goal with *)
(*       | H: _ \/ False |- _ => destruct H; [|contradiction] *)
(*       | |- _ => progress (intros; simpl in *; fwd) *)
(*       | |- _ => rewrite in_map_iff in * || rewrite in_seq in * || rewrite in_flat_map in * *)
(*       | H: In _ (_ ++ _) |- _ => rewrite in_app_iff in H; destruct H *)
(*       | |- _ => congruence || lia *)
(*       | |- _ => destruct_one_match_hyp *)
(*       end. *)
(*   all: (split; [solve[prove_letin_ok] |]) || idtac "fail". *)

(*   all: (split; [solve[t] | ]) || idtac "fail". *)
(*   all: (split; [solve[t] | ]) || idtac "fail". *)
(*   all: (split; [solve[t] | ]) || idtac "fail". *)
(*   all: solve [constructor] || idtac "fail". *)
(*   1: solve[t]. *)
(*   t. *)
(*   constructor; [|constructor]. *)
(*   eexists; split; [reflexivity|]; cbv [clause_ins]; simpl. *)
(*   split; [solve[prove_letin_ok] |]. *)
(*   pose proof lower_Sexpr_goodish1 as H1'. *)
(*   pose proof lower_Sexpr_goodish2 as H2'. *)
(*   pose proof lower_Sexpr_goodish3 as H3'. *)
(*   specialize H1' with (1 := E). specialize H2' with (1 := E). *)
(*   specialize H3' with (1 := E). *)
(*   t'. *)
(*   { specialize (H3' _ ltac:(t)). destruct H3' as [? | [?|?]]; t. } *)
(*   { specialize (H3' _ ltac:(t)). destruct H3' as [? | [?|?]]; t. } *)
(*   { eexists. t'. epose_dep H2'. specialize' H2'. *)
(*     { t. cbv [clause_ins]. rewrite E1. t. } *)
(*     destruct H2' as [?|?]; t. } *)
(*   all: try (eexists; t'; epose_dep H2'; specialize' H2'; [t; cbv [clause_ins]; rewrite E1; t|]; destruct H2'; solve[t]). *)
(*   { apply lower_Sexpr_relnames_good in E. rewrite Forall_forall in E. *)
(*     specialize (E _ ltac:(eassumption)). fwd. congruence. } *)
(*   { apply lower_Sexpr_relnames_good in E. rewrite Forall_forall in E. *)
(*     specialize (E _ ltac:(eassumption)). fwd. congruence. } *)
(* Qed. *)

(* Lemma lower_goodish e out : *)
(*   vars_good [] e -> *)
(*   Forall goodish_rule (lower e out). *)
(* Proof. *)
(*   intros H. cbv [lower]. apply Forall_app. split. *)
(*   - apply lower_rec_goodish; auto. congruence. *)
(*   - constructor; [|constructor]. cbv [goodish_rule]. t. *)
(* Qed. *)

(* Lemma lower_rec_goodish_fun out idxs e name depths : *)
(*   out <> true_rel -> *)
(*   vars_good idxs e -> *)
(*   Forall goodish_fun (snd (lower_rec e out name idxs depths)). *)
(* Proof. *)
(*   revert out name idxs depths. *)
(*   induction e; simpl; intros out name idxs depths Hout Hgood; *)
(*     invert Hgood; repeat destr_lower; simpl. *)
(*   all: try (epose_dep IHe; rewrite E in IHe; specialize (IHe ltac:(congruence) ltac:(assumption))). *)
(*   all: try (epose_dep IHe1; epose_dep IHe2; rewrite E in *; rewrite E0 in *; specialize (IHe1 ltac:(congruence) ltac:(assumption)); specialize (IHe2 ltac:(congruence) ltac:(assumption))). *)
(*   all: repeat rewrite map_app; simpl. *)
(*   all: repeat (apply Forall_app; split; [eauto|]). *)
(*   all: eauto. *)
(*   all: repeat constructor. *)
(*   all: (eexists; split; [reflexivity|]; cbv [clause_ins]; simpl) || idtac "fail". *)
(*   all: (split; [solve[t] |]) || idtac "fail". *)
(*   all: solve [constructor] || idtac "fail". *)
(*   1: solve[t]. *)
(*   t. *)
(*   constructor; [|constructor]. *)
(*   eexists; split; [reflexivity|]; cbv [clause_ins]; simpl. *)
(*   split; [|constructor]. *)
(*   intros. fwd. *)
(*   pose proof lower_Sexpr_goodish1 as H1'. *)
(*   specialize H1' with (1 := E). t. *)
(* Qed. *)

(* Lemma good_index_lower_rec out idxs e name depths : *)
(*   Forall good_index (snd (lower_rec e out name idxs depths)). *)
(* Proof. *)
(*   revert out name idxs depths. *)
(*   induction e; simpl; intros out name idxs depths; *)
(*     repeat destr_lower; simpl. *)
(*   all: try (epose_dep IHe; rewrite E in IHe). *)
(*   all: try (epose_dep IHe1; epose_dep IHe2; rewrite E in *; rewrite E0 in * ). *)
(*   all: repeat (apply Forall_app; split; [eauto|]). *)
(*   all: eauto. *)
(*   all: repeat constructor. *)
(*   all: t. *)
(*   { cbv [clause_ins] in *. simpl in *. t. } *)
(*   constructor; t. *)
(*   cbv [good_index]. t. *)
(* Qed. *)

(* Lemma good_index_lower e out : *)
(*   Forall good_index (lower e out). *)
(* Proof. *)
(*   cbv [lower]. apply Forall_app. split. *)
(*   - apply good_index_lower_rec. *)
(*   - repeat constructor. *)
(* Qed. *)

(* Lemma lower_goodish_fun e out : *)
(*   vars_good [] e -> *)
(*   Forall goodish_fun (lower e out). *)
(* Proof. *)
(*   intros H. cbv [lower]. apply Forall_app. split. *)
(*   - apply lower_rec_goodish_fun; auto. congruence. *)
(*   - constructor; [|constructor]. cbv [goodish_fun]. t. *)
(* Qed. *)

(* Check agree_functional. Print goodish_fun. Search agree. Search goodish_rule. *)

(* Lemma false_not_true e out : *)
(*   prog_impl_fact (lower e out) (true_rel, [Bobj false]) -> False. *)
(* Proof. *)
(*   intros H. cbv [lower] in H. invert H. apply Exists_app in H0. *)
(*   destruct H0 as [H0|H0]. *)
(*   - revert H0. destr_lower. intros H0. simpl in *. apply lower_rec_relnames_good in E. *)
(*     fwd. apply Exists_exists in H0. fwd. rewrite Forall_forall in Ep1. *)
(*     apply Ep1 in H0p0. cbv [good_rule_or_out] in H0p0. *)
(*     cbv [rule_impl] in H0p1. fwd. invert H0p1p1. clear H2 H3 H. *)
(*     apply Exists_exists in H0. rewrite Forall_forall in H0p0. fwd. *)
(*     apply H0p0 in H0p1. invert H0p2. destruct H0p1; [|congruence]. *)
(*     rewrite H in H0. simpl in H0. destruct H0. *)
(*   - invert_list_stuff. cbv [rule_impl] in H2. fwd. invert H2p1. *)
(*     repeat (invert_stuff || simpl in * ). *)
(* Qed. *)

(* Definition nothing_zeroary (r : rule) := *)
(*   Forall (fun c => 0 < length c.(fact_args)) r.(rule_concls). *)

(* Lemma no_zeroary_rules_lower_rec e out name idxs depths : *)
(*   Forall nothing_zeroary (snd (lower_rec e out name idxs depths)). *)
(* Proof. *)
(*   revert out name idxs depths. unfold nothing_zeroary. *)
(*   induction e; simpl; intros out name idxs depths; *)
(*     repeat destr_lower; simpl. *)
(*   all: try (epose_dep IHe; rewrite E in IHe). *)
(*   all: try (epose_dep IHe1; epose_dep IHe2; rewrite E in *; rewrite E0 in * ). *)
(*   all: repeat rewrite map_app; simpl. *)
(*   all: repeat (apply Forall_app; split; [eauto|]). *)
(*   all: eauto. *)
(*   all: repeat (apply Forall_cons || apply Forall_nil); simpl. *)
(*   all: try lia. *)
(*   destruct (lower_Sexpr _ _ _ _) as [[? ?] ?]. simpl. *)
(*   all: repeat (apply Forall_cons || apply Forall_nil ); simpl. *)
(*   lia. *)
(* Qed. *)

(* Lemma no_zeroary_rules_lower e out : *)
(*   Forall nothing_zeroary (lower e out). *)
(* Proof. *)
(*   cbv [lower]. apply Forall_app. split. *)
(*   - apply no_zeroary_rules_lower_rec. *)
(*   - repeat constructor. *)
(* Qed. *)

(* Lemma oni_agree r1 r2 p : *)
(*   nothing_zeroary r1 -> *)
(*   nothing_zeroary r2 -> *)
(*   obviously_non_intersecting r1 r2 -> *)
(*   ~prog_impl_fact p (true_rel, [Bobj false]) -> *)
(*   agree p r1 r2. *)
(* Proof. *)
(*   cbv [obviously_non_intersecting agree]. intros Hr1 Hr2 H Htrue * H1 H2 H3 H4 H5. *)
(*   cbv [rule_impl] in *. fwd. *)
(*   assert (Hor: outs R2 = 1 \/ outs R2 = 0) by (destruct R2; auto). *)
(*   destruct Hor as [Hor|Hor]; rewrite Hor in *. 2: exact H5. *)
(*   destruct args1. *)
(*   { exfalso. invert H1p1. apply Exists_exists in H1. fwd. *)
(*     repeat invert_stuff. cbv [nothing_zeroary] in Hr1. rewrite Forall_forall in Hr1. *)
(*     specialize (Hr1 _ ltac:(eassumption)). rewrite <- H11 in *. simpl in Hr1. lia. } *)
(*   destruct args2. *)
(*   { exfalso. invert H2p1. apply Exists_exists in H1. fwd. *)
(*     repeat invert_stuff. cbv [nothing_zeroary] in Hr2. rewrite Forall_forall in Hr2. *)
(*     specialize (Hr2 _ ltac:(eassumption)). rewrite <- H11 in *. simpl in Hr2. lia. } *)
(*   simpl in H5. subst. *)
(*   specialize H with (1 := H1p1) (2 := H2p1). *)
(*   destruct H as [H|H]; exfalso. *)
(*   - apply Htrue. rewrite Forall_forall in H3. apply H3. apply in_app_iff. eauto. *)
(*   - apply Htrue. rewrite Forall_forall in H4. apply H4. apply in_app_iff. eauto. *)
(* Qed. *)

(* Lemma lower_functional e out : *)
(*   vars_good [] e -> *)
(*   ~ out \in vars_of e \cup referenced_vars e -> *)
(*   functional (lower e out). *)
(* Proof. *)
(*   intros. apply agree_functional. *)
(*   - apply lower_dag; auto. *)
(*   - apply lower_goodish_fun; auto. *)
(*   - apply lower_goodish; auto. *)
(*   - eapply pairs_satisfy_weaken; cycle -1. *)
(*     + apply incl_refl. *)
(*     + apply lower_functional'; auto. sets. *)
(*     + intros. pose proof no_zeroary_rules_lower as H'. epose_dep H'. *)
(*       rewrite Forall_forall in H'. apply oni_agree; eauto. *)
(*       intro. eapply false_not_true. eassumption. *)
(* Qed. *)

(*i do not like fmaps, because you cannot iterate over them,
  so i work with coqutil maps instead.
  ATL things are defined in terms of fmaps, so i will reason
  about fmaps constructed from coqutil maps.
  annoyingly, i cannot construct an equivalent coqutil map from an fmap.
 *)
Definition context_of (v : valuation') : context :=
  map.fold (fun mp k v => map.put mp (inl k) (Zobj v)) map.empty v.

Lemma context_of_fw k val v :
  map.get val k = Some v ->
  map.get (context_of val) (inl k) = Some (Zobj v).
Proof.
  intros H. cbv [context_of]. revert H. apply map.fold_spec.
  - rewrite map.get_empty. congruence.
  - intros. rewrite map.get_put_dec in H1.
    rewrite map.get_put_dec. simpl. destr (k0 =? k)%string; auto. congruence.
Qed.

Lemma context_of_bw k val v :
  map.get (context_of val) k = Some v ->
  match k, v with
  | inl k, Zobj v => map.get val k = Some v
  | _, _ => False
  end.
Proof.
  cbv [context_of]. apply map.fold_spec.
  - rewrite map.get_empty. congruence.
  - intros. rewrite map.get_put_dec in H1. destr (var_eqb (inl k0) k).
    + invert H1. rewrite map.get_put_same. reflexivity.
    + apply H0 in H1. clear H0. destr k; auto. destr v; auto.
      rewrite map.get_put_dec. destr (k0 =? s)%string; congruence.
Qed.

Lemma extends_context_of v1 v2 : map.extends v1 v2 -> map.extends (context_of v1) (context_of v2).
Proof.
  intros H1 ? ? H2. apply context_of_bw in H2. destr x; destr w; try (exfalso; assumption).
  apply context_of_fw. auto.
Qed.

Lemma eval_Zexpr_to_substn v x z :
  eval_Zexpr (fmap_of v) x z ->
  interp_expr (context_of v) (lower_idx x) (Zobj z).
Proof.
  intros H. induction H; simpl;
    repeat match goal with | H: _ = Some _ |- _ => rewrite H end; econstructor; eauto.
  rewrite fmap_of_spec in *. auto using context_of_fw.
Qed.

Lemma eval_Bexpr_to_substn v x b :
  eval_Bexpr (fmap_of v) x b ->
  interp_expr (context_of v) (lower_guard x) (Bobj b).
Proof.
  intros H. induction H; simpl;
    repeat match goal with | H: _ = Some _ |- _ => rewrite H end; econstructor;
    eauto using eval_Zexpr_to_substn.
Qed.

Lemma eval_Zexprlist_to_substn v i lz :
  eval_Zexprlist (fmap_of v) i lz ->
  Forall2 (interp_expr (context_of v)) (map lower_idx i) (map Zobj lz).
Proof.
  intros H. remember (fmap_of v) as v' eqn:E. revert E. induction H; intros; subst.
  - constructor.
  - simpl. constructor; eauto using eval_Zexpr_to_substn.
Qed.

Definition domain_in_ints low high (ctx : context) :=
  forall x y, map.get ctx x = Some y ->
         match x with
         | inr i => low <= i < high
         | inl _ => False
         end.

Lemma domain_in_ints_disj low1 high1 low2 high2 s1 s2 :
  (forall i, low1 <= i < high1 -> low2 <= i < high2 -> False) ->
  domain_in_ints low1 high1 s1 ->
  domain_in_ints low2 high2 s2 ->
  map.disjoint s1 s2.
Proof.
  cbv [domain_in_ints map.disjoint]. intros ? H1 H2 **.
  specialize (H1 _ _ ltac:(eassumption)). specialize (H2 _ _ ltac:(eassumption)).
  destruct k; [contradiction|]. eauto.
Qed.

Lemma domain_in_ints_disj_substn_of low high s v :
  domain_in_ints low high s ->
  map.disjoint s (context_of v).
Proof.
  cbv [domain_in_ints map.disjoint]. intros. specialize H with (1 := H0).
  destruct k; [contradiction|]. apply context_of_bw in H1. auto.
Qed.

Lemma domain_in_ints_empty low high :
  domain_in_ints low high map.empty.
Proof. cbv [domain_in_ints]. intros. rewrite map.get_empty in *. congruence. Qed.

Lemma domain_in_ints_cons low high m x y :
  domain_in_ints low high m ->
  low <= x < high ->
  domain_in_ints low high (map.put m (inr x) y).
Proof.
  cbv [domain_in_ints]. intros. rewrite map.get_put_dec in H1.
  Tactics.destruct_one_match_hyp; auto. eauto. eapply H. eassumption.
Qed.

Lemma context_of_inr v k :
  map.get (context_of v) (inr k) = None.
Proof.
  destruct (map.get _ _) eqn:E; [|reflexivity].
  apply context_of_bw in E. destruct E.
Qed.

Lemma domain_in_ints_weaken lo1 hi1 lo2 hi2 m :
  lo1 <= lo2 ->
  hi2 <= hi1 ->
  domain_in_ints lo2 hi2 m ->
  domain_in_ints lo1 hi1 m.
Proof.
  cbv [domain_in_ints]. intros H1 H2 H3 x y H4. specialize (H3 x y H4).
  destruct x; [auto|lia].
Qed.

Definition idx_map (x : list obj) : context :=
  map.of_func (fun k => match k with
                     | inr n => nth_error x n
                     | inl _ => None
                     end) (map inr (seq O (length x))).

Lemma idx_map_spec x k :
  map.get (idx_map x) k = match k with
                          | inr n => nth_error x n
                          | inl _ => None
                          end.
Proof.
  set (P := match k with | inr n => 0 <= n < length x | inl _ => False end).
  assert (P \/ ~P) by (destruct k; subst P; auto; lia).
  subst P. cbv [idx_map]. destruct H as [H|H].
  - destruct k; [exfalso; auto|]. rewrite map.get_of_func_In. 1: reflexivity.
    apply in_map. apply in_seq. lia.
  - rewrite map.get_of_func_notIn.
    { destruct k; [reflexivity|]. symmetry. apply nth_error_None. lia. }
    intros H'. apply H. apply in_map_iff in H'. destruct H' as (?&?&?). subst.
    apply in_seq in H1. lia.
Qed.

Lemma domain_in_ints_idx_map x :
  domain_in_ints O (length x) (idx_map x).
Proof.
  cbv [domain_in_ints]. intros y z H. rewrite idx_map_spec in H.
  destruct y; [congruence|]. apply nth_error_Some in H. assumption.
Qed.

Lemma idx_map_works idxs :
  Forall2 (interp_expr (idx_map (map Zobj idxs)))
    (map var_expr (map inr (seq O (length idxs))))
    (map Zobj idxs).
Proof.
  apply Forall2_nth_error.
  { repeat rewrite length_map. rewrite length_seq. auto. }
  intros n x1 x2. repeat rewrite nth_error_map. intros.
  invert_list_stuff. apply nth_error_seq_Some in Hp0p0.
  subst. simpl. constructor. rewrite idx_map_spec. rewrite nth_error_map, H0p0.
  reflexivity.
Qed.

Lemma idx_map_None idxs x :
  (0 <= x < length idxs -> False) ->
  map.get (idx_map idxs) (inr x) = None.
Proof.
  intros H. pose proof domain_in_ints_idx_map idxs (inr x) as H'.
  simpl in H'. rewrite idx_map_spec in *.
  destruct (nth_error idxs x); auto. exfalso. eauto.
Qed.

Ltac simpl_map :=
  repeat (rewrite map.get_putmany_left by isNone_solver) ||
    rewrite map.get_put_same ||
    (erewrite context_of_fw by solve_map_get) ||
    rewrite map.get_put_diff by (let x := fresh "x" in intros x; invert x; lia)

      with solve_map_get :=
    simpl_map;
    (reflexivity ||
       assumption ||
       (apply map.get_putmany_right; solve_map_get) ||
         (apply map.get_putmany_left; solve_map_get))
      with isNone_solver :=
      simpl_map;
      apply context_of_inr ||
        (apply putmany_None; isNone_solver) ||
        apply map.get_empty ||
        reflexivity ||
        (apply idx_map_None; simpl; repeat rewrite length_map; simpl; lia) ||
        (rewrite <- fmap_of_spec; solve [eauto using None_dom_lookup]) ||
        idtac.

Ltac domain_in_ints_solver :=
  apply domain_in_ints_idx_map.

Ltac disj_solver' disj_solver :=
    (eapply domain_in_ints_disj_substn_of; domain_in_ints_solver) ||
      (apply map.disjoint_put_l; [isNone_solver|disj_solver]) ||
      (apply map.disjoint_put_r; [isNone_solver|disj_solver]) ||
      (apply map.disjoint_empty_r || apply map.disjoint_empty_l).

Ltac disj_solver :=
  disj_solver' disj_solver || (apply map.disjoint_comm; disj_solver' disj_solver) || idtac.

Ltac ext_refl :=
  match goal with
  | |- map.extends ?a ?b =>
      tryif is_evar a then fail else tryif is_evar b then fail else apply map.extends_refl
  end.

Ltac extends_solver :=
  solve [eauto] || extends_solver' ||
    (eapply extends_trans; [solve[extends_solver'] | solve [extends_solver] ]) || idtac
    (*important to have the backtracking here because of the eapply extends_trans*)
    with extends_solver' :=
    (apply extends_put; isNone_solver) +
      (apply extends_putmany_left; disj_solver) +
      (apply extends_putmany_putmany; solve[extends_solver]) +
      (apply extends_context_of; extends_solver) +
      (apply extends_putmany_right) +
      ext_refl.

(*TODO there's got to be a less hacky way to do this*)
Lemma decomp_fact ctx y blah1 blah2 :
  interp_clause ctx y ({| fact_R := blah1; fact_args := blah2 |} : fact) ->
  interp_clause ctx y {| fact_R := blah1; fact_args := blah2 |}.
Proof. auto. Qed.

Ltac interp_exprs :=
  repeat rewrite map_app; simpl;
  repeat match goal with
    | _ => progress simpl
    | |- Forall2 _ (_ ++ _) _ => apply Forall2_app
    | |- Forall2 _ (_ :: _) _ => constructor
    | |- Forall2 _ nil _ => constructor
    | |- Forall2 _ (map var_expr (map inl _)) _ =>
        do 2 rewrite <- Forall2_map_l; try apply Forall2_firstn; solve [interp_exprs]
    | |- Forall2 _ _ _ =>
        (eapply Forall2_impl; [|eassumption]; simpl; intros) ||
          (eapply Forall2_impl;
           [|apply idx_map_works ||
               (match goal with
                | H: _ = length ?x |- context[seq _ (length ?x)] => rewrite <- H
                | H: length ?x = _ |- context[seq _ (length ?x)] => rewrite H
                end;
                apply idx_map_works)]; simpl; intros)
    | |- interp_expr _ (fun_expr _ _) _ => econstructor
    | |- interp_expr _ (var_expr _) _ => constructor
    | |- interp_expr _ (lower_idx _) _ =>
        eapply interp_expr_subst_more; [|eapply eval_Zexpr_to_substn; eassumption || (apply eval_Zexpr_Z_eval_Zexpr; eassumption)]
    | |- interp_expr _ (lower_guard _) _ =>
        eapply interp_expr_subst_more; [|eapply eval_Bexpr_to_substn; eassumption]
    | |- interp_expr _ _ _ =>
        eapply interp_expr_subst_more; [|eassumption]
    | |- interp_clause _ _ _ =>
        eapply interp_clause_subst_more; [|eassumption]
    | |- map.extends _ _ => extends_solver
    | |- map.get ?ctx' _ = _ => try subst ctx'; solve_map_get
    | |- map.get ?ctx' _ = _ => let H := fresh "H" in eenough (map.extends _ _) as H; [apply H; eassumption|]; solve[extends_solver]
    | |- interp_clause _ _ ?x =>
        try (is_evar x; eapply decomp_fact); split
    | |- _ /\ _ => split; [solve [interp_exprs] |]
    | |- Exists _ [_] => apply Exists_cons_hd
    | |- Forall2 _ (map lower_idx _) _ => eapply Forall2_impl; [|apply eval_Zexprlist_to_substn; eassumption]; intros
    | |- _ => reflexivity
    end.

Lemma lower_Sexpr_correct idxs0 depths v ec s (datalog_ctx : list rule) idxs0':
  Forall2 (fun x y => map.get (context_of v) (inl x) = Some y) idxs0 idxs0' ->
  (forall x r idxs val,
      ec $? x = Some r ->
      result_lookup_Z' idxs r val ->
      exists n,
        map.get depths x = Some n /\
          prog_impl_fact datalog_ctx {| fact_R := (str_rel x, normal);
                                       fact_args := Robj (toR val) :: firstn n idxs0' ++ map Zobj idxs |}) ->
  forall val name val0 hyps name',
    eval_Sexpr (fmap_of v) ec s val ->
    lower_Sexpr idxs0 depths name s = (val0, hyps, name') ->
    exists hyps' substn,
      name <= name' /\
        domain_in_ints name name' substn /\
        Forall2 (interp_clause (map.putmany substn (context_of v))) hyps hyps' /\
        Forall (prog_impl_fact datalog_ctx) hyps' /\
        interp_expr (map.putmany substn (context_of v)) val0 (Robj (toR val)).
Proof.
  intros H1 H2. induction s; intros; simpl in *.
  - invert H.
    pose proof (eval_get_eval_Zexprlist _ _ _ _ ltac:(eassumption)) as [idxs Hidxs].
    pose proof (eval_get_lookup_result_Z' _ _ _ _ ltac:(eassumption) _ ltac:(eassumption)) as Hr.
    specialize (H2 _ _ _ _ ltac:(eassumption) ltac:(eassumption)). fwd.
    eexists. exists (map.put map.empty (inr name) (Robj (toR r))). split.
    { lia. }
    split.
    { apply domain_in_ints_cons. 2: lia. apply domain_in_ints_empty. }
    split.
    { interp_exprs. }
    split.
    { interp_exprs. repeat constructor. assumption. }
    interp_exprs. destruct r; solve_map_get.
  - invert H.
    destruct (lower_Sexpr _ _ name s1) as [[val1 hyps1] name1] eqn:E1.
    destruct (lower_Sexpr _ _ name1 s2) as [[val2 hyps2] name2] eqn:E2.
    invert H0.
    specialize (IHs1 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    specialize (IHs2 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    destruct IHs1 as (hyps1'&substn1&Hname1&Hname1'&Hhyps1&Hhyps1'&Hval1).
    destruct IHs2 as (hyps2'&substn2&Hname2&Hname2'&Hhyps2&Hhyps2'&Hval2).
    exists (hyps1' ++ hyps2')%list. exists (map.putmany substn1 substn2).
    assert (map.extends (map.putmany substn1 substn2) substn1).
    { apply extends_putmany_left. intros k v1 v2 H1' H2'.
      apply Hname1' in H1'. apply Hname2' in H2'. destruct k; auto. lia. }
    split.
    { lia. } split.
    { intros ? ? H'. rewrite map.get_putmany_dec in H'.
      destruct (map.get substn2 x) eqn:E.
      - apply Hname2' in E. destruct x; [contradiction | lia].
      - apply Hname1' in H'. destruct x; [contradiction | lia]. }
    interp_exprs. split.
    { apply Forall_app. split; assumption. }
    interp_exprs.
    simpl. f_equal. f_equal. destruct r1, r2; reflexivity.
  (*!!literally copy-pasted!!*)
  - invert H.
    destruct (lower_Sexpr _ _ name s1) as [[val1 hyps1] name1] eqn:E1.
    destruct (lower_Sexpr _ _ name1 s2) as [[val2 hyps2] name2] eqn:E2.
    invert H0.
    specialize (IHs1 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    specialize (IHs2 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    destruct IHs1 as (hyps1'&substn1&Hname1&Hname1'&Hhyps1&Hhyps1'&Hval1).
    destruct IHs2 as (hyps2'&substn2&Hname2&Hname2'&Hhyps2&Hhyps2'&Hval2).
    exists (hyps1' ++ hyps2')%list. exists (map.putmany substn1 substn2).
    assert (map.extends (map.putmany substn1 substn2) substn1).
    { apply extends_putmany_left. intros k v1 v2 H1' H2'.
      apply Hname1' in H1'. apply Hname2' in H2'. destruct k; auto. lia. }
    split.
    { lia. } split.
    { intros ? ? H'. rewrite map.get_putmany_dec in H'.
      destruct (map.get substn2 x) eqn:E.
      - apply Hname2' in E. destruct x; [contradiction | lia].
      - apply Hname1' in H'. destruct x; [contradiction | lia]. }
    interp_exprs. split.
    { apply Forall_app. split; assumption. }
    interp_exprs.
    simpl. f_equal. f_equal. destruct r1, r2; reflexivity.
  - invert H.
    destruct (lower_Sexpr _ _ name s1) as [[val1 hyps1] name1] eqn:E1.
    destruct (lower_Sexpr _ _ name1 s2) as [[val2 hyps2] name2] eqn:E2.
    invert H0.
    specialize (IHs1 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    specialize (IHs2 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    destruct IHs1 as (hyps1'&substn1&Hname1&Hname1'&Hhyps1&Hhyps1'&Hval1).
    destruct IHs2 as (hyps2'&substn2&Hname2&Hname2'&Hhyps2&Hhyps2'&Hval2).
    exists (hyps1' ++ hyps2')%list. exists (map.putmany substn1 substn2).
    assert (map.extends (map.putmany substn1 substn2) substn1).
    { apply extends_putmany_left. intros k v1 v2 H1' H2'.
      apply Hname1' in H1'. apply Hname2' in H2'. destruct k; auto. lia. }
    split.
    { lia. } split.
    { intros ? ? H'. rewrite map.get_putmany_dec in H'.
      destruct (map.get substn2 x) eqn:E.
      - apply Hname2' in E. destruct x; [contradiction | lia].
      - apply Hname1' in H'. destruct x; [contradiction | lia]. }
    interp_exprs. split.
    { apply Forall_app. split; assumption. }
    interp_exprs.
    simpl. f_equal. f_equal. destruct r1, r2; reflexivity.
  - invert H.
    destruct (lower_Sexpr _ _ name s1) as [[val1 hyps1] name1] eqn:E1.
    destruct (lower_Sexpr _ _ name1 s2) as [[val2 hyps2] name2] eqn:E2.
    invert H0.
    specialize (IHs1 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    specialize (IHs2 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    destruct IHs1 as (hyps1'&substn1&Hname1&Hname1'&Hhyps1&Hhyps1'&Hval1).
    destruct IHs2 as (hyps2'&substn2&Hname2&Hname2'&Hhyps2&Hhyps2'&Hval2).
    exists (hyps1' ++ hyps2')%list. exists (map.putmany substn1 substn2).
    assert (map.extends (map.putmany substn1 substn2) substn1).
    { apply extends_putmany_left. intros k v1 v2 H1' H2'.
      apply Hname1' in H1'. apply Hname2' in H2'. destruct k; auto. lia. }
    split.
    { lia. } split.
    { intros ? ? H'. rewrite map.get_putmany_dec in H'.
      destruct (map.get substn2 x) eqn:E.
      - apply Hname2' in E. destruct x; [contradiction | lia].
      - apply Hname1' in H'. destruct x; [contradiction | lia]. }
    interp_exprs. split.
    { apply Forall_app. split; assumption. }
    interp_exprs.
    simpl. f_equal. f_equal. destruct r1, r2; reflexivity.
  - invert H0. invert H. eexists. exists map.empty.
    split; [lia|]. split.
    { apply domain_in_ints_empty. }
    interp_exprs. split.
    { constructor. }
    interp_exprs.
Qed.

Lemma nth_error_Forall2_r {A B : Type} (R : A -> B -> Prop) l1 l2 n x2 :
  Forall2 R l1 l2 ->
  nth_error l2 n = Some x2 ->
  exists x1,
    nth_error l1 n = Some x1 /\
      R x1 x2.
Proof.
  intros H1 H2. apply nth_error_split in H2. destruct H2 as (l3&l4&H2&H3). subst.
  apply Forall2_app_inv_r in H1. destruct H1 as (l5&l6&H2&H3&H4). subst.
  invert H3. apply Forall2_length in H2. rewrite <- H2.
  exists x. split; [|assumption]. rewrite nth_error_app2 by lia. replace _ with O by lia.
  reflexivity.
Qed.

(*TODO use result_has_shape_flatten_result instead*)
Lemma length_flatten_result n m sh l :
  result_has_shape' (n :: m :: sh) (V l) ->
  length (flatten_result l) = n * m.
Proof.
  revert n. induction l; intros n H; invert H.
  - reflexivity.
  - simpl. invert H4. invert H1. rewrite length_app. erewrite IHl.
    2: { econstructor; [reflexivity|]. assumption. } lia.
Qed.

Lemma div_le_div_ceil a b :
  a / b <= a //n b.
Proof.
  cbv [div_ceil_n]. destruct b.
  { simpl. lia. }
  apply Nat.Div0.div_le_mono. lia.
Qed.

Lemma nth_error_split_result' l k x :
  0 < k ->
  let pad := gen_pad (match result_shape_nat (V l) with
                      | [] => []
                      | _ :: xs => xs
                      end) in
  match nth_error (split_result k l) (x / k) with
  | Some y =>
      match y with
      | V v => (x < length l /\ nth_error v (x mod k) = nth_error l x) \/
                (length l <= x /\ x / k = length l / k /\ nth_error v (x mod k) = Some pad)
      | _ => False
      end
  | _ => True
  end.
Proof.
  intros H1. cbv [split_result]. rewrite nth_error_map.
  destruct (nth_error _ _) eqn:E.
  2: { simpl. constructor. } cbv [gen_pad_list].
  simpl. cbv [nat_range] in E.
  pose proof E as E'. apply nth_error_seq_Some in E'. subst.
  replace (0 + x / k) with (x / k) by lia.
  rewrite nth_error_firstn_elim.
  2: { apply Nat.mod_upper_bound. lia. }
  rewrite nth_error_skipn. rewrite <- Nat.div_mod_eq.
  apply nth_error_Some in E. rewrite length_seq in E.
  assert (H: x < length l \/ length l <= x) by lia. destruct H as [H|H].
  - left. split; [lia|]. rewrite nth_error_app1 by lia. reflexivity.
  - right. split; [lia|]. rewrite nth_error_app2 by lia.
    destruct E as [_ E].
    pose proof mod_0_iff_ceil_eq_floor_0 (length l) k ltac:(lia) as H'.
    pose proof ceil_sub_floor_le_1 (length l) k as H''.
    assert (H''': length l mod k = 0 \/ length l mod k <> 0) by lia.
    destruct H''' as [H'''|H'''].
    { rewrite H'''. exfalso. apply H' in H'''. rewrite H''' in E.
      apply Nat.Div0.div_le_mono with (c := k) in H. lia. }
    pose proof (div_le_div_ceil (length l) k).
    assert (H2: length l //n k = length l / k + 1) by lia.
    rewrite H2 in E. clear -E H H''' H1.
    apply Nat.Div0.div_le_mono with (c := k) in H.
    assert (x / k = length l / k) by lia.
    rewrite Nat.mod_small by lia.
    eassert (x - length l = _) as ->. { rewrite (Nat.div_mod_eq (length l) k). reflexivity. }
    assert (length l mod k < k).
    { apply Nat.mod_upper_bound. lia. }
    split; [assumption|]. apply nth_error_repeat.
    enough (x - k * (length l / k) < k) by lia.
    rewrite (Nat.div_mod_eq x k). rewrite H0.
    assert (x mod k < k).
    { apply Nat.mod_upper_bound. lia. }
    lia.
Qed.

(*following result_lookup_Z_transpose*)
Lemma result_lookup_Z'_transpose l z z0 x n m xs val :
  result_has_shape (V l) (n :: m :: xs) ->
  result_lookup_Z' (z :: z0 :: x) (transpose_result l (m :: n :: xs)) val ->
  result_lookup_Z' (z0 :: z :: x) (V l) val.
Proof.
  simpl. intros.
  pose proof (nth_error_transpose (row_length l) (Z.to_nat z) _ _ _ _ H).
  pose proof result_has_shape_transpose_result as H'.
  specialize (H' _ _ _ _ ltac:(eassumption)).
  destruct l.
  { rewrite <- result_has_shape'_iff in H'. invert H'. invert H.
    cbv [transpose_result] in H0. simpl in H0. invert H0.
    apply nth_error_repeat' in H7. subst. invert H9. rewrite nth_error_empty in H7.
    discriminate H7. }
  cbv [transpose_result] in H0, H'.
  erewrite result_has_shape_row_length in * by (eassumption || congruence).
  assert (0 < n).
  { invert H. lia. }
  erewrite pad_list_result_shape_id in H0, H' by (eassumption || simpl; lia).
  remember (r :: l) as l' eqn:E. clear E.
  invert H0. rewrite H7 in H1.
  assert (0 <= Z.to_nat z < m).
  { rewrite <- result_has_shape'_iff in H'. invert H'. apply nth_error_Some in H7. lia. }
  specialize (H1 ltac:(lia) ltac:(lia)). subst.
  replace (m - (m - Z.to_nat z)) with (Z.to_nat z) in * by lia.
  invert H9.
  assert (0 <= Z.to_nat z0 < n).
  { apply nth_error_Some in H8. erewrite length_get_col in H8 by (eassumption || lia).
    rewrite <- result_has_shape'_iff in H. invert H. lia. }
  erewrite <- nth_error_get_col in H8 by (eassumption || lia).
  clear H7. destruct (nth_error l' (Z.to_nat z0)) eqn:E; [|discriminate H8].
  destruct r0; [discriminate H8|]. econstructor; eauto. econstructor; eauto.
Qed.

Ltac unfp :=
  repeat match goal with
    | H: eval_Zexpr_Z _ _ = Some _ |- _ => apply eval_Zexpr_Z_eval_Zexpr in H
    end.

Lemma lower_rec_complete e idx_ctx idx_ctx' depths out v ec r datalog_ctx l :
  eval_expr (fmap_of v) ec e r ->
  size_of (fmap_of v) e l ->
  nonneg_bounds (fmap_of v) e ->
  gen_lbs_zero e ->
  (forall x (r : result) (idxs : list Z) (val : scalar_result),
      ec $? x = Some r ->
      result_lookup_Z' idxs r val ->
      exists n,
        map.get depths x = Some n /\
          n <= length idx_ctx /\
          prog_impl_fact datalog_ctx
                         {| fact_R := (str_rel x, normal);
                           fact_args := Robj (toR val) :: firstn n idx_ctx' ++ map Zobj idxs |}) ->
  forall idxs name val,
    result_lookup_Z' idxs r val ->
    Forall2 (fun x y => map.get (context_of v) (inl x) = Some y) idx_ctx idx_ctx' ->
    prog_impl_fact (snd (lower_rec e out name idx_ctx depths) ++ datalog_ctx ++ [true_rule])
                   {| fact_R := (out, normal);
                     fact_args := Robj (toR val) :: idx_ctx' ++ map Zobj idxs|}.
Proof.
  revert idx_ctx idx_ctx' depths out v ec r datalog_ctx l. induction e;
    intros idx_ctx idx_ctx' depths out v ec r datalog_ctx l Heval Hsz Hbds Hlbs IH' idxs name val Hidxs Hidx_ctx.
  - simpl in *. fwd. apply invert_eval_gen in Heval.
    destruct Heval as (loz0&hiz0&rl&Hrl&Hlen&Hlo&Hhi&Hbody). unfp. eq_eval_Z.
    move IHe at bottom. invs. invert Hidxs.
    move Hbody at bottom. specialize (Hbody (x)%Z).
    epose proof nth_error_Some as E'. specialize (E' _ _ _ ltac:(eassumption)).
    specialize (Hbody ltac:(lia)). clear E'.
    destruct Hbody as (Hdom&_&Hbody). replace (x - 0)%Z with x in Hbody by lia.
    rewrite H1 in Hbody. rewrite add_fmap_of in Hbody.
    specialize IHe with (1 := Hbody).
    epose proof (IHe (idx_ctx ++ [i]) (idx_ctx' ++ [_]) _ _ _ _) as IHe.
    specialize' IHe.
    { eapply size_of_includes; [|eauto].
      apply fmap_of_extends_includes. extends_solver. }
    specialize' IHe.
    { eapply nonneg_bounds_includes; [|eauto].
      apply fmap_of_extends_includes. extends_solver. }
    specialize (IHe ltac:(assumption)).
    specialize' IHe.
    { move IH' at bottom. intros.
      specialize (IH' _ _ _ _ ltac:(eassumption) ltac:(eassumption)). fwd.
      eexists. split; [eassumption|]. rewrite length_app. simpl. split; [lia|].
      apply Forall2_length in Hidx_ctx.
      rewrite firstn_app. replace (_ - _) with O by lia. simpl. rewrite app_nil_r.
      eassumption. }
    epose_dep IHe. specialize (IHe ltac:(eassumption)).
    specialize' IHe.
    { interp_exprs. }
    rewrite <- app_assoc in IHe. simpl in IHe.
    simpl. apply IHe.
  - intros.
    pose proof dimensions_right as H'.
    specialize (H' _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    specialize (H' _ _ _ _ _ _ ltac:(eassumption)).
    invert H0. simpl in H1.
    specialize IHe with (2 := H10) (3 := H1).
    apply invert_eval_sum in H.
    destruct H as (loz&hiz&summands&Hlen&Hloz&Hhiz&Hsummands&Hbody).
    specialize Hsummands with (1 := H3). destruct Hsummands as (ss&Hs&Hss).
    pose proof dim_idxs as H''. specialize (H'' _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    apply size_of_sizeof in H10. subst. clear H'.
    set (s := map.putmany (context_of v) (idx_map (map Zobj idxs))).
    econstructor.
    + apply eval_Zexpr_Z_eval_Zexpr in Hhiz, Hloz.
      apply eval_Zexpr_to_substn in Hhiz, Hloz.
      simpl. apply Exists_app. left. destr_lower. simpl. apply Exists_app. simpl. right.
      apply Exists_cons_hd. cbv [rule_impl]. do 3 eexists. split; [reflexivity|].
      eapply mk_rule_impl' with (ctx := s).
      -- econstructor; [reflexivity|]. econstructor.
         { interp_exprs. }
         { reflexivity. }
         { instantiate (2 := map Robj (map toR ss)). apply Forall3_zip3.
           move Hss at bottom. move Hs at bottom. move Hbody at bottom.
           apply Forall2_nth_error.
           { repeat rewrite length_map. rewrite length_zrange. apply Forall2_length in Hs. lia. }
           intros n x1 x2 H H0. repeat rewrite nth_error_map in *.
           invert_list_stuff. apply nth_error_zrange_Some in Hp0. subst.
           specialize (Hbody (loz + Z.of_nat n)%Z).
           eassert _ as blah. 2: specialize (Hbody blah); clear blah.
           { split; try lia. apply nth_error_Some in H0p0p0.
             apply Forall2_length in Hs. lia. }
           destruct Hbody as (_&_&Hbody). replace (Z.to_nat _) with n in Hbody by lia.
           epose proof nth_error_Forall2_r as H'.
           specialize (H' _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
           destruct H' as (summand&Hsummand1&Hsummand2). rewrite Hsummand1 in Hbody.
           eexists [_]. simpl. eexists. split; [reflexivity|].
           instantiate (2 := fun _ _ => _). interp_exprs. }
         { reflexivity. }
      -- apply Exists_cons_hd. constructor. simpl. constructor.
         { repeat econstructor. simpl_map. rewrite Hss. f_equal.
           clear. induction ss; simpl; auto. rewrite IHss. reflexivity. }
         interp_exprs.
      -- constructor.
      -- simpl. constructor.
    + simpl. apply Forall_concat. apply Forall_zip. apply Forall2_nth_error.
      { repeat rewrite length_map. rewrite length_zrange. apply Forall2_length in Hs. lia. }
      intros n x1 x2 H H0. constructor; [|solve[constructor]].
      repeat rewrite nth_error_map in *. invert_list_stuff.
      apply nth_error_zrange_Some in Hp0. subst.
      specialize (Hbody (loz + Z.of_nat n)%Z).
      eassert _ as blah. 2: specialize (Hbody blah); clear blah.
      { split; try lia. apply nth_error_Some in H0p0p0.
        apply Forall2_length in Hs. lia. }
      destruct Hbody as (?&_&Hbody). replace (Z.to_nat _) with n in Hbody by lia.
      epose proof nth_error_Forall2_r as H'.
      specialize (H' _ _ _ _ _ Hs ltac:(eassumption)).
      destruct H' as (summand&Hsummand1&Hsummand2). rewrite Hsummand1 in Hbody.
      rewrite add_fmap_of in Hbody.
      eapply prog_impl_fact_subset; cycle 1.
      { eassert (idx_ctx' ++ _ :: _ = (_ ++ [_]) ++ _) as ->.
        { rewrite <- app_assoc. reflexivity. }
        eapply IHe with (idx_ctx := idx_ctx ++ [i]) (name := S name).
        - eassumption.
        - intros. specialize (H2 _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
          fwd. eexists. rewrite length_app. simpl. intuition eauto. 1: lia.
          apply Forall2_length in H4.
          rewrite firstn_app. replace (_ - _) with O by lia. simpl. rewrite app_nil_r.
          eassumption.
        - assumption.
        - interp_exprs. }
      intros x Hx. destr_lower. simpl. repeat rewrite in_app_iff in *. simpl. tauto.
  - simpl. intros. invert H0.
    pose proof dimensions_right as H'.
    pose proof dim_idxs as H''.
    invert H.
    + specialize (H'' _ _ _ _ ltac:(eauto using dim_gen_pad) ltac:(eassumption)).
      eq_size_of. apply size_of_sizeof in H8. subst.
      apply pad_lookup_SX in H3. subst. simpl. econstructor.
      { apply Exists_app. left. destr_lower. simpl.
        apply Exists_app. right. apply Exists_cons_tl. apply Exists_cons_hd.
        set (ctx' := map.putmany (context_of v) (idx_map (map Zobj idxs))).
        eapply normal_rule_impl with (ctx := ctx'); interp_exprs. }
      constructor.
      { econstructor.
        { apply Exists_app. right. apply Exists_app. right.
          apply Exists_cons_hd. simpl. eapply normal_rule_impl with (ctx := map.empty).
          { repeat econstructor. }
          constructor. }
        constructor. }
      constructor.
    + specialize (H' _ _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
      specialize (H'' _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
      pose proof size_of_sizeof as H7'. specialize (H7' _ _ ltac:(eassumption)).
      subst. clear H'. rewrite <- H''. clear H''.
      econstructor.
      { apply Exists_app. left. destr_lower. apply Exists_app. right. apply Exists_cons_hd.
        set (ctx' := map.put (map.putmany (context_of v) (idx_map (map Zobj idxs)))
                       (inr (length idxs)) (Robj (toR val))).
        apply normal_rule_impl with (ctx := ctx'); interp_exprs. }
      constructor.
      { simpl. specialize IHe with (name := S name).
        simpl in IHe.
        eapply prog_impl_fact_subset.
        2: { eapply IHe; eauto. }
        intros x Hx. destr_lower. simpl. repeat rewrite in_app_iff in *. simpl. tauto. }
      constructor.
      { simpl. econstructor.
        { apply Exists_app. right. apply Exists_app. right. apply Exists_cons_hd.
          eapply normal_rule_impl with (ctx := map.empty); repeat econstructor. }
        constructor. }
      constructor.
  - simpl. intros. destruct H1 as (H1&H1_). invert H0.
    pose proof Forall2_length as H4'. specialize H4' with (1 := H4).
    invert H.
    + destr_lower. destr_lower. simpl.
      eapply prog_impl_fact_subset.
      2: { eapply IHe2 with (name := name') (depths := map.put depths x _); eauto.
           intros * H1' H2'.
           apply lookup_split in H1'. destruct H1' as [(H1'&H3')|(H1'&H3')].
           2: { subst. specialize IHe1 with (name := name).
                simpl in IHe1. move IHe1 at bottom. exists (length idx_ctx).
                rewrite map.get_put_same. split; [reflexivity|]. split; [lia|].
                rewrite H4'. rewrite firstn_all. eapply IHe1; eauto. }
           move H2 at bottom.
           specialize (H2 _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
           fwd. eexists. rewrite map.get_put_diff by eassumption. intuition eauto.
           eapply prog_impl_fact_subset; [|eassumption].
           intros. repeat rewrite in_app_iff. simpl. tauto. }
      rewrite E, E0. intros. repeat rewrite in_app_iff in *. tauto.
    + destr_lower. destr_lower. simpl.
      eapply prog_impl_fact_subset.
      2: { eapply IHe2 with (name := name') (depths := map.put depths x _); eauto.
           intros * H1' H2'.
           apply lookup_split in H1'. destruct H1' as [(H1'&H3')|(H1'&H3')].
           2: { subst. specialize IHe1 with (name := name).
                simpl in IHe1. move IHe1 at bottom. exists (length idx_ctx).
                rewrite map.get_put_same. split; [reflexivity|]. split; [lia|].
                rewrite H4'. rewrite firstn_all. eapply IHe1; eauto. }
           move H2 at bottom.
           specialize (H2 _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
           fwd. eexists. rewrite map.get_put_diff by eassumption. intuition eauto.
           eapply prog_impl_fact_subset; [|eassumption].
           intros. repeat rewrite in_app_iff. simpl. tauto. }
      rewrite E, E0. intros. repeat rewrite in_app_iff in *. tauto.
  - simpl. intros. destruct H1 as (He1&He2). invert H0. invert H.
    destr_lower. destr_lower. rename H6 into Hsz1. rename H7 into Hsz2.
    pose proof ResultToArrayDelta.size_of_eval_expr_result_has_shape as He1'.
    specialize (He1' _ _ Hsz1 _ _ _ _ ltac:(eassumption)).
    pose proof ResultToArrayDelta.size_of_eval_expr_result_has_shape as He2'.
    specialize (He2' _ _ Hsz2 _ _ _ _ ltac:(eassumption)).
    apply result_has_shape_length in He1', He2'.
    invert H3.
    pose proof dimensions_right as H'.
    pose proof dim_idxs as H''.
    assert (Hidx: Z.to_nat x < length l1 \/ length l1 <= Z.to_nat x) by lia.
    pose proof size_of_sizeof as Hsz1'. specialize Hsz1' with (1 := Hsz1).
    rewrite Hsz1'. clear Hsz1'.
    destruct Hidx as [Hidx|Hidx].
    + rewrite nth_error_app1 in H1 by assumption.
      specialize (H' _ _ _ e1 _ _ ltac:(eassumption) ltac:(eassumption)).
      simpl in H'.
      specialize H'' with (1 := H'). clear H'.
      eassert _ as blah. 2: epose proof (H'' _ _ blah) as H'; clear H''.
      { econstructor; eassumption. }
      simpl in H'. cbn [length]. rewrite <- H'.
      econstructor.
      { apply Exists_app. left. apply Exists_app. right. apply Exists_app.
        right. apply Exists_cons_hd.
        { cbn -[seq]. replace (length xs - 0) with (length xs) by lia.
          eset (ctx' := map.put
                       (map.put
                          (map.putmany (context_of v) (idx_map (map Zobj xs)))
                          (inr (S (length xs))) (Robj (toR _)))
                       (inr (length xs)) (Zobj _)).
          eapply normal_rule_impl with (ctx := ctx'); interp_exprs. } }
      constructor.
      { cbn -[seq]. eapply prog_impl_fact_subset.
      2: { specialize IHe1 with (name := S (S name)) (idxs := x :: xs).
           simpl in IHe1. move IHe1 at bottom. eapply IHe1; eauto. }
      intros. repeat rewrite in_app_iff in *. rewrite E in *. tauto. }
      constructor; [|solve[constructor]].
      simpl. econstructor.
      { apply Exists_app. right. apply Exists_app. right. apply Exists_cons_hd.
        eapply normal_rule_impl; [|solve[constructor]]. apply Exists_cons_hd.
        interp_exprs. simpl. f_equal. f_equal. remember (Z.of_nat _) as y.
        destr (x <? y)%Z; [reflexivity|lia]. }
      constructor.
    + rewrite nth_error_app2 in H1 by assumption.
      specialize (H' _ _ _ e2 _ _ ltac:(eassumption) ltac:(eassumption)).
      simpl in H'.
      specialize H'' with (1 := H'). clear H'.
      eassert _ as blah. 2: epose proof (H'' _ _ blah) as H'; clear H''.
      { econstructor. 3: eassumption.
        2: { rewrite Nat2Z.id. eassumption. }
        lia. }
      clear blah.
      simpl in H'. cbn [length].
      rewrite <- H'. clear H'.
      simpl. replace (length xs - 0) with (length xs) by lia.
      econstructor.
      { apply Exists_app. left. apply Exists_app. right. apply Exists_app.
        right. apply Exists_cons_tl. apply Exists_cons_hd.
        { cbn -[seq].
          eset (ctx' := map.put
                          (map.put
                             (map.putmany (context_of v) (idx_map (map Zobj xs)))
                             (inr (S (length xs))) (Robj _))
                          (inr (length xs)) (Zobj _)).
          eapply normal_rule_impl with (ctx := ctx'); interp_exprs. } }
      simpl. constructor.
      { eapply prog_impl_fact_subset.
        2: { move IHe2 at bottom.
             specialize IHe2 with (idxs := (x - Z.of_nat (length l1) :: xs)%Z).
             simpl in IHe2. eapply IHe2; eauto.
             econstructor. 1: lia. 2: eassumption. rewrite <- H1. f_equal. lia. }
        intros. rewrite E0 in *. repeat rewrite in_app_iff in *. tauto. }
      simpl. constructor; [|solve[constructor]]. econstructor.
      { apply Exists_app. right. apply Exists_app. right. apply Exists_cons_hd.
        eapply normal_rule_impl; [|solve[constructor]]. apply Exists_cons_hd. interp_exprs.
        simpl. f_equal. f_equal. remember (Z.of_nat _) as y.
        destr (y <=? x)%Z; [reflexivity|lia]. }
      constructor.
  - simpl. intros. invert H. invert H0. destr_lower. simpl.
    pose proof ResultToArrayDelta.size_of_eval_expr_result_has_shape as He.
    specialize (He _ _ ltac:(eassumption) _ _ _ _ ltac:(eassumption)).
    simpl in He.
    pose proof nth_error_flatten as H'. specialize H' with (5 := He).
    pose proof dimensions_right as Hd1.
    pose proof dim_idxs as Hd2.
    specialize (Hd1 _ _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    specialize Hd2 with (2 := H3). eassert _ as blah.
    2: epose proof (Hd2 _ blah) as Hd3; clear blah Hd2.
    { constructor. apply dim_flatten_result. simpl in Hd1. eapply Hd1. }
    rewrite <- result_has_shape'_iff in He. invert He. invert H3.
    simpl in Hd3. invert Hd3.
    (*TODO factor out into lemma?*)
    assert (0 < m).
    { destruct m; [|lia]. clear -H7 H10.
      induction l0.
      - simpl in H7. rewrite nth_error_empty in H7. discriminate H7.
      - simpl in H7. invert H10. invert H1. destruct xs; [|discriminate H3].
        simpl in H7. auto. }
    eassert (nth_error _ _ = Some _) as H''. 2: erewrite H' in H''; cycle 1.
    { rewrite <- H7. f_equal. rewrite Div.div_mod_eq. 1: reflexivity. lia. }
    { apply Z_div_nonneg_nonneg; lia. }
    { apply nth_error_Some in H''. erewrite length_flatten_result in H''.
      2: { constructor; [reflexivity|eassumption]. }
      assert (0 <= x / Z.of_nat m)%Z.
      { apply Z_div_nonneg_nonneg; lia. }
      assert (0 <= x mod Z.of_nat m)%Z.
      { apply mod_nonneg. lia. }
      assert (H''': Z.to_nat (x / Z.of_nat m * Z.of_nat m) < (length l0) * m) by lia.
      clear H''.
      rewrite Z2Nat.inj_mul in H''' by lia.
      rewrite Z2Nat.inj_div in H''' by lia.
      replace (Z.to_nat (Z.of_nat m)) with m in H''' by lia.
      rewrite <- Nat.mul_lt_mono_pos_r in H''' by lia.
      rewrite Z2Nat.inj_lt by lia. rewrite Z2Nat.inj_div by lia.
      do 2 rewrite Nat2Z.id. assumption. }
    { apply mod_nonneg. lia. }
    { apply Div.mod_upper_bound. lia. }
    destruct (nth_error l0 _) eqn:E0; [|discriminate H''].
    destruct r; [discriminate H''|].
    econstructor.
    { apply Exists_app. left. apply Exists_app. right. apply Exists_cons_hd. simpl.
      pose proof size_of_sizeof as H'''. specialize (H''' _ _ ltac:(eassumption)).
      rewrite H'''. simpl. replace (length sh0 - 0) with (length sh0) by lia. clear H'.
      eset (ctx' := map.put
                      (map.put (map.putmany (context_of v) (idx_map (map Zobj xs)))
                         (inr (length sh0)) (Zobj _))
                      (inr (S (length sh0))) (Robj _)).
      eapply normal_rule_impl with (ctx := ctx'); interp_exprs. }
    simpl. constructor; [|solve[constructor]].
    eapply prog_impl_fact_subset.
    2: { move IHe at bottom. eset (idxs := _ :: _ :: _: list Z).
         specialize IHe with (name := S name) (idxs := idxs). subst idxs. simpl in IHe.
         eapply IHe; eauto. econstructor.
         { apply Z_div_nonneg_nonneg; lia. }
         { eassumption. }
         econstructor.
         { apply mod_nonneg. lia. }
         { eassumption. }
         eassumption. }
    intros. rewrite E in *. repeat rewrite in_app_iff in *. tauto.
  - simpl. intros. invert H. invert H0. destr_lower.
    rename H6 into Hk. apply eval_Zexpr_Z_eval_Zexpr in Hk.
    cbv [eval_Zexpr_Z_total] in *. rewrite Hk in *. invert_list_stuff.
    pose proof ResultToArrayDelta.size_of_eval_expr_result_has_shape as He.
    specialize (He _ _  ltac:(eassumption) _ _ _ _ ltac:(eassumption)).
    simpl in He.
    pose proof nth_error_split_result' as H'.
    pose proof dimensions_right as Hd1.
    pose proof dim_idxs as Hd2.
    specialize (Hd1 _ _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    simpl in Hd1. invert Hd1.
    specialize Hd2 with (2 := H3). eassert _ as blah.
    2: epose proof (Hd2 _ blah) as Hd3; clear blah Hd2.
    { constructor. apply dim_split_result. eassumption. }
    cbv [eval_Zexpr_Z_total].
    set (k' := Z.to_nat kz).
    replace (Z.to_nat kz) with k' in * by (subst k'; reflexivity).
    pose proof result_has_shape_split_result as Hssr. specialize Hssr with (2 := He).
    specialize (Hssr k' ltac:(lia)). rewrite <- result_has_shape'_iff in Hssr.
    invert Hssr.
    rewrite <- result_has_shape'_iff in He. invert He. invert H3.
    simpl in Hd3. invert Hd3. destruct xs as [|x0 xs]; [discriminate H3|].
    simpl in H3. invert H3. invert H15.
    specialize (H' l0 k' (Z.to_nat x * k' + Z.to_nat x0) ltac:(lia)).
    assert (Hx0: Z.to_nat x0 < k').
    { apply nth_error_Some in H17. apply nth_error_In in H6.
      rewrite Forall_forall in H10. apply H10 in H6. invert H6. lia. }
    rewrite Nat.div_add_l in H' by lia.
    rewrite Nat.div_small in H' by lia.
    replace (Z.to_nat x + 0) with (Z.to_nat x) in H' by lia.
    rewrite H6 in H'. rewrite Nat.Div0.add_mod in H' by lia.
    rewrite Nat.Div0.mod_mul in H' by lia. simpl in H'.
    rewrite Nat.Div0.mod_mod in H' by lia.
    rewrite Nat.mod_small in H' by lia.
    destruct H' as [(H'&H'')|(H'&H''&H''')].
    + econstructor.
      { apply Exists_app. left. apply Exists_app. right. apply Exists_cons_hd. simpl.
        pose proof size_of_sizeof as H'''. specialize (H''' _ _ ltac:(eassumption)).
        rewrite H'''. simpl. replace (length sh0 - 0) with (length sh0) by lia. clear H'.
        eset (ctx' := map.put
                        (map.put
                           (map.put
                              (map.putmany (context_of v) (idx_map (map Zobj xs)))
                              (inr (length sh0)) (Zobj _))
                           (inr (S (length sh0))) (Zobj _))
                        (inr (S (S (length sh0)))) (Robj _)).
        eapply normal_rule_impl with (ctx := ctx'); interp_exprs. }
      simpl. constructor.
      { eapply prog_impl_fact_subset.
        2: { move IHe at bottom. eset (idxs := _ :: _: list Z).
             specialize IHe with (name := S name) (idxs := idxs). subst idxs. simpl in IHe.
             eapply IHe; eauto. econstructor.
           { lia. }
           { eassert (Z.to_nat _ = _) as ->. 2: rewrite <- H''.
             { lia. }
             eassumption. }
           eassumption. }
        intros. rewrite E in *. repeat rewrite in_app_iff in *. tauto. }
      constructor; [|solve[constructor]]. econstructor.
      { apply Exists_app. right. apply Exists_app. right. apply Exists_cons_hd.
        eapply normal_rule_impl; [|solve[constructor]]. apply Exists_cons_hd. interp_exprs.
        simpl. f_equal. f_equal. remember (Z.of_nat _) as y.
        destr (x =? y / Z.of_nat k')%Z; destr (y mod Z.of_nat k' <=? x0)%Z; try reflexivity.
        subst. clear -H' E0.
        remember (length l0) as n' eqn:E. clear E. clearbody k'.
        pose proof (Nat.div_mod_eq n' k'). rewrite Z2Nat.inj_div in * by lia.
        repeat rewrite Nat2Z.id in *.
        enough (n' mod k' <= Z.to_nat x0) by lia. clear -E0.
        rewrite <- Nat2Z.inj_mod in E0. lia. }
      constructor.
    + rewrite H''' in H17. invert H17.
      pose proof pad_lookup_SX as H''''.
      specialize (H'''' _ _ _  ltac:(eassumption)). subst.
      econstructor.
      { apply Exists_app. left. apply Exists_app. right. apply Exists_cons_tl.
        apply Exists_cons_hd. simpl.
        pose proof size_of_sizeof as H''''. specialize (H'''' _ _ ltac:(eassumption)).
        rewrite H''''. simpl. replace (length sh0 - 0) with (length sh0) by lia.
        eset (ctx' := map.put
                     (map.putmany (context_of v) (idx_map (map Zobj xs)))
                     (inr (length sh0)) (Zobj _)).
        eapply normal_rule_impl with (ctx := ctx'); interp_exprs.
        simpl. f_equal. f_equal. rewrite <- Nat2Z.inj_div. lia. }
      constructor; [|solve[constructor]].
      econstructor.
      { apply Exists_app. right. apply Exists_app. right. apply Exists_cons_hd.
        simpl. eapply normal_rule_impl with (ctx := map.empty); [|solve[constructor]].
        repeat econstructor. simpl. f_equal. f_equal. symmetry. apply Z.leb_le.
        move H' at bottom. move H'' at bottom.
        rewrite H'' in H'.
        remember (length l0 / k') as blah. rewrite (Nat.div_mod_eq (length l0) k') in H'.
        subst. rewrite Nat.mul_comm in H'.
        assert (H'''': length l0 mod k' <= Z.to_nat x0) by lia. clear H'.
        rewrite <- Nat2Z.inj_mod. lia. }
      constructor.
  - simpl. intros. invert H. invert H0. destr_lower.
    pose proof ResultToArrayDelta.size_of_eval_expr_result_has_shape as He.
    specialize (He _ _ ltac:(eassumption) _ _ _ _ ltac:(eassumption)).
    simpl in He.
    pose proof dimensions_right as Hd1.
    specialize (Hd1 _ _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    pose proof dim_idxs as Hd2.
    eq_size_of. invert_list_stuff.
    pose proof size_of_sizeof as H9'. specialize H9' with (1 := H9).
    specialize Hd2 with (2 := H3). eassert _ as blah.
    2: epose proof (Hd2 _ blah) as Hd3; clear blah Hd2.
    { simpl. apply dim_transpose_result.
      - simpl. reflexivity.
      - simpl. assumption. }
    destruct idxs as [ | x [|x0 idxs] ]; [discriminate Hd3|discriminate Hd3|].
    simpl in Hd3. invert Hd3.
    econstructor.
    { apply Exists_app. left. apply Exists_app. right. apply Exists_cons_hd. simpl.
      rewrite H9'. simpl. replace (length sh0 - 0) with (length sh0) by lia. clear H9.
      rewrite <- H0.
      eset (ctx' := map.put
                      (map.put
                         (map.put (map.putmany (context_of v) (idx_map (map Zobj idxs)))
                            (inr (S (length idxs))) (Zobj _))
                         (inr (S (S (length idxs)))) (Zobj _))
                      (inr (S (S (S (length idxs))))) (Robj _)).
      eapply normal_rule_impl with (ctx := ctx'); interp_exprs. }
    simpl. constructor; [|solve[constructor]].
    eapply prog_impl_fact_subset.
    2: { move IHe at bottom. eset (idxs0 := _ :: _ :: _ : list Z).
         specialize IHe with (name := S name) (idxs := idxs0). subst idxs0.
         eapply IHe; eauto. eapply result_lookup_Z'_transpose; eassumption. }
    intros. rewrite E in *. repeat rewrite in_app_iff in *. tauto.
  - intros. invert H. invert H0. simpl in H1. simpl. eapply IHe; eauto.
    move H3 at bottom. invert H3. rewrite nth_error_truncr in H5.
    2: { apply nth_error_Some in H5. rewrite length_rev in H5.
         rewrite length_truncl_list in H5. rewrite length_rev in H5. lia. }
    econstructor; eassumption.
  - simpl. intros. invert H. invert H0. destr_lower. simpl in H1.
    rename H6 into Hk. pose proof Hk as Hk'.
    eapply eval_Zexpr_includes_valuation in Hk'; [|apply empty_includes].
    apply eval_Zexpr_Z_eval_Zexpr in Hk'. rewrite Hk' in *. invert_list_stuff.
    apply eval_Zexpr_Z_eval_Zexpr in Hk.
    cbv [eval_Zexpr_Z_total] in *. rewrite Hk in *.
    invert H3. rewrite nth_error_truncl in H5.
    pose proof ResultToArrayDelta.size_of_eval_expr_result_has_shape as He.
    specialize (He _ _ ltac:(eassumption) _ _ _ _ ltac:(eassumption)).
    simpl in He.
    pose proof dimensions_right as Hd1.
    specialize (Hd1 _ _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    pose proof dim_idxs as Hd2. pose proof size_of_sizeof as H8'.
    specialize (H8' _ _ ltac:(eassumption)).
    specialize Hd2 with (2 := H7). eassert _ as blah.
    2: epose proof (Hd2 _ blah) as Hd3; clear blah Hd2.
    { simpl. apply nth_error_In in H5. invert Hd1. rewrite Forall_forall in H6.
      apply H6 in H5. eassumption. }
    rewrite H8'. simpl. replace (length sh0 - 0) with (length sh0) by lia.
    rewrite <- Hd3 in *. clear Hd3 Hd1.
    econstructor.
    { apply Exists_app. left. apply Exists_app. right. apply Exists_cons_hd.
      eset (ctx' := map.put
                   (map.put (map.putmany (context_of v) (idx_map (map Zobj xs)))
                      (inr (length xs)) (Zobj _))
                   (inr (S (length xs))) (Robj _)).
      eapply normal_rule_impl with (ctx := ctx'); interp_exprs. }
    constructor; [|solve[constructor]]. simpl.
    eapply prog_impl_fact_subset.
    2: { move IHe at bottom. eset (idxs0 := _ :: _ : list Z).
         specialize IHe with (name := S name) (idxs := idxs0). subst idxs0.
         eapply IHe; eauto. econstructor; eauto.
         { lia. }
         rewrite <- H5. f_equal. lia. }
    intros. rewrite E in *. repeat rewrite in_app_iff in *. tauto.
  - simpl. intros. invert H. invert H0. destr_lower. simpl in H1.
    rename H6 into Hk. pose proof Hk as Hk'.
    eapply eval_Zexpr_includes_valuation in Hk'; [|apply empty_includes].
    apply eval_Zexpr_Z_eval_Zexpr in Hk'. rewrite Hk' in *. invert_list_stuff.
    pose proof ResultToArrayDelta.size_of_eval_expr_result_has_shape as He.
    eq_size_of. invert_list_stuff.
    specialize (He _ _ ltac:(eassumption) _ _ _ _ ltac:(eassumption)).
    simpl in He.
    pose proof dimensions_right as Hd1.
    specialize (Hd1 _ _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    pose proof dim_idxs as Hd2. pose proof size_of_sizeof as H8'.
    specialize (H8' _ _ ltac:(eassumption)).
    invert H3.
    specialize Hd2 with (2 := H7). eassert _ as blah.
    2: epose proof (Hd2 _ blah) as Hd3; clear blah Hd2.
    { simpl. apply nth_error_In in H5. invert Hd1. rewrite Forall_forall in H6.
      apply in_app_iff in H5. destruct H5 as [H5|H5].
      2: { apply repeat_spec in H5. subst. apply dim_gen_pad. }
      auto. }
    rewrite H8'. simpl. replace (length sh0 - 0) with (length sh0) by lia.
    rewrite <- Hd3 in *. clear Hd3 Hd1.
    assert (Hx: Z.to_nat x < length l0 \/ length l0 <= Z.to_nat x) by lia.
    destruct Hx as [Hx|Hx].
    + rewrite nth_error_app1 in H5 by lia. econstructor.
      { apply Exists_app. left. apply Exists_app. right. apply Exists_cons_hd. simpl.
        eset (ctx' := map.put
                        (map.put
                           (map.putmany (context_of v) (idx_map (map Zobj xs)))
                           (inr (length xs)) (Zobj _))
                        (inr (S (length xs))) (Robj _)).
        eapply normal_rule_impl with (ctx := ctx'); interp_exprs. }
      constructor.
      { eapply prog_impl_fact_subset.
        2: { move IHe at bottom. eset (idxs0 := _ :: _ : list Z).
             specialize IHe with (name := S name) (idxs := idxs0). subst idxs0.
             eapply IHe; eauto. econstructor; eauto. }
        simpl. intros. rewrite E in *. repeat rewrite in_app_iff in *. tauto. }
      constructor; [|solve[constructor]]. econstructor.
      { apply Exists_app. right. apply Exists_app. right. apply Exists_cons_hd.
        eapply normal_rule_impl; [|solve[constructor]]. apply Exists_cons_hd. interp_exprs.
        simpl. f_equal. f_equal. remember (Z.of_nat _) as y.
        destr (x <? y)%Z; try reflexivity. apply nth_error_Some in H5.
        rewrite <- result_has_shape'_iff in He. invert He. lia. }
      constructor.
    + rewrite nth_error_app2 in H5 by lia. apply nth_error_In, repeat_spec in H5.
      subst. apply pad_lookup_SX in H7. subst.
      econstructor.
      { apply Exists_app. left. apply Exists_app. right. apply Exists_cons_tl.
        apply Exists_cons_hd. simpl.
        eset (ctx' := map.put (map.putmany (context_of v) (idx_map (map Zobj xs)))
                       (inr (length xs)) (Zobj _)).
        eapply normal_rule_impl with (ctx := ctx'); interp_exprs. }
      constructor; [|solve[constructor]]. simpl.
      econstructor.
      { apply Exists_app. right. apply Exists_app. right. apply Exists_cons_hd.
        simpl. eapply normal_rule_impl with (ctx := map.empty); interp_exprs.
        simpl. f_equal. f_equal.
        rewrite <- result_has_shape'_iff in He. invert He.
        symmetry. apply Z.leb_le. lia. }
      constructor.
  - simpl. intros. invert H. invert H0. destr_lower. simpl in H1.
    rename H6 into Hk. pose proof Hk as Hk'.
    eapply eval_Zexpr_includes_valuation in Hk'; [|apply empty_includes].
    apply eval_Zexpr_Z_eval_Zexpr in Hk'. rewrite Hk' in *. invert_list_stuff.
    apply eval_Zexpr_Z_eval_Zexpr in Hk.
    cbv [eval_Zexpr_Z_total] in *. rewrite Hk in *.
    invert H3. eq_size_of. invert_list_stuff.
    pose proof ResultToArrayDelta.size_of_eval_expr_result_has_shape as He.
    specialize (He _ _ ltac:(eassumption) _ _ _ _ ltac:(eassumption)).
    simpl in He.
    pose proof dimensions_right as Hd1.
    specialize (Hd1 _ _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    pose proof dim_idxs as Hd2. pose proof size_of_sizeof as H8'.
    specialize (H8' _ _ ltac:(eassumption)).
    specialize Hd2 with (2 := H7). eassert _ as blah.
    2: epose proof (Hd2 _ blah) as Hd3; clear blah Hd2.
    { simpl. apply nth_error_In in H5. invert Hd1. rewrite Forall_forall in H6.
      apply in_app_iff in H5. destruct H5 as [H5|H5].
      { apply repeat_spec in H5. subst. apply dim_gen_pad. }
      auto. }
    rewrite H8'. simpl. replace (length sh0 - 0) with (length sh0) by lia.
    rewrite <- Hd3 in *. clear Hd3 Hd1.
    set (k' := Z.to_nat kz).
    replace (Z.to_nat kz) with k' in * by reflexivity.
    assert (Hx: Z.to_nat x < k' \/ k' <= Z.to_nat x) by lia.
    destruct Hx as [Hx|Hx].
    + rewrite nth_error_app1 in H5 by (rewrite repeat_length; lia).
      apply nth_error_In, repeat_spec in H5.
      subst. apply pad_lookup_SX in H7. subst.
      econstructor.
      { apply Exists_app. left. apply Exists_app. right. apply Exists_cons_tl.
        apply Exists_cons_hd. simpl.
        eset (ctx' := map.put
                        (map.putmany (context_of v) (idx_map (map Zobj xs)))
                        (inr (length xs)) (Zobj _)).
        eapply normal_rule_impl with (ctx := ctx'); interp_exprs. }
      constructor; [|solve[constructor]]. simpl.
      econstructor.
      { apply Exists_app. right. apply Exists_app. right. apply Exists_cons_hd.
        simpl. eapply normal_rule_impl with (ctx := map.empty); interp_exprs.
        simpl. f_equal. f_equal. symmetry. apply Z.ltb_lt. lia. }
      constructor.
    + rewrite nth_error_app2 in H5 by (rewrite repeat_length; lia). econstructor.
      { apply Exists_app. left. apply Exists_app. right. apply Exists_cons_hd. simpl.
        eset (ctx' := map.put
                        (map.put (map.putmany (context_of v) (idx_map (map Zobj xs)))
                           (inr (length xs)) (Zobj _))
                        (inr (S (length xs))) (Robj _)).
        eapply normal_rule_impl with (ctx := ctx'); interp_exprs. }
      constructor.
      { eapply prog_impl_fact_subset.
        2: { move IHe at bottom. eset (idxs0 := _ :: _ : list Z).
             specialize IHe with (name := S name) (idxs := idxs0). subst idxs0.
             eapply IHe; eauto. econstructor; eauto. 1: lia. rewrite <- H5.
             rewrite repeat_length. f_equal. lia.
        }
        simpl. intros. rewrite E in *. repeat rewrite in_app_iff in *. tauto. }
      constructor; [|solve[constructor]]. econstructor.
      { apply Exists_app. right. apply Exists_app. right. apply Exists_cons_hd.
        eapply normal_rule_impl; [|solve[constructor]]. apply Exists_cons_hd. interp_exprs.
        simpl. f_equal. f_equal. remember (Z.of_nat _) as y.
        destr (x <? y)%Z; destr (y <=? x)%Z; reflexivity || lia. }
      constructor.
  - intros. simpl. destruct (lower_Sexpr _ _ O s) as [ [val0 hyps] name'] eqn:E.
    simpl. invert H. pose proof lower_Sexpr_correct as H'.
    specialize H' with (1 := H4) (3 := H8) (4 := E).
    epose proof (H' _) as H'. specialize' H'.
    { intros. specialize (H2 _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
      fwd. eauto. }
    destruct H' as (hyps'&substn&_&Hsubstn&Hhyps&Hhyps'&Hval0).
    invert H3. econstructor.
    { constructor. simpl. set (ctx' := map.putmany substn (context_of v)).
      rewrite app_nil_r. eapply normal_rule_impl with (ctx := ctx'); interp_exprs. }
    eapply Forall_impl; [|eassumption]. intros.
    eapply prog_impl_fact_subset.
    2: eassumption.
    simpl. intros. rewrite in_app_iff. tauto.
    Unshelve. (*why*) all: exact map.empty.
Qed.

Lemma lower_complete out e r l :
  eval_expr $0 $0 $0 e r ->
  size_of e l ->
  gen_lbs_zero e ->
  forall (idxs : list Z) (val : scalar_result),
    result_lookup_Z' idxs r val ->
    prog_impl_fact (lower e out) (str_rel out, Robj (toR val) :: map Zobj idxs).
Proof.
  intros. pose proof lower_rec_complete as H'.
  specialize H' with (idx_ctx' := nil) (datalog_ctx := nil) (v := map.empty).
  simpl in H'. eapply H'; eauto.
  - rewrite fmap_of_empty. eassumption.
  - clear. intros * H. rewrite lookup_empty in H. discriminate H.
Qed.

Lemma lower_correct out e r l :
  eval_expr $0 $0 $0 e r ->
  size_of e l ->
  vars_good [] e ->
  gen_lbs_zero e ->
  ~ out \in vars_of e \cup referenced_vars e ->
  forall idxs val,
    result_lookup_Z' idxs r val ->
    (forall val',
         val' = Robj (toR val) <->
          prog_impl_fact (lower e out) (str_rel out, val' :: map Zobj idxs)).
Proof.
  intros H1 H2 H3 H5 H6 idxs val H4 val'.
  split; intros H; subst; eauto using lower_complete.
  eapply lower_complete in H4; eauto. eapply lower_functional in H; auto.
  specialize (H H4). simpl in H. specialize (H eq_refl). invert H. reflexivity.
Qed.
End __.
