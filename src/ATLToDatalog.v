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

Import ListNotations.
From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics.
From Lower Require Import Zexpr Bexpr Array Range Sexpr Result ListMisc
  Meshgrid VarGeneration Injective Constant InterpretReindexer
  WellFormedEnvironment.

Require Import ATLDeep.
Require Import ContextsAgree.
Require Import Datalog.Datalog.
Open Scope string_scope.

From Coq Require Import Arith.PeanoNat. Import Nat. Check S.
Import Datatypes. Check S.

Inductive result_has_shape' : list nat -> result -> Prop :=
| ScalarShape' s : result_has_shape' [] (Result.S s)
| VectorShape' xs n sh :
  n = length xs ->
  Forall (result_has_shape' sh) xs ->
  result_has_shape' (n :: sh) (V xs).

Lemma result_has_shape'_iff r sh :
  result_has_shape' sh r <-> result_has_shape r sh.
Proof.
  revert sh. induction r.
  - intros sh. split; intros H; invert H; constructor.
  - intros sh. split; intros H'; invert H'.
    + destruct v.
      -- constructor.
      -- invert H3. invert H. simpl. constructor; auto. 1: apply H3; assumption.
         eapply Forall_impl. 2: apply Forall_and; [apply H4|apply H5]. simpl.
         intros ? (?&H'). edestruct H'. eauto.
    + constructor; auto.
    + constructor; auto. invert H. constructor. 1: apply H4; assumption.
      eapply Forall_impl. 2: apply Forall_and; [apply H3|apply H5]. simpl.
      intros ? (?&H'). edestruct H'. eauto.
Qed.

Definition get_inl {X Y : Type} (xy : X + Y) : option X :=
  match xy with
  | inl x => Some x
  | inr _ => None
  end.
Definition get_inr {X Y : Type} (xy : X + Y) : option Y :=
  match xy with
  | inl _ => None
  | inr y => Some y
  end.
Print Bexpr.

Variant obj : Set :=
  Bobj : bool -> obj | Zobj : Z -> obj | Robj : R -> obj.

(*just like Bexpr, except i added blit*)
Variant Bfn : Set :=
  fn_BAnd | fn_BLt | fn_BLe | fn_BEq | fn_BLit (_ : bool).

Definition interp_Bfn (f : Bfn) (l : list obj) : option bool :=
  match f, l with
  | fn_BAnd, [Bobj x; Bobj y] => Some (x && y)
  | fn_BLt, [Zobj x; Zobj y] => Some (x <? y)
  | fn_BLe, [Zobj x; Zobj y] => Some (x <=? y)
  | fn_BEq, [Zobj x; Zobj y] => Some (x =? y)
  | fn_BLit b, [] => Some b
  | _, _ => None
  end%Z.
(*just like Zexpr but no ZVar*)
Variant Zfn : Set :=
  fn_ZPlus | fn_ZMinus | fn_ZTimes | fn_ZDivf | fn_ZDivc | fn_ZMod | fn_Zmax(*i added this to make writing the compiler convenient*) | fn_ZLit (x : Z).
Definition interp_Zfn (f : Zfn) (l : list obj) : option Z :=
  match f, l with
  | fn_ZPlus, [Zobj x; Zobj y] => Some (x + y)
  | fn_ZMinus, [Zobj x; Zobj y] => Some (x - y)
  | fn_ZTimes, [Zobj x; Zobj y] => Some (x * y)
  | fn_ZDivf, [Zobj x; Zobj y] => Some (x / y)
  | fn_ZDivc, [Zobj x; Zobj y] => Some (x // y)
  | fn_ZMod, [Zobj x; Zobj y] => Some (x mod y)
  | fn_Zmax, [Zobj x; Zobj y] => Some (Z.max x y)
  | fn_ZLit x, [] => Some x
  | _, _ => None
  end%Z.
(*just like Sstmt but no SVar, SGet*)
Variant Rfn : Set :=
  fn_SMul | fn_SAdd | fn_SDiv | fn_SSub | fn_SLit (x : R).

Definition interp_Rfn (f : Rfn) (l : list obj) : option R :=
  match f, l with
  | fn_SMul, [Robj x; Robj y] => Some (x * y)
  | fn_SAdd, [Robj x; Robj y] => Some (x + y)
  | fn_SDiv, [Robj x; Robj y] => Some (x / y)
  | fn_SSub, [Robj x; Robj y] => Some (x - y)
  | fn_SLit x, [] => Some (x)
  | _, _ => None
  end%R.

Variant fn : Set :=
  fn_B (_ : Bfn) | fn_Z (_ : Zfn) | fn_R (_ : Rfn).

Definition interp_fn (f : fn) (l : list obj) : option obj :=
  match f with
  | fn_B f => option_map Bobj (interp_Bfn f l)
  | fn_Z f => option_map Zobj (interp_Zfn f l)
  | fn_R f => option_map Robj (interp_Rfn f l)
  end.

Variant rel : Set :=
  | str_rel (s : string)
  | nat_rel (n : nat)
  | true_rel (*unary, true if arg is true*)
  | false_rel.

Definition var : Set := string + nat.

Search Sstmt. Print eval_Sstmt. Print context. Print fmap. Check Build_rule. Check Build_fact.

Fixpoint lower_idx (idx: Zexpr) : expr var fn :=
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

Print Bexpr.
Fixpoint lower_guard (g: Bexpr) : expr var fn :=
  match g with
  | Bexpr.And x y => fun_expr (fn_B fn_BAnd) [lower_guard x; lower_guard y]
  | Bexpr.Lt x y => fun_expr (fn_B fn_BLt) [lower_idx x; lower_idx y]
  | Bexpr.Le x y => fun_expr (fn_B fn_BLe) [lower_idx x; lower_idx y]
  | Bexpr.Eq x y => fun_expr (fn_B fn_BEq) [lower_idx x; lower_idx y]
  end.

Print Sexpr.
Fixpoint lower_Sexpr (next_varname : nat) (e : Sexpr) :
  expr var fn (*value of expr*) *
    list (fact rel var fn) (*hypotheses*) *
    nat (*next varname *) :=
  match e with
  | Var x => (var_expr (inr next_varname),
              [{| fact_R := str_rel x; fact_args := [var_expr (inr next_varname)] |}],
              succ next_varname)
  | Get x idxs => (var_expr (inr next_varname),
                   [{| fact_R := str_rel x; fact_args := var_expr (inr next_varname) :: map lower_idx idxs |}],
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

Definition map_empty : var -> option fn := fun _ => None.

Definition var_eqb (x y : var) : bool :=
  match x, y with
  | inl x, inl y => x =? y
  | inr x, inr y => Nat.eqb x y
  | _, _ => false
  end.
Lemma var_eqb_refl x :
  var_eqb x x = true.
Proof.
  destruct x; simpl.
  - apply String.eqb_refl.
  - apply Nat.eqb_refl.
Qed.

Lemma var_eqb_eq x y :
  var_eqb x y = true ->
  x = y.
Proof.
  cbv [var_eqb]. intros H. destruct x, y; try congruence; f_equal.
  - apply String.eqb_eq in H. auto.
  - apply Nat.eqb_eq in H. auto.
Qed.
  
Definition map_cons (x : var) (y : option fn) (m : var -> option fn) :=
  fun v => if var_eqb x v then y else m v.
Search (scalar_result -> R).
Definition toR (s : scalar_result) :=
  match s with
  | SS s => s
  | SX => 0%R
  end.
  

Search (list Z). Search "shape".
Print sizeof. Print rule. Print fact. Print eval_expr. Print fact. Print Rfn. Print Zexpr. Print rule.  Print lower. Print size_of. Search constant_nonneg_bounds.
Fixpoint lower
  (e : ATLexpr)
  (out: rel)
  (name: nat)
  (*i don't use the bounds at all (yet)*)
  (idxs_bds : list (Zexpr * Zexpr))
  : list (rule rel var fn) :=
  match e with
  | Gen i lo hi body =>
      lower body out name (idxs_bds ++ [(ZMinus (ZVar i) lo, ZMinus hi lo)])
  | Sum i lo hi body =>
      let dimvars := map inr (seq O (length (sizeof body))) in
      let x := length (sizeof body) in
      let i' := Datatypes.S x in
      let y := Datatypes.S i' in
      let aux := name in
      let aux' := Datatypes.S aux in
      (*set aux(body(i), i, ...)*)
      lower body (nat_rel aux) (Datatypes.S aux') [(ZVar i, ZMinus hi lo)] ++
        [(*set aux'(O, lo, ...)*)
          {| rule_hyps := [];
            rule_concl := {| fact_R := nat_rel aux';
                            fact_args := [fun_expr (fn_R (fn_SLit 0%R)) [];
                                          lower_idx lo] ++
                                          map var_expr dimvars(*arbitrary index into summand*) |} |};
          (*set aux' (body(i) + \sum_{j < i} body(j), S i, ...)*)
          {| rule_hyps := [{| fact_R := nat_rel aux';
                             fact_args :=
                               [var_expr (inr x)(*\sum_{j < i} body(j)*);
                                var_expr (inr i') (*index into aux'*)] ++
                                map var_expr dimvars(*arbitrary idx into summand*) |};
                           {| fact_R := nat_rel aux;
                             fact_args :=
                               [var_expr (inr y)(*body(i)*);
                                var_expr (inr i') (*index into aux*)] ++
                                map var_expr dimvars (*arbitrary idx into summand*) |}];
            rule_concl := {| fact_R := nat_rel aux';
                            fact_args :=
                              [fun_expr (fn_R fn_SAdd) [var_expr (inr y);
                                                        var_expr (inr x)];
                               fun_expr (fn_Z fn_ZPlus) [var_expr (inr i');
                                                        fun_expr (fn_Z (fn_ZLit 1%Z)) []]] ++
                               map var_expr dimvars (*arbitrary idx into accumulated sum*) |} |};
          (*set out (\sum_j body(j), idxs)*)
          {| rule_hyps := [{| fact_R := (nat_rel aux');
                             fact_args :=
                               [var_expr (inr x)(*\sum_j body(j)*);
                                (*basically the next arg should just be hi, except i am dealing with the dumb case where hi < lo*)
                                fun_expr (fn_Z fn_Zmax) [lower_idx lo; lower_idx hi]] ++
                                map var_expr dimvars(*arbitrary idx into sum*) |}];
            rule_concl := {| fact_R := out;
                            fact_args :=
                              var_expr (inr x) ::
                                map lower_idx (map fst idxs_bds) ++
                                map var_expr dimvars(*arbitrary idx into sum*) |} |}]
  | Guard b body =>
      let dimvars := map inr (seq O (length (sizeof body))) in
      let x := length (sizeof body) in
      let aux := name in
      lower body (nat_rel aux) (S aux) [] ++
        [{| rule_concl := {| fact_R := out;
                            fact_args :=
                              var_expr (inr x) ::
                                map lower_idx (map fst idxs_bds) ++
                                map var_expr dimvars |};
           rule_hyps := [{| fact_R := nat_rel aux;
                           fact_args :=
                             var_expr (inr x) ::
                               map var_expr dimvars |};
                         {| fact_R := true_rel;
                           fact_args := [lower_guard b] |}] |};
         {| rule_concl := {| fact_R := out;
                            fact_args :=
                              fun_expr (fn_R (fn_SLit 0%R)) [] ::
                                map lower_idx (map fst idxs_bds) ++       
                                map var_expr dimvars |};
           rule_hyps := [{| fact_R := false_rel;
                           fact_args := [lower_guard b] |}] |}
        ]
  | Lbind x e1 e2 =>
      (*will eventually have to do better with name generation here..*)
      lower e1 (str_rel x) name [] ++ lower e2 out name idxs_bds
  | Concat e1 e2 =>
      (*should have length (sizeof e1) = length (sizeof e2)*)
      let dimvarO := inr O in
      let dimvars := map inr (seq 1 (length (sizeof e1) - 1)) in
      let x := length (sizeof e1) in
      let aux1 := name in
      let aux2 := S name in
      (*here is the first place i use the const_nonneg_bounds hypothesis*)
      let len1 := Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 (match sizeof e1 with
                  | [] => (| 0 |)%z
                  | n :: _ => n
                  end))) in
  (*need better names here..*)
      lower e1 (nat_rel aux1) (S (S name)) [] ++
        lower e2 (nat_rel aux2) (S (S name)) [] ++
        [{| rule_concl := {| fact_R := out;
                            fact_args :=
                              var_expr (inr x) ::
                                map lower_idx (map fst idxs_bds) ++
                                map var_expr (dimvarO :: dimvars) |};
           rule_hyps := [{| fact_R := nat_rel aux1;
                           fact_args :=
                             var_expr (inr x) ::
                               map var_expr (dimvarO :: dimvars) |}] |};
         {| rule_concl := {| fact_R := out;
                            fact_args :=
                              var_expr (inr x) ::
                                map lower_idx (map fst idxs_bds) ++
                                fun_expr (fn_Z fn_ZPlus)
                                [var_expr dimvarO;
                                 fun_expr (fn_Z (fn_ZLit len1)) []] ::
                                map var_expr dimvars |};
           rule_hyps := [{| fact_R := nat_rel aux2;
                           fact_args :=
                             var_expr (inr x) ::
                               map var_expr (dimvarO :: dimvars) |} ] |} ]
  | Flatten e =>
      let dimvars := map inr (seq O (length (sizeof e) - 2)) in
      let dimvar1 := inr (length (sizeof e) - 2) in
      let dimvar2 := inr (length (sizeof e) - 1) in
      let x := inr (length (sizeof e)) in
      let len2 := 
        match sizeof e with
        | _ :: di :: _ => Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 di))
        | _ => 0%Z
        end in
      let aux := name in
      lower e (nat_rel aux) (S aux) [] ++
        [{| rule_concl := {| fact_R := out;
                            fact_args :=
                              var_expr x ::
                                map lower_idx (map fst idxs_bds) ++
                                fun_expr
                                (fn_Z fn_ZPlus)
                                [fun_expr (fn_Z fn_ZTimes)
                                   [var_expr dimvar1;
                                    fun_expr (fn_Z (fn_ZLit len2)) []];
                                 var_expr dimvar2] :: map var_expr dimvars |};
           rule_hyps := [{| fact_R := nat_rel aux;
                           fact_args := var_expr x ::
                                          var_expr dimvar1 ::
                                          var_expr dimvar2 ::
                                          map var_expr dimvars |}] |}]
  | Scalar s =>
      let '(val, hyps, _) := lower_Sexpr O s in
      [{| rule_hyps := hyps; rule_concl := {| fact_R := out; fact_args := val :: map lower_idx (map fst idxs_bds) |} |}]
  | _ => nil end.

(*I thought about using fmaps here, but it's not even clear to me that that is possible.
  How do you iterate over an fmap?  i could get the domain, which is a 'set', but idk
  how to iterate over a set, either...*)
Definition substn_of (v : valuation) : var -> option fn :=
  fun x => match x with
        | inl x => option_map (fun y => fn_Z (fn_ZLit y)) (v $? x)
        | inr x => None
        end.

Lemma includes_extends v1 v2 : v1 $<= v2 -> extends (substn_of v2) (substn_of v1).
Proof.
  intros H. cbv [extends substn_of]. intros x y Hxy. destruct x; [|congruence].
  destruct (v1 $? s) eqn:E; simpl in Hxy; [|congruence].
  eapply includes_lookup in E; try eassumption. rewrite E. assumption.
Qed.

Lemma eval_Zexpr_to_substn v x z :
  eval_Zexpr v x z ->
  interp_expr interp_fn (subst_in_expr (substn_of v) (lower_idx x)) (Zobj z).
Proof.
  intros H. induction H; simpl; repeat match goal with | H: _ = Some _ |- _ => rewrite H end; econstructor; eauto.
Qed.

Lemma eval_Bexpr_to_substn v x b :
  eval_Bexpr v x b ->
  interp_expr interp_fn (subst_in_expr (substn_of v) (lower_guard x)) (Bobj b).
Proof.
  intros H. induction H; simpl; repeat match goal with | H: _ = Some _ |- _ => rewrite H end; econstructor; eauto using eval_Zexpr_to_substn.
Qed.

Lemma eval_Zexprlist_to_substn v i lz :
  eval_Zexprlist v i lz ->
  Forall2 (interp_expr interp_fn) (map (subst_in_expr (substn_of v)) (map lower_idx i)) (map Zobj lz).
Proof.
  intros H. induction H.
  - constructor.
  - simpl. constructor.
    + apply eval_Zexpr_to_substn. assumption.
    + assumption.
Qed.

Lemma compose_domain {A B : Type} (s s' : A -> option B) x y :
  compose s s' x = Some y ->
  s x = Some y \/ s' x = Some y.
Proof. cbv [compose]. intros H. destruct (s' x), (s x); auto. Qed.

Inductive result_lookup_Z' : list Z -> result -> scalar_result -> Prop :=
| rlz'_cons x xs v v' val : (0 <= x)%Z ->
                            nth_error v (Z.to_nat x) = Some v' ->
                            result_lookup_Z' xs v' val ->
                            result_lookup_Z' (x :: xs) (V v) val
| rlz'_nil val : result_lookup_Z' [] (Result.S val) val.

(*closely following lemma eval_get_lookup_result_Z*)
Lemma eval_get_lookup_result_Z' : forall l v rs r,
    eval_get v rs l r ->
    forall x0,
      eval_Zexprlist v l x0 ->
      result_lookup_Z' x0 (V rs) r.
Proof.
  Fail induct 1. induction 1; intros.
  - invert H3. simpl.
    eq_eval_Z. econstructor; eauto.
  - invert H2. invert H8. eq_eval_Z. econstructor; eauto. constructor.
Qed.

Definition domain_in_ints low high (substn : var -> option fn) :=
  forall x y, substn x = Some y ->
         match x with
         | inr i => low <= i < high
         | inl _ => False
         end.

Definition disj {A B : Type} (s1 s2 : A -> option B) :=
  forall x y1 y2,
    s1 x = Some y1 ->
    s2 x = Some y2 ->
    False.

Lemma domain_in_ints_disj low1 high1 low2 high2 s1 s2 :
  (forall i, low1 <= i < high1 -> low2 <= i < high2 -> False) ->
  domain_in_ints low1 high1 s1 ->
  domain_in_ints low2 high2 s2 ->
  disj s1 s2.
Proof.
  cbv [domain_in_ints disj]. intros ? H1 H2 **.
  specialize (H1 _ _ ltac:(eassumption)). specialize (H2 _ _ ltac:(eassumption)).
  destruct x; [contradiction|]. eauto.
Qed.

Lemma domain_in_ints_disj_substn_of low high s v :
  domain_in_ints low high s ->
  disj s (substn_of v).
Proof.
  cbv [domain_in_ints disj substn_of]. intros. specialize H with (1 := H0).
  destruct x; [contradiction|congruence].
Qed.

Lemma compose_extends_r {A B : Type} (s1 s2 : A -> option B) :
  extends (compose s1 s2) s2.
Proof.
  cbv [extends compose]. intros * H. rewrite H. reflexivity.
Qed.
  
Lemma compose_extends_l {A B : Type} (s1 s2 : A -> option B) :
  disj s1 s2 ->
  extends (compose s1 s2) s1.
Proof.
  cbv [disj extends compose]. intros Hdisj * H. destruct (s2 x) eqn:E; eauto.
  exfalso. eauto.
Qed.

Lemma domain_in_ints_empty low high :
  domain_in_ints low high map_empty.
Proof. cbv [domain_in_ints map_empty]. congruence. Qed.

Lemma domain_in_ints_cons low high m x y :
  domain_in_ints low high m ->
  low <= x < high ->
  domain_in_ints low high (map_cons (inr x) y m).
Proof.
  cbv [domain_in_ints map_cons]. intros. destruct x0.
  { simpl in H1. specialize H with (1 := H1). simpl in H. contradiction. }
  simpl in H1. destruct (x =? n)%nat eqn:E.
  - apply Nat.eqb_eq in E. subst. assumption.
  - specialize H with (1 := H1). simpl in H. assumption.
Qed.
Check eval_Sexpr.
Lemma lower_Sexpr_correct sh v ec s (datalog_ctx : list (rule rel var fn)):
  (forall x r idxs val,
      ec $? x = Some r ->
      result_lookup_Z' idxs r val ->
      prog_impl_fact interp_fn datalog_ctx (str_rel x, Robj (toR val) :: (map Zobj idxs))) ->
  forall val name val0 hyps name',
    eval_Sexpr sh v ec s val ->
    lower_Sexpr name s = (val0, hyps, name') ->
    exists hyps' substn,
      name <= name' /\
      domain_in_ints name name' substn /\
        Forall2 (interp_fact interp_fn) (map (subst_in_fact (substn)) (map (subst_in_fact (substn_of v)) hyps)) hyps' /\
        Forall (prog_impl_fact interp_fn datalog_ctx) hyps' /\
        interp_expr interp_fn (subst_in_expr substn (subst_in_expr (substn_of v) val0)) (Robj (toR val)).
Proof.
  intros H. induction s; intros; simpl in *.
  - inversion H1. subst. clear H1. simpl. eexists.
    exists (map_cons (inr name) (Some (fn_R (fn_SLit (toR val)))) map_empty). split.
    { cbv [succ]. lia. } split.
    { apply domain_in_ints_cons. 2: cbv [succ]; lia. apply domain_in_ints_empty. }
    split.
    { repeat constructor. simpl. cbv [map_cons]. rewrite var_eqb_refl. simpl.
      repeat econstructor. }
    inversion H0. subst. clear H0. simpl. split.
    + repeat constructor. 
      specialize H with (idxs := nil) (1 := H2). simpl in H.
      specialize (H r). specialize (H ltac:(constructor)). destruct r; apply H.
    + cbv [map_cons]. rewrite var_eqb_refl. simpl. repeat econstructor.
  - inversion H1. subst. clear H1. simpl. inversion H0. subst. clear H0.
    pose proof (eval_get_eval_Zexprlist _ _ _ _ ltac:(eassumption)) as [idxs Hidxs].
    Check eval_get_lookup_result_Z.
    pose proof (eval_get_lookup_result_Z' _ _ _ _ ltac:(eassumption) _ ltac:(eassumption)) as Hr.
    eexists.
    exists (map_cons (inr name) (Some (fn_R (fn_SLit (toR r)))) map_empty).
    split.
    { cbv [succ]. lia. } split.
    { apply domain_in_ints_cons. 2: cbv [succ]; lia. apply domain_in_ints_empty. }
    split.
    { constructor. 2: constructor. cbv [subst_in_fact]. simpl. constructor. simpl.
      cbv [map_cons]. simpl. rewrite Nat.eqb_refl. simpl.
      apply eval_Zexprlist_to_substn in Hidxs. Print lower_idx.
      repeat econstructor.
      repeat rewrite <- Forall2_map_l in *. eapply Forall2_impl. 2: eassumption.
      simpl. intros a b H'. rewrite subst_in_expr_subst_in_expr.
      eapply interp_expr_subst_more'. 2: eassumption. cbv [extends].
      clear. intros x y H. cbv [compose]. destruct x; simpl in *.
      1: rewrite H; reflexivity. inversion H. }
    simpl. split.
    { repeat constructor. eapply H; eauto. }
    cbv [map_cons]. rewrite var_eqb_refl. simpl. repeat econstructor. simpl.
    destruct r; reflexivity.
  - inversion H0. subst. clear H0.
    destruct (lower_Sexpr name s1) as [[val1 hyps1] name1] eqn:E1.
    destruct (lower_Sexpr name1 s2) as [[val2 hyps2] name2] eqn:E2.
    inversion H1. subst. clear H1.
    specialize (IHs1 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    specialize (IHs2 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    destruct IHs1 as (hyps1'&substn1&Hname1&Hname1'&Hhyps1&Hhyps1'&Hval1).
    destruct IHs2 as (hyps2'&substn2&Hname2&Hname2'&Hhyps2&Hhyps2'&Hval2).
    exists (hyps1' ++ hyps2')%list. exists (compose substn1 substn2).
    assert (extends (compose substn1 substn2) substn1).
    { cbv [extends]. intros. cbv [compose].
        rewrite H0. apply Hname1' in H0. destruct x; [contradiction|].
        destruct (substn2 (inr n)) eqn:E. 2: reflexivity. apply Hname2' in E. lia. }
    assert (extends (compose substn1 substn2) substn2).
    { cbv [extends]. intros. cbv [compose]. rewrite H1. reflexivity. }
    split.
    { lia. } split.
    { intros ? ? H'. apply compose_domain in H'. destruct H' as [H'|H'].
      - apply Hname1' in H'. destruct x; [contradiction | lia].
      - apply Hname2' in H'. destruct x; [contradiction | lia]. } split.
    { repeat rewrite <- Forall2_map_l in *. apply Forall2_app.
      - eapply Forall2_impl. 2: eassumption. simpl. intros * H'.
        pose proof interp_fact_subst_more as H''. specialize H'' with (2 := H').
        rewrite H''. 1: assumption. assumption.
      - eapply Forall2_impl. 2: eassumption. simpl. intros * H'.
        pose proof interp_fact_subst_more as H''. specialize H'' with (2 := H').
        rewrite H''. 1: assumption. assumption. } split.
    { apply Forall_app. split; assumption. }
    simpl. econstructor.
    { repeat econstructor.
      - pose proof interp_expr_subst_more as H'.
        specialize H' with (2 := Hval1). rewrite H'. 1: eassumption.
        assumption.
      - pose proof interp_expr_subst_more as H'.
        specialize H' with (2 := Hval2). rewrite H'. 1: eassumption.
        assumption. }
    simpl. f_equal. f_equal. destruct r1, r2; reflexivity.
    (*!!literally copy-pasted!!*)
  - inversion H0. subst. clear H0.
    destruct (lower_Sexpr name s1) as [[val1 hyps1] name1] eqn:E1.
    destruct (lower_Sexpr name1 s2) as [[val2 hyps2] name2] eqn:E2.
    inversion H1. subst. clear H1.
    specialize (IHs1 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    specialize (IHs2 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    destruct IHs1 as (hyps1'&substn1&Hname1&Hname1'&Hhyps1&Hhyps1'&Hval1).
    destruct IHs2 as (hyps2'&substn2&Hname2&Hname2'&Hhyps2&Hhyps2'&Hval2).
    exists (hyps1' ++ hyps2')%list. exists (compose substn1 substn2).
    assert (extends (compose substn1 substn2) substn1).
    { cbv [extends]. intros. cbv [compose].
        rewrite H0. apply Hname1' in H0. destruct x; [contradiction|].
        destruct (substn2 (inr n)) eqn:E. 2: reflexivity. apply Hname2' in E. lia. }
    assert (extends (compose substn1 substn2) substn2).
    { cbv [extends]. intros. cbv [compose]. rewrite H1. reflexivity. }
    split.
    { lia. } split.
    { intros ? ? H'. apply compose_domain in H'. destruct H' as [H'|H'].
      - apply Hname1' in H'. destruct x; [contradiction | lia].
      - apply Hname2' in H'. destruct x; [contradiction | lia]. } split.
    { repeat rewrite <- Forall2_map_l in *. apply Forall2_app.
      - eapply Forall2_impl. 2: eassumption. simpl. intros * H'.
        pose proof interp_fact_subst_more as H''. specialize H'' with (2 := H').
        rewrite H''. 1: assumption. assumption.
      - eapply Forall2_impl. 2: eassumption. simpl. intros * H'.
        pose proof interp_fact_subst_more as H''. specialize H'' with (2 := H').
        rewrite H''. 1: assumption. assumption. } split.
    { apply Forall_app. split; assumption. }
    simpl. econstructor.
    { repeat econstructor.
      - pose proof interp_expr_subst_more as H'.
        specialize H' with (2 := Hval1). rewrite H'. 1: eassumption.
        assumption.
      - pose proof interp_expr_subst_more as H'.
        specialize H' with (2 := Hval2). rewrite H'. 1: eassumption.
        assumption. }
    simpl. f_equal. f_equal. destruct r1, r2; reflexivity.
  - inversion H0. subst. clear H0.
    destruct (lower_Sexpr name s1) as [[val1 hyps1] name1] eqn:E1.
    destruct (lower_Sexpr name1 s2) as [[val2 hyps2] name2] eqn:E2.
    inversion H1. subst. clear H1.
    specialize (IHs1 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    specialize (IHs2 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    destruct IHs1 as (hyps1'&substn1&Hname1&Hname1'&Hhyps1&Hhyps1'&Hval1).
    destruct IHs2 as (hyps2'&substn2&Hname2&Hname2'&Hhyps2&Hhyps2'&Hval2).
    exists (hyps1' ++ hyps2')%list. exists (compose substn1 substn2).
    assert (extends (compose substn1 substn2) substn1).
    { cbv [extends]. intros. cbv [compose].
        rewrite H0. apply Hname1' in H0. destruct x; [contradiction|].
        destruct (substn2 (inr n)) eqn:E. 2: reflexivity. apply Hname2' in E. lia. }
    assert (extends (compose substn1 substn2) substn2).
    { cbv [extends]. intros. cbv [compose]. rewrite H1. reflexivity. }
    split.
    { lia. } split.
    { intros ? ? H'. apply compose_domain in H'. destruct H' as [H'|H'].
      - apply Hname1' in H'. destruct x; [contradiction | lia].
      - apply Hname2' in H'. destruct x; [contradiction | lia]. } split.
    { repeat rewrite <- Forall2_map_l in *. apply Forall2_app.
      - eapply Forall2_impl. 2: eassumption. simpl. intros * H'.
        pose proof interp_fact_subst_more as H''. specialize H'' with (2 := H').
        rewrite H''. 1: assumption. assumption.
      - eapply Forall2_impl. 2: eassumption. simpl. intros * H'.
        pose proof interp_fact_subst_more as H''. specialize H'' with (2 := H').
        rewrite H''. 1: assumption. assumption. } split.
    { apply Forall_app. split; assumption. }
    simpl. econstructor.
    { repeat econstructor.
      - pose proof interp_expr_subst_more as H'.
        specialize H' with (2 := Hval1). rewrite H'. 1: eassumption.
        assumption.
      - pose proof interp_expr_subst_more as H'.
        specialize H' with (2 := Hval2). rewrite H'. 1: eassumption.
        assumption. }
    simpl. f_equal. f_equal. destruct r1, r2; reflexivity.
  - inversion H0. subst. clear H0.
    destruct (lower_Sexpr name s1) as [[val1 hyps1] name1] eqn:E1.
    destruct (lower_Sexpr name1 s2) as [[val2 hyps2] name2] eqn:E2.
    inversion H1. subst. clear H1.
    specialize (IHs1 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    specialize (IHs2 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    destruct IHs1 as (hyps1'&substn1&Hname1&Hname1'&Hhyps1&Hhyps1'&Hval1).
    destruct IHs2 as (hyps2'&substn2&Hname2&Hname2'&Hhyps2&Hhyps2'&Hval2).
    exists (hyps1' ++ hyps2')%list. exists (compose substn1 substn2).
    assert (extends (compose substn1 substn2) substn1).
    { cbv [extends]. intros. cbv [compose].
        rewrite H0. apply Hname1' in H0. destruct x; [contradiction|].
        destruct (substn2 (inr n)) eqn:E. 2: reflexivity. apply Hname2' in E. lia. }
    assert (extends (compose substn1 substn2) substn2).
    { cbv [extends]. intros. cbv [compose]. rewrite H1. reflexivity. }
    split.
    { lia. } split.
    { intros ? ? H'. apply compose_domain in H'. destruct H' as [H'|H'].
      - apply Hname1' in H'. destruct x; [contradiction | lia].
      - apply Hname2' in H'. destruct x; [contradiction | lia]. } split.
    { repeat rewrite <- Forall2_map_l in *. apply Forall2_app.
      - eapply Forall2_impl. 2: eassumption. simpl. intros * H'.
        pose proof interp_fact_subst_more as H''. specialize H'' with (2 := H').
        rewrite H''. 1: assumption. assumption.
      - eapply Forall2_impl. 2: eassumption. simpl. intros * H'.
        pose proof interp_fact_subst_more as H''. specialize H'' with (2 := H').
        rewrite H''. 1: assumption. assumption. } split.
    { apply Forall_app. split; assumption. }
    simpl. econstructor.
    { repeat econstructor.
      - pose proof interp_expr_subst_more as H'.
        specialize H' with (2 := Hval1). rewrite H'. 1: eassumption.
        assumption.
      - pose proof interp_expr_subst_more as H'.
        specialize H' with (2 := Hval2). rewrite H'. 1: eassumption.
        assumption. }
    simpl. f_equal. f_equal. destruct r1, r2; reflexivity.
  - inversion H0. subst. clear H0. inversion H1. subst. clear H1. eexists. exists map_empty.
    split; [lia|]. split.
    { cbv [map_empty]. intros. congruence. } split.
    { simpl. constructor. } split.
    { constructor. }
    simpl. econstructor. 1: constructor. simpl. reflexivity.
Qed.

(*because i really want to do induction on syntax, not execution*)
Lemma invert_eval_gen sh v ctx i lo hi body r :
  eval_expr sh v ctx (Gen i lo hi body) r ->
  exists loz hiz rl,
    r = V rl /\
      length rl = Z.to_nat (hiz - loz) /\
      eval_Zexpr_Z v lo = Some loz /\
      eval_Zexpr_Z v hi = Some hiz /\
      (forall i', (loz <= i' < hiz)%Z ->
             (~ i \in dom v) /\
               (~ contains_substring "?" i) /\
               match nth_error rl (Z.to_nat (i' - loz)) with
               | None => False
               | Some r =>  eval_expr sh (v $+ (i, i')) ctx body r
               end).
Proof.
  intros H. remember (Gen _ _ _ _) as e eqn:E. revert lo E.
  induction H; intros lo_ H'; inversion H'; subst; clear H'.
  - exists loz, hiz, nil. simpl. intuition lia.
  - clear IHeval_expr1.
    specialize (IHeval_expr2 _ ltac:(reflexivity)). (*why is eq_refl not eq_refl*)
    destruct IHeval_expr2 as (loz_&hiz_&l_&Hl_&Hlen&Hloz&Hhiz&IH2).
    rewrite H0 in Hhiz. inversion Hhiz. subst. clear Hhiz.
    inversion Hl_. subst. clear Hl_.
    simpl in Hloz. rewrite H in Hloz. inversion Hloz. subst. clear Hloz.
    eexists _, _, _. intuition eauto.
    { simpl. lia. }
    assert (Hor : (i' = loz \/ loz + 1 <= i')%Z) by lia.
    destruct Hor as [Hle|Heq].
    + subst. replace (Z.to_nat _) with O by lia. simpl. assumption.
    + specialize (IH2 i' ltac:(lia)). destruct (Z.to_nat (i' - loz)) eqn:E. 1: lia.
      simpl. destruct IH2 as (_&_&IH2). replace (Z.to_nat _) with n in IH2 by lia.
      apply IH2.
Qed.
Search nth_error repeat.
Lemma nth_error_repeat' {A : Type} (x : A) y m n :
  nth_error (repeat x m) n = Some y ->
  x = y.
Proof.
  intros H. Search nth_error. epose proof nth_error_Some as H1.
  specialize (H1 _ _ _ ltac:(eassumption)). pose proof nth_error_repeat as H2.
  rewrite repeat_length in H1. rewrite nth_error_repeat in H by lia. inversion_clear H.
  reflexivity.
Qed.

Lemma pad_lookup_SX sh idxs val :
  result_lookup_Z' idxs (gen_pad sh) val ->
  val = SX.
Proof.
  revert idxs val. induction sh.
  - intros * H. inversion H. subst. reflexivity.
  - intros * H. inversion H. apply nth_error_repeat' in H2. subst. eapply IHsh; eauto.
Qed.

Print add_result. Search add_scalar_result. (*why not a function :( *)
Definition add_scalar_result' (x y : scalar_result) :=
  match x, y with
  | SX, SX => SX
  | SX, SS sy => SS sy
  | SS sx, SX => SS sx
  | SS sx, SS sy => SS (sx + sy)
  end.

Lemma add_scalar_result_iff_add_scalar_result' a b c :
  add_scalar_result' a b = c <-> add_scalar_result a b c.
Proof.
  split.
  - intros. subst. destruct a, b; constructor.
  - intros H. inversion H; reflexivity.
Qed.

Lemma add_list_nth a b c a' b' i :
  add_list a b c ->
  nth_error a i = Some a' ->
  nth_error b i = Some b' ->
  exists c',
    nth_error c i = Some c' /\
      add_result a' b' c'.
Proof.
  intros H. revert a' b' i. induction H.
  - intros * H1 H2. destruct i; simpl in *.
    + inversion H1. subst. inversion H2. subst. clear H1 H2. eauto.
    + specialize IHadd_list with (1 := H1) (2 := H2).
      destruct IHadd_list as (c'&IH1&IH2). eauto.
  - intros. destruct i; simpl in *; congruence.
Qed.

Lemma add_list_nth_bw a b c c' i :
  add_list a b c ->
  nth_error c i = Some c' ->
  exists a' b',
    nth_error a i = Some a' /\
      nth_error b i = Some b' /\
      add_result a' b' c'.
Proof.
  intros H. revert c' i. induction H.
  - intros * H1. destruct i; simpl in *.
    + inversion H1. subst. eauto.
    + specialize IHadd_list with (1 := H1). destruct IHadd_list as (a'&b'&IH1&IH2&IH3).
      eauto.
  - intros. destruct i; simpl in *; congruence.
Qed.

Lemma add_result_lookup_Z' idxs x y z x' y' :
  add_result x y z ->
  result_lookup_Z' idxs x x' ->
  result_lookup_Z' idxs y y' ->
  result_lookup_Z' idxs z (add_scalar_result' x' y').
Proof. 
  revert x y z. induction idxs.
  - intros x y z H H1 H2. 
    inversion H1. inversion H2. subst. inversion H. subst.
    apply add_scalar_result_iff_add_scalar_result' in H4. subst. constructor.
  - intros x y z H H1 H2. inversion H1. subst. inversion H2. subst. inversion H. subst.
    clear H1 H2 H.
    pose proof add_list_nth as H'. specialize (H' _ _ _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
    destruct H' as (c'&H'1&H'2). econstructor; eauto.
Qed.

Lemma add_result_same_domain_bw idxs x y z z' :
  add_result x y z ->
  result_lookup_Z' idxs z z' ->
  exists x' y',
    result_lookup_Z' idxs x x' /\
      result_lookup_Z' idxs y y' /\
      z' = add_scalar_result' x' y'.
Proof.
  revert x y z. induction idxs; intros x y z H1 H2.
  - inversion H2. subst. clear H2. inversion H1. subst. clear H1. do 2 eexists.
    apply add_scalar_result_iff_add_scalar_result' in H3. subst.
    intuition constructor.
  - inversion H2. subst. clear H2. inversion H1. subst. clear H1.
    pose proof add_list_nth_bw as H'. specialize (H' _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    destruct H' as (?&?&?&?&?). specialize (IHidxs _ _ _ ltac:(eassumption) ltac:(eassumption)). destruct IHidxs as (?&?&?&?). do 2 eexists. intuition eauto; econstructor; eauto.
Qed.

Lemma add_result_has_shape a b c :
  exists sh,
  add_result a b c ->
  result_has_shape c sh.
Proof.
  revert a b. induction c; intros a b; subst.
  - eexists. econstructor.
  - destruct v.
    + eexists. econstructor.
    + inversion H. subst. clear H. specialize (H2 a b). destruct H2 as [sh H2].
      eexists. intros H. inversion H. subst. clear H. inversion H5. subst. clear H5.
      Abort. (*not true*) Locate "+".
    
Lemma invert_eval_sum sh v ctx i lo hi body r :
  eval_expr sh v ctx (Sum i lo hi body) r ->
  exists loz hiz summands,
    length summands = Z.to_nat (hiz - loz) /\
      eval_Zexpr_Z v lo = Some loz /\
      eval_Zexpr_Z v hi = Some hiz /\
      (forall idxs val,
          result_lookup_Z' idxs r val ->
          exists scalar_summands,
            Forall2 (result_lookup_Z' idxs) summands scalar_summands /\
              toR val = fold_right Rplus 0%R (map toR scalar_summands)) /\
      (forall i', (loz <= i' < hiz)%Z ->
             (~ i \in dom v) /\
               (~ contains_substring "?" i) /\
               match nth_error summands (Z.to_nat (i' - loz)) with
               | None => False
               | Some r =>  eval_expr sh (v $+ (i, i')) ctx body r
               end).
Proof.
  intros H. remember (Sum _ _ _ _) as e eqn:E. revert lo E.
  induction H; intros lo_ H'; inversion H'; subst; clear H'.
  2: { exists loz, hiz, nil. simpl. intuition auto; try lia.
       exists nil. split; [constructor|]. simpl. apply pad_lookup_SX in H4. subst.
       reflexivity. }
  clear IHeval_expr1. specialize (IHeval_expr2 _ Logic.eq_refl).
  destruct IHeval_expr2 as (loz'&hiz'&summands'&Hlen&Hloz'&Hhiz'&Hsummands'&IH).
  simpl in Hloz'. rewrite H0 in Hhiz'. invert Hhiz'. rewrite H in Hloz'. invert Hloz'.
  exists loz, hiz', (r :: summands'). intuition.
  + simpl. lia.
  + pose proof add_result_same_domain_bw as H'.
    specialize (H' _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)). destruct H' as (x'&y'&Hx'&Hy'&Hval). subst.
    specialize (Hsummands' _ _ ltac:(eassumption)). destruct Hsummands' as (ss&Hss1&Hss2).
    exists (x' :: ss). split.
    -- constructor; [eassumption|]. assumption.
    -- simpl. rewrite <- Hss2. destruct x', y'; simpl; ring.
  + clear Hsummands'.
    assert (Hor : (i' = loz \/ loz + 1 <= i')%Z) by lia.
    destruct Hor as [Hle|Heq].
    -- subst. replace (Z.to_nat _) with O by lia. simpl. assumption.
    -- 
       specialize (IH i' ltac:(lia)). destruct IH as (_&_&IH).
       replace (Z.to_nat (i' - loz)) with (Datatypes.S (Z.to_nat (i' - (loz + 1)))) by lia.
       simpl. assumption.
Qed.

Lemma disj_comm {A B : Type} (x y : A -> option B) : disj x y -> disj y x.
Proof. cbv [disj]. eauto. Qed.

Definition idx_map (x : list fn) : var -> option fn :=
  fun v =>
    match v with
    | inr n => nth_error x n
    | inl _ => None
    end.

Lemma domain_in_ints_idx_map x :
  domain_in_ints O (length x) (idx_map x).
Proof.
  cbv [domain_in_ints idx_map]. intros y z H. destruct y; [congruence|].
  apply nth_error_Some in H. assumption.
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

Lemma gen_pad_bounds idxs dims val :
  result_lookup_Z' idxs (gen_pad dims) val ->
  length dims = length idxs.
Proof.
  revert dims. induction idxs.
  - simpl. intros dims H. inversion H. subst. clear H. destruct dims; [reflexivity|].
    simpl in H0. discriminate H0.
  - intros dims H. inversion H. subst. clear H. destruct dims; [discriminate H2|].
    simpl in H2. inversion H2. subst. clear H2. simpl. f_equal. apply IHidxs.
    apply nth_error_repeat' in H4. subst. assumption.
Qed.

Inductive result_has_dim : nat -> result -> Prop :=
| ScalarDim s : result_has_dim O (Result.S s)
| VectorConsDim n xs : Forall (result_has_dim n) xs ->
                       result_has_dim (S n) (V xs).

Lemma dim_sum a b c n :
  add_result a b c ->
  result_has_dim n a ->
  result_has_dim n c.
Proof.
  revert a b c. induction n; intros a b c Hadd Ha; invert Hadd; invert Ha.
  - constructor.
  - constructor. revert v1 v2 H H2. induction r; intros v1 v2 H H2.
    + constructor.
    + invert H. invert H2. constructor; eauto.
Qed.

Lemma dim_gen_pad l :
  result_has_dim (length l) (gen_pad l).
Proof.
  induction l; simpl; constructor. apply Forall_repeat. assumption.
Qed.

Lemma dim_gen_pad' l n :
  length l = n ->
  result_has_dim n (gen_pad l).
Proof. intros. subst. apply dim_gen_pad. Qed.
Search transpose_result. Print transpose_result.

Lemma dim_gen_pad_list sh :
  Forall (result_has_dim (length sh - 1)) (gen_pad_list sh).
Proof.
  destruct sh; simpl. 1: constructor. apply Forall_repeat. apply dim_gen_pad'. lia.
Qed.

Lemma dim_gen_pad_list' sh n :
  length sh - 1 = n ->
  Forall (result_has_dim n) (gen_pad_list sh).
Proof. intros. subst. apply dim_gen_pad_list. Qed.

Lemma dim_pad_list_result_to_shape l sh :
  Forall (result_has_dim (length sh - 1)) l ->
  Forall (result_has_dim (length sh - 1)) (pad_list_result_to_shape l sh).
Proof.
  intros H. cbv [pad_list_result_to_shape]. destruct l; [|assumption].
  apply dim_gen_pad_list'. reflexivity.
Qed.

Lemma dim_pad_list_result_to_shape' l sh n :
  length sh - 1 = n ->
  Forall (result_has_dim n) l ->
  Forall (result_has_dim n) (pad_list_result_to_shape l sh).
Proof. intros. subst. apply dim_pad_list_result_to_shape. assumption. Qed.
Print transpose_result_list.
Print get_col. Print size_of. Print result_has_shape.

Lemma dim_goes_down n v x r :
  nth_error v x = Some r ->
  result_has_dim (S n) (V v) ->
  result_has_dim n r.
Proof.
  intros H1 H2. inversion H2. subst. apply nth_error_In in H1.
  rewrite Forall_forall in H3. auto.
Qed.

Lemma dim_transpose_result_list l n m :
  Forall (result_has_dim (S n)) l ->
  Forall (result_has_dim (S n)) (transpose_result_list l m).
Proof.
  intros H. induction m.
  - simpl. constructor.
  - simpl. constructor. 2: assumption. constructor. Print get_col.
    remember (row_length l - S m) as x. clear Heqx. clear IHm. revert x.
    induction l; intros x; simpl.
    + constructor.
    + destruct a. 1: constructor. destruct (nth_error v x) eqn:E. 2: constructor.
      invert H. constructor. 2: auto. eapply dim_goes_down; eauto.
Qed.

Lemma dim_transpose_result n l sh :
  length sh = S (S n) ->
  result_has_dim (S (S n)) (V l) ->
  result_has_dim (S (S n)) (transpose_result l sh).
Proof.
  intros ? H. subst. cbv [transpose_result]. invert H. constructor.
  apply dim_pad_list_result_to_shape'. 1: lia. apply dim_transpose_result_list.
  assumption.
Qed.
(*proving stronger things---e.g., shape of r agrees with sizeof e---requires either some
  cleverness or some assumption like the bounds all being constants*)
(*i don't think i need the stronger things, so i'll just stick with this for now*)
(*I was trying to avoid having size_of as an assumption, but looking at the concat case
  of eval_expr makes it clear that it is necessary; there's no restriction about the
  things even having the same dimensions..*)
Search size_of.
Lemma dim_flatten_result n l :
  result_has_dim (S (S n)) (V l) ->
  Forall (result_has_dim n) (flatten_result l).
Proof.
  intros H. invert H. induction l; simpl.
  - constructor.
  - invert H2. invert H1. apply Forall_app. auto.
Qed.

Lemma dim_result_shape_nat n r :
  result_has_dim n r ->
  length (result_shape_nat r) = n.
Proof.
  revert r. induction n; intros r H; invert H.
  - reflexivity.
  - simpl. destruct xs. Abort.

Lemma dim_gen_pad_result_shape_nat n r :
  result_has_dim n r ->
  result_has_dim n (gen_pad (result_shape_nat r)).
Proof.
  revert r. induction n; intros r H; invert H.
  - simpl. constructor.
  - simpl. destruct xs.
    + constructor. simpl. constructor.
    + simpl. constructor. invert H1. constructor. 1: auto.
      apply Forall_repeat. auto.
Qed.
        
Lemma dim_split_result n k l :
  Forall (result_has_dim n) l ->
  Forall (result_has_dim (S n)) (split_result k l).
Proof.
  intros H. cbv [split_result]. apply Forall_map. apply Forall_forall. intros x Hx.
  apply In_nat_range in Hx. constructor. destruct l.
  { destruct k.
    - simpl in Hx. vm_compute in Hx. lia.
    - simpl in Hx. rewrite div_ceil_n_0 in Hx by lia. lia. }
  cbn -[gen_pad_list List.app]. apply forall_firstn. apply forall_skipn.
  apply Forall_app. split; [assumption|]. simpl. Print result_shape_nat.
  apply Forall_repeat. apply dim_gen_pad_result_shape_nat. invert H. assumption.
Qed.

Lemma dimensions_right sh v ctx e r l :
  eval_expr sh v ctx e r ->
  size_of e l ->
  result_has_dim (length l) r.
Proof.
  intros H. revert l. induction H; intros lsz Hsz; invert Hsz.
  - constructor. constructor.
  - simpl in *. constructor.
    specialize (IHeval_expr2 _ ltac:(constructor; eassumption)).
    simpl in IHeval_expr2. invert IHeval_expr2. constructor; eauto.
  - simpl in *. eapply dim_sum; eauto.
  - simpl. apply size_of_sizeof in H2, H9. subst.
    apply dim_gen_pad'. rewrite map_length. apply length_eval_Zexprlist in H3.
    auto.
  - simpl. apply size_of_sizeof in H0, H5. subst.
    apply dim_gen_pad'. rewrite map_length. apply length_eval_Zexprlist in H1.
    auto.
  - eauto.
  - eauto.
  - eauto.
  - simpl. constructor. apply Forall_app; auto.
    specialize (IHeval_expr1 _ ltac:(eassumption)).
    specialize (IHeval_expr2 _ ltac:(eassumption)).
    simpl in *. invert IHeval_expr1. invert IHeval_expr2. specialize (H6 $0).
    eassert (blah: forall x y, x = y -> length x = length y) by (intros; subst; reflexivity).
    apply blah in H6. do 2 rewrite map_length in H6. rewrite H6 in *. auto.
  - simpl. specialize (IHeval_expr _ ltac:(eassumption)).
    apply size_of_sizeof in H0, H3. rewrite H0 in H3. invert H3.
    apply length_eval_Zexprlist in H1. simpl in H1. invert H1. simpl in *.
    rewrite H3 in *. apply dim_transpose_result.
    + simpl. rewrite map_length. reflexivity.
    + assumption.
  - simpl in *. constructor. specialize (IHeval_expr _ ltac:(eassumption)).
    simpl in IHeval_expr. apply dim_flatten_result. assumption.
  - simpl in *. constructor. specialize (IHeval_expr _ ltac:(eassumption)).
    simpl in *. invert IHeval_expr. apply dim_split_result. assumption.
  - simpl in *. constructor. specialize (IHeval_expr _ ltac:(eassumption)).
    simpl in *. apply Forall_rev. invert IHeval_expr. rewrite truncl_list_skipn.
    apply forall_skipn. apply Forall_rev. assumption.
  - simpl in *. constructor. specialize (IHeval_expr _ ltac:(eassumption)).
    simpl in *. invert IHeval_expr. rewrite truncl_list_skipn. apply forall_skipn.
    assumption.
  - simpl in *. constructor. specialize (IHeval_expr _ ltac:(eassumption)).
    simpl in *. invert IHeval_expr. apply Forall_app. split; [assumption|].
    apply Forall_repeat. apply dim_gen_pad'. rewrite map_length.
    apply size_of_sizeof in H1, H7. rewrite H1 in H7. invert H7.
    apply length_eval_Zexprlist in H3. auto.
  - simpl in *. constructor. specialize (IHeval_expr _ ltac:(eassumption)).
    simpl in *. invert IHeval_expr. apply Forall_app. split; [|assumption].
    apply Forall_repeat. apply dim_gen_pad'. rewrite map_length.
    apply size_of_sizeof in H1, H7. rewrite H1 in H7. invert H7.
    apply length_eval_Zexprlist in H3. auto.
  - simpl. constructor.
Qed.

Lemma dim_idxs n r val idxs :
  result_has_dim n r ->
  result_lookup_Z' idxs r val ->
  length idxs = n.
Proof.
  revert r val idxs. induction n; intros r val idxs H1 H2; invert H1; invert H2.
  - reflexivity.
  - simpl. f_equal. eapply IHn; eauto. apply nth_error_In in H3.
    rewrite Forall_forall in H0. auto.
Qed.

Lemma map_cons_something x y m :
  (map_cons x y m) x = y.
Proof. cbv [map_cons]. rewrite var_eqb_refl. reflexivity. Qed.

Lemma Forall2_nth_error (A B : Type) (R : A -> B -> Prop) l1 l2 :
  length l1 = length l2 ->
  (forall n x1 x2,
      nth_error l1 n = Some x1 ->
      nth_error l2 n = Some x2 ->
      R x1 x2) ->
  Forall2 R l1 l2.
Proof.
  revert l2. induction l1; intros l2 H1 H2.
  - destruct l2; [|discriminate H1]. constructor.
  - destruct l2; [discriminate H1|]. simpl in H1. invert H1.
    pose proof (H2 O _ _ ltac:(reflexivity) ltac:(reflexivity)).
    constructor; [assumption|]. apply IHl1; auto. intros n.
    specialize (H2 (S n)). simpl in H2. exact H2.
Qed.

Ltac destruct_option_map_Some :=
  match goal with
  | H: option_map ?f ?x = Some ?y |- _ =>
      destruct x eqn:?E; [cbn [option_map] in H; invert H|discriminate H]
  end.

Lemma nth_error_seq_Some n1 n2 n3 n4 :
  nth_error (seq n1 n2) n3 = Some n4 ->
  n4 = n1 + n3.
Proof.
  revert n1 n3 n4. induction n2; intros n1 n3 n4 H; simpl in *.
  - destruct n3; discriminate H.
  - destruct n3; simpl in H.
    + invert H. lia.
    + apply IHn2 in H. lia.
Qed.

Lemma idx_map_works idxs :
  Forall2 (interp_expr interp_fn)
    (map (subst_in_expr (idx_map (map (fun x => fn_Z (fn_ZLit x)) idxs)))
       (map var_expr (map inr (seq O (length idxs)))))
    (map Zobj idxs).
Proof.
  apply Forall2_nth_error.
  { repeat rewrite map_length. rewrite seq_length. auto. }
  intros n x1 x2. repeat rewrite nth_error_map. intros.
  do 4 destruct_option_map_Some. apply nth_error_seq_Some in E0.
  simpl in E0. subst. simpl. cbv [compose map_cons]. simpl.
  epose proof nth_error_Some as H. specialize (H _ _ _ ltac:(eassumption)).
  rewrite nth_error_map. rewrite E. simpl. repeat econstructor.
Qed.

Lemma extends_trans {A B : Type} (a b c : A -> option B) :
  extends a b ->
  extends b c ->
  extends a c.
Proof. cbv [extends]. auto. Qed.

Lemma extends_map_cons a x y :
  a x = None ->
  extends (map_cons x (Some y) a) a.
Proof.
  intros. cbv [extends map_cons]. intros. destruct (var_eqb x x0) eqn:E.
  - apply var_eqb_eq in E. subst. rewrite H in H0. congruence.
  - assumption.
Qed.

Lemma gross1 val idxs v :
  let s := compose
             (substn_of v)
             (map_cons
                (inr (length idxs)) (Some (fn_R (fn_SLit (toR val))))
                (idx_map (map (fun x => fn_Z (fn_ZLit x)) idxs))) in
  Forall2 (interp_expr interp_fn)
    (map (subst_in_expr s)
       (map var_expr (map inr (seq 0 (length idxs)))))
    (map Zobj idxs).
Proof.
  intros s.
  pose proof idx_map_works idxs. repeat rewrite <- Forall2_map_l in *.
  eapply Forall2_impl; [|eassumption]. cbv beta. intros a b Hab.
  eapply interp_expr_subst_more'. 2: eassumption. subst s.
  eapply extends_trans. apply compose_extends_r. apply extends_map_cons.
  cbv [idx_map]. Search nth_error None. apply nth_error_None.
  rewrite map_length. lia.
Qed.

Lemma gross2 val idxs v :
  let s := compose
             (substn_of v)
             (map_cons
                (inr (length idxs)) (Some (fn_R (fn_SLit (toR val))))
                (idx_map (map (fun x => fn_Z (fn_ZLit x)) idxs))) in
  extends s (substn_of v).
Proof.
  apply compose_extends_l. Search domain_in_ints disj. apply disj_comm.
  eapply domain_in_ints_disj_substn_of with (low := O) (high := S (length idxs)).
  apply domain_in_ints_cons; [|lia]. Check domain_in_ints_idx_map.
  eapply domain_in_ints_weaken. 3: apply domain_in_ints_idx_map. 1: lia.
  rewrite map_length. lia.
Qed.


Search var_eqb.
Lemma var_eqb_neq x y :
  x <> y -> var_eqb x y = false.
Proof.
  intros H. cbv [var_eqb]. destruct x, y; try reflexivity.
  - apply String.eqb_neq. congruence.
  - apply Nat.eqb_neq. congruence.
Qed.

Lemma map_cons_nothing m x x' y :
  x <> x' ->
  (map_cons x y m) x' = m x'.
Proof.
  intros. cbv [map_cons]. rewrite var_eqb_neq by assumption. reflexivity.
Qed.

Lemma nth_error_skipn {A : Type} (l : list A) n1 n2 :
  nth_error (skipn n1 l) n2 = nth_error l (n1 + n2).
Proof.
  revert n1 n2. induction l; intros n1 n2; simpl.
  - destruct n1, n2; reflexivity.
  - destruct n1; simpl; auto.
Qed.

Lemma Forall2_firstn {A B : Type} (l1 : list A) (l2 : list B) R n :
  Forall2 R l1 l2 ->
  Forall2 R (firstn n l1) (firstn n l2).
Proof.
  revert l1 l2. induction n; simpl.
  - intros. constructor.
  - intros. invert H; constructor; auto.
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
  invert H3. apply Forall2_length in H2. rewrite <- H2. Search (nth_error (_ ++ _)).
  exists x. split; [|assumption]. rewrite nth_error_app2 by lia. replace _ with O by lia.
  reflexivity.
Qed.
Print result_has_shape.

Definition true_rule : rule rel var fn :=
  {| rule_concl := {| fact_R := true_rel;
                     fact_args := [fun_expr (fn_B (fn_BLit true)) []] |};
    rule_hyps := [] |}.

Definition false_rule : rule rel var fn :=
  {| rule_concl := {| fact_R := false_rel;
                     fact_args := [fun_expr (fn_B (fn_BLit false)) []] |};
    rule_hyps := [] |}.

Lemma Forall2_impl_in_l {A B : Type} (R1 R2 : A -> B -> Prop) l1 l2 :
  (forall x y, In x l1 -> R1 x y -> R2 x y) ->
  Forall2 R1 l1 l2 ->
  Forall2 R2 l1 l2.
Proof.
  intros H1 H2. revert H1. induction H2; intros H1.
  - constructor.
  - simpl in *. constructor; auto.
Qed.

Print result_has_shape.  

Lemma length_flatten_result n m sh l :
  result_has_shape' (n :: m :: sh) (V l) ->
  length (flatten_result l) = n * m.
Proof.
  revert n. induction l; intros n H; invert H.
  - reflexivity.
  - simpl. invert H4. invert H1. rewrite app_length. erewrite IHl.
    2: { econstructor; [reflexivity|]. assumption. } lia.
Qed.

Lemma compose_None {A B : Type} (f1 f2 : A -> option B) x : f1 x = None -> f2 x = None -> compose f1 f2 x = None.
Proof. intros. cbv [compose]. rewrite H, H0. reflexivity. Qed.

Lemma idx_map_None idxs x :
  (0 <= x < length idxs -> False) ->
  idx_map idxs (inr x) = None.
Proof.
  intros H. pose proof domain_in_ints_idx_map idxs (inr x) as H'.
  simpl in H'. simpl. destruct (nth_error idxs x); auto. exfalso. eauto.
Qed.

Ltac simpl_map_cons :=
  repeat (rewrite map_cons_something || rewrite map_cons_nothing by (intros blah; invert blah; lia)).

Ltac isNone_solver :=
  simpl_map_cons;
  (solve [apply compose_None; isNone_solver]) ||
    reflexivity ||
    (apply idx_map_None; simpl; repeat rewrite map_length; simpl; lia) ||
    idtac.

Ltac domain_in_ints_solver :=
  apply domain_in_ints_idx_map.

Ltac disj_solver' :=
  (eapply domain_in_ints_disj_substn_of; domain_in_ints_solver).

Ltac disj_solver :=
  disj_solver' || (apply disj_comm; disj_solver') || idtac.

Ltac extends_solver' :=            
  (apply extends_map_cons; isNone_solver) ||
    (apply compose_extends_l; disj_solver) ||
    apply compose_extends_r.

Ltac extends_solver :=
  extends_solver' || (eapply extends_trans;
                     [solve[extends_solver'] |extends_solver]) || idtac.



Lemma lower_correct e out sh v ctx r datalog_ctx l :
  eval_expr sh v ctx e r ->
  size_of e l ->
  constant_nonneg_bounds e ->
  (forall x (r : result) (idxs : list Z) (val : scalar_result),
      ctx $? x = Some r ->
      result_lookup_Z' idxs r val ->
      prog_impl_fact interp_fn datalog_ctx (str_rel x, Robj (toR val) :: map Zobj idxs)) ->
  forall idxs name val idx_ctx idx_ctx',
    result_lookup_Z' idxs r val ->
    Forall2 (interp_expr interp_fn) (map (subst_in_expr (substn_of v)) (map lower_idx (map fst idx_ctx))) idx_ctx' ->
        prog_impl_fact interp_fn (lower e out name idx_ctx ++ datalog_ctx ++ [true_rule; false_rule]) (out, Robj (toR val) :: idx_ctx' ++ map Zobj idxs).
Proof.
  revert out sh v ctx r datalog_ctx l. induction e. 
  { simpl. intros. apply invert_eval_gen in H.
    destruct H as (loz&hiz&rl&Hrl&Hlen&Hlo&Hhi&Hbody). subst.
    move IHe at bottom. invert H3. move Hbody at bottom. specialize (Hbody (loz + x)%Z).
    epose proof nth_error_Some as E'. specialize E' with (1 := H6).
    specialize (Hbody ltac:(lia)). clear E'.
    destruct Hbody as (Hdom&_&Hbody). replace (loz + x - loz)%Z with x in Hbody by lia.
    rewrite H6 in Hbody. specialize IHe with (1 := Hbody). invert H0.
    destruct H1 as (_&_&_&H1).
    specialize IHe with (1 := H11) (2 := H1) (3 := H2).
    specialize IHe with (1 := H8). eassert _ as blah.
    2: epose proof (IHe _ _ (idx_ctx ++ [((! i ! - lo)%z, (hi - lo)%z)])%list _ blah) as IHe_; clear IHe.
    { repeat rewrite map_app. apply Forall2_app.
      - move H4 at bottom. repeat rewrite <- Forall2_map_l in *.
        eapply Forall2_impl. 2: eassumption. simpl. intros a b Hab.
        pose proof interp_expr_subst_more as Hab'. specialize Hab' with (2 := Hab).
        rewrite Hab'. 1: assumption. apply includes_extends.
        apply includes_add_new. apply None_dom_lookup. assumption.
      - repeat constructor. simpl. rewrite lookup_add_eq by reflexivity.
        simpl. repeat econstructor.
        { Search lo. apply eval_Zexpr_Z_eval_Zexpr in Hlo.
          pose proof eval_Zexpr_to_substn as H'. specialize H' with (1 := Hlo).
          repeat econstructor.
          + pose proof interp_expr_subst_more as H''. specialize H'' with (2 := H').
            rewrite H''. 1: eassumption. clear -Hdom. apply includes_extends.
          Search includes. apply includes_add_new. Search (_ $? _ = None).
          apply None_dom_lookup. assumption. }
        reflexivity. }
    rewrite <- app_assoc in IHe_. simpl in IHe_.
    replace (loz + x - loz)%Z with x in IHe_ by lia. simpl. apply IHe_. }
  12: { intros. simpl. destruct (lower_Sexpr O s) as [ [val0 hyps] name'] eqn:E.
        simpl. inversion H. subst. clear H. pose proof lower_Sexpr_correct as H'.
        specialize H' with (1 := H2) (2 := H8) (3 := E).
        destruct H' as (hyps'&substn&_&Hsubstn&Hhyps&Hhyps'&Hval0).
        invert H3. econstructor.
        { constructor. simpl. exists (compose substn (substn_of v)). split.
          - cbv [subst_in_fact]. simpl. constructor. simpl. repeat constructor.
            + rewrite subst_in_expr_subst_in_expr in Hval0. apply Hval0.
            + rewrite app_nil_r. move H4 at bottom.
              repeat rewrite <- Forall2_map_l in *. eapply Forall2_impl. 2: eassumption.
              simpl. intros a b Hab. pose proof interp_expr_subst_more as Hab'.
              specialize Hab' with (2 := Hab). rewrite Hab'. 1: assumption.
              apply compose_extends_r.
          - rewrite map_map in Hhyps. erewrite map_ext. 1: eassumption.
            simpl. intros. rewrite subst_in_fact_subst_in_fact. reflexivity. }
        intros. eapply prog_impl_fact_subset.
        2: { rewrite Forall_forall in Hhyps'. apply Hhyps'. assumption. }
        simpl. intros. rewrite in_app_iff. auto. }
  { intros.
    pose proof dimensions_right as H'.
    specialize (H' _ _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    invert H0. simpl in H1. destruct H1 as (_&_&H1).
    specialize IHe with (2 := H10) (3 := H1) (4 := H2).
    apply invert_eval_sum in H.
    destruct H as (loz&hiz&summands&Hlen&Hloz&Hhiz&Hsummands&Hbody).
    specialize Hsummands with (1 := H3). destruct Hsummands as (ss&Hs&Hss).
    pose proof dim_idxs as H''. specialize (H'' _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    apply size_of_sizeof in H10. subst. clear H'.
    set (s := compose
                (substn_of v)
                (map_cons
                   (inr (length idxs)) (Some (fn_R (fn_SLit (toR val))))
                   (idx_map (map (fun x => fn_Z (fn_ZLit x)) idxs)))).
    econstructor.
    - simpl. apply Exists_app. left. apply Exists_app. simpl. right.
      apply Exists_cons_tl. apply Exists_cons_tl. constructor. simpl.
      exists s.
      simpl. cbv [subst_in_fact]. simpl. split.
      { constructor. simpl. constructor.
        { subst s. cbv [compose map_cons]. simpl. rewrite H'', Nat.eqb_refl. repeat econstructor. }
        rewrite map_app. apply Forall2_app.
        - repeat rewrite <- Forall2_map_l in *. eapply Forall2_impl. 2: eassumption.
          simpl. intros a b Hab. eapply interp_expr_subst_more'. 2: eassumption.
          extends_solver. apply disj_comm.
          eapply domain_in_ints_disj_substn_of with (low := 0) (high := Datatypes.S (length idxs)).
          apply domain_in_ints_cons.
          + eapply domain_in_ints_weaken. 3: apply domain_in_ints_idx_map. 1: lia.
            rewrite map_length. lia.
          + lia.
        - rewrite <- H''. apply gross1. }
      constructor. 2: constructor. constructor. simpl. constructor.
      { subst s. cbv [compose map_cons]. simpl. rewrite H'', Nat.eqb_refl. repeat econstructor. }
      constructor.
      { Search lower_idx. apply eval_Zexpr_Z_eval_Zexpr in Hhiz, Hloz.
        apply eval_Zexpr_to_substn in Hhiz, Hloz. repeat econstructor.
        + eapply interp_expr_subst_more'. 2: eassumption. apply gross2.
        + eapply interp_expr_subst_more'. 2: eassumption. apply gross2.
        + simpl. reflexivity. }
      rewrite <- H''. apply gross1.
    - apply Forall_forall. constructor; [|constructor]. simpl.
      assert (Hor: (hiz < loz \/ hiz = loz + Z.of_nat (length ss))%Z).
      { subst. apply Forall2_length in Hs. rewrite <- Hs. lia. }
      destruct Hor as [weird|normal].
      { replace (Z.max loz hiz) with loz by lia. econstructor.
        replace (Z.to_nat _) with O in Hlen by lia.
        destruct summands; [|discriminate Hlen]. invert Hs. simpl in Hss.
        rewrite Hss in *.
        - apply Exists_app. left. apply Exists_app. right. simpl.
          apply Exists_cons_hd. simpl.
          exists s. cbv [subst_in_fact]. simpl. split; [|constructor]. constructor.
          simpl. constructor.
          { repeat econstructor. }
          apply eval_Zexpr_Z_eval_Zexpr in Hhiz, Hloz.
          apply eval_Zexpr_to_substn in Hhiz, Hloz.
          constructor.
          { eapply interp_expr_subst_more'. 2: eassumption. apply gross2. }
          rewrite <- H''. apply gross1.
        - apply Forall_forall. constructor. }
      subst.
      move Hss at bottom. rewrite Hss. clear H3 Hss val s.
      replace ss with (firstn (length ss) ss).
      2: { apply firstn_all. }
      rewrite firstn_length. rewrite min_id.
      set (n := length ss).
      replace (Z.max loz (loz + Z.of_nat n)) with (loz + Z.of_nat n)%Z by lia.
      apply eval_Zexpr_Z_eval_Zexpr in Hhiz, Hloz.
      apply eval_Zexpr_to_substn in Hhiz, Hloz.
      assert (Hn: n <= length ss) by lia. clearbody n. revert Hn.
      induction n.
      + econstructor.
        -- apply Exists_app. left. apply Exists_app. right. simpl. Print Exists.
           apply Exists_cons_hd. simpl.
           (*need to handle the case that hi < lo...*)
           (*amusingly, having constant_nonneg_bounds as a hypothesis would not help;
             it only restricts generator bounds to be nonnegative.*)
           (*two choices: either do some guard with booleans,
             or else have the upper bound be Z.max lo hi instead of hi*)
           (*nope actually i should just use the constant_nonneg_bounds hypothesis,
            which does help!  constant bounds allows us to check at compile time whether
            hi < lo.*)
           (*TODO: for now i'll just stick with the code that works for arbitaryr bounds*)
           eset (s := compose
                       (substn_of v)
                       (map_cons
                          (inr (length idxs)) (Some (fn_R (fn_SLit _)))
                          (idx_map (map (fun x => fn_Z (fn_ZLit x)) idxs)))).
           exists s. split; [|constructor].
           cbv [subst_in_fact]. simpl. replace (loz + 0)%Z with loz by lia.
           constructor. constructor.
           { repeat econstructor. }
           constructor.
           { eapply interp_expr_subst_more'; [|eassumption]. apply gross2. }
           rewrite <- H''. apply gross1.
        -- apply Forall_forall. constructor.
      + intros Hn. assert (Hs': (exists a, nth_error ss n = Some a /\
                                        firstn (S n) ss = firstn n ss ++ [a])%list).
        { replace (S n) with (n + 1) by lia. Search (firstn (_ + _)).
          rewrite firstn_add.
          replace (nth_error ss n) with (nth_error ss (n + O)) by (f_equal; lia).
          rewrite <- nth_error_skipn. destruct (skipn n ss) eqn:E.
          { eassert (blah: forall x y, x = y -> length x = length y) by (intros; subst; auto).
            apply blah in E. rewrite skipn_length in E. simpl in E. lia. }
          simpl. eexists. split; [reflexivity|]. reflexivity. }
        destruct Hs' as (a & Ha & Hs').
        econstructor.
        -- apply Exists_app. left. apply Exists_app. right. apply Exists_cons_tl.
           apply Exists_cons_hd. rewrite Hs' in *. simpl.
           set (s := map_cons
                       (*x := accumulated sum*)
                       (inr (length idxs)) (Some (fn_R (fn_SLit (fold_right Rplus 0 (map toR (firstn n ss)))%R)))
                       (map_cons
                          (*i' := summation index*)
                          (inr (S (length idxs))) (Some (fn_Z (fn_ZLit (loz + Z.of_nat n))))
                          (map_cons
                             (*y := new addend*)
                             (inr (S (S (length idxs)))) ((Some (fn_R (fn_SLit (toR a)))))
                             (idx_map (map (fun x => fn_Z (fn_ZLit x)) idxs))))).
           assert (fact1: Forall2 (interp_expr interp_fn)
                            (map (subst_in_expr s) (map var_expr (map inr (seq 0 (length (sizeof e))))))
                            (map Zobj idxs)).
           { apply Forall2_nth_error.
             { repeat rewrite map_length. rewrite seq_length. auto. }
             intros n0 x1 x2. repeat rewrite nth_error_map. intros.
             do 4 destruct_option_map_Some. apply nth_error_seq_Some in E0.
             simpl in E0. subst s. subst. simpl.
             epose proof nth_error_Some as H00. specialize (H00 _ _ _ ltac:(eassumption)).
             simpl_map_cons. cbv [idx_map].
             rewrite nth_error_map. rewrite E. simpl. repeat econstructor. }
           exists s. split.
           ++ simpl. constructor. simpl. constructor.
              { simpl. subst s. simpl. cbv [map_cons]. rewrite <- H''.
                repeat rewrite var_eqb_refl. cbv [var_eqb]. simpl.
                replace (_ =? _)%nat with false.
                2: { symmetry. apply Nat.eqb_neq. lia. }
                replace (_ =? _)%nat with false.
                2: { symmetry. apply Nat.eqb_neq. lia. }
                repeat econstructor. simpl. rewrite map_app.
                (*shouldn't really have to rely on commutativity or associativity here...*)
                rewrite <- fold_symmetric; [|intros; ring|intros; ring].
                rewrite <- fold_symmetric; [|intros; ring|intros; ring].
                rewrite fold_left_app. rewrite Rplus_comm. reflexivity. }
              constructor.
              { repeat econstructor.
                - subst s. rewrite <- H''. simpl_map_cons. repeat econstructor.
                - simpl. f_equal. f_equal. lia. }
              apply fact1.              
           ++ cbv [subst_in_fact]. simpl. subst s.
              rewrite <- H''. simpl_map_cons. constructor.
              { constructor. simpl. constructor.
                { repeat econstructor. }
                constructor.
                { repeat econstructor. }
                rewrite <- H'' in *. apply fact1. }
              constructor.
              { constructor. simpl. repeat econstructor. repeat rewrite <- H'' in *.
                apply fact1. }
              constructor.
        -- apply Forall_forall. simpl. constructor.
           { remember (_ ++ _)%list as ll. apply IHn. lia. }
           clear IHn. constructor. 
           { specialize (Hbody (loz + Z.of_nat n)%Z ltac:(lia)).
             destruct Hbody as (_&_&Hbody).
             epose proof nth_error_Forall2_r as H'.
             specialize H' with (1 := Hs) (2 := Ha). destruct H' as (s1&Hs1&Hs2).
             replace (Z.to_nat _) with n in Hbody by lia. rewrite Hs1 in Hbody.
             specialize IHe with (1 := Hbody) (2 := Hs2).
             specialize IHe with (idx_ctx := [((! i !)%z, (hi - lo)%z)]).
             simpl in IHe. Search ((_ $+ (_, _)) $? _). rewrite lookup_add_eq in IHe by reflexivity.
             eassert _ as blah. 2: epose proof (IHe _ _ _ blah) as IH; clear IHe.
             { simpl. repeat econstructor. }
             simpl in IH. eapply prog_impl_fact_subset.
             2: { apply IH. }
             intros x Hx. apply in_app_iff. apply in_app_iff in Hx.
             destruct Hx as [Hx|Hx].
             ++ left. apply in_app_iff. left. eassumption.
             ++ right. assumption. }
           constructor. }
  Unshelve. 11: exact (SS 0).
  { simpl. intros. invert H0.
    pose proof dimensions_right as H'. 
    pose proof dim_idxs as H''.
    invert H.
    - specialize (H'' _ _ _ _ ltac:(eauto using dim_gen_pad) ltac:(eassumption)).
      rewrite map_length in H''.
      pose proof length_eval_Zexprlist as H'''.
      specialize (H''' _ _ _ ltac:(eassumption)). rewrite <- H''' in H''. clear H'''.
      apply size_of_sizeof in H8, H10. rewrite H8 in H10. invert H10.
      apply pad_lookup_SX in H3. subst. simpl. econstructor.
      { apply Exists_app. left. apply Exists_app. right. apply Exists_cons_tl.
        apply Exists_cons_hd. simpl.
        exists (compose (substn_of v) (idx_map (map (fun x => fn_Z (fn_ZLit x)) idxs))).
        cbv [subst_in_fact]. simpl. constructor.
        - constructor. simpl. constructor.
          { repeat econstructor. }
          repeat rewrite map_app. apply Forall2_app.
          + repeat rewrite <- Forall2_map_l in *. eapply Forall2_impl; [|eassumption].
            simpl. intros a b Hab. eapply interp_expr_subst_more'; [|eassumption].
            extends_solver.
          + rewrite <- H''. pose proof idx_map_works idxs as Hidxs.
            repeat rewrite <- Forall2_map_l in *.
            eapply Forall2_impl; [|eassumption]. cbv beta. intros a b Hab.
            eapply interp_expr_subst_more'; [|eassumption]. extends_solver.
        - repeat econstructor. eapply interp_expr_subst_more'.
          2: { apply eval_Bexpr_to_substn. eassumption. }
          extends_solver. }
      apply Forall_forall. constructor.
      { econstructor.
        { apply Exists_app. right. apply Exists_app. right. apply Exists_cons_tl.
          apply Exists_cons_hd. simpl. exists map_empty. split; [|constructor].
          constructor. simpl. repeat econstructor. }
        apply Forall_forall. constructor. }
      constructor.
    - specialize (H' _ _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
      specialize (H'' _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
      pose proof size_of_sizeof as H7'. specialize (H7' _ _ ltac:(eassumption)).
      subst. clear H'. rewrite <- H''. clear H''.
      econstructor.
      { apply Exists_app. left. apply Exists_app. right. apply Exists_cons_hd.
        exists (map_cons (inr (length idxs)) (Some (fn_R (fn_SLit (toR val))))
             (compose (substn_of v) (idx_map (map (fun x => fn_Z (fn_ZLit x)) idxs)))).
        simpl. cbv [subst_in_fact]. cbn -[subst_in_expr]. split.
        { constructor. simpl. rewrite map_cons_something. constructor.
          { repeat econstructor. }
          repeat rewrite map_app. apply Forall2_app.
          - repeat rewrite <- Forall2_map_l in *. eapply Forall2_impl; [|eassumption].
            cbv beta. intros a b Hab. eapply interp_expr_subst_more'; [|eassumption].
            extends_solver.
          - pose proof idx_map_works idxs as H'. repeat rewrite <- Forall2_map_l in *.
            eapply Forall2_impl; [|eassumption]. cbv beta. intros a b Hab.
            eapply interp_expr_subst_more'; [|eassumption]. extends_solver. }
        constructor.
        { constructor. simpl. rewrite map_cons_something. constructor.
          { repeat econstructor. }
          (*copy-pasted*)
          pose proof idx_map_works idxs as H'. repeat rewrite <- Forall2_map_l in *.
          eapply Forall2_impl; [|eassumption]. cbv beta. intros a b Hab.
          eapply interp_expr_subst_more'; [|eassumption]. extends_solver. }
        repeat econstructor. eapply interp_expr_subst_more'.
        2: { apply eval_Bexpr_to_substn. eassumption. }
        extends_solver. }
      apply Forall_forall. constructor.
      { simpl.
        specialize IHe with (name := S name) (idx_ctx := nil) (idx_ctx' := nil).
        simpl in IHe.
        eapply prog_impl_fact_subset.
        2: { eapply IHe; eauto. }
        intros x Hx. repeat rewrite in_app_iff in *. simpl. tauto. }
      constructor.
      { simpl. econstructor.
        { apply Exists_app. right. apply Exists_app. right. apply Exists_cons_hd.
          exists map_empty. repeat econstructor. }
        apply Forall_forall. constructor. }
      constructor. }
  { simpl. intros. destruct H1 as (H1&H1_). invert H0. invert H.
    - eapply prog_impl_fact_subset.
      2: { eapply IHe2 with (name := name); eauto. intros * H1' H2'. 
           apply lookup_split in H1'. destruct H1' as [(H1'&H3')|(H1'&H3')].
           2: { subst.
                specialize IHe1 with (name := name) (idx_ctx := nil) (idx_ctx' := nil).
                simpl in IHe1. eapply IHe1; eauto. }
           eapply prog_impl_fact_subset. 2: eauto. intros.
           repeat rewrite in_app_iff. simpl. tauto. }
      intros. repeat rewrite in_app_iff in *. tauto.
    - (*copy-pasted*)
      eapply prog_impl_fact_subset.
      2: { eapply IHe2 with (name := name); eauto. intros * H1' H2'. 
           apply lookup_split in H1'. destruct H1' as [(H1'&H3')|(H1'&H3')].
           2: { subst.
                specialize IHe1 with (name := name) (idx_ctx := nil) (idx_ctx' := nil).
                simpl in IHe1. eapply IHe1; eauto. }
           eapply prog_impl_fact_subset. 2: eauto. intros.
           repeat rewrite in_app_iff. simpl. tauto. }
      intros. repeat rewrite in_app_iff in *. tauto. }
  { simpl. intros. destruct H1 as (He1&He2). invert H0. invert H.
    pose proof ResultToArrayDelta.constant_nonneg_bounds_size_of_eval_expr_result_has_shape as He1'.
    specialize He1' with (1 := He1). specialize (He1' _ ltac:(eassumption) _ _ _ _ ltac:(eassumption)).
    pose proof ResultToArrayDelta.constant_nonneg_bounds_size_of_eval_expr_result_has_shape as He2'.
    specialize He2' with (1 := He2). specialize (He2' _ ltac:(eassumption) _ _ _ _ ltac:(eassumption)).
    apply result_has_shape_length in He1', He2'.
    invert H3.
    pose proof dimensions_right as H'.
    pose proof dim_idxs as H''.
    assert (Hidx: Z.to_nat x < length l0 \/ length l0 <= Z.to_nat x) by lia.
    pose proof size_of_sizeof as H6'. specialize H6' with (1 := H6). rewrite H6'. clear H6'.
    destruct Hidx as [Hidx|Hidx].
    - rewrite nth_error_app1 in H1 by assumption.
      specialize (H' _ _ _ e1 _ _ ltac:(eassumption) ltac:(eassumption)).
      simpl in H'. 
      specialize H'' with (1 := H'). clear H'.
      eassert _ as blah. 2: epose proof (H'' _ _ blah) as H'; clear H''.
      { econstructor; eassumption. }
      simpl in H'. cbn [length]. rewrite <- H'.
      econstructor. apply Exists_app. left. apply Exists_app. right. apply Exists_app.
      right. apply Exists_cons_hd.
      { cbn -[seq].
        set (s := map_cons (inr (S (length xs))) (Some (fn_R (fn_SLit (toR val)))) (compose (substn_of v) (idx_map (map (fun x => fn_Z (fn_ZLit x)) (x :: xs))))).
        exists s.
        cbv [subst_in_fact]. cbn -[seq]. split.
        - simpl. constructor. constructor.
           { cbv [s]. rewrite map_cons_something. repeat econstructor. } 
          repeat rewrite map_app. apply Forall2_app.
          + move H4 at bottom. repeat rewrite <- Forall2_map_l in *.
            eapply Forall2_impl; [|eassumption]. cbv beta. intros a b Hab.
            eapply interp_expr_subst_more'; [|eassumption]. extends_solver.
          + pose proof idx_map_works (x :: xs) as H''.
            simpl. simpl in H''. invert H''. constructor.
            { assumption. }
            repeat rewrite <- Forall2_map_l in *.
            replace (length xs - O) with (length xs) by lia.
            eapply Forall2_impl; [|eassumption]. cbv beta. intros a b Hab.
            eapply interp_expr_subst_more'; [|eassumption]. extends_solver.
        - unfold s at 1. rewrite map_cons_something. constructor; [|solve[constructor]]. constructor.
          cbn [fact_args]. constructor.
          { repeat econstructor. }
          pose proof idx_map_works (x :: xs) as H''.
          simpl in H''. invert H''. constructor; [eassumption|].
          repeat rewrite <- Forall2_map_l in *. replace (_ - 0) with (length xs) by lia.
          eapply Forall2_impl; [|eassumption]. cbv beta. intros a b Hab.
          eapply interp_expr_subst_more'; [|eassumption].
          extends_solver. }
      apply Forall_forall. constructor; [|solve[constructor]]. cbn -[seq].
      eapply prog_impl_fact_subset.
      2: { specialize IHe1 with (name := S (S name)) (idxs := x :: xs) (idx_ctx := nil) (idx_ctx' := nil).
           simpl in IHe1. eapply IHe1; eauto. }
      intros. repeat rewrite in_app_iff in *. tauto.
    - rewrite nth_error_app2 in H1 by assumption.
      specialize (H' _ _ _ e2 _ _ ltac:(eassumption) ltac:(eassumption)).
      simpl in H'. 
      specialize H'' with (1 := H'). clear H'.
      eassert _ as blah. 2: epose proof (H'' _ _ blah) as H'; clear H''.
      { econstructor. 3: eassumption.
        2: { rewrite Nat2Z.id. eassumption. }
        lia. }
      clear blah.
      simpl in H'. cbn [length].
      specialize (H9 $0).
      eassert (blah: forall x y, x = y -> length x = length y) by (intros; subst; reflexivity).
      apply blah in H9. clear blah. do 2 rewrite map_length in H9. rewrite <- H9 in H'.
      clear H9. rewrite <- H'. clear H'.
      econstructor.
      { apply Exists_app. left. apply Exists_app. right. apply Exists_app.
        right. apply Exists_cons_tl. apply Exists_cons_hd.
      { cbn -[seq].
        exists (map_cons (inr (S (length xs))) (Some (fn_R (fn_SLit (toR val)))) (compose (substn_of v) (idx_map (map (fun x => fn_Z (fn_ZLit x)) ((x - Z.of_nat (length l0))%Z :: xs))))).
        cbv [subst_in_fact]. cbn -[seq]. split.
        - constructor. cbn -[seq]. constructor.
          { rewrite map_cons_something. repeat econstructor. } 
          repeat rewrite map_app. apply Forall2_app.
          + move H4 at bottom. repeat rewrite <- Forall2_map_l in *.
            eapply Forall2_impl; [|eassumption]. cbv beta. intros a b Hab.
            eapply interp_expr_subst_more'; [|eassumption].
            
            eapply extends_trans.
            { apply extends_map_cons. cbv [compose].
              destruct (idx_map _ _) eqn:E.
              - apply domain_in_ints_idx_map in E. simpl in E. rewrite map_length in E. lia.
            - reflexivity. }
            apply compose_extends_l. Search disj. apply disj_comm. Search disj.
            eapply domain_in_ints_disj_substn_of. apply domain_in_ints_idx_map.
          + pose proof idx_map_works (x - Z.of_nat (length l0) :: xs)%Z as H''.
            simpl in H''. simpl. invert H''. constructor.
            { repeat econstructor. simpl. f_equal. f_equal. lia. }
            repeat rewrite <- Forall2_map_l in *.
            replace (length xs - 0) with (length xs) by lia.
            eapply Forall2_impl_in_l; [|eassumption]. cbv beta. intros a b Ha Hab.
            eapply interp_expr_subst_more'; [|eassumption]. extends_solver.
        - constructor.
          { constructor. simpl. rewrite map_cons_something. constructor.
            { repeat econstructor. }
            constructor.
            { repeat econstructor. }
            pose proof idx_map_works (x - Z.of_nat (length l0) :: xs)%Z as H''.
            simpl in H''. simpl. invert H''.
            repeat rewrite <- Forall2_map_l in *.
            replace (length xs - 0) with (length xs) by lia.
            eapply Forall2_impl_in_l; [|eassumption]. cbv beta. intros a b Ha Hab.
            eapply interp_expr_subst_more'; [|eassumption].
            extends_solver. }
          constructor. } }
      apply Forall_forall. constructor; [|solve[constructor]].
      simpl.
      eapply prog_impl_fact_subset.
      2: { specialize IHe2 with (name := S (S name)) (idxs := (x - Z.of_nat (length l0) :: xs)%Z) (idx_ctx := nil) (idx_ctx' := nil).
           simpl in IHe2. eapply IHe2; eauto.
           econstructor. 1: lia. 2: eassumption. rewrite <- H1. f_equal. lia. }
      intros. repeat rewrite in_app_iff in *. tauto. }
  { simpl. intros. invert H. invert H0.
    pose proof ResultToArrayDelta.constant_nonneg_bounds_size_of_eval_expr_result_has_shape as He.
    specialize (He _ _ ltac:(eassumption) ltac:(eassumption) _ _ _ _ ltac:(eassumption)).
    simpl in He. Search flatten_result.
    Search (nth_error (flatten_result _)).
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
    assert (0 < Z.to_nat (eval_Zexpr_Z_total $0 m)).
    { destruct (Z.to_nat (eval_Zexpr_Z_total $0 m)); [|lia]. clear -H7 H10.
      induction l0.
      - simpl in H7. rewrite nth_error_empty in H7. discriminate H7.
      - simpl in H7. invert H10. invert H1. destruct xs; [|discriminate H3].
        simpl in H7. auto. }
    eassert (nth_error _ _ = Some _) as H''. 2: erewrite H' in H''; cycle 1.
    { rewrite <- H7. f_equal. rewrite Div.div_mod_eq. 1: reflexivity. lia. }
    { Search (0 <= _ / _)%Z. apply Z_div_nonneg_nonneg; lia. }
    { apply nth_error_Some in H''. erewrite length_flatten_result in H''.
      2: { constructor; eassumption. }
      remember (Z.to_nat (eval_Zexpr_Z_total $0 m)) as m'.
      remember (Z.to_nat (eval_Zexpr_Z_total $0 n)) as n'.
      assert (0 <= x / Z.of_nat m')%Z.
      { Search (0 <= _ / _)%Z. apply Z_div_nonneg_nonneg; lia. }
      assert (0 <= x mod Z.of_nat m')%Z.
      { Search (0 <= _ mod _)%Z. apply mod_nonneg. lia. }
      assert (H''': Z.to_nat (x / Z.of_nat m' * Z.of_nat m') < n' * m') by lia.
      clear H''.
      Search (Z.to_nat (_ * _)). rewrite Z2Nat.inj_mul in H''' by lia.
      rewrite Z2Nat.inj_div in H''' by lia.
      replace (Z.to_nat (Z.of_nat m')) with m' in H''' by lia. Search (_ * _ < _ * _).
      rewrite <- mul_lt_mono_pos_r in H''' by lia. Search (Z.to_nat _ <= Z.to_nat _).
      rewrite Z2Nat.inj_lt by lia. rewrite Z2Nat.inj_div by lia.
      Search  (Z.to_nat (Z.of_nat _)). do 2 rewrite Nat2Z.id. assumption. }
    { Search (0 <= _ mod _)%Z. apply mod_nonneg. lia. }
    { Search (_ mod _ < _)%Z. apply Div.mod_upper_bound. lia. }
    destruct (nth_error l0 _) eqn:E; [|discriminate H''].
    destruct r; [discriminate H''|].
    econstructor.
    { apply Exists_app. left. apply Exists_app. right. apply Exists_cons_hd. simpl.
      pose proof size_of_sizeof as H'''. specialize (H''' _ _ ltac:(eassumption)).
      rewrite H'''. simpl. replace (length l1 - 0) with (length l1) by lia. clear H'.
      eset (s := map_cons (inr (S (S (length l1)))) (Some (fn_R (fn_SLit _)))
                   (map_cons (inr (S (length l1))) (Some (fn_Z (fn_ZLit _)))
                      (map_cons (inr (length l1)) (Some (fn_Z (fn_ZLit _)))
                  (compose (substn_of v) (idx_map (map (fun x => fn_Z (fn_ZLit x)) xs)))))).
      exists s. cbv [subst_in_fact]. simpl. constructor.
      { constructor. simpl. unfold s at 1. rewrite map_cons_something. constructor.
        { repeat econstructor. }
        rewrite map_app. apply Forall2_app.
        - repeat rewrite <- Forall2_map_l in *.
          eapply Forall2_impl; [|eassumption]. cbv beta. intros a b Hab.
          eapply interp_expr_subst_more'; [|eassumption]. extends_solver.
        - simpl. constructor.
          { econstructor.
            { constructor.
              { cbv [s]. simpl_map_cons. repeat econstructor. }
              cbv [s]. simpl_map_cons. repeat econstructor. }
            simpl. rewrite Div.div_mod_eq. 1: reflexivity. lia. }
          pose proof idx_map_works xs as Him. rewrite <- H3.
          repeat rewrite <- Forall2_map_l in *.
          eapply Forall2_impl; [|eassumption]. cbv beta. intros a b Hab.
          eapply interp_expr_subst_more'; [|eassumption].
          extends_solver. }
      constructor; [|solve[constructor]].
      constructor. simpl. unfold s at 1. unfold s at 1. unfold s at 1.
      simpl_map_cons. constructor.
      { repeat econstructor. }
      constructor.
      { repeat econstructor. }
      constructor.
      { repeat econstructor. }
      pose proof idx_map_works xs as Him. rewrite <- H3.
      repeat rewrite <- Forall2_map_l in *.
      eapply Forall2_impl; [|eassumption]. cbv beta. intros a b Hab.
      eapply interp_expr_subst_more'; [|eassumption].
      extends_solver. }
    apply Forall_forall. simpl. constructor; [|solve[constructor]].
    eapply prog_impl_fact_subset.
    2: { move IHe at bottom. eset (idxs := _ :: _ :: _: list Z).
         specialize IHe with (name := S name) (idxs := idxs). subst idxs. simpl in IHe.
         specialize IHe with (idx_ctx := nil) (idx_ctx' := nil). simpl in IHe.
         eapply IHe; eauto. econstructor.
         { Search (0 <= _ / _)%Z. apply Z_div_nonneg_nonneg; lia. }
         { eassumption. }
         econstructor.
         { Search (0 <= _ mod _)%Z. apply mod_nonneg. lia. }
         { eassumption. }
         eassumption. }
    intros. repeat rewrite in_app_iff in *. tauto. }
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
  | Truncr n e =>
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
