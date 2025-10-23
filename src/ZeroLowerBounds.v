From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
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

From Datalog Require Import Datalog RevRel Dag Map List Tactics Interpreter QueryableToRunnable. 
From coqutil Require Import Map.Interface Map.Properties Map.Solver Map.OfFunc Tactics.fwd Tactics.destr Tactics Decidable.

Import Datatypes.

Open Scope list_scope.


(*I can't have arbitrary Zexprs in idxs of conclusion.  Two options to accomplish this:
  1) zero out lower bounds of gens and sums
  2) leave the lower bounds as they are, but index into arrays starting from lb instead of zero-indexing.

  (2) seems obnoxious for gens, but fine for sums.  I will use approach (2) for sums and (1) for sums.
 *)

Section __.
Context {valuation' : map.map Var.var Z} {valuation'_ok : map.ok valuation'}.
Context {str_nat : map.map string nat} {str_nat_ok : map.ok str_nat}.
Context {str_Zexpr : map.map string Zexpr} {str_Zexpr_ok : map.ok str_Zexpr}.

Fixpoint subst_vars_in_Zexpr substn e :=
  match e with
  | ZPlus e1 e2 => ZPlus (subst_vars_in_Zexpr substn e1) (subst_vars_in_Zexpr substn e2)
  | ZMinus e1 e2 => ZMinus (subst_vars_in_Zexpr substn e1) (subst_vars_in_Zexpr substn e2)
  | ZTimes e1 e2 => ZTimes (subst_vars_in_Zexpr substn e1) (subst_vars_in_Zexpr substn e2)
  | ZDivf e1 e2 => ZDivf (subst_vars_in_Zexpr substn e1) (subst_vars_in_Zexpr substn e2)
  | ZDivc e1 e2 => ZDivc (subst_vars_in_Zexpr substn e1) (subst_vars_in_Zexpr substn e2)
  | ZMod e1 e2 => ZMod (subst_vars_in_Zexpr substn e1) (subst_vars_in_Zexpr substn e2)
  | ZLit x => ZLit x
  | ZVar v => match substn v with
             | Some ev => ev
             | None => ZVar v
             end
  end.

Fixpoint map_Zexprs_in_Bexpr f e :=
  match e with
  | Bexpr.And x y => Bexpr.And (map_Zexprs_in_Bexpr f x) (map_Zexprs_in_Bexpr f y)
  | Bexpr.Lt x y => Bexpr.Lt (f x) (f y)
  | Bexpr.Le x y => Bexpr.Le (f x) (f y)
  | Bexpr.Eq x y => Bexpr.Eq (f x) (f y)
  end.

Lemma map_Zexprs_in_Bexpr_same ctx ctx' e e' f :
  (forall ze ze', eval_Zexpr ctx ze ze' ->
             eval_Zexpr ctx' (f ze) ze') ->
  eval_Bexpr ctx e e' ->
  eval_Bexpr ctx' (map_Zexprs_in_Bexpr f e) e'.
Proof.
  induction 2; simpl; econstructor; eauto.
Qed.

Fixpoint map_Zexprs_in_Sexpr f e :=
  match e with
  | Var x => Var x
  | Get x idxs => Get x (map f idxs)
  | Mul x y => Mul (map_Zexprs_in_Sexpr f x) (map_Zexprs_in_Sexpr f y)
  | Div x y => Div (map_Zexprs_in_Sexpr f x) (map_Zexprs_in_Sexpr f y)
  | Add x y => Add (map_Zexprs_in_Sexpr f x) (map_Zexprs_in_Sexpr f y)
  | Sub x y => Sub (map_Zexprs_in_Sexpr f x) (map_Zexprs_in_Sexpr f y)
  | Lit x => Lit x
  end.

Lemma map_Zexprs_in_Sexpr_same sh ectx ctx ctx' e e' f :
  (forall ze ze', eval_Zexpr ctx ze ze' ->
             eval_Zexpr ctx' (f ze) ze') ->
  eval_Sexpr sh ctx ectx e e' ->
  eval_Sexpr sh ctx' ectx (map_Zexprs_in_Sexpr f e) e'.
Proof.
  induction 2; simpl; try econstructor; eauto.
  - rewrite length_map. assumption.
  - (*it'd be nice if eval_get were characterized in terms of eval_Zexprlist*)
    clear -H3 H.
    (*this is confusing and magical.  somehow solve makes econstructor pick the right constructor.  that is, induction H3; econstructor; eauto leaves goals unsolved*)
    induction H3; solve [econstructor; eauto].
Qed.

Lemma subst_vars_in_Zexpr_correct ctx ctx' e e' substn :
  (forall v v',
      ctx $? v = Some v' ->
      match substn v with
      | Some ve => eval_Zexpr ctx' ve v'
      | None => ctx' $? v = Some v'
      end) ->
  eval_Zexpr ctx e e' ->
  eval_Zexpr ctx' (subst_vars_in_Zexpr substn e) e'.
Proof.
  induction 2; simpl; try solve [econstructor; eauto].
  apply H in H0. destruct (substn _) eqn:E; eauto.
Qed.

Definition ctxs_correspond offsets ctx ctx' :=
  forall v v',
    ctx $? v = Some v' ->
    match map.get offsets v with
    | Some lo => exists v0' lo', ctx' $? v = Some v0' /\
                             eval_Zexpr ctx' lo lo' /\
                             (v' = v0' - lo')%Z
    | None => ctx' $? v = Some v'
    end.

Definition offset_Zexpr offsets e :=
  subst_vars_in_Zexpr (fun i => option_map (fun lo => ZMinus (ZVar i) lo) (map.get offsets i)) e.

Lemma offset_Zexpr_correct offsets ctx ctx' e e' :
  ctxs_correspond offsets ctx ctx' ->
  eval_Zexpr ctx e e' ->
  eval_Zexpr ctx' (offset_Zexpr offsets e) e'.
Proof.
  intros H1 H2. cbv [offset_Zexpr]. eapply subst_vars_in_Zexpr_correct; eauto.
  intros v v' Hv. apply H1 in Hv. destruct (map.get offsets v); fwd; simpl; eauto.
Qed.  

Fixpoint zero_lbs_rec offsets e :=
  let offset := offset_Zexpr offsets in
  match e with
  | Gen i lo hi e1 => Gen i (ZLit 0) (offset (ZMinus hi lo)) (zero_lbs_rec (map.put offsets i lo) e1)
  | Sum i lo hi e1 => Sum i (offset lo) (offset hi) (zero_lbs_rec offsets e1)
  | Guard g e1 => Guard (map_Zexprs_in_Bexpr offset g) (zero_lbs_rec offsets e1)
  | Flatten e1 => Flatten (zero_lbs_rec offsets e1)
  | Split k e1 => Split (offset k) (zero_lbs_rec offsets e1)
  | Transpose e1 => Transpose (zero_lbs_rec offsets e1)
  | Truncr k e1 => Truncr (offset k) (zero_lbs_rec offsets e1)
  | Truncl k e1 => Truncl (offset k) (zero_lbs_rec offsets e1)
  | Padr k e1 => Padr (offset k) (zero_lbs_rec offsets e1)
  | Padl k e1 => Padr (offset k) (zero_lbs_rec offsets e1)
  | Lbind x e1 e2 => Lbind x (zero_lbs_rec offsets e1) (zero_lbs_rec offsets e2)
  | Concat e1 e2 => Concat (zero_lbs_rec offsets e1) (zero_lbs_rec offsets e2)
  | Scalar s => Scalar (map_Zexprs_in_Sexpr offset s)
  end.

Lemma eval_Zexpr_Z_complete z v x :
  eval_Zexpr v z x -> eval_Zexpr_Z v z = Some x.
Proof. rewrite eval_Zexpr_Z_eval_Zexpr. auto. Qed.

Lemma eval_Zexpr_Z_sound z v x :
  eval_Zexpr_Z v z = Some x -> eval_Zexpr v z x.
Proof. rewrite eval_Zexpr_Z_eval_Zexpr. auto. Qed.

Hint Resolve eval_Zexpr_Z_complete eval_Zexpr_Z_sound offset_Zexpr_correct : core.
Hint Resolve map_Zexprs_in_Bexpr_same map_Zexprs_in_Sexpr_same : core.

Hint Extern 2 (_ <= _)%Z => lia : core.
Hint Constructors eval_expr : core.
Hint Constructors size_of : core.
Search (Zexpr -> Zexpr -> Prop).
Search (list Zexpr -> list Zexpr -> Prop). Print eq_Z_index_list. Search eq_Z_index_list.
Search eq_zexpr.
(* e1 is better than e2*)
Definition better_Zexpr e1 e2 :=
  forall ctx e', eval_Zexpr ctx e2 e' -> eval_Zexpr ctx e1 e'.


Lemma zero_lbs_rec_size_of offsets e sh :
  size_of e sh ->
  exists sh',
    (forall lz ctx ctx', ctxs_correspond offsets ctx ctx' ->
                    eval_Zexprlist ctx sh lz ->
                    eval_Zexprlist ctx' sh' lz) /\
      size_of (zero_lbs_rec offsets e) sh'.
Proof.
  intros H. revert offsets. induction H; intros offsets; simpl; eauto.
  - epose_dep IHsize_of. fwd. eexists. split.
    2: { constructor. eassumption. }
    intros. invert H1. constructor; eauto.
    2: { eapply IHsize_ofp0. 2: eassumption. Abort.
    eauto. cbv [better_Zexpr].
    intros. eassert (e' = _) as ->. 2: econstructor; eauto.
    2: { eapply offset_Zexpr_correct. 2: eassumption. econstructor; eauto. 2: constructor. split; [constructor; eauto|].
    eexists. remember (Gen _ _ _). eassert (offset_Zexpr _ _ = _) as ->. 2: subst; econstructor; eauto. Abort.

Opaque offset_Zexpr.
Lemma zero_lbs_rec_correct sh ctx ec e r ctx' offsets :
  eval_expr sh ctx ec e r ->
  ctxs_correspond offsets ctx ctx' ->
  eval_expr sh ctx' ec (zero_lbs_rec offsets e) r.
Proof. Check subst_vars_in_Zexpr_correct.
  intros H. revert ctx' offsets. 
  induction H; intros ctx' offsets Hctx'; simpl; eauto 7.
       - econstructor; simpl; eauto 6.
       - (* :(( *) econstructor; simpl; eauto 6; admit.
       - econstructor; simpl; eauto 6; admit.
       - econstructor; simpl; eauto 6; admit.
       - econstructor; simpl; eauto. all: admit.
       - econstructor; simpl; eauto. all: admit.
       - Search Lbind. eapply EvalLbindV; simpl. ; eauto.
       - eapply EvalGuardTrue; eauto.
