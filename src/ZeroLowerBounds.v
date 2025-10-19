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

Lemma eval_Zexpr_Z_total_complete z v x :
  eval_Zexpr v z x -> eval_Zexpr_Z_total v z = x.
Proof. rewrite eval_Zexpr_Z_eval_Zexpr. cbv [eval_Zexpr_Z_total]. intros H. rewrite H. auto. Qed.

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

Lemma no_vars_of_subst_in_Zexpr substn e :
  vars_of_Zexpr e = [] ->
  vars_of_Zexpr (subst_vars_in_Zexpr substn e) = [].
Proof. Admitted.

Lemma no_vars_of_offset_Zexpr offsets e :
  vars_of_Zexpr e = [] ->
  vars_of_Zexpr (offset_Zexpr offsets e) = [].
Proof. Admitted.

Search eval_Zexpr eval_Zexpr_Z_total.
Lemma no_vars_eval_Zexpr e v :
  vars_of_Zexpr e = [] ->
  eval_Zexpr v e (eval_Zexpr_Z_total $0 e).
Proof. Admitted.

Print ctxs_correspond.
Lemma empty_ctxs_correspond offsets ctx' :
  ctxs_correspond offsets $0 ctx'.
Proof.
  cbv [ctxs_correspond]. intros. rewrite lookup_empty in *. congruence.
Qed. Print constant_nonneg_bounds.

Print constant_nonneg_bounds. Search ZDivc. Locate "//". Search div_ceil nat.

Inductive size_of' : ATLexpr -> list nat -> Prop :=
| SizeOfGen : forall i lo loz hi hiz body sh d,
    size_of' body sh ->
    eval_Zexpr $0 lo loz ->
    eval_Zexpr $0 hi hiz ->
    d = Z.to_nat (hiz - loz) ->
    size_of' (Gen i lo hi body) (d :: sh)
| SizeOfSum : forall i lo hi body sh,
    size_of' body sh ->
    size_of' (Sum i lo hi body) sh
| SizeOfGuard : forall p e sh,
    size_of' e sh ->
    size_of' (Guard p e) sh
| SizeOfLBind : forall e1 e2 x sh2,
    size_of' e2 sh2 ->
    size_of' (Lbind x e1 e2) sh2
| SizeOfConcat : forall e1 e2 l1 l2 n m d,
    size_of' e1 (n::l1) ->
    size_of' e2 (m::l2) ->
    d = n + m ->
    size_of' (Concat e1 e2) (d::l1)
| SizeOfFlatten : forall e n m sh d,
    size_of' e (n :: m :: sh) ->
    d = n * m ->
    size_of' (Flatten e) (d :: sh)
| SizeOfSplit : forall e n sh k kz d1 d2,
    size_of' e (n::sh) ->
    eval_Zexpr $0 k kz ->
    d1 = n //n (Z.to_nat kz) ->
    d2 = Z.to_nat kz ->
    size_of' (Split k e) (d1 :: d2 :: sh)
| SizeOfTranspose : forall e n m sh,
    size_of' e (n::m::sh) ->
    size_of' (Transpose e) (m::n::sh)
| SizeOfTruncr : forall n nz e m sh d,
    size_of' e (m::sh) ->
    eval_Zexpr $0 n nz ->
    d = m - Z.to_nat nz ->
    size_of' (Truncr n e) (d :: sh)
| SizeOfTruncl : forall n nz e m sh d,
    size_of' e (m :: sh) ->
    eval_Zexpr $0 n nz ->
    d = m - Z.to_nat nz ->
    size_of' (Truncl n e) (d :: sh)
| SizeOfPadr : forall n nz e m sh d,
    size_of' e (m :: sh) ->
    eval_Zexpr $0 n nz ->
    d = m + Z.to_nat nz ->
    size_of' (Padr n e) (d :: sh)
| SizeOfPadl : forall n nz e m sh d,
    size_of' e (m :: sh) ->
    eval_Zexpr $0 n nz ->
    d = m + Z.to_nat nz ->
    size_of' (Padl n e) (d :: sh)
| SizeOfScalar : forall s,
    size_of' (Scalar s) [].

Lemma const_size_of_size_of' e sz sh :
  constant_nonneg_bounds e ->
  size_of e sz ->
  eval_Zexprlist $0 sz sh ->
  size_of' e (map Z.to_nat sh).
Proof.
  intros H1 H2. revert H1. revert sh. induction H2; simpl; intros sh Hc He; fwd; try invert1 He; simpl; try solve [econstructor; eauto].
  - invert H3. econstructor; eauto.
  - invert H3. econstructor.
    + eapply (IHsize_of1 (_ :: _)); eauto.
    + eapply (IHsize_of2 (_ :: _)); eauto. constructor; eauto.
      apply forall_no_vars_eval_Zexpr_Z_total.
      eapply constant_nonneg_bounds_size_of_no_vars in Hcp1; [|eauto].
      invert_list_stuff. assumption.
    + eapply constant_nonneg_bounds_size_of_nonneg in Hcp0, Hcp1; eauto.
      2: { econstructor; eauto.
           apply forall_no_vars_eval_Zexpr_Z_total.
           eapply constant_nonneg_bounds_size_of_no_vars in Hcp1; [|eauto].
           invert_list_stuff. assumption. }
      invert_list_stuff. lia.
  - invert H3. econstructor.
    + eapply (IHsize_of (_ :: _ :: _)); eauto.
    + eapply constant_nonneg_bounds_size_of_nonneg in Hc; eauto.
      invert_list_stuff. rewrite Z2Nat.inj_mul; lia.
  - invert H3. invert H5. simpl. econstructor; eauto.
    + eapply (IHsize_of (_ :: _)); eauto.
    + eapply constant_nonneg_bounds_size_of_nonneg in Hcp1; eauto. invert_list_stuff.
      rewrite eval_Zexpr_Z_eval_Zexpr in H4. cbv [eval_Zexpr_Z_total] in Hcp2.
      rewrite H4 in Hcp2. rewrite eval_Zexpr_Z_eval_Zexpr in H6. rewrite H4 in H6.
      invert_list_stuff. rewrite Z2Nat_div_distr; eauto.
  - invert H5. simpl. econstructor; eauto. eapply (IHsize_of (_ :: _ :: _)); eauto.
  - invert H3. econstructor; eauto.
    + eapply (IHsize_of (_ :: _)); eauto.
    + clear Hcp3. rewrite eval_Zexpr_Z_eval_Zexpr in H6.
      cbv [eval_Zexpr_Z_total] in Hcp2. rewrite H6 in Hcp2. lia.
  - invert H3. econstructor; eauto.
    + eapply (IHsize_of (_ :: _)); eauto.
    + clear Hcp3. rewrite eval_Zexpr_Z_eval_Zexpr in H6.
      cbv [eval_Zexpr_Z_total] in Hcp2. rewrite H6 in Hcp2. lia.
  - invert H3. econstructor; eauto.
    + eapply (IHsize_of (_ :: _)); eauto.
    + rewrite eval_Zexpr_Z_eval_Zexpr in H6.
      cbv [eval_Zexpr_Z_total] in Hcp2. rewrite H6 in Hcp2.
      eapply constant_nonneg_bounds_size_of_nonneg in Hcp0; eauto. invert_list_stuff.
      lia.
  - invert H3. econstructor; eauto.
    + eapply (IHsize_of (_ :: _)); eauto.
    + rewrite eval_Zexpr_Z_eval_Zexpr in H6.
      cbv [eval_Zexpr_Z_total] in Hcp2. rewrite H6 in Hcp2.
      eapply constant_nonneg_bounds_size_of_nonneg in Hcp0; eauto. invert_list_stuff.
      lia.
Qed.

Lemma size_of'_size_of e sh' :
  size_of' e sh' ->
  exists sh sh0',
    size_of e sh /\
      eval_Zexprlist $0 sh sh0' /\
      sh' = map Z.to_nat sh0'.
Proof.
  intros H. induction H; fwd; subst; simpl in *;
    repeat match goal with
    | H: _ :: _ = map _ ?x |- _ => is_var x; destruct x; simpl in *; invert_list_stuff
    end; invs; eexists; eexists; eauto 6.
  - split.
    + econstructor; eauto. admit.
    + split; eauto. simpl. f_equal. lia.
  
  - eexists. eexists. split; eauto.

Hint Resolve offset_Zexpr_correct : core.
Hint Immediate empty_ctxs_correspond : core.
Hint Constructors size_of' : core.

Opaque offset_Zexpr.
Lemma zero_lbs_rec_size_of' offsets e sh :
  size_of' e sh ->
  size_of' (zero_lbs_rec offsets e) sh.
Proof.
  intros H. revert offsets. induction H; simpl; intros; econstructor; eauto; lia.
Qed.

Hint Resolve zero_lbs_rec_size_of' : core.

Lemma zero_lbs_rec_correct sh' sh ctx ec e r ctx' offsets :
  eval_expr sh ctx ec e r ->
  size_of' e sh' ->
  ctxs_correspond offsets ctx ctx' ->
  eval_expr sh ctx' ec (zero_lbs_rec offsets e) r.
Proof.
  intros H. revert ctx' offsets sh'. 
  induction H; intros ctx' offsets sh' Hsz Hctx'; invert Hsz; simpl; eauto 7.
  - econstructor; simpl; eauto 6.
    eapply eval_Zexpr_includes_valuation in H8, H9; try apply empty_includes.
    rewrite eval_Zexpr_Z_eval_Zexpr in H8, H9. rewrite H9 in H0. rewrite H8 in H.
    invert_list_stuff. lia.
  - (* :(( *) econstructor; simpl; eauto 6. all: admit.
  - econstructor; simpl; eauto 6. all: admit.
  - econstructor; simpl; eauto 6. all: admit.
  - eapply EvalGuardFalse; eauto. econstructor; simpl; eauto 6.
       - econstructor; simpl; eauto. all: admit.
       - econstructor; simpl; eauto. all: admit.
       - split. 1: eapply EvalLbindV; simpl. all: admit.
       - eapply EvalGuardTrue; eauto.
