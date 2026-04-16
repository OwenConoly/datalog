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

From Datalog Require Import Datalog Dag Map List Tactics ATLUtils.
From coqutil Require Import Map.Interface Map.Properties Map.Solver Map.OfFunc Tactics.fwd Tactics.destr Tactics Decidable.

Import Datatypes.

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
  | Get x idxs => Get x (map f idxs)
  | Mul x y => Mul (map_Zexprs_in_Sexpr f x) (map_Zexprs_in_Sexpr f y)
  | Div x y => Div (map_Zexprs_in_Sexpr f x) (map_Zexprs_in_Sexpr f y)
  | Add x y => Add (map_Zexprs_in_Sexpr f x) (map_Zexprs_in_Sexpr f y)
  | Sub x y => Sub (map_Zexprs_in_Sexpr f x) (map_Zexprs_in_Sexpr f y)
  | Lit x => Lit x
  end.

Lemma map_Zexprs_in_Sexpr_same ectx ctx ctx' e e' f :
  (forall ze ze', eval_Zexpr ctx ze ze' ->
             eval_Zexpr ctx' (f ze) ze') ->
  eval_Sexpr ctx ectx e e' ->
  eval_Sexpr ctx' ectx (map_Zexprs_in_Sexpr f e) e'.
Proof.
  induction 2; simpl; try econstructor; eauto.
  (*it'd be nice if eval_get were characterized in terms of eval_Zexprlist*)
  clear -H1 H.
  induction H1; econstructor; eauto.
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
    | Some lo => exists lo', eval_Zexpr ctx' lo lo' /\
                         ctx' $? v = Some (v' - lo')%Z
    | None => ctx' $? v = Some v'
    end.

Definition offset_Zexpr offsets e :=
  subst_vars_in_Zexpr (fun i => option_map (fun lo => ZPlus (ZVar i) lo) (map.get offsets i)) e.

Lemma offset_Zexpr_correct offsets ctx ctx' e e' :
  ctxs_correspond offsets ctx ctx' ->
  eval_Zexpr ctx e e' ->
  eval_Zexpr ctx' (offset_Zexpr offsets e) e'.
Proof.
  intros H1 H2. cbv [offset_Zexpr]. eapply subst_vars_in_Zexpr_correct; eauto.
  intros v v' Hv. apply H1 in Hv. destruct (map.get offsets v); fwd; simpl; eauto.
  eenough (v' = _) as ->; [eauto|]. lia.
Qed.

Fixpoint zero_lbs_rec offsets e :=
  let offset := offset_Zexpr offsets in
  match e with
  | Gen i lo hi e1 => Gen i (ZLit 0) (offset (ZMinus hi lo)) (zero_lbs_rec (map.put offsets i (offset lo)) e1)
  | Sum i lo hi e1 => Sum i (offset lo) (offset hi) (zero_lbs_rec offsets e1)
  | Guard g e1 => Guard (map_Zexprs_in_Bexpr offset g) (zero_lbs_rec offsets e1)
  | Flatten e1 => Flatten (zero_lbs_rec offsets e1)
  | Split k e1 => Split (offset k) (zero_lbs_rec offsets e1)
  | Transpose e1 => Transpose (zero_lbs_rec offsets e1)
  | Truncr k e1 => Truncr (offset k) (zero_lbs_rec offsets e1)
  | Truncl k e1 => Truncl (offset k) (zero_lbs_rec offsets e1)
  | Padr k e1 => Padr (offset k) (zero_lbs_rec offsets e1)
  | Padl k e1 => Padl (offset k) (zero_lbs_rec offsets e1)
  | Lbind x e1 e2 => Lbind x (zero_lbs_rec offsets e1) (zero_lbs_rec offsets e2)
  | Concat e1 e2 => Concat (zero_lbs_rec offsets e1) (zero_lbs_rec offsets e2)
  | Scalar s => Scalar (map_Zexprs_in_Sexpr offset s)
  end.

Definition zero_lbs := zero_lbs_rec map.empty.

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

Lemma empty_ctxs_correspond offsets ctx':
  ctxs_correspond offsets $0 ctx'.
Proof.
  cbv [ctxs_correspond]. intuition auto.
Qed.

Lemma ctxs_correspond_put_offset i lo offsets ctx ctx' loz i' :
  ~ i \in dom ctx' ->
  eval_Zexpr ctx' lo loz ->
  ctxs_correspond offsets ctx ctx' ->
  ctxs_correspond (map.put offsets i lo) (ctx $+ (i, (loz + i')%Z)) (ctx' $+ (i, i')).
Proof.
  intros H0 H1 H2. cbv [ctxs_correspond]. ssplit.
  - intros v v' H. rewrite map.get_put_dec. destr (i =? v).
    + rewrite lookup_add_eq in * by reflexivity. fwd. eexists. split.
      -- eapply eval_Zexpr_includes_valuation; eauto.
      -- f_equal. lia.
    + rewrite lookup_add_ne in * by auto. specialize (H2 _ _ ltac:(eassumption)).
      destruct_one_match_hyp; eauto. fwd. eexists. split; eauto.
      eapply eval_Zexpr_includes_valuation; eauto.
Qed.

Lemma ctxs_correspond_put_no_offset i offsets ctx ctx' i' :
  ~ i \in dom ctx' ->
  map.get offsets i = None ->
  ctxs_correspond offsets ctx ctx' ->
  ctxs_correspond offsets (ctx $+ (i, i')) (ctx' $+ (i, i')).
Proof.
  intros H1 H2 H3. cbv [ctxs_correspond].
  intros v v' H. assert (Hor: i = v \/ i <> v) by sets.
  (*is it sneakily using excluded middle?*)
  destruct Hor.
  + subst. rewrite lookup_add_eq in H by reflexivity. fwd.
    apply lookup_add_eq. reflexivity.
  + rewrite lookup_add_ne in * by auto. specialize (H3 _ _ ltac:(eassumption)).
    destruct_one_match_hyp; eauto. fwd. eexists. split; eauto.
    eapply eval_Zexpr_includes_valuation; eauto.
Qed.
Print Assumptions ctxs_correspond_put_no_offset.
Hint Resolve offset_Zexpr_correct : core.
Hint Immediate empty_ctxs_correspond : core.

Ltac size_of_constr :=
  match goal with
  | |- size_of _ _ ?x => is_evar x; econstructor
  | |- size_of _ _ ?x => eassert (x = _) as ->; cycle 1; [econstructor|]
  end.

Lemma eval_expr_iter_vars_disj v ec e r :
  eval_expr v ec e r ->
  dom v \cap iter_vars e = constant [].
Proof.
  induction 1; simpl; eauto.
  (*not true*)
Abort.

Lemma ctxs_correspond_put_not_in offsets ctx ctx' i x :
  ctxs_correspond offsets ctx ctx' ->
  ctx $? i = None ->
  ctxs_correspond (map.put offsets i x) ctx ctx'.
Proof.
  intros H1 H2. cbv [ctxs_correspond]. intros i' x' H'.
  rewrite map.get_put_dec. destr (i =? i').
  - congruence.
  - apply H1. assumption.
Qed.

(* Lemma size_of_zero_lbs_rec v v' offsets e sh : *)
(*   size_of v e sh -> *)
(*   dom v \cap iter_vars e = constant [] -> *)
(*   ctxs_correspond offsets v v' -> *)
(*   size_of v' (zero_lbs_rec offsets e) sh. *)
(* Proof. *)
(*   intros H1 H2. revert offsets. *)
(*   induction H1; simpl in *; intros; size_of_constr; eauto; try (lia || f_equal; lia). *)
(*   apply IHsize_of; auto. apply ctxs_correspond_put_not_in; auto. *)
(*   apply None_dom_lookup. sets. *)
(* Qed. *)

Lemma no_shadowing_subset s s' e :
  no_shadowing s' e ->
  s \subseteq s' ->
  no_shadowing s e.
Proof.
  revert s s'. induction e; simpl; intros; fwd; eauto.
  - split; [sets|]. eapply IHe; eauto.
  - split; [sets|]. eapply IHe; eauto.
Qed.
Hint Resolve no_shadowing_subset : core.

Lemma size_of_zero_lbs_rec v v' offsets e sh :
  size_of v e sh ->
  no_shadowing (dom v) e ->
  ctxs_correspond offsets v v' ->
  size_of v' (zero_lbs_rec offsets e) sh.
Proof.
  intros H1 H2. revert offsets.
  induction H1; simpl in *; fwd; intros; size_of_constr; eauto; try (lia || f_equal; lia).
  apply IHsize_of; eauto. apply ctxs_correspond_put_not_in; auto.
Qed.
Hint Resolve size_of_zero_lbs_rec : core.

Lemma vars_of_zero_lbs_rec offsets e :
  vars_of (zero_lbs_rec offsets e) = vars_of e.
Proof.
  revert offsets. induction e; simpl; sets.
Qed.

(*hmm can i "autorewrite" instead?*)
Hint Extern 3 => match goal with
                | |- context[vars_of (zero_lbs_rec _ _)] => rewrite vars_of_zero_lbs_rec
                end : core.

Opaque offset_Zexpr.
Lemma zero_lbs_rec_correct sh ctx ec e r ctx' offsets :
  eval_expr ctx ec e r ->
  size_of ctx e sh ->
  ctxs_correspond offsets ctx ctx' ->
  dom ctx = dom ctx' ->
  (forall x, ~x \in dom ctx -> map.get offsets x = None) ->
  no_shadowing (dom ctx) e ->
  eval_expr ctx' ec (zero_lbs_rec offsets e) r.
Proof.
  revert sh ctx ec r ctx' offsets.
  induction e; intros sh ctx ec r ctx' offsets Heval Hsz Hctx' Hdom1 Hdom2 Hdom3;
    ((pose proof Heval as Heval'; apply invert_eval_sum' in Heval) || apply invert_eval_gen in Heval || invert Heval);
    simpl in *;
    fwd;
    invert Hsz; simpl;
    repeat match goal with
      | H: eval_Zexpr_Z _ _ = Some _ |- _ => apply eval_Zexpr_Z_eval_Zexpr in H
      end;
    eq_eval_Z;
    try solve [econstructor; eauto].
  (*bafflingly, doing just "eauto 6" solves fewer cases*)
  - eapply mk_eval_gen; [|eauto..].
    + eauto.
    + lia.
    + intros i' Hi'. specialize (Hevalp4 (loz0 + i')%Z ltac:(lia)). fwd.
      ssplit; auto.
      -- sets.
      -- eenough (Z.to_nat _ = _) as ->; [rewrite E|lia]. eapply IHe; eauto 4.
         ++ eapply ctxs_correspond_put_offset; eauto. sets.
         ++ do 2 rewrite dom_add. sets.
         ++ rewrite dom_add. intros. rewrite map.get_put_dec. destr (i =? x); sets.
         ++ rewrite dom_add. simpl in *. sets.
  - simpl in *. fwd. eq_size_of. eapply mk_eval_sum; eauto.
    intros i' Hi'. specialize (Hevalp5 (i')%Z ltac:(lia)). fwd.
    ssplit; auto.
    -- sets.
    -- eapply IHe; eauto 4.
       ++ eapply ctxs_correspond_put_no_offset; eauto. sets.
       ++ do 2 rewrite dom_add. sets.
       ++ rewrite dom_add. intros. apply Hdom2. sets.
       ++ rewrite dom_add. eauto.
 Qed.

Lemma zero_lbs_correct sz ctx ec e r :
  size_of ctx e sz ->
  no_shadowing (dom ctx) e ->
  eval_expr ctx ec e r ->
  eval_expr ctx ec (zero_lbs e) r.
Proof.
  intros. eapply zero_lbs_rec_correct; eauto.
  - cbv [ctxs_correspond]. intros. rewrite map.get_empty. assumption.
  - intros. apply map.get_empty.
Qed.

Fixpoint gen_lbs_zero e :=
  match e with
  | Gen _ lo _ e1 => lo = | 0 |%z /\ gen_lbs_zero e1
  | Sum _ _ _ e1 | Guard _ e1 | Flatten e1 | Split _ e1 | Transpose e1
  | Truncr _ e1 | Truncl _ e1 | Padr _ e1 | Padl _ e1 =>
                                              gen_lbs_zero e1
  | Lbind _ e1 e2 | Concat e1 e2 =>
                      gen_lbs_zero e1 /\ gen_lbs_zero e2
  | Scalar _ => True
  end.

Lemma zero_lbs_rec_zeroes_lbs offsets e :
  gen_lbs_zero (zero_lbs_rec offsets e).
Proof. revert offsets. induction e; simpl; auto. Qed.

Lemma zero_lbs_zeroes_lbs e :
  gen_lbs_zero (zero_lbs e).
Proof. apply zero_lbs_rec_zeroes_lbs. Qed.
End __.
