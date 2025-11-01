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
From coqutil Require Import Map.Interface Map.Properties Map.Solver Map.OfFunc Tactics.fwd Tactics.destr Tactics Decidable Datatypes.List.

Import Datatypes.

Open Scope list_scope.
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
  induction H; intros lo_ H'; invert H'.
  - exists loz, hiz, nil. simpl. intuition lia.
  - clear IHeval_expr1.
    specialize (IHeval_expr2 _ ltac:(reflexivity)). (*why is eq_refl not eq_refl*)
    destruct IHeval_expr2 as (loz_&hiz_&l_&Hl_&Hlen&Hloz&Hhiz&IH2).
    rewrite H0 in Hhiz. invert Hhiz. invert Hl_.
    simpl in Hloz. rewrite H in Hloz. invert Hloz.
    eexists _, _, _. intuition eauto.
    { simpl. lia. }
    assert (Hor : (i' = loz \/ loz + 1 <= i')%Z) by lia.
    destruct Hor as [Hle|Heq].
    + subst. replace (Z.to_nat _) with O by lia. simpl. assumption.
    + specialize (IH2 i' ltac:(lia)). destruct (Z.to_nat (i' - loz)) eqn:E. 1: lia.
      simpl. destruct IH2 as (_&_&IH2). replace (Z.to_nat _) with n in IH2 by lia.
      apply IH2.
Qed.

Lemma mk_eval_gen sh v ctx i lo hi body loz hiz rl :
  length rl = Z.to_nat (hiz - loz) ->
  eval_Zexpr_Z v lo = Some loz ->
  eval_Zexpr_Z v hi = Some hiz ->
  (forall i', (loz <= i' < hiz)%Z ->
         (~ i \in dom v) /\
           (~ contains_substring "?" i) /\
           match nth_error rl (Z.to_nat (i' - loz)) with
           | None => False
           | Some r =>  eval_expr sh (v $+ (i, i')) ctx body r
           end) ->
  eval_expr sh v ctx (Gen i lo hi body) (V rl).
Proof.
  intros Hlen Hlo Hhi Hbody. revert lo loz Hlen Hlo Hbody.
  induction rl; intros lo loz Hlen Hlo Hbody.
  - eapply EvalGenBase; eauto. simpl in Hlen. lia.
  - simpl in Hlen.
    pose proof (Hbody loz ltac:(lia)) as Hbody0. fwd.
    replace (loz - loz)%Z with 0%Z in * by lia. simpl in *. fwd.
    econstructor; eauto; try lia. eapply IHrl; eauto.
    2: { simpl. rewrite Hlo. reflexivity. }
    { lia. }
    intros i' Hi'. specialize (Hbody i' ltac:(lia)). fwd. intuition.
    replace (Z.to_nat (i' - loz)) with (S (Z.to_nat (i' - (loz + 1)))) in * by lia.
    simpl in E. rewrite E. assumption.
Qed.

Definition toR (s : scalar_result) :=
  match s with
  | SS s => s
  | SX => 0%R
  end.

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
  induct 1; intros.
  - invert H3. simpl.
    eq_eval_Z. econstructor; eauto.
  - invert H2. invert H8. eq_eval_Z. econstructor; eauto. constructor.
Qed.

Lemma pad_lookup_SX sh idxs val :
  result_lookup_Z' idxs (gen_pad sh) val ->
  val = SX.
Proof.
  revert idxs val. induction sh.
  - intros * H. invert H. reflexivity.
  - intros * H. invert H. apply nth_error_repeat' in H2. subst. eapply IHsh; eauto.
Qed.

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
  - intros H. invert H; reflexivity.
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
    + invert H1. invert H2. eauto.
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
    + invert H1. eauto.
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
    invert H1. invert H2. invert H.
    apply add_scalar_result_iff_add_scalar_result' in H2. subst. constructor.
  - intros x y z H H1 H2. invert H1. invert H2. invert H.
    pose proof add_list_nth as H'. specialize (H' _ _ _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
    destruct H' as (c'&H'1&H'2). econstructor; eauto.
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
    + invert H. specialize (H2 a b). destruct H2 as [sh H2].
      eexists. intros H. invert H. invert H5.
Abort. (*not true*) Locate "+".

Lemma add_result_same_domain_bw idxs x y z z' :
  add_result x y z ->
  result_lookup_Z' idxs z z' ->
  exists x' y',
    result_lookup_Z' idxs x x' /\
      result_lookup_Z' idxs y y' /\
      z' = add_scalar_result' x' y'.
Proof.
  revert x y z. induction idxs; intros x y z H1 H2.
  - invert H2. invert H1. do 2 eexists.
    apply add_scalar_result_iff_add_scalar_result' in H3. subst.
    intuition constructor.
  - invert H2. invert H1.
    pose proof add_list_nth_bw as H'. specialize (H' _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    destruct H' as (?&?&?&?&?). specialize (IHidxs _ _ _ ltac:(eassumption) ltac:(eassumption)). destruct IHidxs as (?&?&?&?). do 2 eexists. intuition eauto; econstructor; eauto.
Qed.

Print add_result.
Search (?T -> ?T -> Prop) (list ?T -> Prop).
Print fold_left.
Fixpoint fold_left_rel {A B : Type} (R : A -> B -> A -> Prop) (l : list B) (P0 : A -> Prop) :=
  match l with
  | [] => P0
  | b :: l0 => fun a => exists a0, P0 a0 /\ fold_left_rel R l0 (R a0 b) a
  end.

Inductive fold_left_rel' {A B : Type} (R : A -> B -> A -> Prop) : list B -> (A -> Prop) -> A -> Prop :=
| flr_nil P0 a : P0 a -> fold_left_rel' R [] P0 a
| flr_cons P0 b l0 a0 a :
  P0 a0 ->
  fold_left_rel' R l0 (R a0 b) a ->
  fold_left_rel' R (b :: l0) P0 a
.

Print fold_right.
Inductive fold_right_rel' {A B : Type} (R : B -> A -> A -> Prop) : (A -> Prop) -> list B -> A -> Prop :=
| frr_nil P0 a : P0 a -> fold_right_rel' R P0 [] a
| frr_cons P0 b l0 a a' :
  fold_right_rel' R P0 l0 a' ->
  R b a' a ->
  fold_right_rel' R P0 (b :: l0) a
.
Hint Constructors fold_right_rel' : core.

Definition add_list_result sh :=
  fold_right_rel' add_result (Logic.eq (gen_pad sh)).

Lemma invert_eval_sum' sh v ctx i lo hi body r :
  eval_expr sh v ctx (Sum i lo hi body) r ->
  exists loz hiz summands sz,
    size_of body sz /\
      length summands = Z.to_nat (hiz - loz) /\
      eval_Zexpr_Z v lo = Some loz /\
      eval_Zexpr_Z v hi = Some hiz /\
      add_list_result sz summands r /\
      (forall i', (loz <= i' < hiz)%Z ->
             (~ i \in dom v) /\
               (~ contains_substring "?" i) /\
               match nth_error summands (Z.to_nat (i' - loz)) with
               | None => False
               | Some r =>  eval_expr sh (v $+ (i, i')) ctx body r
               end).
Proof.
  intros H. remember (Sum _ _ _ _) as e eqn:E. revert lo E.
  induction H; intros lo_ H'; invert H'.
  2: { exists loz, hiz, nil, sz. simpl. intuition auto; try lia.
       constructor. eauto. }
  clear IHeval_expr1. specialize (IHeval_expr2 _ Logic.eq_refl).
  destruct IHeval_expr2 as (loz'&hiz'&summands'&sz'&Hsz'&Hlen&Hloz'&Hhiz'&Hsummands'&IH).
  simpl in Hloz'. rewrite H0 in Hhiz'. invert Hhiz'. rewrite H in Hloz'. invert Hloz'.
  exists loz, hiz', (r :: summands'), sz'. intuition.
  + simpl. lia.
  + econstructor. 1: eassumption. assumption.
  + clear Hsummands'.
    assert (Hor : (i' = loz \/ loz + 1 <= i')%Z) by lia.
    destruct Hor as [Hle|Heq].
    -- subst. replace (Z.to_nat _) with O by lia. simpl. assumption.
    -- 
      specialize (IH i' ltac:(lia)). destruct IH as (_&_&IH).
      replace (Z.to_nat (i' - loz)) with (Datatypes.S (Z.to_nat (i' - (loz + 1)))) by lia.
      simpl. assumption.
Qed.

Lemma mk_eval_sum' sz sh v ctx i lo hi body r loz hiz summands :
  size_of body sz ->
  length summands = Z.to_nat (hiz - loz) ->
  eval_Zexpr_Z v lo = Some loz ->
  eval_Zexpr_Z v hi = Some hiz ->
  add_list_result sz summands r ->
  (forall i', (loz <= i' < hiz)%Z ->
         (~ i \in dom v) /\
           (~ contains_substring "?" i) /\
           match nth_error summands (Z.to_nat (i' - loz)) with
           | None => False
           | Some r =>  eval_expr sh (v $+ (i, i')) ctx body r
           end) ->
  eval_expr sh v ctx (Sum i lo hi body) r.
Proof.
  intros Hsz Hlen Hlo Hhi Hsum Hbody. revert lo loz r Hlen Hlo Hsum Hbody.
  induction summands; intros lo loz r Hlen Hlo Hsum Hbody.
  - invert Hsum. fwd. eapply EvalSumBase; eauto. simpl in Hlen. lia.
  - simpl in Hlen. invert Hsum.
    pose proof (Hbody loz ltac:(lia)) as Hbody0. fwd.
    replace (loz - loz)%Z with 0%Z in * by lia. simpl in *. fwd.
    econstructor; eauto; try lia. eapply IHsummands; eauto.
    2: { simpl. rewrite Hlo. reflexivity. }
    { lia. }
    intros i' Hi'. specialize (Hbody i' ltac:(lia)). fwd. intuition.
    replace (Z.to_nat (i' - loz)) with (S (Z.to_nat (i' - (loz + 1)))) in * by lia.
    simpl in E. rewrite E. assumption.
Qed.

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
  induction H; intros lo_ H'; invert H'.
  2: { exists loz, hiz, nil. simpl. intuition auto; try lia.
       exists nil. split; [constructor|]. simpl. apply pad_lookup_SX in H3. subst.
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
