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

From Datalog Require Import Datalog Dag Map List Tactics Interpreter QueryableToRunnable.
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

Fixpoint vars_of_Sexpr s :=
  match s with
  | Var x => constant [x]
  | Get x _ => constant [x]
  | Mul x y | Div x y | Add x y | Sub x y => vars_of_Sexpr x \cup vars_of_Sexpr y
  | Lit x => constant []
  end.

Fixpoint referenced_vars e :=
  match e with
  | Gen _ _ _ e1 | Sum _ _ _ e1 | Guard _ e1 | Flatten e1 | Split _ e1
  | Transpose e1 | Truncr _ e1 | Truncl _ e1 | Padr _ e1 | Padl _ e1 =>
                                                             referenced_vars e1
  | Lbind _ e1 e2 | Concat e1 e2 =>
                      referenced_vars e1 \cup referenced_vars e2
  | Scalar s => vars_of_Sexpr s
  end.

Lemma gen_pad_bounds idxs dims val :
  result_lookup_Z' idxs (gen_pad dims) val ->
  length dims = length idxs.
Proof.
  revert dims. induction idxs.
  - simpl. intros dims H. invert H. destruct dims; [reflexivity|].
    simpl in H0. discriminate H0.
  - intros dims H. invert H. destruct dims; [discriminate H2|].
    simpl in H2. invert H2. simpl. f_equal. apply IHidxs.
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

Lemma dim_goes_down n v x r :
  nth_error v x = Some r ->
  result_has_dim (S n) (V v) ->
  result_has_dim n r.
Proof.
  intros H1 H2. invert H2. apply nth_error_In in H1.
  rewrite Forall_forall in H3. auto.
Qed.

Lemma dim_transpose_result_list l n m :
  Forall (result_has_dim (S n)) l ->
  Forall (result_has_dim (S n)) (transpose_result_list l m).
Proof.
  intros H. induction m.
  - simpl. constructor.
  - simpl. constructor. 2: assumption. constructor.
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
  apply Forall_app. split; [assumption|]. simpl.
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
    specialize (IHeval_expr2 _ ltac:(constructor; eauto)).
    simpl in IHeval_expr2. invert IHeval_expr2. constructor; eauto.
  - simpl in *. eapply dim_sum; eauto.
  - apply size_of_sizeof in H2, H8. subst.
    apply dim_gen_pad'. reflexivity.
  - simpl. apply size_of_sizeof in H0, H4. subst.
    apply dim_gen_pad'. reflexivity.
  - eauto.
  - eauto.
  - eauto.
  - simpl. constructor. apply Forall_app; auto.
    specialize (IHeval_expr1 _ ltac:(eassumption)).
    specialize (IHeval_expr2 _ ltac:(eassumption)).
    simpl in *. invert IHeval_expr1. invert IHeval_expr2. auto.
  - simpl. specialize (IHeval_expr _ ltac:(eassumption)).
    apply size_of_sizeof in H0, H2. rewrite H0 in H2. invert H2.
    apply dim_transpose_result.
    + reflexivity.
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
    apply Forall_repeat. apply dim_gen_pad'. apply size_of_sizeof in H1, H7.
    rewrite H1 in H7. invert H7. reflexivity.
  - simpl in *. constructor. specialize (IHeval_expr _ ltac:(eassumption)).
    simpl in *. invert IHeval_expr. apply Forall_app. split; [|assumption].
    apply Forall_repeat. apply dim_gen_pad'. apply size_of_sizeof in H1, H7.
    rewrite H1 in H7. invert H7. reflexivity.
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

Lemma length_zrange min max :
  length (zrange min max) = Z.to_nat (max - min).
Proof.
  cbv [zrange]. rewrite length_zrange'. reflexivity.
Qed.

Search zrange'.

Lemma zrange'_seq x n start :
  zrange' x n = map (fun y => x + Z.of_nat y - Z.of_nat start)%Z (seq start n).
Proof.
  revert x start. induction n; simpl; auto. intros. f_equal; [lia|]. erewrite IHn.
  apply map_ext. lia.
Qed.

Lemma zrange_seq min max :
  zrange min max = map (fun y => min + Z.of_nat y)%Z (seq O (Z.to_nat (max - min))).
Proof.
  cbv [zrange]. erewrite zrange'_seq. apply map_ext. lia.
Qed.

Check nth_error_seq_Some.
Lemma nth_error_zrange_Some min max n x :
  nth_error (zrange min max) n = Some x ->
  x = (min + Z.of_nat n)%Z.
Proof.
  rewrite zrange_seq, nth_error_map. intros H. invert_list_stuff.
  apply nth_error_seq_Some in Hp0. subst. lia.
Qed.
