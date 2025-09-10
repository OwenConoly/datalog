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
Require Import Datalog.
Open Scope string_scope.

Definition option_map2 {X Y Z : Type} (f : X -> Y -> Z) x y :=
  match x, y with
  | Some x, Some y => Some (f x y)
  | _, _ => None
  end.

Definition option_unwrap {X : Type} (x : option (option X)) :=
  match x with
  | None => None
  | Some x => x
  end.

Definition option_all {X : Type} (l : list (option X)) :=
  fold_right (option_map2 cons) (Some nil) l.

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
(*p is target*)
(*f is reindexer*)
(*asn is StoreType += or =*)
(*sh is shape of something?*)
Search Zexpr.
Print eval_Zexpr.
(*just like Zexpr but no ZVar*)
Variant Zfn : Set :=
  fn_ZPlus | fn_ZMinus | fn_ZTimes | fn_ZDivf | fn_ZDivc | fn_ZMod | fn_ZLit (x : Z).
Definition interp_Zfn (f : Zfn) (l : list Z) : option Z :=
  match f, l with
  | fn_ZPlus, [x; y] => Some (x + y)
  | fn_ZMinus, [x; y] => Some (x - y)
  | fn_ZTimes, [x; y] => Some (x * y)
  | fn_ZDivf, [x; y] => Some (x / y)
  | fn_ZDivc, [x; y] => Some (x // y)
  | fn_ZMod, [x; y] => Some (x mod y)
  | fn_ZLit x, [] => Some x
  | _, _ => None
  end%Z.
(*just like Sstmt but no SVar, SGet*)
Variant Rfn : Set :=
  fn_SMul | fn_SAdd | fn_SDiv | fn_SSub | fn_SLit (x : R).

Definition interp_Rfn (f : Rfn) (l : list R) : option R :=
  match f, l with
  | fn_SMul, [x; y] => Some (x * y)
  | fn_SAdd, [x; y] => Some (x + y)
  | fn_SDiv, [x; y] => Some (x / y)
  | fn_SSub, [x; y] => Some (x - y)
  | fn_SLit x, [] => Some (x)
  | _, _ => None
  end%R.

Variant tfn : Set :=
  fn_Z (_ : Zfn) | fn_R (_ : Rfn).

Definition interp_fn (f : tfn) (l : list (Z+R)) : option (Z + R) :=
  match f with
  | fn_Z f => option_map inl (option_unwrap (option_map (interp_Zfn f) (option_all (map get_inl l))))
  | fn_R f => option_map inr (option_unwrap (option_map (interp_Rfn f) (option_all (map get_inr l))))
  end.

Definition rel : Set := string.
(*inl s is string representing indexing variable (e.g. i, j), which came directly from source program
  inr n is nat (that i generated) representing value in some intermediate thing
 *)
Definition var : Set := string + nat.
Definition trule := rule rel var tfn.

Search Sstmt. Print eval_Sstmt. Print context. Print fmap. Check Build_rule. Check Build_fact.

Fixpoint lower_idx (idx: Zexpr) : expr var tfn :=
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

Print Sexpr.
Fixpoint lower_Sexpr (next_varname : nat) (e : Sexpr) :
  expr var tfn (*value of expr*) *
    list (fact rel var tfn) (*hypotheses*) *
    nat (*next varname *) :=
  match e with
  | Var x => (var_expr (inr next_varname),
              [{| fact_R := x; fact_args := [var_expr (inr next_varname)] |}],
              succ next_varname)
  | Get x idxs => (var_expr (inr next_varname),
                   [{| fact_R := x; fact_args := var_expr (inr next_varname) :: map lower_idx idxs |}],
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

Definition map_empty : var -> option tfn := fun _ => None.
Search ((_ + _) -> (_ + _) -> bool).
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
  
Definition map_cons (x : var) (y : option tfn) (m : var -> option tfn) :=
  fun v => if var_eqb x v then y else m v.
Search (scalar_result -> R).
Definition toR (s : scalar_result) :=
  match s with
  | SS s => s
  | SX => 0%R
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
Print eval_expr. Print context. Print valuation.
Print prog_impl_fact.
Check eval_expr. Print result. Search result. Print result_lookup_Z_option.
Print lower_Sexpr. Print eval_Sexpr. Print expr_context. Print fmap. Locate "$?".
Search eval_get. Search result. Print result_lookup_Z.

Search eval_get.

Print valuation.
Definition substn_of (v : valuation) : var -> option tfn :=
  fun x => match x with
        | inl x => option_map (fun y => fn_Z (fn_ZLit y)) (v $? x)
        | inr x => None
        end.

Lemma eval_Z_to_substn v x z :
  eval_Zexpr v x z ->
  interp_expr interp_fn (subst_in_expr (substn_of v) (lower_idx x)) (inl z).
Proof.
  intros H. induction H; simpl; repeat match goal with | H: _ = Some _ |- _ => rewrite H end; econstructor; eauto.
Qed.

Lemma eval_Zexprlist_to_substn v i lz :
  eval_Zexprlist v i lz ->
  Forall2 (interp_expr interp_fn) (map (subst_in_expr (substn_of v)) (map lower_idx i)) (map inl lz).
Proof.
  intros H. induction H.
  - constructor.
  - simpl. constructor.
    + apply eval_Z_to_substn. assumption.
    + assumption.
Qed.

Print lower_Sexpr. Check prog_impl_fact. Print interp_expr.

Lemma compose_domain {A B : Type} (s s' : A -> option B) x y :
  compose s s' x = Some y ->
  s x = Some y \/ s' x = Some y.
Proof. cbv [compose]. intros H. destruct (s' x), (s x); auto. Qed.

Fixpoint result_lookup_Z_option' indices r :=
  match indices with
  | (Z.neg _)::xs => None
  | x::xs => match r with
           | V v => match nth_error v (Z.to_nat x) with
                   | None => None
                   | Some v' => result_lookup_Z_option' xs v'
                   end
           | _ => None
           end
  | _ => match r with
        | S r => Some r
        | _ => None
        end
  end.

(*closely following lemma eval_get_lookup_result_Z*)
Lemma eval_get_lookup_result_Z_option' : forall l v rs r,
    eval_get v rs l r ->
    forall x0,
      eval_Zexprlist v l x0 ->
      Some r = result_lookup_Z_option' x0 (V rs).
Proof.
  induct 1; intros.
  - invert H3. simpl.
    eq_eval_Z. rewrite H1.
    cases z; try lia; eauto.
  - invert H2. invert H8. eq_eval_Z. simpl. rewrite H1.
    cases z; try lia; eauto.
Qed.

Lemma lower_Sexpr_correct sh v ec s (datalog_ctx : list (rule rel var tfn)):
  (forall x r idxs val,
      ec $? x = Some r ->
      result_lookup_Z_option' idxs r = Some val ->
      prog_impl_fact interp_fn datalog_ctx (x, inr (toR val) :: (map inl idxs))) ->
  forall val name val0 hyps name',
    eval_Sexpr sh v ec s val ->
    lower_Sexpr name s = (val0, hyps, name') ->
    exists hyps' substn,
      name <= name' /\
      (forall x y, substn x = Some y ->
              match x with
              | inr i => name <= i < name'
              | inl _ => False
              end) /\
        Forall2 (interp_fact interp_fn) (map (subst_in_fact (substn)) (map (subst_in_fact (substn_of v)) hyps)) hyps' /\
        Forall (prog_impl_fact interp_fn datalog_ctx) hyps' /\
        interp_expr interp_fn (subst_in_expr substn (subst_in_expr (substn_of v) val0)) (inr (toR val)).
Proof.
  intros H. induction s; intros; simpl in *.
  - inversion H1. subst. clear H1. simpl. eexists.
    exists (map_cons (inr name) (Some (fn_R (fn_SLit (toR val)))) map_empty). split.
    { cbv [succ]. lia. } split.
    { cbv [map_cons map_empty]. intros. destruct x; simpl in H1; inversion H1.
      destruct (name =? n)%nat eqn:E; inversion H3. apply Nat.eqb_eq in E. subst. cbv [succ]. lia. } split.
    { repeat constructor. simpl. cbv [map_cons]. rewrite var_eqb_refl. simpl.
      repeat econstructor. }
    inversion H0. subst. clear H0. simpl. split.
    + repeat constructor. 
      specialize H with (idxs := nil) (1 := H2). simpl in H.
      specialize (H r). specialize (H ltac:(reflexivity)). destruct r; apply H.
    + cbv [map_cons]. rewrite var_eqb_refl. simpl. repeat econstructor.
  - inversion H1. subst. clear H1. simpl. inversion H0. subst. clear H0.
    pose proof (eval_get_eval_Zexprlist _ _ _ _ ltac:(eassumption)) as [idxs Hidxs].
    Check eval_get_lookup_result_Z.
    pose proof (eval_get_lookup_result_Z_option' _ _ _ _ ltac:(eassumption) _ ltac:(eassumption)) as Hr.
    eexists.
    exists (map_cons (inr name) (Some (fn_R (fn_SLit (toR r)))) map_empty).
    split.
    { cbv [succ]. lia. } split.
    { cbv [map_cons map_empty]. intros. destruct x; simpl in H0; inversion H0.
      destruct (name =? n)%nat eqn:E; inversion H2. apply Nat.eqb_eq in E. subst. cbv [succ]. lia. }
    split.
    { constructor. 2: constructor. cbv [subst_in_fact]. simpl. constructor. simpl.
      cbv [map_cons]. simpl. rewrite Nat.eqb_refl. simpl.
      apply eval_Zexprlist_to_substn in Hidxs. Print lower_idx.
      repeat econstructor.
      repeat rewrite <- Forall2_map_l in *. eapply Forall2_impl. 2: eassumption.
      simpl. intros a b H'. Search interp_expr _ (subst_in_expr _ _).
      pose proof interp_expr_subst_more as H''. specialize H'' with (2 := H').
      rewrite subst_in_expr_subst_in_expr. rewrite H''. 1: assumption. cbv [extends].
      clear. intros x y H. cbv [compose]. destruct x; simpl in *. 1: rewrite H; reflexivity.
      inversion H. }
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
Search (list (Zexpr * Zexpr)). Print flatten_index.
Search (list (Zexpr * Zexpr)) (list Z). Print flatten. Check eval_expr.
Print valuation. Print expr_context.
Lemma lower_correct e out sh v ctx r datalog_ctx :
  eval_expr sh v ctx e r ->
  (forall (x : rel) (r : result) (idxs : list Z) (val : scalar_result),
      ctx $? x = Some r ->
      result_lookup_Z_option' idxs r = Some val ->
      prog_impl_fact interp_fn datalog_ctx (x, inr (toR val) :: map inl idxs)) ->
  forall idxs val idx_ctx,
    result_lookup_Z_option' idxs r = Some val ->
    exists idx_ctx',
      Forall2 (interp_expr interp_fn) (map (subst_in_expr (substn_of v)) (map lower_idx (map fst idx_ctx))) idx_ctx' /\
        prog_impl_fact interp_fn (lower e out idx_ctx ++ datalog_ctx) (out, inr (toR val) :: idx_ctx' ++ (map inl idxs)).
Proof.
  intros H. induction H.
  { (*this case seems more trivial than it should be, because we are not proving anything
      about the shape of the output...*)
    simpl. intros.
    destruct idxs. 1: simpl in H3; inversion H3. destruct z; simpl in H3.
    1,3: congruence. rewrite nth_error_empty in H3. inversion H3. }
  { simpl. intros. destruct idxs; simpl in H7; [congruence|].
    assert (0 <= z)%Z as Hz.
    { destruct z; [lia|lia|congruence]. }
    eassert _ as Hz'.
    { destruct z eqn:Ez; [exact H7|exact H7|congruence]. }
    clear H7.
    specialize (IHeval_expr1 ltac:(assumption)).
    specialize (IHeval_expr2 ltac:(assumption)).
    remember (Z.to_nat z) as n eqn:En. replace z with (Z.of_nat n) by lia.
    clear z En Hz.
    destruct n; simpl in Hz'.
    - (*first iteration*)
      clear IHeval_expr2. specialize IHeval_expr1 with (1 := Hz').
      specialize (IHeval_expr1 (((! i ! - lo)%z, (hi - lo)%z) :: idx_ctx)).
      destruct IHeval_expr1 as (idx_ctx'&Hidx_ctx'&IH1).
      inversion Hidx_ctx'. subst. clear Hidx_ctx'.
      exists l'. split.
      { (* use that i not in dom v*)
        [assumption|]. inversion H9. subst. clear H9.
      inversion H10. subst. clear H10. inversion H14. subst. clear H14.
      inversion H15. subst. clear H15. simpl in H9. inversion H9. subst. clear H9. H10.
      simpl in H13. cbv [
      
      destruct z; simpl in H7; [| |congruence].
    { simpl in H7.
  17: { intros. simpl. destruct (lower_Sexpr O s) as [ [val0 hyps] name'] eqn:E.
        simpl. pose proof lower_Sexpr_correct as H'.
        specialize H' with (1 := H0) (2 := H) (3 := E).
        destruct H' as (hyps'&substn&_&Hsubstn&Hhyps&Hhyps'&Hval0).
        destruct idxs.
        2: { simpl in H1. destruct z; congruence. }
        econstructor.
        { constructor. simpl. exists (compose substn (substn_of v)). split.
          - cbv [subst_in_fact]. simpl. constructor. simpl. repeat constructor.
            rewrite subst_in_expr_subst_in_expr in Hval0. Search val. simpl in H1.
            inversion H1. subst. clear H1. apply Hval0.
          - rewrite map_map in Hhyps. erewrite map_ext. 1: eassumption.
            simpl. intros. rewrite subst_in_fact_subst_in_fact. reflexivity. }
        intros. eapply prog_impl_fact_subset.
        2: { rewrite Forall_forall in Hhyps'. apply Hhyps'. assumption. }
        simpl. auto. }
  (* { intros H' * H''. destruct idxs; simpl in H''; try solve [inversion H'']. *)
  (*   destruct z; simpl in H''; try rewrite nth_error_empty in H''; solve [inversion H'']. } *)
  (* { intros H' * H''. admit. (*should be doable*) } *)
    
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
