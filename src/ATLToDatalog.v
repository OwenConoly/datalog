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

Definition rel : Set := string + nat.
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
              [{| fact_R := inl x; fact_args := [var_expr (inr next_varname)] |}],
              succ next_varname)
  | Get x idxs => (var_expr (inr next_varname),
                   [{| fact_R := inl x; fact_args := var_expr (inr next_varname) :: map lower_idx idxs |}],
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
  

Search (list Z). Search "shape".
Print sizeof. Print rule. Print fact. Print eval_expr. Print fact. Print Rfn. Print Zexpr. Print trule. 
Fixpoint lower
  (e : ATLexpr)
  (out: rel)
  (name: nat)
  (*i don't use the bounds at all (yet)*)
  (idxs_bds : list (Zexpr * Zexpr))
  : list trule :=
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
      lower body (inr aux) (Datatypes.S aux') [(ZVar i, ZMinus hi lo)] ++
        [(*set aux'(O, lo, ...)*)
          {| rule_hyps := [];
            rule_concl := {| fact_R := (inr aux');
                            fact_args := [fun_expr (fn_R (fn_SLit 0%R)) [];
                                          lower_idx lo] ++
                                          map var_expr dimvars(*arbitrary index into summand*) |} |};
          (*set aux' (body(i) + \sum_{j < i} body(j), S i, ...)*)
          {| rule_hyps := [{| fact_R := (inr aux');
                             fact_args :=
                               [var_expr (inr x)(*\sum_{j < i} body(j)*);
                                var_expr (inr i') (*index into aux'*)] ++
                                map var_expr dimvars(*arbitrary idx into summand*) |};
                           {| fact_R := (inr aux);
                             fact_args :=
                               [var_expr (inr y)(*body(i)*);
                                var_expr (inr i') (*index into aux*)] ++
                                map var_expr dimvars (*arbitrary idx into summand*) |}];
            rule_concl := {| fact_R := (inr aux');
                            fact_args :=
                              [fun_expr (fn_R fn_SAdd) [var_expr (inr x);
                                                       var_expr (inr y)];
                               fun_expr (fn_Z fn_ZPlus) [var_expr (inr i');
                                                        fun_expr (fn_Z (fn_ZLit 1%Z)) []]] ++
                               map var_expr dimvars (*arbitrary idx into accumulated sum*) |} |};
          (*set out (\sum_j body(j), idxs)*)
          {| rule_hyps := [{| fact_R := (inr aux');
                             fact_args :=
                               [var_expr (inr x)(*\sum_j body(j)*);
                                lower_idx hi] ++
                                map var_expr dimvars(*arbitrary idx into sum*) |}];
            rule_concl := {| fact_R := out;
                            fact_args :=
                              var_expr (inr x) ::
                                map lower_idx (map fst idxs_bds) ++
                                map var_expr dimvars(*arbitrary idx into sum*) |} |}]
  | Scalar s =>
      let '(val, hyps, _) := lower_Sexpr O s in
      [{| rule_hyps := hyps; rule_concl := {| fact_R := out; fact_args := val :: map lower_idx (map fst idxs_bds) |} |}]
  | _ => nil end.
Print eval_expr. Print context. Print valuation.
Print prog_impl_fact.
Check eval_expr. Print result. Search result. Print result_lookup_Z_option.
Print lower_Sexpr. Print eval_Sexpr. Print expr_context. Print fmap. Locate "$?".
Search eval_get. Search result. Print result_lookup_Z.

Search eval_get.

(*I thought about using fmaps here, but it's not even clear to me that that is possible.
  How do you iterate over an fmap?  i could get the domain, which is a 'set', but idk
  how to iterate over a set, either...*)
Definition substn_of (v : valuation) : var -> option tfn :=
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
    + apply eval_Zexpr_to_substn. assumption.
    + assumption.
Qed.

Print lower_Sexpr. Check prog_impl_fact. Print interp_expr.

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

Definition domain_in_ints low high (substn : var -> option tfn) :=
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
Lemma lower_Sexpr_correct sh v ec s (datalog_ctx : list (rule rel var tfn)):
  (forall x r idxs val,
      ec $? x = Some r ->
      result_lookup_Z' idxs r val ->
      prog_impl_fact interp_fn datalog_ctx (inl x, inr (toR val) :: (map inl idxs))) ->
  forall val name val0 hyps name',
    eval_Sexpr sh v ec s val ->
    lower_Sexpr name s = (val0, hyps, name') ->
    exists hyps' substn,
      name <= name' /\
      domain_in_ints name name' substn /\
        Forall2 (interp_fact interp_fn) (map (subst_in_fact (substn)) (map (subst_in_fact (substn_of v)) hyps)) hyps' /\
        Forall (prog_impl_fact interp_fn datalog_ctx) hyps' /\
        interp_expr interp_fn (subst_in_expr substn (subst_in_expr (substn_of v) val0)) (inr (toR val)).
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

(*how am i supposed to do induction on results?*)
Fixpoint result_sz (r : result) :=
  match r with
  | Result.S _ => O
  | V v => Datatypes.S (fold_right Nat.max O (map result_sz v))
  end.

Check result_ind.
Lemma result_ind' P :
  (forall z, P (Result.S z)) ->
  (forall v, Forall P v -> P (V v)) ->
  forall r, P r.
Proof.
  intros * H1 H2 r. remember (result_sz r) as sz eqn:E.
  assert (Hr: (result_sz r < Datatypes.S sz)%nat) by lia.
  clear E. revert r Hr. induction (Datatypes.S sz); intros.
  - lia.
  - destruct r; auto. apply H2. induction v.
    + constructor.
    + constructor.
      -- apply IHn. simpl in Hr. lia.
      -- apply IHv. simpl in Hr. simpl. lia.
Qed.
Print add_result.
Lemma add_result_has_shape a b c :
  exists sh,
  add_result a b c ->
  result_has_shape c sh.
Proof.
  revert a b. induction c using result_ind'; intros a b; subst.
  - eexists. econstructor.
  - destruct v.
    + eexists. econstructor.
    + inversion H. subst. clear H. specialize (H2 a b). destruct H2 as [sh H2].
      eexists. intros H. inversion H. subst. clear H. inversion H5. subst. clear H5.
      Abort. (*not true*)
    
Lemma invert_eval_sum sh v ctx i lo hi body r :
  eval_expr sh v ctx (Sum i lo hi body) r ->
  exists loz hiz summands,
    eval_Zexpr_Z v lo = Some loz /\
      eval_Zexpr_Z v hi = Some hiz /\
      (forall idxs val,
          result_lookup_Z' idxs r val ->
          exists scalar_summands,
            Forall2 (result_lookup_Z' idxs) summands scalar_summands /\
              toR val = fold_right (fun a b => toR a + b)%R 0%R scalar_summands) /\
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
  destruct IHeval_expr2 as (loz'&hiz'&summands'&Hloz'&Hhiz'&Hsummands'&IH).
  exists loz, hiz, (r :: summands'). intuition.
  + pose proof add_result_same_domain_bw as H'. specialize (H' _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)). destruct H' as (x'&y'&Hx'&Hy'&Hval). subst.
    specialize (Hsummands' _ _ ltac:(eassumption)). destruct Hsummands' as (ss&Hss1&Hss2).
    exists (x' :: ss). split.
    -- constructor; [eassumption|]. assumption.
    -- simpl. rewrite <- Hss2. destruct x', y'; simpl; ring.
  + clear Hsummands'.
    assert (Hor : (i' = loz \/ loz + 1 <= i')%Z) by lia.
    destruct Hor as [Hle|Heq].
    -- subst. replace (Z.to_nat _) with O by lia. simpl. assumption.
    -- simpl in Hloz'. rewrite H0 in Hhiz'. inversion Hhiz'. subst. clear Hhiz'.
       rewrite H in Hloz'. inversion Hloz'. subst. clear Hloz'.
       specialize (IH i' ltac:(lia)). destruct IH as (_&_&IH).
       replace (Z.to_nat (i' - loz)) with (Datatypes.S (Z.to_nat (i' - (loz + 1)))) by lia.
       simpl. assumption.
Qed.

Lemma disj_comm {A B : Type} (x y : A -> option B) : disj x y -> disj y x.
Proof. cbv [disj]. eauto. Qed.

Definition idx_map (x : list tfn) : var -> option tfn :=
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

Print ATLexpr. Print sizeof.
Print eval_expr.

Check eval_Zexpr_includes_valuation.
Lemma eval_Zexpr_Z_includes :
  forall (v : valuation) (l0 : Zexpr) (zs : Z),
       eval_Zexpr_Z v l0 = Some zs ->
       forall v' : fmap Var.var Z, v $<= v' -> eval_Zexpr_Z v' l0 = Some zs.
Proof. Admitted.
Search eval_Zexpr.
Lemma is_succ n :
  1 <= n ->
  n = Datatypes.S (n - 1).
Proof. lia. Qed.
Print result_has_shape.

Print result_has_shape.

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
    
Lemma lower_correct e out sh v ctx r datalog_ctx :
  eval_expr sh v ctx e r ->
  (forall x (r : result) (idxs : list Z) (val : scalar_result),
      ctx $? x = Some r ->
      result_lookup_Z' idxs r val ->
      prog_impl_fact interp_fn datalog_ctx (inl x, inr (toR val) :: map inl idxs)) ->
  forall idxs name val idx_ctx idx_ctx',
    result_lookup_Z' idxs r val ->
    Forall2 (interp_expr interp_fn) (map (subst_in_expr (substn_of v)) (map lower_idx (map fst idx_ctx))) idx_ctx' ->
        prog_impl_fact interp_fn (lower e out name idx_ctx ++ datalog_ctx) (out, inr (toR val) :: idx_ctx' ++ map inl idxs).
Proof.
  revert out sh v ctx r datalog_ctx. induction e. 
  { simpl. intros. apply invert_eval_gen in H.
    destruct H as (loz&hiz&rl&Hrl&Hlen&Hlo&Hhi&Hbody). subst.
    move IHe at bottom. inversion H1. subst. clear H1.
    move Hbody at bottom. specialize (Hbody (loz + x)%Z).
    epose proof nth_error_Some as E'. specialize E' with (1 := H4).
    specialize (Hbody ltac:(lia)). clear E'.
    destruct Hbody as (Hdom&_&Hbody). replace (loz + x - loz)%Z with x in Hbody by lia.
    rewrite H4 in Hbody. specialize IHe with (1 := Hbody). specialize IHe with (1 := H0).
    specialize IHe with (1 := H6). eassert _ as blah.
    2: epose proof (IHe _ _ (idx_ctx ++ [((! i ! - lo)%z, (hi - lo)%z)])%list _ blah) as IHe_; clear IHe.
    { repeat rewrite map_app. apply Forall2_app.
      - move H2 at bottom. repeat rewrite <- Forall2_map_l in *.
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
        specialize H' with (1 := H0) (2 := H6) (3 := E).
        destruct H' as (hyps'&substn&_&Hsubstn&Hhyps&Hhyps'&Hval0).
        inversion H1. subst. clear H1. econstructor.
        { constructor. simpl. exists (compose substn (substn_of v)). split.
          - cbv [subst_in_fact]. simpl. constructor. simpl. repeat constructor.
            + rewrite subst_in_expr_subst_in_expr in Hval0. apply Hval0.
            + rewrite app_nil_r. move H2 at bottom.
              repeat rewrite <- Forall2_map_l in *. eapply Forall2_impl. 2: eassumption.
              simpl. intros a b Hab. pose proof interp_expr_subst_more as Hab'.
              specialize Hab' with (2 := Hab). rewrite Hab'. 1: assumption.
              apply compose_extends_r.
          - rewrite map_map in Hhyps. erewrite map_ext. 1: eassumption.
            simpl. intros. rewrite subst_in_fact_subst_in_fact. reflexivity. }
        intros. eapply prog_impl_fact_subset.
        2: { rewrite Forall_forall in Hhyps'. apply Hhyps'. assumption. }
        simpl. auto. }
  { intros. specialize IHe with (2 := H0). apply invert_eval_sum in H.
    destruct H as (loz&hiz&summands&Hloz&Hhiz&Hsummands&Hbody).
    specialize Hsummands with (1 := H1). destruct Hsummands as (ss&Hs&Hss).
    econstructor.
    - simpl. apply Exists_app. left. apply Exists_app. simpl. right.
      apply Exists_cons_tl. apply Exists_cons_tl. constructor. simpl.
      exists (compose
           (substn_of v)
           (map_cons
              (inr (Datatypes.length (sizeof e))) (Some (fn_R (fn_SLit (toR val))))
              (idx_map (map (fun x => fn_Z (fn_ZLit x)) idxs)))).
      simpl. cbv [subst_in_fact]. simpl. split.
      { constructor. simpl. constructor.
        { cbv [compose map_cons]. simpl. rewrite Nat.eqb_refl. repeat econstructor. }
        rewrite map_app. apply Forall2_app.
        - repeat rewrite <- Forall2_map_l in *. eapply Forall2_impl. 2: eassumption.
          simpl. intros a b Hab. eapply interp_expr_subst_more'. 2: eassumption.
          apply compose_extends_l. apply disj_comm. Search (disj _ (substn_of _)).
          eapply domain_in_ints_disj_substn_of with (low := 0) (high := Datatypes.S (length idxs)).
          apply domain_in_ints_cons.
          + eapply domain_in_ints_weaken. 3: apply domain_in_ints_idx_map. 1: lia.
            rewrite map_length. lia.
          + (*need that length (sizeof e) = length idxs*)
      
    
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
