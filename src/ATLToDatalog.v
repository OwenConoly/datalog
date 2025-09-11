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
  (*this list is backwards compared to the other lowering alg*)
  (*also, i don't use the bounds at all (yet)*)
  (idxs_bds : list (Zexpr * Zexpr))
  : list trule :=
  match e with
  | Gen i lo hi body =>
      lower body out name (idxs_bds ++ [(ZMinus (ZVar i) lo, ZMinus hi lo)])
  | Sum i lo hi body =>
      let x := O in
      let i' := Datatypes.S x in
      let y := Datatypes.S i' in
      let dimvars := map inr (seq (Datatypes.S y) (length (sizeof body))) in
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
                               map var_expr dimvars(*arbitrary idx into sum*) |} |}]
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
    { apply domain_in_ints_cons. 2: cbv [succ]; lia. apply domain_in_ints_empty. }
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

Print eval_expr. Search (eval_expr _ _ _ (Gen _ _ _ _)).
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
  
Lemma lower_correct e out sh v ctx r datalog_ctx :
  eval_expr sh v ctx e r ->
  (forall (x : rel) (r : result) (idxs : list Z) (val : scalar_result),
      ctx $? x = Some r ->
      result_lookup_Z_option' idxs r = Some val ->
      prog_impl_fact interp_fn datalog_ctx (x, inr (toR val) :: map inl idxs)) ->
  forall idxs val idx_ctx idx_ctx',
    result_lookup_Z_option' idxs r = Some val ->
    Forall2 (interp_expr interp_fn) (map (subst_in_expr (substn_of v)) (map lower_idx (map fst idx_ctx))) idx_ctx' ->
        prog_impl_fact interp_fn (lower e out idx_ctx ++ datalog_ctx) (out, inr (toR val) :: idx_ctx' ++ map inl idxs). Print lower.
Proof.
  revert out sh v ctx r datalog_ctx. induction e. 
  { simpl. intros. apply invert_eval_gen in H.
    destruct H as (loz&hiz&rl&Hrl&Hlen&Hlo&Hhi&Hbody). subst.
    move IHe at bottom.
    destruct idxs; simpl in H1; [congruence|].
    assert (0 <= z)%Z as Hz.
    { destruct z; [lia|lia|congruence]. }
    eassert _ as Hz'.
    { destruct z eqn:Ez; [exact H1|exact H1|congruence]. }
    clear H1. move Hbody at bottom. specialize (Hbody (loz + z)%Z).
    destruct (nth_error rl (Z.to_nat z)) eqn:E. 2: congruence.
    epose proof nth_error_Some as E'. specialize E' with (1 := E).
    specialize (Hbody ltac:(lia)). clear E'.
    destruct Hbody as (Hdom&_&Hbody). replace (loz + z - loz)%Z with z in Hbody by lia.
    rewrite E in Hbody. specialize IHe with (1 := Hbody). specialize IHe with (1 := H0).
    specialize IHe with (1 := Hz'). eassert _ as blah.
    2: epose proof (IHe _ (idx_ctx ++ [((! i ! - lo)%z, (hi - lo)%z)])%list _ blah) as IHe_; clear IHe.
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
    replace (loz + z - loz)%Z with z in IHe_ by lia. simpl. apply IHe_. }
  12: { intros. simpl. destruct (lower_Sexpr O s) as [ [val0 hyps] name'] eqn:E.
        simpl. inversion H. subst. clear H. pose proof lower_Sexpr_correct as H'.
        specialize H' with (1 := H0) (2 := H6) (3 := E).
        destruct H' as (hyps'&substn&_&Hsubstn&Hhyps&Hhyps'&Hval0).
        destruct idxs.
        2: { simpl in H1. destruct z; congruence. }
        econstructor.
        { constructor. simpl. exists (compose substn (substn_of v)). split.
          - cbv [subst_in_fact]. simpl. constructor. simpl. repeat constructor.
            + rewrite subst_in_expr_subst_in_expr in Hval0. Search val. simpl in H1.
              inversion H1. subst. clear H1. apply Hval0.
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
