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
From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics.

From coqutil Require Import Map.Interface Map.Properties.

Import ListNotations.

Section __.
  (*relations, variables, and functions.  constants are 0-ary functions.*)
  Context (rel: Type) (var: Type) (fn: Type) (aggregator: Type).
  Context (T : Type).
  (*returning None means inputs not in domain (e.g., number of args was wrong)*)
  Context (interp_fun : fn -> (list T) -> option T).
  (*if x represents a finite set, then get_set x = Some ([x1; ...; xn]), where x1, ..., xn are the elements of the set*)
  Context (get_set : T -> option (list T)).
  (*agg_id sum = O, agg_id prod = 1, agg_id min = inf, etc*)
  (*interp_agg takes an aggregator and returns the corresponding binop...
    arguably type should be aggregator -> T -> T -> option T,
    but i dont want to bother with that*)
  Context (agg_id : aggregator -> T) (interp_agg : aggregator -> T -> T -> T).
  Context {context : map.map var T} {context_ok : map.ok context}.
  Context {var_eqb : var -> var -> bool} {var_eqb_spec :  forall x0 y0 : var, BoolSpec (x0 = y0) (x0 <> y0) (var_eqb x0 y0)}.

  Inductive fact (expr : Type) :=
    { fact_R : rel;
      fact_args : list (expr) }.
  Arguments fact_R {_}.
  Arguments fact_args {_}.
  
  (*avoid generating useless induction principle*)
  Unset Elimination Schemes.
  Inductive expr :=
  | lit_expr (t : T)
  | var_expr (v : var)
  | fun_expr (f : fn) (args : list (expr))
  (* for example, (agg_expr sum i [] s body nil) is \sum_{i \in s} body.
     in general, the hyps argument may bind some variables vs other than i.
     for instance, (agg_expr sum i [j] s (var_expr j) [R(i, j)]) is \sum_{i \in s} j,
     where for each i, the body j may (nondeterministically) evaluate to any j such that
     R(i, j) holds.
   *)
  | agg_expr (a : aggregator) (i : var) (vs : list var) (s : expr) (body: expr) (hyps: list (fact expr)).
  Set Elimination Schemes.

  Definition fact_map {expr: Type} (f : expr -> expr) (fct : fact expr) :=
    {| fact_R := fct.(fact_R); fact_args := map f fct.(fact_args) |}.

  Definition remove_many (vs : list var) (m : context) :=
    fold_left map.remove vs m.
  
  Fixpoint subst_in_expr (ctx : context) (e : expr) :=
    match e with
    | lit_expr t => lit_expr t
    | var_expr v => match map.get ctx v with
                   | Some t => lit_expr t
                   | None => var_expr v
                   end
    | fun_expr f args => fun_expr f (map (subst_in_expr ctx) args)
    | agg_expr a i vs s body hyps =>
        agg_expr a i vs (subst_in_expr ctx s) (subst_in_expr (remove_many vs ctx) body) (map (fact_map (subst_in_expr (remove_many vs ctx))) hyps)
    end.

  Definition subst_in_fact s := fact_map (subst_in_expr s).

  Definition fact_size {expr: Type} (expr_size : expr -> nat) (fct : fact expr) :=
    fold_right Nat.max O (map expr_size fct.(fact_args)).

  Fixpoint expr_size (e : expr) :=
    match e with
    | lit_expr _ => O
    | var_expr _ => O
    | fun_expr _ args => S (fold_right Nat.max O (map expr_size args))
    | agg_expr a i vs s body hyps => S (Nat.max (expr_size s) (Nat.max (expr_size body) (fold_right Nat.max O (map (fact_size expr_size) hyps))))
    end.
  
  (*This is stupid.  how do people normally do it?*)
  Lemma expr_ind P :
    (forall t, P (lit_expr t)) ->
    (forall v, P (var_expr v)) ->
    (forall f args,
        Forall P args ->
        P (fun_expr f args)) ->
    (forall a i vs s body hyps,
        P s ->
        P body ->
        Forall (fun hyp => Forall P hyp.(fact_args)) hyps ->
        P (agg_expr a i vs s body hyps)) ->
    forall e, P e.
  Proof.
    intros. remember (expr_size e) as sz eqn:E.
    assert (He: (expr_size e < Datatypes.S sz)%nat) by lia.
    clear E. revert e He. induction (Datatypes.S sz); intros.
    - lia.
    - destruct e; simpl in He; auto.
      + apply H1. clear -IHn He. induction args; [constructor|].
        simpl in *. constructor; [|apply IHargs; lia]. apply IHn. lia.
      + apply H2. 1,2: apply IHn; lia. clear -IHn He. induction hyps; [constructor|].
        simpl in *. constructor; [|apply IHhyps; lia]. clear IHhyps. cbv [fact_size] in He.
        remember (fact_args a) as args eqn:E. clear E. induction args; [constructor|].
        simpl in *. constructor; [|apply IHargs; lia]. apply IHn. lia.
  Qed.

  Inductive interp_fact' (interp_expr : expr -> T -> Prop) : fact expr -> rel * list T -> Prop :=
  | mk_interp_fact f args' :
    Forall2 interp_expr f.(fact_args) args' ->
    interp_fact' interp_expr f (f.(fact_R), args').

  Unset Elimination Schemes.
  Inductive interp_expr (fact_holds : rel * list T -> Prop) : context -> expr -> T -> Prop :=
  | interp_lit_expr ctx t : interp_expr _ ctx (lit_expr t) t
  | interp_fun_expr ctx f args args' x :
    Forall2 (interp_expr _ ctx) args args' ->
    interp_fun f args' = Some x ->
    interp_expr _ ctx (fun_expr f args) x
  | interp_agg_expr ctx a i vs S S' is' bodies' body hyps hyps' :
    interp_expr _ ctx S S' ->
    get_set S' = Some is' ->
    Forall2 (fun i' body' =>
               exists vs',
                 let s := map.put (map.of_list (combine vs vs')) i i' in
                 Forall2 (interp_fact' (interp_expr _ (map.putmany ctx s))) hyps hyps' /\
                   Forall fact_holds hyps' /\
                   interp_expr _ (map.putmany ctx s) body body')
      is' bodies' ->
    interp_expr _ ctx (agg_expr a i vs S body hyps) (fold_right (interp_agg a) (agg_id a) bodies').
  Set Elimination Schemes.

  Definition interp_fact fact_holds ctx := interp_fact' (interp_expr fact_holds ctx).
  
  Record rule :=
    { rule_hyps: list (fact expr);
      rule_concls: list (fact expr) }.

  Definition subst_in_rule (s : context) (r : rule) : rule :=
    {| rule_hyps := map (subst_in_fact s) r.(rule_hyps);
      rule_concls := map (subst_in_fact s) r.(rule_concls) |}.
  
  (* Fixpoint appears_in_expr (v : var) (e : expr) := *)
  (*   match e with *)
  (*   | fun_expr _ args => fold_left (fun acc arg => acc \/ appears_in_expr v arg) args False *)
  (*   | var_expr v0 => v0 = v *)
  (*   end. *)

  (* Definition appears_in_fact (v : var) (f : fact) := *)
  (*   Exists (appears_in_expr v) f.(fact_args). *)
  (* Check eq. (*WHY*) Locate "=". *)
  (* Definition barely_appears_in_fact (v : var) (f : fact) := *)
  (*   Exists (Logic.eq (var_expr v)) f.(fact_args). *)
  
  (* Definition good_rule (r : rule) := *)
  (*   forall v, Exists (appears_in_fact v) r.(rule_concls) \/ Exists (appears_in_fact v) r.(rule_hyps) -> *)
  (*        Exists (barely_appears_in_fact v) r.(rule_hyps). *)

  (* Definition good_prog (p : list rule) := Forall good_rule p. *)

  (*"small-step" semantics, with pftree as "star operator", were more appealing when exprs didn't have facts in them... now i'm not sure there'd be any point to it, since the small-step definition would still be nontrivially recursive.
    or i guess it wouldn't have to be recursive, but i'd have to pull out hyps from facts within exprs and so on; this would be annoying.
    so i'll stick with big-step semantics for now.  which might be annoying if i try to prove an interpeter?  i definitely should prove an interpreter as a sanity check, since semantics are getting a bit more complicated now.
   *)
  Inductive pftree {T : Type} (P : T -> list T -> Prop) : T -> Prop :=
  | mkpftree x l :
    P x l ->
    Forall (pftree P) l ->
    pftree P x.

  Inductive prog_impl_fact (p : list rule) : rel * list T -> Prop :=
  | impl_step f hyps pif :
    Exists
      (fun r =>
         exists ctx,
           Exists (fun c => interp_fact pif ctx c f) r.(rule_concls) /\
             Forall2 (interp_fact pif ctx) r.(rule_hyps) hyps)
      p ->
    Forall pif hyps ->
    (*do this to get good induction principle*)
    (forall f', pif f' -> prog_impl_fact p f') ->
    prog_impl_fact p f.

  Lemma mk_pif p f hyps :
    Exists
      (fun r =>
         exists ctx,
           Exists (fun c => interp_fact (prog_impl_fact p) ctx c f) r.(rule_concls) /\
             Forall2 (interp_fact (prog_impl_fact p) ctx) r.(rule_hyps) hyps)
      p ->
    Forall (prog_impl_fact p) hyps ->
    prog_impl_fact p f.
  Proof. econstructor; eauto. Qed.

  Lemma prog_impl_fact_subset (p1 p2 : list rule) f :
    (forall x, In x p1 -> In x p2) ->
    prog_impl_fact p1 f ->
    prog_impl_fact p2 f.
  Proof.
    intros ? H. induction H. apply Exists_exists in H.
    econstructor. 2,3: eassumption. apply Exists_exists.
    destruct H as (?&?&?). eexists. intuition eauto.
  Qed.

  Lemma Forall2_map_l (A B C : Type) R (f : A -> B) (l1 : list A) (l2 : list C) :
    Forall2 (fun x => R (f x)) l1 l2 <->
      Forall2 R (map f l1) l2.
  Proof.
    split; intros H.
    - induction H. 1: constructor. constructor; assumption.
    - remember (map f l1) as l1' eqn:E. revert l1 E. induction H; intros l1 Hl1.
      + destruct l1; inversion Hl1. constructor.
      + destruct l1; inversion Hl1. subst. constructor; auto.
  Qed.

  Lemma extends_putmany_putmany (m1 m2 m : context) :
    map.extends m1 m2 ->
    map.extends (map.putmany m1 m) (map.putmany m2 m).
  Proof.
    intros H. cbv [map.extends]. intros x y Hx. Search map.putmany.
    edestruct @map.putmany_spec as [H'|H']. 1,2: eassumption.
    - destruct H' as [v (H1&H2)]. rewrite Hx in H2. invert H2.
      apply map.get_putmany_right. assumption.
    - destruct H' as (H1&H2). rewrite map.get_putmany_left.
      + rewrite H2 in Hx. apply H. assumption.
      + assumption.
  Qed.
  
  Lemma interp_expr_subst_more pif s s' v e :
    map.extends s' s ->
    interp_expr pif s e v ->
    interp_expr pif s' e v.
  Proof.
    intros Hext H. revert s s' Hext v H. induction e; intros s s' Hext.
    - intros v Hv. invert Hv. constructor.
    - intros t Hv. invert Hv.
    - intros v Hv. invert Hv. econstructor; eauto. clear H5. induction H3.
      + constructor.
      + invert H. constructor; eauto.
    - intros. simpl in *. invert H0. econstructor; eauto.
      eapply Forall2_impl; [|eassumption]. simpl.
      intros x1 x2 (vs'&H1&H2&H3).
      eexists. split.
      { clear -H H1. (*why*) clear H9 H10 H11 H3 H2 IHe1 IHe2.
        instantiate (1 := hyps'). instantiate (1 := vs'). induction H1; [constructor|].
        invert H. constructor; auto. clear H5 IHForall2 H1. invert H0. constructor.
        remember (fact_args x) as y eqn:E. clear E.
        induction H; [constructor|]. invert H4. constructor; auto.
        eapply H3; eauto. apply extends_putmany_putmany. assumption. }
      eauto using extends_putmany_putmany.
  Qed.

  Lemma interp_fact_subst_more pif s s' f f' :
    map.extends s' s ->
    interp_fact pif s f f' ->
    interp_fact pif s' f f'.
  Proof.
    intros. invert H0. constructor. eapply Forall2_impl; [|eassumption].
    eauto using interp_expr_subst_more.
  Qed.
End __.
Arguments Build_rule {_ _ _}.
Arguments Build_fact {_ _ _}.
Arguments fun_expr {_ _}.
Arguments var_expr {_ _}.
Arguments prog_impl_fact {_ _ _ _}.
Arguments fact_args {_ _ _}.
Arguments subst_in_expr {_ _}.
Arguments interp_expr {_ _ _}.
Arguments interp_fact {_ _ _ _}.
Arguments subst_in_fact {_ _ _}.
Arguments fact_R {_ _ _}.
Arguments rule_concls {_ _ _}.
Arguments rule_hyps {_ _ _}.
