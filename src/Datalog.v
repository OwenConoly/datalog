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
From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics.

From coqutil 

Require Import Datalog.Maps.

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

  Inductive fact (expr : Type) :=
    { fact_R : rel;
      fact_args : list (expr) }.
  Arguments fact_R {_}.
  Arguments fact_args {_}.
  
  (*avoid generating useless induction principle*)
  Unset Elimination Schemes.
  Inductive expr :=
  | fun_expr (f : fn) (args : list (expr))
  | var_expr (v : var)
  (* for example, (agg_expr sum i [] S body nil) is \sum_{i \in S} body.
     in general, the hyps argument may bind some variables vs other than i.
     for instance, (agg_expr sum i [j] S (var_expr j) [R(i, j)]) is \sum_{i \in S} j,
     where for each i, the body j may (nondeterministically) evaluate to any j such that
     R(i, j) holds.
   *)
  | agg_expr (a : aggregator) (i : var) (vs : list var) (S : expr) (body: expr) (hyps: list (fact expr)).
  Set Elimination Schemes.

  Definition fact_map {expr: Type} (f : expr -> expr) (fct : fact expr) :=
    {| fact_R := fct.(fact_R); fact_args := map f fct.(fact_args) |}.

  Fixpoint subst_in_expr (s : var -> option fn) (e : expr) :=
    match e with
    | fun_expr f args => fun_expr f (map (subst_in_expr s) args)
    | var_expr v => match s v with
                   | Some f => fun_expr f []
                   | None => var_expr v
                   end
    | agg_expr a i vs S_ body hyps =>
        agg_expr a i vs (subst_in_expr s S_) (subst_in_expr (removemany vs s) body) (map (fact_map (subst_in_expr (removemany vs s))) hyps)
    end.

  Definition subst_in_fact s := fact_map (subst_in_expr s).

  Definition fact_size {expr: Type} (expr_size : expr -> nat) (fct : fact expr) :=
    fold_right Nat.max O (map expr_size fct.(fact_args)).

  Fixpoint expr_size (e : expr) :=
    match e with
    | fun_expr _ args => S (fold_right Nat.max O (map expr_size args))
    | var_expr _ => O
    | agg_expr a i vs s body hyps => S (Nat.max (expr_size s) (Nat.max (expr_size body) (fold_right Nat.max O (map (fact_size expr_size) hyps))))
    end.
  
  (*This is stupid.  how do people normally do it?*)
  Lemma expr_ind P :
    (forall f args,
        Forall P args ->
        P (fun_expr f args)) ->
    (forall v, P (var_expr v)) ->
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
      + apply H. clear -IHn He. induction args; [constructor|].
        simpl in *. constructor; [|apply IHargs; lia]. apply IHn. lia.
      + apply H1. 1,2: apply IHn; lia. clear -IHn He. induction hyps; [constructor|].
        simpl in *. constructor; [|apply IHhyps; lia]. clear IHhyps. cbv [fact_size] in He.
        remember (fact_args a) as args eqn:E. clear E. induction args; [constructor|].
        simpl in *. constructor; [|apply IHargs; lia]. apply IHn. lia.
  Qed.

  Inductive interp_fact' (interp_expr : expr -> T -> Prop) : fact expr -> rel * list T -> Prop :=
  | mk_interp_fact f args' :
    Forall2 interp_expr f.(fact_args) args' ->
    interp_fact' interp_expr f (f.(fact_R), args').
  
  Unset Elimination Schemes.
  Inductive interp_expr (fact_holds : rel * list T -> Prop) : expr -> T -> Prop :=
  | interp_fun_expr f args args' x :
    Forall2 (interp_expr fact_holds) args args' ->
    interp_fun f args' = Some x ->
    interp_expr fact_holds (fun_expr f args) x
  | interp_agg_expr a i vs S S' is' bodies' body hyps hyps' :
    interp_expr fact_holds S S' ->
    get_set S' = Some is' ->
    Forall2 (fun i' body' =>
               exists s fi,
                 (*this is horrible; i should have literals built in maybe, instead of calling them functions*)
                 s i = Some fi /\
                   interp_expr _ (fun_expr fi []) i' /\
                   Forall2 (interp_fact' (interp_expr _)) (map (subst_in_fact s) hyps) hyps' /\
                   Forall fact_holds hyps' /\
                   interp_expr _ (subst_in_expr s body) body')
      is' bodies' ->
    interp_expr _ (agg_expr a i vs S body hyps) (fold_right (interp_agg a) (agg_id a) bodies').
  Set Elimination Schemes.

  Definition interp_fact fact_holds := interp_fact' (interp_expr fact_holds).
  
  Record rule :=
    { rule_hyps: list (fact expr);
      rule_concls: list (fact expr) }.

  Definition subst_in_rule (s : var -> option fn) (r : rule) : rule :=
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
         exists s,
           let r' := subst_in_rule s r in
           Exists (fun c => interp_fact pif c f) r'.(rule_concls) /\
             Forall2 (interp_fact pif) r'.(rule_hyps) hyps)
      p ->
    Forall pif hyps ->
    (*do this to get good induction principle*)
    (forall f', pif f' -> prog_impl_fact p f') ->
    prog_impl_fact p f.

  Lemma mk_pif p f hyps :
    Exists
      (fun r =>
         exists s,
           let r' := subst_in_rule s r in
           Exists (fun c => interp_fact (prog_impl_fact p) c f) r'.(rule_concls) /\
             Forall2 (interp_fact (prog_impl_fact p)) r'.(rule_hyps) hyps)
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

  Definition extends {A B : Type} (f1 f2 : A -> option B) :=
    forall x y, f2 x = Some y -> f1 x = Some y.
  
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
  
  Lemma interp_expr_subst_more pif s s' v e :
    extends s' s ->
    interp_expr pif (subst_in_expr s e) v ->
    subst_in_expr s' e = subst_in_expr s e.
  Proof.
    intros Hext H. revert v H. induction e.
    - intros v Hv. simpl in *. inversion Hv. subst. clear Hv. f_equal.
      apply map_ext_Forall. clear -H H2. revert args' H H2.
      induction args; [constructor|]. intros args' H H2.
      inversion H. subst. clear H. inversion H2. subst.
      constructor; eauto.
    - intros. simpl in *. destruct (s v) eqn:E.
      + apply Hext in E. rewrite E. reflexivity.
      + inversion H.
    - intros. simpl in *. invert H0. f_equal; eauto. Abort. (*not true anymore*)

  (*this is only true if i handle shadowing in a reasonable way..*)
  Lemma interp_expr_subst_more' pif s s' v e :
    extends s' s ->
    interp_expr pif (subst_in_expr s e) v ->
    interp_expr pif (subst_in_expr s' e) v.
  Proof.
    intros Hext H. revert v s s' Hext H. induction e.
    - intros v s s' Hext Hv. simpl in *. invert Hv. econstructor; eauto.
      clear - H H2 Hext. revert args' H2.
      induction H; intros args' H1; invert H1; simpl; constructor; eauto.
    - intros. simpl in *. destruct (s v) eqn:E.
      + apply Hext in E. rewrite E. assumption.
      + invert H.
    - intros. simpl in *. invert H0. econstructor; eauto.
      eapply Forall2_impl; eauto. simpl. intros x1 x2 (s0&fi&H1&H2&H3&H4&H5).
      do 2 eexists. split; [eassumption|]. split; [assumption|].
      split; [|split]; [|eassumption|].
      + clear -H H3. revert hyps' H3.
        induction H; intros args' H1; invert H1; simpl; constructor; auto.
        invert H4. simpl. eassert (fact_R x = _) as ->. 2: econstructor. 1: reflexivity.
        simpl in *. apply IHForall. eapply Forall2_impl. 2: eauto. idtac.


  Qed.

  Lemma interp_fact_subst_more s s' v f :
    extends s' s ->
    interp_fact (subst_in_fact s f) v ->
    subst_in_fact s' f = subst_in_fact s f.
  Proof.
    intros. inversion H0. subst. clear H0. cbv [subst_in_fact] in *. simpl in *. f_equal.
    apply map_ext_Forall. apply Forall2_map_l in H1. remember (fact_args f) as x eqn:E.
    clear E. revert args' H1. induction x; intros args' H1. 1: constructor.
    inversion H1. subst. clear H1.
    constructor; eauto using interp_expr_subst_more.
  Qed.    
  
  Lemma interp_fact_subst_more' s s' v f :
    extends s' s ->
    interp_fact (subst_in_fact s f) v ->
    interp_fact (subst_in_fact s' f) v.
  Proof.
    intros. erewrite interp_fact_subst_more; eauto.
  Qed.

  Definition compose {A B : Type} (s s' : A -> option B) :=
    fun x => match s' x with
          | Some y => Some y
          | None => s x
          end.

  Lemma subst_in_expr_subst_in_expr s s' e :
    subst_in_expr s (subst_in_expr s' e) = subst_in_expr (compose s s') e.
  Proof.
    induction e.
    - simpl. f_equal. rewrite map_map. apply map_ext_Forall. assumption.
    - simpl. cbv [compose]. destruct (s' v); simpl; destruct (s v); reflexivity.
  Qed.

  Lemma subst_in_fact_subst_in_fact s s' f :
    subst_in_fact s (subst_in_fact s' f) = subst_in_fact (compose s s') f.
  Proof.
    cbv [subst_in_fact]. simpl. f_equal. rewrite map_map. apply map_ext.
    intros. apply subst_in_expr_subst_in_expr.
  Qed.

  (* it's a dag if we can keep peeling away nodes that aren't being pointed to*)
  (* Inductive dag : list rule -> Type := *)
  (* | dag_nil : dag [] *)
  (* | dag_cons l1 x l2 : *)
  (*   Forall (fun r => Forall (fun f => f.(fact_R) <> x.(rule_concl).(fact_R)) r.(rule_hyps)) (l1 ++ x :: l2) -> *)
  (*   dag (l1 ++ l2) -> *)
  (*   dag (l1 ++ x :: l2). *)

  (* Context (T_eq_dec : forall (x y : T), {x = y} + {x <> y}). *)
  (* Context (rel_eq_dec : forall (x y : T), {x = y} + {x <> y}). *)

  (* (*very dumb evaluation, mainly to prove something*) *)
  
  (* Fixpoint choose_n (l : list T) (n : nat) : list (list T) := *)
  (*   match n with *)
  (*   | O => [ [] ] *)
  (*   | S n' => flat_map (fun x => map (cons x) (choose_n l n')) l *)
  (*   end. *)

  (* Lemma choose_n_spec l n l' : *)
  (*   length l' = n -> *)
  (*   (forall x, In x l' -> In x l) -> *)
  (*   In l' (choose_n l n). *)
  (* Proof. Admitted. *)

  (* Definition get_substn (arg: expr) (arg' : T) := *)
  (*   match arg with *)
  (*   | fun_expr _ _ => [] *)
  (*   | var_expr v => [(v, arg)] *)
  (*   end. *)

  (* Definition get_fact_substn (f : fact) (f' : rel * list T) := *)
  (*   flat_map (fun '(x, y) => get_substn x y) (List.zip f (snd f')). *)
  
  (* Fixpoint implications (r : rule) (l : list (rel * list T)) : list (rel * list T) := *)
  (*   match l with *)
  (*   |  *)

  (* Lemma dags_terminate p : *)
  (*   dag p -> *)
  (*   exists l, forall f, prog_impl_fact p f -> In f l. *)
  (* Proof. *)
  (*   intros H. induction H. *)
  (*   - exists nil. intros f Hf. invert Hf. invert H. *)
  (*   - destruct IHdag as [l IHl]. *)
  
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
