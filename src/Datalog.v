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

From Datalog Require Import Map Tactics Fp List.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List.

Import ListNotations.

Section __.
  (*relations, variables, functions, and "aggregator functions" (e.g. min, max, sum, prod)*)
  Context {rel var fn aggregator : Type}.
  (* A datalog program talks about facts R(x1, ..., xn), where (R : rel) and (x1 : T), (x2 : T), etc. *)
  Context {T : Type}.
  Context {context : map.map var T} {context_ok : map.ok context}.
  Context {var_eqb : var -> var -> bool} {var_eqb_spec :  forall x0 y0 : var, BoolSpec (x0 = y0) (x0 <> y0) (var_eqb x0 y0)}.
  (*returning None means inputs not in domain (e.g., number of args was wrong)*)
  Context (interp_fun : fn -> (list T) -> option T).
  (*if x represents a finite set, then get_set x = Some ([x1; ...; xn]), where x1, ..., xn are the elements of the set*)
  Context (get_set : T -> option (list T)).
  (*agg_id sum = O, agg_id prod = 1, agg_id min = inf, etc*)
  Context (agg_id : aggregator -> T).
  (*interp_agg takes an aggregator and returns the corresponding binop...
    arguably type should be aggregator -> T -> T -> option T,
    but i dont want to bother with that*)
  Context (interp_agg : aggregator -> T -> T -> T).

  (*avoid generating useless induction principle*)
  Unset Elimination Schemes.
  Inductive expr :=
  | var_expr (v : var)
  | fun_expr (f : fn) (args : list (expr)).
  Set Elimination Schemes.

  Inductive fact :=
    { fact_R : rel;
      fact_args : list expr }.

  Unset Elimination Schemes.
  (*semantics of expressions*)
  Inductive interp_expr (ctx : context) : expr -> T -> Prop :=
  | interp_var_expr x v :
    map.get ctx x = Some v ->
    interp_expr ctx (var_expr x) v
  | interp_fun_expr f args args' x :
    Forall2 (interp_expr ctx) args args' ->
    interp_fun f args' = Some x ->
    interp_expr ctx (fun_expr f args) x.
  Set Elimination Schemes.

  (*semantics of facts*)
  Inductive interp_fact (ctx: context) : fact -> rel * list T -> Prop :=
  | mk_interp_fact f args' :
    Forall2 (interp_expr ctx) f.(fact_args) args' ->
    interp_fact ctx f (f.(fact_R), args').

  Record agg_expr :=
    { agg_agg : aggregator; agg_i : var; agg_vs : list var; agg_s: expr; agg_body: expr; agg_hyps: list fact }.

  Inductive interp_agg_expr (ctx : context) : agg_expr -> T -> list (list (rel * list T)) -> Prop :=
  | mk_interp_agg_expr a i vs s s' i's body's body hyps hyps's result :
    interp_expr ctx s s' ->
    get_set s' = Some i's ->
    Forall3 (fun i' body' hyps' =>
               exists vs' ctx',
                 map.of_list_zip vs vs' = Some ctx' /\
                   let ctx'' := map.putmany (map.put ctx i i') ctx' in
                   Forall2 (interp_fact ctx'') hyps hyps' /\
                     interp_expr ctx'' body body')
      i's body's hyps's ->
    result = fold_right (interp_agg a) (agg_id a) body's ->
    interp_agg_expr _ {| agg_agg := a; agg_i := i; agg_vs := vs; agg_s := s; agg_body := body; agg_hyps := hyps |} result hyps's.

  Record rule := { rule_agg : option (var * agg_expr); rule_concls : list fact; rule_hyps : list fact }.

  (*semantics of rules*)
  Inductive rule_impl' : rule -> rel * list T -> list (rel * list T) -> list (list (rel * list T)) -> Prop :=
  | mk_rule_impl' r agg_hyps's ctx' f' hyps' ctx :
    match r.(rule_agg) with
    | Some (res, aexpr) => exists res',
        interp_agg_expr ctx aexpr res' agg_hyps's /\
          ctx' = map.put ctx res res'
    | None =>
        agg_hyps's = [] /\ ctx' = ctx
    end ->
    Exists (fun c => interp_fact ctx' c f') r.(rule_concls) ->
    Forall2 (interp_fact ctx) r.(rule_hyps) hyps' ->
    rule_impl' r f' hyps' agg_hyps's.

  Hint Constructors rule_impl' : core.

  Definition rule_impl r f hyps'_agg_hyps's :=
    exists hyps' agg_hyps's,
      hyps'_agg_hyps's = hyps' ++ concat agg_hyps's /\ rule_impl' r f hyps' agg_hyps's.

  Lemma normal_rule_impl hyps concls f' hyps' ctx :
    Exists (fun c => interp_fact ctx c f') concls ->
    Forall2 (interp_fact ctx) hyps hyps' ->
    rule_impl {| rule_agg := None; rule_hyps := hyps; rule_concls := concls|} f' hyps'.
  Proof.
    intros. cbv [rule_impl]. exists hyps', nil. rewrite app_nil_r. intuition.
    econstructor; simpl; eauto.
  Qed.

  Unset Elimination Schemes.
  Inductive pftree {T : Type} (P : T -> list T -> Prop) : T -> Prop :=
  | mkpftree x l :
    P x l ->
    Forall (pftree P) l ->
    pftree P x.
  Set Elimination Schemes.

  (*semantics of programs*)
  Definition prog_impl_fact (p : list rule) : rel * list T -> Prop :=
    pftree (fun f' hyps' => Exists (fun r => rule_impl r f' hyps') p).

  Unset Elimination Schemes.
  Inductive partial_pftree {T : Type} (P : T -> list T -> Prop) (Q : T -> Prop) : T -> Prop :=
  | partial_in x :
    Q x ->
    partial_pftree _ _ x
  | partial_step x l :
    P x l ->
    Forall (partial_pftree _ _) l ->
    partial_pftree _ _ x.
  Set Elimination Schemes.
  
  Hint Constructors partial_pftree : core.

  Lemma pftree_ind {U : Type} (P : U -> list U -> Prop) Q :
    (forall x l,
        P x l ->
        Forall (pftree P) l ->
        Forall Q l ->
        Q x) ->
    forall x, pftree P x -> Q x.
  Proof.
    intros H. fix self 2.
    (*i find using fix to be hacky ( e.g. i can't use Forall_impl here :( )
      but i don't know an easy way to get around it.
      trick with expr below doesn't easily work, since pftree goes to Prop.
     *)
    intros x Hx. invert Hx. eapply H; eauto.
    clear -self H1. induction H1; eauto.
  Qed.

  Lemma partial_pftree_ind {U : Type} (P : U -> list U -> Prop) Q R :
    (forall x, Q x -> R x) ->
    (forall x l,
        P x l ->
        Forall (partial_pftree P Q) l ->
        Forall R l ->
        R x) ->
    forall x, partial_pftree P Q x -> R x.
  Proof.
    intros H1 H2. fix self 2. 
    intros x Hx. invert Hx. 1: auto. eapply H2. 1,2: eassumption.
    clear -H0 self. induction H0; eauto.
  Qed.

  Lemma partial_pftree_trans {U : Type} P (x : U) Q :
    partial_pftree P (partial_pftree P Q) x ->
    partial_pftree P Q x.
  Proof. induction 1; eauto. Qed.
    
  Definition prog_impl_implication (p : list rule) : (rel * list T -> Prop) -> rel * list T -> Prop :=
    partial_pftree (fun f' hyps' => Exists (fun r => rule_impl r f' hyps') p).
  
  Lemma pftree_lfp {U : Type} (P : U -> list U -> Prop) :
    equiv (pftree P) (lfp (fun Q x => Q x \/ exists l, P x l /\ Forall Q l)).
  Proof.
    intros x. split; intros Hx.
    - intros S Hfp. move Hx at bottom. induction Hx. eauto.
    - cbv [lfp] in Hx. apply Hx. clear x Hx. cbv [fp]. intros x Hx.
      destruct Hx; eauto. fwd. econstructor; eauto.
  Qed.

  Definition F p Q Px :=
    let '(P, x) := Px in
    P x \/ Q (P, x) \/ exists hyps', Exists (fun r => rule_impl r x hyps') p /\ Forall (fun x => Q (P, x)) hyps'.

  Lemma F_mono p S1 S2 :
    (forall x, S1 x -> S2 x) ->
    (forall x, F p S1 x -> F p S2 x).
  Proof.
    cbv [F]. intros Hle [P x] H. intuition auto. fwd. right. right. eexists.
    split; [eassumption|]. eapply Forall_impl; eauto. simpl. auto.
  Qed.
    
  Definition S_sane {U : Type} (S : (U -> Prop) * U -> Prop) :=
    (forall P x, P x -> S (P, x)) /\
      (forall P1 x P2,
          S (P1, x) ->
          (forall y, P1 y -> S (P2, y)) ->
          S (P2, x)).

  Lemma partial_pftree_lfp {U : Type} (P : U -> list U -> Prop) :
    equiv (fun '(Q0, x) => partial_pftree P Q0 x)
      (lfp (fun Q '(Q0, x) => Q0 x \/ Q (Q0, x) \/ exists l, P x l /\ Forall (fun y => Q (Q0, y)) l)).
  Proof.
    cbv [equiv lfp fp]. intros [Q0 x]. split; intros; fwd.
    - apply H0. induction H; eauto.
      right. right. exists l. split; [assumption|]. eapply Forall_impl; [|eassumption].
      simpl. intros y. apply (H0 (_, _)).
    - apply (H (fun '(Q, x) => _)). clear. intros [Q x]. intros [Hx| [Hx |Hx] ]; eauto.
      fwd. eapply partial_step; eassumption.
  Qed.
      
  Lemma prog_impl_fact_lfp p :
    equiv (fun '(P, f) => prog_impl_implication p P f) (lfp (F p)).
  Proof.
    cbv [equiv]. intros. cbv [prog_impl_implication].
    epose proof partial_pftree_lfp as H. cbv [equiv] in H. rewrite H.
    cbv [F]. reflexivity.
  Qed.

  Lemma S_sane_ext {U : Type} (P Q : (U -> Prop) * U -> Prop) :
    equiv P Q ->
    S_sane P ->
    S_sane Q.
  Proof.
    cbv [equiv S_sane]. intros.
    assert ((forall x, P x -> Q x) /\ (forall x, Q x -> P x)) by (split; intros; apply H; assumption).
    fwd. eauto 9.
  Qed.

  Hint Unfold prog_impl_implication : core.

  Hint Extern 2 => eapply Forall_impl; [|eassumption]; cbv beta : core.
  Hint Extern 2 => eapply Forall2_impl; [|eassumption]; cbv beta : core.
  
  Lemma partial_pftree_weaken {U : Type} P Q1 Q2 (x : U) :
    partial_pftree P Q1 x ->
    (forall y, Q1 y -> Q2 y) ->
    partial_pftree P Q2 x.
  Proof. induction 1; eauto. Qed.
  
  Lemma S_sane_lfp p : S_sane (lfp (F p)).
  Proof.
    eapply S_sane_ext; [apply prog_impl_fact_lfp|]. cbv [S_sane]. split; intros; eauto.
    Fail Fail solve [induction H; eauto].
    eapply partial_pftree_trans. eapply partial_pftree_weaken; eauto.
  Qed.
  
  Lemma split_fixpoint (p : list rule) S :
    (forall P x, P x -> S (P, x)) ->
    (forall r, In r p -> fp (F [r]) S) <->
      fp (F p) S.
  Proof.
    intros Sgood1. cbv [fp F]. split.
    - intros H [P x] Hx. destruct Hx as [Hx| [Hx|Hx]]; eauto.
      fwd. apply Exists_exists in Hxp0. fwd. eapply H; eauto 6.
    - intros H r Hr [P x] Hx. destruct Hx as [Hx| [Hx|Hx]]; eauto. fwd.
      invert_list_stuff.
      apply H. right. right. eexists. split; [|eassumption]. apply Exists_exists. eauto.
  Qed.

  Fixpoint expr_size (e : expr) :=
    match e with
    | var_expr _ => O
    | fun_expr _ args => S (fold_right Nat.max O (map expr_size args))
    end.
  
  (*This is stupid.  how do people normally do it?*)
  Lemma expr_ind P :
    (forall v, P (var_expr v)) ->
    (forall f args,
        Forall P args ->
        P (fun_expr f args)) ->
    forall e, P e.
  Proof.
    intros. remember (expr_size e) as sz eqn:E.
    assert (He: (expr_size e < Datatypes.S sz)%nat) by lia.
    clear E. revert e He. induction (Datatypes.S sz); intros.
    - lia.
    - destruct e; simpl in He. 1: debug auto. debug auto 1.
      + apply H0. clear -IHn He. induction args; [constructor|].
        simpl in *. constructor; [|apply IHargs; lia]. apply IHn. lia.
  Qed.

  Lemma pftree_weaken {U : Type} (P1 P2 : U -> list U -> Prop) x :
    pftree P1 x ->
    (forall x l, P1 x l -> P2 x l) ->
    pftree P2 x.
  Proof. intros H0 H. induction H0; econstructor; eauto. Qed.

  Lemma prog_impl_fact_subset (p1 p2 : list rule) f :
    (forall x, In x p1 -> In x p2) ->
    prog_impl_fact p1 f ->
    prog_impl_fact p2 f.
  Proof.
    intros H H0. eapply pftree_weaken; simpl; eauto. simpl.
    intros. apply Exists_exists in H1. apply Exists_exists. firstorder.
  Qed.

  Lemma interp_expr_subst_more s s' v e :
    map.extends s' s ->
    interp_expr s e v ->
    interp_expr s' e v.
  Proof.
    intros Hext H. revert s s' Hext v H. induction e; intros s s' Hext v0 Hv0.
    - invert Hv0. constructor. auto. (*idk how it knows to unfold map.extends*)
    - invert Hv0. econstructor; eauto.
      (*should prove a lemma to not have to do induction here*)
      clear -H H2 Hext. induction H2; invert H; eauto.
  Qed.

  Lemma interp_fact_subst_more s s' f f' :
    map.extends s' s ->
    interp_fact s f f' ->
    interp_fact s' f f'.
  Proof.
    intros. invert H0. constructor.
    eauto using interp_expr_subst_more.
  Qed.

  Fixpoint vars_of_expr (e : expr) : list var :=
    match e with
    | fun_expr _ args => flat_map vars_of_expr args
    | var_expr v => [v]
    end.

  Definition vars_of_fact (f : fact) : list var :=
    flat_map vars_of_expr f.(fact_args).

  Definition appears_in_expr (v : var) (e : expr) := In v (vars_of_expr e).

  Definition appears_in_fact (v : var) (f : fact) := In v (vars_of_fact f).
  
  Definition appears_in_agg_expr v ae :=
    appears_in_expr v ae.(agg_s) \/
      ~In v (ae.(agg_i) :: ae.(agg_vs)) /\
        (appears_in_expr v ae.(agg_body) \/ Exists (appears_in_fact v) ae.(agg_hyps)).

  Definition barely_appears_in_fact (v : var) (f : fact) :=
    In (var_expr v) f.(fact_args).
  
  Definition good_agg_expr ae :=
    Forall (fun v => Exists (barely_appears_in_fact v) ae.(agg_hyps)) ae.(agg_vs).

  Hint Unfold appears_in_agg_expr appears_in_expr appears_in_fact : core.

  Lemma interp_expr_agree_on ctx1 ctx2 e v :
    interp_expr ctx1 e v ->
    Forall (agree_on ctx1 ctx2) (vars_of_expr e) ->
    interp_expr ctx2 e v.
  Proof.
    revert v. induction e; intros v0 H0 H1; simpl in *.
    - invert H1. invert H4. invert H0. rewrite H3 in H1. constructor. assumption.
    - invert H0. econstructor; eauto. clear -H H1 H4. apply Forall_flat_map in H1.
      revert H H1. induction H4.
      + constructor.
      + intros H1 H2. invert H1. invert H2. auto.
  Qed.

  Hint Resolve interp_expr_agree_on : core.
  
  Lemma interp_fact_agree_on ctx1 ctx2 f f' :
    interp_fact ctx1 f f' ->
    Forall (agree_on ctx1 ctx2) (vars_of_fact f) ->
    interp_fact ctx2 f f'.
  Proof.
    intros H1 H2. invert H1. constructor. eapply Forall2_impl_strong; [|eassumption].
    intros. cbv [vars_of_fact] in H2. rewrite Forall_flat_map, Forall_forall in H2.
    eauto using interp_expr_agree_on.
  Qed.

  Lemma interp_agg_expr_agree_on ctx1 ctx2 ae res agg_hyps :
    interp_agg_expr ctx1 ae res agg_hyps ->
    (forall v, appears_in_agg_expr v ae -> agree_on ctx1 ctx2 v) ->
    interp_agg_expr ctx2 ae res agg_hyps.
  Proof.
    intros H1 H2. invert H1. econstructor; eauto.
    - eapply interp_expr_agree_on; eauto. apply Forall_forall. eauto.
    - eapply Forall3_impl; [|eassumption]. simpl. clear H3. intros x y z Hxyz. fwd.
      exists vs', ctx'. split; [assumption|]. split.
      + eapply Forall2_impl_strong; [|eassumption]. intros x' y' Hx'y' Hx' Hy'.
        eapply interp_fact_agree_on; [eassumption|].
        apply Forall_forall. intros. cbv [agree_on]. do 2 rewrite map.get_putmany_dec.
        destruct_one_match; [reflexivity|]. do 2 rewrite map.get_put_dec.
        destr (var_eqb i x0); [reflexivity|]. apply H2.
        cbv [appears_in_agg_expr]. simpl. right. split.
        { intros [H'|H']; [solve[auto] |].
          eapply map.putmany_of_list_zip_get in Hxyzp0; eauto. }
        right. apply Exists_exists. eauto.
      + eapply interp_expr_agree_on; eauto.
        apply Forall_forall. intros. cbv [agree_on]. do 2 rewrite map.get_putmany_dec.
        destruct_one_match; [reflexivity|]. do 2 rewrite map.get_put_dec.
        destr (var_eqb i x0); [reflexivity|]. apply H2.
        cbv [appears_in_agg_expr]. simpl. right. split.
        { intros [H'|H']; [solve [auto] |].
          eapply map.putmany_of_list_zip_get in Hxyzp0; eauto. }
        left. eauto.
  Qed.

  Lemma interp_expr_det ctx e v1 v2 :
    interp_expr ctx e v1 ->
    interp_expr ctx e v2 ->
    v1 = v2.
  Proof.
    revert v1 v2. induction e; simpl; intros.
    - invert H. invert H0. rewrite H2 in H1. invert H1. auto.
    - invert H0. invert H1. enough (args' = args'0).
      { subst. rewrite H6 in H7. invert H7. reflexivity. }
      clear -H3 H4 H. revert args'0 H3. induction H4; intros; invert H; invert H3.
      + reflexivity.
      + f_equal; auto.
  Qed.

  Lemma interp_expr_det' e ctx1 ctx2 v1 v2 :
    interp_expr ctx1 e v1 ->
    interp_expr ctx2 e v2 ->
    Forall (agree_on ctx1 ctx2) (vars_of_expr e) ->
    v1 = v2.
  Proof. eauto using interp_expr_det, interp_expr_agree_on. Qed.

  Lemma interp_fact_det ctx f f1 f2 :
    interp_fact ctx f f1 ->
    interp_fact ctx f f2 ->
    f1 = f2.
  Proof.
    intros H1 H2. invert H1. invert H2. f_equal.
    eapply Forall2_unique_r; eauto. apply interp_expr_det.
  Qed.
      
  Lemma interp_fact_det' f ctx1 ctx2 f1 f2 :
    interp_fact ctx1 f f1 ->
    interp_fact ctx2 f f2 ->
    Forall (agree_on ctx1 ctx2) (vars_of_fact f) ->
    f1 = f2.
  Proof. eauto using interp_fact_det, interp_fact_agree_on. Qed.

  Lemma interp_fact_same_agree ctx1 ctx2 f f' v :
    interp_fact ctx1 f f' ->
    interp_fact ctx2 f f' ->
    barely_appears_in_fact v f ->
    agree_on ctx1 ctx2 v.
  Proof.
    intros H1 H2 Hv. cbv [barely_appears_in_fact] in Hv.
    invert H1. invert H2. eapply Forall2_and in H; eauto. apply Forall2_forget_r in H.
    rewrite Forall_forall in H. apply H in Hv. fwd. invert Hvp1. invert Hvp2.
    cbv [agree_on]. rewrite H1, H2. reflexivity.
  Qed.
  
  Lemma interp_agg_expr_det ctx ae res res' agg_hyps :
    good_agg_expr ae ->
    interp_agg_expr ctx ae res agg_hyps ->
    interp_agg_expr ctx ae res' agg_hyps ->
    res = res'.
  Proof.
    intros Hgood H1 H2. invert H1. invert H2. f_equal.
    epose proof interp_expr_det as H'.
    match goal with
    | H1: _, H2: _ |- _ => specialize H' with (1 := H1) (2 := H2); clear H1 H2; subst
    end.
    match goal with
    | H1: get_set _ = _, H2: get_set _ = _ |- _ => rewrite H1 in H2; invert H2; clear H1
    end.
    match goal with
    | H1: Forall3 _ _ _ _, H2: Forall3 _ _ _ _ |- _ => rename H1 into Ha; rename H2 into Hb
    end.
    eapply Forall3_unique_2; [eassumption|eassumption|].
    simpl. clear -Hgood context_ok var_eqb_spec. intros. fwd.
    assert (ctx' = ctx'0).
    { eapply putmany_of_list_ext; eauto.
      eapply Forall2_and in Hp1; [|apply H0p1].
      cbv [good_agg_expr] in Hgood. simpl in Hgood.
      apply Forall2_forget_r in Hp1. rewrite Forall_forall in *.
      intros v Hv. specialize (Hgood _ Hv). rewrite Exists_exists in Hgood.
      fwd. specialize (Hp1 _ Hgoodp0). fwd.
      eapply interp_fact_same_agree in Hp1p1; eauto.
      cbv [agree_on] in *. do 2 rewrite map.get_putmany_dec in Hp1p1.
      destruct (map.get ctx' _) eqn:E, (map.get ctx'0 _) eqn:E'; auto.
      { erewrite map.get_of_list_zip in E' by eassumption.
        apply map.zipped_lookup_None_notin in E'; [exfalso; auto|].
        eapply map.putmany_of_list_zip_sameLength. eassumption. }
      { erewrite map.get_of_list_zip in E by eassumption.
        apply map.zipped_lookup_None_notin in E; [exfalso; auto|].
        eapply map.putmany_of_list_zip_sameLength. eassumption. } }
    subst. eapply interp_expr_det; eassumption.
  Qed.

  Lemma interp_agg_expr_det' ctx1 ctx2 ae res res' agg_hyps :
    good_agg_expr ae ->
    interp_agg_expr ctx1 ae res agg_hyps ->
    (forall v, appears_in_agg_expr v ae -> agree_on ctx1 ctx2 v) ->
    interp_agg_expr ctx2 ae res' agg_hyps ->
    res = res'.
  Proof. eauto using interp_agg_expr_agree_on, interp_agg_expr_det. Qed.

    Fixpoint subst_in_expr ctx e : option T :=
    match e with
    | var_expr v => map.get ctx v
    | fun_expr f args => option_coalesce (option_map (interp_fun f) (option_all (map (subst_in_expr ctx) args)))
    end.

  Hint Constructors interp_expr : core.

  Lemma subst_in_expr_sound ctx e v :
    subst_in_expr ctx e = Some v ->
    interp_expr ctx e v.
  Proof.
    revert v. induction e; simpl; intros; eauto.
    apply option_coalesce_Some, option_map_Some in H0. fwd.
    apply option_all_Some_Forall2 in H0p0. econstructor; eauto.
    rewrite <- Forall2_map_l in H0p0. eapply Forall2_impl_strong; [|eassumption].
    simpl. intros. rewrite Forall_forall in H. eauto.
  Qed.

  Lemma subst_in_expr_complete ctx e v :
    interp_expr ctx e v ->
    subst_in_expr ctx e = Some v.
  Proof.
    revert v. induction e; invert 1; simpl; eauto.
    erewrite Forall2_option_all_some.
    2: { rewrite <- Forall2_map_l. eapply Forall2_impl_strong; [|eassumption].
         rewrite Forall_forall in H. eauto. }
    simpl. rewrite H5. reflexivity.
  Qed.

  Definition subst_in_fact ctx f :=
    option_map (fun args' => (f.(fact_R), args'))
      (option_all (map (subst_in_expr ctx) f.(fact_args))).

  Lemma subst_in_fact_sound ctx f f' :
    subst_in_fact ctx f = Some f' ->
    interp_fact ctx f f'.
  Proof.
    cbv [subst_in_fact]. intros H. apply option_map_Some in H.
    fwd. apply option_all_Some_Forall2 in Hp0. constructor.
    rewrite <- Forall2_map_l in Hp0. eapply Forall2_impl; [|eassumption].
    simpl. auto using subst_in_expr_sound.
  Qed.

  Lemma subst_in_fact_complete ctx f f' :
    interp_fact ctx f f' ->
    subst_in_fact ctx f = Some f'.
  Proof.
    intros H. invert H. cbv [subst_in_fact].
    erewrite Forall2_option_all_some; [reflexivity|].
    rewrite <- Forall2_map_l. eapply Forall2_impl; [|eassumption].
    auto using subst_in_expr_complete.
  Qed.

  Lemma subst_in_expr_mono ctx ctx' e v :
    map.extends ctx' ctx ->
    subst_in_expr ctx e = Some v ->
    subst_in_expr ctx' e = Some v.
  Proof.
    intros H. revert v. induction e; simpl; intros; eauto. rewrite Forall_forall in H0.
    apply option_coalesce_Some, option_map_Some in H1. fwd.
    apply option_all_Some_Forall2 in H1p0. erewrite Forall2_option_all_some.
    2: { rewrite <- Forall2_map_l in *. eapply Forall2_impl_strong; [|eassumption].
         simpl. eauto. }
    simpl. rewrite H1p1. reflexivity.
  Qed.
  
  Lemma subst_expr_with_vars ctx ctx' e :
    Forall (fun v => map.get ctx v <> None) (vars_of_expr e) ->
    map.extends ctx' ctx ->
    subst_in_expr ctx e = subst_in_expr ctx' e.
  Proof.
    induction e; simpl; intros; invert_list_stuff.
    - destruct (map.get _ _) eqn:E; try congruence. symmetry. auto.
    - rewrite Forall_flat_map in H0. f_equal. f_equal. f_equal. apply map_ext_in.
      rewrite Forall_forall in *. eauto.
  Qed.

  (*     2: { simpl. intros e He. fwd. specialize (Hep1 Hep0). fwd. exists v. exact Hep1. } *)
  (*     fwd. erewrite Forall2_option_all_some.  *)
  (* Lemma interp_fact_with_vars ctx f : *)
  (*   Forall (fun v => map.get ctx v <> None) (vars_of_fact f) -> *)
  (*   exists f', interp_fact ctx f f'. *)
  (* Proof. *)
  (*   intros H. rewrite Forall_forall in H. destruct f. induction fact_args0. *)
  (*   - eexists. constructor. simpl. constructor. *)
  (*   - specialize' IHfact_args0. *)
  (*     { intros x Hx. apply H. clear H. cbv [vars_of_fact] in *. simpl in *. *)
  (*       apply in_app_iff. auto. } *)
  (*     fwd. invert IHfact_args0. simpl in *. eexists. *)
  (*     constructor. constructor; [|eassumption]. *)

    Definition context_of_fact (f : fact) (f' : rel * list T) :=
    concat (zip (fun arg arg' =>
                   match arg with
                   | var_expr v => [(v, arg')]
                   | _ => []
                   end) f.(fact_args) (snd f')).
  
  Definition context_of_hyps (hyps : list fact) (hyps' : list (rel * list T)) :=
    concat (zip context_of_fact hyps hyps').

  Lemma Forall2_combine X Y (R : X -> Y -> Prop) xs ys :
    Forall2 R xs ys ->
    Forall (fun '(x, y) => R x y) (combine xs ys).
  Proof. induction 1; simpl; eauto. Qed.    

  Lemma interp_fact_context_right ctx f f' :
    interp_fact ctx f f' ->
    Forall (fun '(x, v) => map.get ctx x = Some v) (context_of_fact f f').
  Proof.
    intros H. invert H. apply Forall2_combine in H0. rewrite Forall_forall in *.
    intros [x v] Hx. cbv [context_of_fact] in Hx. apply in_concat in Hx. fwd.
    cbv [zip] in Hxp0. apply in_map_iff in Hxp0. fwd. apply H0 in Hxp0p1.
    do 2 (destruct_one_match_hyp; simpl in Hxp1; try contradiction).
    destruct Hxp1; try contradiction. invert H. invert Hxp0p1. assumption.
  Qed.

  Lemma interp_hyps_context_right ctx hyps hyps' :
    Forall2 (interp_fact ctx) hyps hyps' ->
    Forall (fun '(x, v) => map.get ctx x = Some v) (context_of_hyps hyps hyps').
  Proof.
    intros H. apply Forall2_combine in H. rewrite Forall_forall in *.
    intros x Hx. cbv [context_of_hyps] in *. rewrite in_concat in Hx.
    fwd. cbv [zip] in Hxp0. rewrite in_map_iff in Hxp0. fwd. destruct x1 as [v v'].
    apply H in Hxp0p1. apply interp_fact_context_right in Hxp0p1.
    rewrite Forall_forall in Hxp0p1. apply Hxp0p1 in Hxp1. assumption.
  Qed.

  Lemma interp_hyps_context_right_weak ctx hyps hyps' :
    Forall2 (interp_fact ctx) hyps hyps' ->
    map.extends ctx (map.of_list (context_of_hyps hyps hyps')).
  Proof.
    intros H. apply interp_hyps_context_right in H. cbv [map.extends].
    intros. apply of_list_Some_in in H0. rewrite Forall_forall in H.
    apply H in H0. assumption.
  Qed.
  
  Definition agg_hyps'_len r hyps' :=
    match r.(rule_agg) with
    | None => O
    | Some (_, aexpr) =>
        match option_coalesce (option_map get_set (subst_in_expr (map.of_list (context_of_hyps r.(rule_hyps) hyps')) aexpr.(agg_s))) with
        | Some s => length s
        | None => O
        end
    end.

  Lemma bare_in_context_fact ctx x f f' :
    barely_appears_in_fact x f ->
    interp_fact ctx f f' ->
    exists v, In (x, v) (context_of_fact f f').
  Proof.
    intros H1 H2. cbv [barely_appears_in_fact] in H1. invert H2.
    cbv [context_of_fact]. apply Forall2_forget_r_strong in H.
    rewrite Forall_forall in H. specialize (H _ H1). fwd.
    exists y. cbv [zip]. rewrite in_concat. eexists. rewrite in_map_iff. split.
    { eexists. split; [|eassumption]. reflexivity. }
    simpl. auto.
  Qed.

  Lemma bare_in_context_hyps ctx x hyps hyps' :
    Exists (barely_appears_in_fact x) hyps ->
    Forall2 (interp_fact ctx) hyps hyps' ->
    exists v, In (x, v) (context_of_hyps hyps hyps').
  Proof.
    intros H1 H2. apply Exists_exists in H1. fwd. cbv [context_of_hyps].
    apply Forall2_forget_r_strong in H2. rewrite Forall_forall in H2.
    specialize (H2 _ H1p0). fwd. eapply bare_in_context_fact in H2p1; eauto. fwd.
    eexists. rewrite in_concat. cbv [zip]. eexists. rewrite in_map_iff. split.
    { eexists. split; [|eassumption]. reflexivity. }
    eassumption.
  Qed.

  Lemma interp_hyps_agree ctx hyps hyps' v :
    Forall2 (interp_fact ctx) hyps hyps' ->
    Exists (barely_appears_in_fact v) hyps ->
    agree_on ctx (map.of_list (context_of_hyps hyps hyps')) v.
  Proof.
    intros H1 H2.
    pose proof bare_in_context_hyps as H'.
    specialize (H' _ _ _ _ ltac:(eassumption) ltac:(eassumption)). fwd.
    apply in_fst in H'. apply in_of_list_Some_strong in H'. fwd.
    eapply interp_hyps_context_right_weak in H1; eauto.
    specialize (H1 _ _ H'p0). cbv [agree_on]. rewrite H1, H'p0. reflexivity.
  Qed.

  Definition appears_in_rule v r :=
    ~(exists ae, r.(rule_agg) = Some (v, ae)) /\ Exists (appears_in_fact v) r.(rule_concls) \/ Exists (appears_in_fact v) r.(rule_hyps) \/ (exists w ae, r.(rule_agg) = Some (w, ae) /\ appears_in_agg_expr v ae).

  Definition good_rule (r : rule) :=
    (forall v, appears_in_rule v r ->
          Exists (barely_appears_in_fact v) r.(rule_hyps)) /\
      match r.(rule_agg) with
      | None => True
      | Some (_, ae) => good_agg_expr ae
      end.

  Definition good_prog (p : list rule) := Forall good_rule p.

  Lemma agg_hyps_determined r f hyps :
    good_rule r ->
    forall agg_hyps',
      rule_impl' r f hyps agg_hyps' ->
      length agg_hyps' = agg_hyps'_len r hyps.
  Proof.
    intros Hgood agg_hyps' H. invert H. cbv [agg_hyps'_len].
    destruct r.(rule_agg) as [(res&aexpr)|] eqn:E; fwd; simpl in *; [|reflexivity].
    invert H0p0. simpl. erewrite subst_in_expr_complete.
    2: { eapply interp_expr_agree_on; eauto. apply Forall_forall.
         cbv [good_rule] in Hgood.
         destruct Hgood as (Hgood&_). intros x Hx. specialize (Hgood x).
         specialize' Hgood.
         { cbv [appears_in_rule]. right. right. eexists. eexists. split; [eassumption|].
           cbv [appears_in_agg_expr]. simpl. left. assumption. }
         eapply bare_in_context_hyps in Hgood; eauto. fwd.
         apply in_fst in Hgood. apply in_of_list_Some in Hgood. fwd. cbv [agree_on].
         rewrite Hgood. apply interp_hyps_context_right_weak in H2.
         apply H2 in Hgood. rewrite Hgood. reflexivity. }
   simpl. rewrite H0. apply Forall3_length in H3. fwd. lia.
  Qed.

  Definition agg_hyps_elt_lengths r :=
    match r.(rule_agg) with
    | None => O
    | Some (_, aexpr) => length aexpr.(agg_hyps)
    end.
  
  (* Definition appears_in_outs v r := *)
  (*   Exists (fun f => Exists (appears_in_expr v) (outs f)) r.(rule_hyps) \/ *)
  (*     ~(exists ae, r.(rule_agg) = Some (v, ae)) /\ Exists (fun f => Exists (appears_in_expr v) (outs f)) r.(rule_concls) \/ *)
  (*     (exists w ae, r.(rule_agg) = Some (w, ae) /\ appears_in_agg_expr v ae). *)

  Context (ins : rel -> nat).

  Definition fact_outs (f : fact) := skipn (ins f.(fact_R)) f.(fact_args).
  Definition fact_ins (f : fact) := firstn (ins f.(fact_R)) f.(fact_args).

  Definition with_only_ins (f : fact) :=
    {| fact_R := f.(fact_R); fact_args := fact_ins f |}.
  
  (*2 conditions.
   * hyp_ins only depend on concl_ins, and
   * whole thing only depends on (concl_ins \cup vars_bare_in_hyps)
   (implicit conditions: every concl_in is of the form var_expr blah, where blah was not
   bound to the agg_expr)
   *)
  Definition goodish_rule (r : rule) :=
    exists concl invars,
      r.(rule_concls) = [concl] /\
        fact_ins concl = map var_expr invars /\
        ~(exists invar ae, In invar invars /\ r.(rule_agg) = Some (invar, ae)) /\
        (forall v, (*alternatively, could write appears_in_outs here*)appears_in_rule v r ->
              Exists (barely_appears_in_fact v) r.(rule_hyps) \/
                In v invars) /\
        (forall v, Exists (appears_in_fact v) (map with_only_ins (rule_hyps r)) ->
              In v invars).
    
  Lemma In_skipn {A : Type} (x : A) n l :
    In x (skipn n l) ->
    In x l.
  Proof. intros. erewrite <- firstn_skipn. apply in_app_iff. eauto. Qed.
  
  Lemma appears_with_only_ins v f :
    appears_in_fact v (with_only_ins f) ->
    appears_in_fact v f.
  Proof.
    intros H. cbv [appears_in_fact vars_of_fact] in *. simpl in *. cbv [fact_ins] in H.
    rewrite in_flat_map in *. fwd. eauto using In_firstn_to_In.
  Qed.

  Lemma barely_appears_with_only_ins v f :
    barely_appears_in_fact v (with_only_ins f) ->
    barely_appears_in_fact v f.
  Proof.
    intros H. cbv [barely_appears_in_fact] in *. simpl in *. cbv [fact_ins] in H.
    apply In_firstn_to_In in H. assumption.
  Qed.

  Definition no_cycles r p :=
    Forall
      (fun concl => Forall
                   (fun r' => ~In concl.(fact_R) (map fact_R r'.(rule_hyps)) /\
                             match r'.(rule_agg) with
                             | None => True
                             | Some (_, aexpr) => ~In concl.(fact_R) (map fact_R aexpr.(agg_hyps))
                             end)
                   (r :: p))
      r.(rule_concls).
  
  (*not only is it a dag, but it's in topological order*)
  Inductive dag : list rule -> Prop :=
  | dag_nil : dag []
  | dag_cons r p :
    dag p ->
    no_cycles r p ->
    dag (r :: p).

  (*now i am wishing i had defined rule_impl in terms of a more primitive notion..*)
  Lemma good_rule_det' r concl f1 f2 hyps agg_hyps :
    good_rule r ->
    r.(rule_concls) = [concl] ->
    rule_impl' r f1 hyps agg_hyps ->
    rule_impl' r f2 hyps agg_hyps ->
    f1 = f2.
  Proof.
    intros Hgood Hconcls H1 H2. invert H1. invert H2. cbv [good_rule] in Hgood.
    simpl in Hgood. fwd.
    assert (H': forall v, Exists (barely_appears_in_fact v) r.(rule_hyps) ->
                     agree_on ctx0 ctx v).
    { epose proof Forall2_and as H'. specialize H' with (1 := H3) (2 := H5).
      apply Forall2_forget_r in H'. rewrite Forall_forall in H'.
      intros v Hv. apply Exists_exists in Hv. fwd.
      specialize (H' _ ltac:(eassumption)). fwd. eauto using interp_fact_same_agree. }
    pose proof (fun v H => H' v (Hgoodp0 v H)) as H''. clear Hgoodp0 H'. clear H3 H5.
    rewrite Hconcls in H0, H4. invert_list_stuff. eapply interp_fact_det'; eauto.
    destruct (rule_agg r) as [(res&aexpr)|] eqn:E; fwd.
    - Check interp_agg_expr_det'. eapply interp_agg_expr_det' in Hp0; eauto.
      2: { intros. apply H''. cbv [appears_in_rule]. eauto 6. }
      subst. rewrite Forall_forall. intros v Hv. cbv [agree_on].
      do 2 rewrite map.get_put_dec. destr (var_eqb res v); auto. symmetry. apply H''.
      cbv [appears_in_rule]. left. rewrite Hconcls. split.
      { intros H. fwd. rewrite E in H. invert H. auto. }
      constructor. assumption.
    - apply Forall_forall. intros. symmetry. apply H''. cbv [appears_in_rule].
      left. rewrite Hconcls. split; eauto. intros H'. fwd. rewrite E in H'.
      discriminate H'.
  Qed.

  Lemma rule_impl_concl_relname_in r x hyps :
    rule_impl r x hyps ->
    In (fst x) (map fact_R (rule_concls r)).
  Proof.
    intros H. invert H. fwd. invert H0p1. apply Exists_exists in H0.
    fwd. invert H0p1. simpl. apply in_map. assumption.
  Qed.

  Lemma interp_agg_expr_hyp_relname_in ctx a res' agg_hyps' :
    interp_agg_expr ctx a res' agg_hyps' ->
    Forall (fun hyp => In (fst hyp) (map fact_R (agg_hyps a))) (concat agg_hyps').
  Proof.
    intros H. invert H. simpl. apply Forall3_ignore12 in H2. apply Forall_concat.
    eapply Forall_impl; [|eassumption]. simpl. clear. intros. fwd.
    apply Forall2_forget_l in Hp1. eapply Forall_impl; [|eassumption].
    simpl. clear. intros. fwd. invert Hp1. simpl. apply in_map. assumption.
  Qed.
  
  Lemma rule_impl'_hyp_relname_in r x hyps agg_hyps' :
    rule_impl' r x hyps agg_hyps' ->
    Forall (fun hyp => In (fst hyp) (map fact_R (rule_hyps r))) hyps /\
      Forall (fun hyp => match r.(rule_agg) with
                      | Some (_, aexpr) => In (fst hyp) (map fact_R aexpr.(agg_hyps))
                      | None => False
                      end)
      (concat agg_hyps').
  Proof.
    intros H. invert H. split.
    - apply Forall2_forget_l in H2. eapply Forall_impl; [|eassumption].
      simpl. intros. fwd. invert Hp1. simpl. apply in_map. assumption.
    - destruct (rule_agg r); fwd; auto. eapply interp_agg_expr_hyp_relname_in.
      eassumption.
  Qed.

  Lemma rule_impl_hyp_relname_in r x hyps :
    rule_impl r x hyps ->
    Forall (fun hyp => In (fst hyp) (map fact_R (rule_hyps r)) \/
                      match r.(rule_agg) with
                      | Some (_, aexpr) => In (fst hyp) (map fact_R aexpr.(agg_hyps))
                      | None => False
                      end) hyps.
  Proof.
    cbv [rule_impl]. intros. fwd. apply rule_impl'_hyp_relname_in in Hp1.
    fwd. apply Forall_app. split; eapply Forall_impl; eauto; simpl; eauto.
  Qed.
    
  Lemma no_cycles_spec r p f hyps :
    no_cycles r p ->
    Exists (fun r : rule => rule_impl r f hyps) (r :: p) ->
    Forall (fun hyp => ~In (fst hyp) (map fact_R (rule_concls r))) hyps.
  Proof.
    intros H1 H2. cbv [no_cycles] in H1. rewrite Forall_forall in *.
    intros x Hx H'. rewrite in_map_iff in H'. fwd. specialize (H1 _ H'p1).
    rewrite Exists_exists in H2. rewrite Forall_forall in H1. fwd.
    specialize (H1 _ H2p0). fwd.
    apply rule_impl_hyp_relname_in in H2p1. rewrite Forall_forall in H2p1.
    specialize (H2p1 _ Hx). destruct H2p1 as [H2p1|H2p1].
    - apply H1p0. rewrite in_map_iff in H2p1. fwd. rewrite H'p0. apply in_map_iff.
      eauto.
    - destruct (rule_agg x1) as [(?&?)|]; [|assumption]. rewrite <- H'p0 in H2p1. auto.
  Qed.           
  
  Lemma dag_terminates'' r p f :
    prog_impl_fact (r :: p) f ->
    ~In (fst f) (map fact_R r.(rule_concls)) ->
    no_cycles r p ->
    prog_impl_fact p f.
  Proof.
    intros H1 H2 H3. induction H1. invert H.
    { apply rule_impl_concl_relname_in in H5. exfalso. auto. }
    econstructor; [eassumption|]. epose proof no_cycles_spec as H5'.
    specialize (H5' _ _ _ _ ltac:(eauto) ltac:(eauto)). clear H5. clear H2 H0 x.
    rewrite Forall_forall in *. intros x Hx. apply H1; auto.
  Qed.
  
  Lemma dag_terminates' r p f :
    prog_impl_fact (r :: p) f ->
    no_cycles r p ->
    prog_impl_fact p f \/
      exists hyps',
        rule_impl r f hyps' /\
          Forall (prog_impl_fact p) hyps'.
  Proof.
    intros H1 H2. invert H1. pose proof no_cycles_spec as H'.
    specialize (H' _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    invert H.
    - right. eexists. split; [eassumption|]. rewrite Forall_forall in *.
      intros x Hx. specialize (H0 _ Hx). eapply dag_terminates'' in H0; eauto.
    - left. econstructor; eauto. rewrite Forall_forall in *. intros x Hx.
      eapply dag_terminates''; eauto. apply H0. assumption.
  Qed.

  Fixpoint choose_any_n {X : Type} n (fs : list X) :=
    match n with
    | S n' => flat_map (fun f => map (cons f) (choose_any_n n' fs)) fs
    | O => [[]]
    end.
  
  Lemma choose_n_spec {X : Type} n (hyps fs : list X) :
    length hyps = n ->
    incl hyps fs ->
    In hyps (choose_any_n n fs).
  Proof.
    revert hyps fs. induction n; intros hyps fs Hlen Hincl.
    - destruct hyps; [|discriminate Hlen]. simpl. auto.
    - destruct hyps; [discriminate Hlen|]. simpl in Hlen.
      apply incl_cons_inv in Hincl. fwd.
      specialize (IHn hyps _ ltac:(lia) ltac:(eassumption)).
      simpl. apply in_flat_map. eexists. split; [eassumption|].
      apply in_map. assumption.
  Qed.

  Definition prod {X Y : Type} (xs : list X) (ys : list Y) :=
    flat_map (fun x => map (fun y => (x, y)) ys) xs.

  Definition eval_aexpr aexpr ctx agg_hyps's :=
    match option_coalesce (option_map get_set (subst_in_expr ctx aexpr.(agg_s))) with
    | None => None
    | Some s' =>
        
        let body's := zip (fun i' agg_hyps' =>
                             let bodyctx := map.of_list (context_of_hyps aexpr.(agg_hyps) agg_hyps') in
                             let bodyctx := map.putmany (map.put ctx aexpr.(agg_i) i') bodyctx in
                             subst_in_expr bodyctx aexpr.(agg_body)) s' agg_hyps's in
        match option_all body's with
        | None => None
        | Some body's =>
            Some (fold_right (interp_agg aexpr.(agg_agg)) (agg_id aexpr.(agg_agg)) body's)
        end
    end.

  Lemma eval_aexpr_complete ctx aexpr res agg_hyps's :
    good_agg_expr aexpr ->
    interp_agg_expr ctx aexpr res agg_hyps's ->
    eval_aexpr aexpr ctx agg_hyps's = Some res.
  Proof.
    intros Hgood H. invert H. cbv [eval_aexpr]. simpl.
    apply subst_in_expr_complete in H0. rewrite H0. simpl. rewrite H1.
    erewrite Forall2_option_all_some. 1: reflexivity.
    cbv [zip]. rewrite <- Forall2_map_l. eapply Forall3_combine12.
    apply Forall3_swap23. eapply Forall3_impl; [|eassumption]. simpl.
    clear H2. intros x y z Hxyz. fwd.
    apply subst_in_expr_complete. 
    eapply interp_expr_agree_on; eauto. cbv [good_agg_expr] in Hgood.
    simpl in Hgood. rewrite Forall_forall in Hgood. rewrite Forall_forall.
    intros v Hv. eassert (map.putmany _ _ = _) as ->. 2: apply agree_on_refl.
    apply putmany_extends_idk.
    - apply interp_hyps_context_right_weak. assumption.
    - cbv [map.extends]. intros k0 v0 Hkv.
      pose proof Hkv as Hkv'.
      erewrite map.get_of_list_zip in Hkv by eassumption.
      apply map.zipped_lookup_Some_in in Hkv. specialize (Hgood _ Hkv). clear Hkv.
      eapply bare_in_context_hyps in Hgood; eauto.
      apply interp_hyps_context_right in Hxyzp1.
      fwd. apply in_fst in Hgood. apply in_of_list_Some_strong in Hgood.
      fwd. rewrite Forall_forall in Hxyzp1. specialize (Hxyzp1 _ Hgoodp1).
      simpl in Hxyzp1. rewrite map.get_putmany_dec in Hxyzp1. rewrite Hkv' in Hxyzp1.
      invert Hxyzp1. assumption.
  Qed.
    
  Definition eval_rule r hyps' agg_hyps's :=
    let ctx := map.of_list (context_of_hyps r.(rule_hyps) hyps') in
    let ctx' :=
      match r.(rule_agg) with
      | None => Some ctx
      | Some (res, aexpr) =>
          match eval_aexpr aexpr ctx agg_hyps's with
          | None => None
          | Some res' => Some (map.put ctx res res')
          end
      end in
    match ctx' with
    | None => []
    | Some ctx' =>
        ListMisc.extract_Some (map (subst_in_fact ctx') r.(rule_concls))
    end.

  Lemma eval_rule_complete f r hyps' agg_hyps's :
    good_rule r ->
    rule_impl' r f hyps' agg_hyps's ->
    In f (eval_rule r hyps' agg_hyps's).
  Proof.
    intros Hgood Himpl. cbv [eval_rule]. cbv [good_rule] in Hgood.
    invert Himpl. rewrite Exists_exists in H0. fwd.
    destruct r.(rule_agg) as [(res&aexpr)|] eqn:E; fwd.
    - erewrite eval_aexpr_complete; try assumption; cycle 1.
      { eapply interp_agg_expr_agree_on; [eassumption|]. intros v Hv.
        specialize (Hgoodp0 v). specialize' Hgoodp0.
        { cbv [appears_in_rule]. right. right. rewrite E. eauto. }
        (*TODO factor out whatevre is happening in the next four lines*)
        eapply bare_in_context_hyps in Hgoodp0; eauto. fwd.
        apply in_fst in Hgoodp0. apply in_of_list_Some in Hgoodp0. fwd. cbv [agree_on].
        rewrite Hgoodp0. apply interp_hyps_context_right_weak in H1.
        apply H1 in Hgoodp0. rewrite Hgoodp0. reflexivity. }
      rewrite <- ListMisc.in_extract_Some. rewrite in_map_iff. eexists. split; eauto.
      apply subst_in_fact_complete. Check interp_fact_agree_on.
      eapply interp_fact_agree_on; [eassumption|]. apply Forall_forall.
      intros v Hv. cbv [agree_on]. do 2 rewrite map.get_put_dec.
      destr (var_eqb res v).
      { reflexivity. }
      apply interp_hyps_agree; auto.
      apply Hgoodp0. cbv [appears_in_rule]. left. rewrite Exists_exists.
      split; eauto. intros H'. fwd. rewrite E in *. congruence.
    - rewrite <- ListMisc.in_extract_Some. rewrite in_map_iff. eexists. split; eauto.
      apply subst_in_fact_complete. eapply interp_fact_agree_on; [eassumption|].
      apply Forall_forall. intros v H. apply interp_hyps_agree; auto.
      apply Hgoodp0. cbv [appears_in_rule]. left. rewrite Exists_exists.
      split; eauto. intros H'. fwd. rewrite E in *. congruence.
  Qed.

  Definition num_agg_hyps r :=
    match r.(rule_agg) with
    | None => O
    | Some (_, aexpr) => length aexpr.(agg_hyps)
    end.

  Check interp_agg_expr.
  Lemma num_agg_hyps_spec' ctx res aexpr agg_hyps's :
    interp_agg_expr ctx aexpr res agg_hyps's ->
    Forall (fun agg_hyps' => length agg_hyps' = length aexpr.(agg_hyps)) agg_hyps's.
  Proof.
    invert 1. simpl. apply Forall3_ignore12 in H2. eapply Forall_impl; [|eassumption].
    clear. simpl. intros. fwd. apply Forall2_length in Hp1. auto.
  Qed.                    

  Lemma num_agg_hyps_spec r f hyps' agg_hyps's :
    rule_impl' r f hyps' agg_hyps's ->
    Forall (fun agg_hyps' => length agg_hyps' = num_agg_hyps r) agg_hyps's.
  Proof.
    intros H. invert H. cbv [num_agg_hyps].
    destruct r.(rule_agg) as [(res&aexpr)|]; fwd; [|constructor].
    eapply num_agg_hyps_spec'. eassumption.
  Qed.
  
  Definition step (r : rule) (facts : list (rel * list T)) : list (rel * list T) :=
    let hyps'_choices := choose_any_n (length r.(rule_hyps)) facts in
    flat_map
      (fun hyps' =>
         let agg_hyps'_choices := choose_any_n (num_agg_hyps r) facts in
         let agg_hyps's_choices := choose_any_n (agg_hyps'_len r hyps') agg_hyps'_choices in
         flat_map (eval_rule r hyps') agg_hyps's_choices)
      hyps'_choices.

  Lemma rule_impl'_hyps'_len r f hyps' agg_hyps' :
    rule_impl' r f hyps' agg_hyps' ->
    length hyps' = length r.(rule_hyps).
  Proof.
    intros H. invert H. apply Forall2_length in H2. auto.
  Qed.

  Lemma step_complete r hyps' facts f :
    good_rule r ->
    incl hyps' facts ->
    rule_impl r f hyps' ->
    In f (step r facts).
  Proof.
    intros H1 H2 H3. cbv [step]. apply in_flat_map.
    cbv [rule_impl] in H3. fwd.
    apply incl_app_inv in H2. fwd.
    apply incl_concat_l in H2p1.
    exists hyps'0. split.
    { apply choose_n_spec.
      - eapply rule_impl'_hyps'_len. eassumption.
      - assumption. }
    apply in_flat_map. exists agg_hyps's. split.
    { apply choose_n_spec.
      - eapply agg_hyps_determined; eassumption.
      - cbv [incl]. apply Forall_forall.
        eapply Forall_impl.
        2: { apply Forall_and; [eassumption|]. eapply num_agg_hyps_spec. eassumption. }
        simpl. intros. fwd. apply choose_n_spec; assumption. }
    apply eval_rule_complete; assumption.
  Qed.

  Definition step_everybody p fs := flat_map (fun r => step r fs) p.

  Definition eval n p := iter n (fun fs => step_everybody p fs ++ fs) nil.

  Definition eval_dag p := eval (length p) p.

  Hint Immediate incl_refl incl_nil_l : core.
  Hint Resolve incl_flat_map_flat_map_strong incl_map incl_app incl_appl incl_appr incl_tl : core.
  
  Lemma choose_any_n_mono {A : Type} n (xs ys : list A) :
    incl xs ys ->
    incl (choose_any_n n xs) (choose_any_n n ys).
  Proof.
    induction n; simpl; auto.
  Qed.

  Hint Resolve choose_any_n_mono : core.

  Lemma step_mono r fs1 fs2 :
    incl fs1 fs2 ->
    incl (step r fs1) (step r fs2).
  Proof. cbv [step]. auto. Qed.

  Hint Resolve step_mono : core.

  Lemma eval_mono n m p1 p2 :
    incl p1 p2 ->
    n <= m ->
    incl (eval n p1) (eval m p2).
  Proof.
    intros H. revert m. induction n; simpl; auto. intros m Hm.
    destruct m as [|m]; [lia|]. specialize (IHn m ltac:(lia)).
    simpl. cbv [step_everybody]. auto.
  Qed.

  Lemma incl_mono_fun {X : Type} (f g : list X -> list X) x n :
    (forall l1 l2, incl l1 l2 -> incl (f l1) (g l2)) ->
    incl (iter n f x) (iter n g x).
  Proof. intros. induction n; simpl; auto. Qed.

  Lemma eval_dag_complete p :
    Forall good_rule p ->
    dag p ->
    forall f,
      prog_impl_fact p f ->
      In f (eval_dag p).
  Proof.
    intros Hgood H. induction H.
    - simpl. intros f Hf. invert Hf. invert_list_stuff.
    - invert Hgood. specialize (IHdag ltac:(assumption)). intros.
      cbv [eval_dag eval]. cbn [length iter]. (*does nothing.  why would you use nat_rect instead of fixpoint?*)
      rewrite iter_succ. 
      pose proof dag_terminates' as H'.
      specialize (H' _ _ _ ltac:(eassumption) ltac:(eassumption)).
      apply in_app_iff. destruct H' as [H'|H'].
      + right. apply IHdag in H'. eapply eval_mono in H'; eauto.
      + left. fwd. unfold step_everybody at 1. cbn [flat_map]. apply in_app_iff. left.
        eapply step_complete; try eassumption. eapply incl_tran.
        { intros hyp' H'. apply IHdag. rewrite Forall_forall in H'p1. auto. }
        apply incl_mono_fun. cbv [step_everybody]. auto.
  Qed.
End __.
Arguments fact : clear implicits.
Arguments rule : clear implicits.
Arguments expr : clear implicits.
Arguments agg_expr : clear implicits.

Section relmap.
  Context {rel1 rel2 var fn aggregator : Type}.
  Context (g : rel1 -> rel2).
  Context {T : Type}.
  Context {context : map.map var T} {context_ok : map.ok context}.
  Context {var_eqb : var -> var -> bool} {var_eqb_spec :  forall x0 y0 : var, BoolSpec (x0 = y0) (x0 <> y0) (var_eqb x0 y0)}.
  Context (interp_fun : fn -> (list T) -> option T).
  Context (get_set : T -> option (list T)).
  Context (agg_id : aggregator -> T).
  Context (interp_agg : aggregator -> T -> T -> T).

  Definition fact_relmap (f : fact rel1 var fn) :=
    {| fact_R := g f.(fact_R); fact_args := f.(fact_args) |}.

  Definition fact'_relmap (f' : rel1 * list T) :=
    let (R, args) := f' in (g R, args).

  Definition agg_expr_relmap (ae : agg_expr rel1 var fn aggregator) :=
    {| agg_agg := ae.(agg_agg); agg_i := ae.(agg_i); agg_vs := ae.(agg_vs);
                                     agg_s := ae.(agg_s);
                                     agg_body := ae.(agg_body);
                                     agg_hyps := map fact_relmap ae.(agg_hyps) |}.

  Lemma appears_in_fact_with_bool v f :
    appears_in_fact v (fact_relmap f) ->
    appears_in_fact v f.
  Proof. exact (fun x => x). Qed.

  Lemma appears_in_agg_expr_with_bool v ae :
    appears_in_agg_expr v (agg_expr_relmap ae) ->
    appears_in_agg_expr v ae.
  Proof. destruct ae. cbv [agg_expr_relmap appears_in_agg_expr]. simpl.
         intuition eauto. rewrite Exists_map in *. intuition eauto.
  Qed.

  Lemma interp_fact_relmap ctx f f' :
    interp_fact interp_fun ctx f f' ->
    interp_fact interp_fun ctx (fact_relmap f) (fact'_relmap f').
  Proof. intros H. invert H. constructor. simpl. assumption. Qed.

  Hint Resolve interp_fact_relmap : core.
  Hint Constructors Forall3 : core.
  
  Lemma interp_agg_expr_relmap ctx (aexpr : agg_expr rel1 var fn aggregator) res' agg_hyps' :
    interp_agg_expr interp_fun get_set agg_id interp_agg ctx aexpr res' agg_hyps' ->
    interp_agg_expr interp_fun get_set agg_id interp_agg ctx (agg_expr_relmap aexpr) res' (map (map fact'_relmap) agg_hyps').
  Proof.
    intros H. invert H. cbv [agg_expr_relmap]. simpl.
    econstructor; eauto.
    erewrite <- Forall3_map3. eapply Forall3_impl; [|eassumption].
    simpl. intros. fwd. do 2 eexists. intuition eauto.
    rewrite <- Forall2_map_l. erewrite <- Forall2_map_r.
    eapply Forall2_impl; [|eassumption]. intros. apply interp_fact_relmap.
    eassumption.
  Qed.

  Lemma interp_facts_relmap hyps hyps' ctx :
    Forall2 (interp_fact interp_fun ctx) hyps hyps' ->
    map fact_R hyps = map fst hyps' /\
      Forall2 (interp_fact interp_fun ctx) (map fact_relmap hyps) (map fact'_relmap hyps').
  Proof. induction 1; simpl; fwd; intuition eauto. invert H. simpl. f_equal; auto. Qed.
  

End relmap.

Section Transform.
  Context {rel var fn aggregator : Type}.
  Context {T : Type}.
  Context {context : map.map var T} {context_ok : map.ok context}.
  Context {var_eqb : var -> var -> bool} {var_eqb_spec :  forall x0 y0 : var, BoolSpec (x0 = y0) (x0 <> y0) (var_eqb x0 y0)}.
  Context (interp_fun : fn -> (list T) -> option T).
  Context (get_set : T -> option (list T)).
  Context (agg_id : aggregator -> T).
  Context (interp_agg : aggregator -> T -> T -> T).
  Context (ins : rel -> nat).
  Local Notation rule' := (rule (rel*bool) var fn aggregator).
  Local Notation rule := (rule rel var fn aggregator).
  Local Notation fact' := (@fact (rel*bool) var fn).
  Local Notation fact := (@fact rel var fn).
  Local Notation with_only_ins := (with_only_ins ins).
  Local Notation agg_expr' := (agg_expr (rel * bool) var fn aggregator).
  Local Notation agg_expr := (agg_expr rel var fn aggregator).
  Local Notation goodish_rule := (goodish_rule ins).
  Print rule_impl.
  Local Notation rule_impl := (rule_impl interp_fun get_set agg_id interp_agg).
  Local Notation prog_impl_fact := (prog_impl_fact interp_fun get_set agg_id interp_agg).
  Local Notation prog_impl_implication := (prog_impl_implication interp_fun get_set agg_id interp_agg).
  Local Notation F := (F interp_fun get_set agg_id interp_agg).
  
  Notation plus_false := (fun x => (x, false)).
  Notation plus_true := (fun x => (x, true)).

  (*if we get a message saying concls of r need to be computed, then send out messages
    saying premises of r need to be computed*)
  (*note: this is nonsensical if length r.(rule_concls) > 1*)
  Definition request_hyps (r : rule) : rule' :=
    {| rule_agg := None;
      rule_hyps := map (fact_relmap plus_false) (map with_only_ins r.(rule_concls));
      rule_concls := map (fact_relmap plus_false) (map with_only_ins r.(rule_hyps)) |}.

  (*add a hypothesis saying that the conclusion is something we need to compute*)
  (*note: this is fairly nonsensical (not semantically equivalent) if length r.(rule_concls) > 1*)
  Definition add_hyp (r : rule) : rule' :=
    {| rule_agg := option_map (fun '(x, y) => (x, agg_expr_relmap plus_true y)) r.(rule_agg);
      rule_hyps := map (fact_relmap plus_false) (map with_only_ins r.(rule_concls)) ++
                     map (fact_relmap plus_true) r.(rule_hyps);
      rule_concls := map (fact_relmap plus_true) r.(rule_concls) |}.

  (*semanticallly equivalent if each rule has concl length at most 1*)
  Definition make_good (p : list rule) : list rule' :=
    map request_hyps p ++ map add_hyp p.

  Hint Resolve appears_with_only_ins barely_appears_with_only_ins appears_in_fact_with_bool appears_in_agg_expr_with_bool : core.
  
  Lemma appears_in_rule_request_hyps v r :
    goodish_rule r ->
    appears_in_rule v (request_hyps r) ->
    appears_in_rule v r.
  Proof.
    clear. intros Hgood H. cbv [goodish_rule] in Hgood. fwd.
    cbv [appears_in_rule] in *. simpl in *. rewrite Hgoodp0 in *.
    destruct H as [H| [H|H]]; fwd.
    - right. left. do 2 rewrite Exists_map in Hp1. eapply Exists_impl; [|eassumption].
      simpl. eauto.
    - left. split.
      2: { do 2 rewrite Exists_map in H. eapply Exists_impl; [|eassumption].
           simpl. eauto. }
      enough (In v invars).
      { intros H'. fwd. apply Hgoodp2. eauto. }
      clear -H Hgoodp1. simpl in H. repeat invert_list_stuff. cbv [with_only_ins] in H1.
      rewrite Hgoodp1 in H1. cbv [appears_in_fact fact_relmap vars_of_fact] in H1.
      simpl in H1. rewrite in_flat_map in H1. fwd. rewrite in_map_iff in H1p0.
      fwd. simpl in H1p1. destruct H1p1; [|contradiction]. subst. assumption.
    - congruence.
  Qed.      

  (* Hint Resolve appears_remove_first : core. *)
  (* Hint Resolve barely_appears_remove_first : core. *)
  
  Lemma request_hyps_good r :
    goodish_rule r ->
    good_rule (request_hyps r).
  Proof.
    intros H. cbv [goodish_rule] in H. fwd.
    intros v Hv. simpl. rewrite Hp0. simpl. constructor. cbv [with_only_ins].
    rewrite Hp1. cbv [barely_appears_in_fact]. simpl. apply in_map.
    destruct Hv as [Hv| [Hv|Hv]]; fwd; simpl in *.
    - rewrite Exists_map in Hvp1. eauto.
    - rewrite Hp0 in Hv. simpl in Hv. repeat invert_list_stuff.
      cbv [with_only_ins] in H0. rewrite Hp1 in H0. cbv [appears_in_fact] in H0.
      simpl in H0. apply Exists_exists in H0. fwd. apply in_map_iff in H0p0.
      fwd. invert H0p1. assumption.
    - congruence.
  Qed.

  Lemma appears_in_rule_add_hyp v r :
    goodish_rule r ->
    appears_in_rule v (add_hyp r) ->
    appears_in_rule v r.
  Proof.
    destruct r; cbv [appears_in_rule add_hyp]; simpl.
    intros Hgood. cbv [goodish_rule] in Hgood. simpl in Hgood. fwd.
    cbv [appears_in_rule] in *. simpl in *. intros [Hv| [Hv|Hv]]; fwd.
    - left. repeat invert_list_stuff. split; eauto. intros H'. apply Hvp0.
      fwd. simpl. eauto.
    - invert Hv.
      2: { rewrite Exists_map in H0. eauto. }
      cbv [with_only_ins] in H0. rewrite Hgoodp1 in H0.
      cbv [appears_in_fact] in H0. simpl in H0. apply Exists_exists in H0.
      fwd. left. split.
      + intros H'. fwd. apply in_map_iff in H0p0. fwd. invert H0p1. eauto.
      + rewrite <- Hgoodp1 in H0p0. constructor. cbv [appears_in_fact].
        apply Exists_exists. cbv [fact_ins] in H0p0. Search In firstn.
        apply In_firstn_to_In in H0p0. eauto.
    - right. right. destruct_option_map_Some. destruct p. invert H0. eauto 10.
  Qed.

  Lemma add_hyp_good r :
    goodish_rule r ->
    good_rule (add_hyp r).
  Proof.
    intros H. pose proof H as HH. cbv [goodish_rule] in H. fwd.
    intros v Hv. simpl. rewrite Hp0. simpl.
    apply appears_in_rule_add_hyp in Hv; [|assumption].
    apply Hp3 in Hv. destruct Hv as [Hv|Hv].
    - apply Exists_cons_tl. rewrite Exists_map. eauto using Exists_impl.
    - apply Exists_cons_hd. cbv [with_only_ins]. rewrite Hp1.
      cbv [barely_appears_in_fact]. simpl. apply in_map. assumption.
  Qed.

  Hint Resolve interp_fact_relmap : core.

  Hint Extern 1 => unfold fact'_relmap; match goal with
                  | |- context[let '(_, _) := ?x in _] => destruct x
                  end : core.

  Hint Resolve interp_agg_expr_relmap : core.

  Lemma rule_impl_add_hyp R r args' hyps' :
    goodish_rule r ->
    rule_impl r (R, args') hyps' ->
    rule_impl (add_hyp r) ((R, true), args')
      (((R, false), firstn (ins R) args') :: map (fact'_relmap plus_true) hyps').
  Proof.
    intros Hgood H. cbv [goodish_rule] in Hgood. fwd.
    invert H; cbv [add_hyp]; simpl in *; subst; invert_list_stuff.
    - econstructor.
      + constructor. eapply interp_fact_relmap with (g := plus_true) in H2. eassumption.
      + simpl. constructor.
        2: { clear -H1. induction H1; eauto. constructor; eauto. }
        cbv [with_only_ins]. rewrite Hgoodp1.
        invert H2. eassert (fact_R concl = _) as ->. 2: econstructor. 1: reflexivity.
        simpl. cbv [fact_ins] in Hgoodp1. revert H3. eassert (fact_args concl = _) as ->.
        { erewrite <- (firstn_skipn _ (fact_args _)). rewrite Hgoodp1. reflexivity. }
        intros H2.  apply Forall2_app_inv_l in H2. fwd. eassert (firstn _ _ = _) as ->.
        2: eassumption. apply Forall2_length in H2p0, H2p1.
        eassert (H: forall x y, x = y -> length x = length y) by (intros; subst; reflexivity).
        apply H in Hgoodp1. rewrite length_firstn in *. rewrite length_map in *.
        rewrite length_skipn in *. rewrite <- Hgoodp1 in H2p0.
        assert (length l1' <= ins (fact_R concl)) by lia.
        assert (H': length l1' = ins (fact_R concl) \/ length l2' = 0) by lia.
        destruct H' as [H'|H'].
        -- Search firstn _ (_ ++ _). rewrite firstn_app_l by auto. reflexivity.
        -- destruct l2'; [|discriminate H']. rewrite app_nil_r.
           apply firstn_all2. lia.
    - invert H3. econstructor.
      + eauto.
      + simpl. constructor. constructor. assumption.
      + simpl. constructor.
        2: { clear -H2. induction H2; simpl; eauto. }
        cbv [with_only_ins]. rewrite Hgoodp1.
        eassert (fact_R concl = _) as ->. 2: econstructor. 1: reflexivity.
        simpl. cbv [fact_ins] in Hgoodp1. revert H4. eassert (fact_args concl = _) as ->.
        { erewrite <- (firstn_skipn _ (fact_args _)). rewrite Hgoodp1. reflexivity. }
        intros H3.  apply Forall2_app_inv_l in H3. fwd. eassert (firstn _ _ = _) as ->.
        2: { rewrite <- Forall2_map_l in *. eapply Forall2_impl_strong; [|eassumption].
             simpl. intros. invert H. constructor. rewrite map.get_put_diff in H5; auto.
             intros ?. subst. eauto. }
        apply Forall2_length in H3p0, H3p1.
        eassert (H: forall x y, x = y -> length x = length y) by (intros; subst; reflexivity).
        apply H in Hgoodp1. rewrite length_firstn in *. rewrite length_map in *.
        rewrite length_skipn in *. rewrite <- Hgoodp1 in H3p0.
        assert (length l1' <= ins (fact_R concl)) by lia.
        assert (H': length l1' = ins (fact_R concl) \/ length l2' = 0) by lia.
        destruct H' as [H'|H'].
        -- Search firstn _ (_ ++ _). rewrite firstn_app_l by auto. reflexivity.
        -- destruct l2'; [|discriminate H']. rewrite app_nil_r.
           apply firstn_all2. lia.
  Qed.

  Definition f (wanted : _ * ((rel * bool) * list T) -> Prop)
    (S : (rel * list T -> Prop) * (rel * list T) -> Prop)
    (Px : ((rel * bool) * list T -> Prop) * ((rel * bool) * list T)) :=
    let '(P, x) := Px in
    let '((R, b), args) := x in
    if b then S (fun '(R, args) => P ((R, true), args), (R, args)) else
      wanted (P, ((R, false), args)).

  Definition g (S' : ((rel * bool) * list T -> Prop) * ((rel * bool) * list T) -> Prop)
    (Px : ((rel * list T) -> Prop) * (rel * list T)) :=
    let '(P, x) := Px in
    let '(R, args) := x in
    S' (fun '((R', b'), args') => match b' with
                               | true => P (R', args')
                               | false => (R', args') = (R, firstn (ins R) args) end, ((R, true), args)).

  Goal forall w S x, g (f w S) x <-> S x.
    intros w S [P [R args]]. split.
    - simpl. admit. (*very true*)
    - simpl. admit. (*very true*)
  Abort.

  Lemma invert_rule_impl_request_hyps R r b ins' hyps' :
    rule_impl (request_hyps r) (R, b, ins') hyps' -> b = false.
  Proof.
    intros H. invert H. apply Exists_exists in H2. fwd. rewrite map_map in H2p0.
    apply in_map_iff in H2p0. fwd. invert H2p1. reflexivity.
  Qed.

  Search Forall2.
  Lemma Forall2_In_r {X Y : Type} (R : X -> Y -> Prop) xs ys y :
    Forall2 R xs ys ->
    In y ys ->
    Exists (fun x => R x y) xs.
  Proof. induction 1; simpl; intuition. subst. eauto. Qed.    

  Lemma Forall2_firstn {X Y : Type} (R : X -> Y -> Prop) xs ys n :
    Forall2 R xs ys ->
    Forall2 R (firstn n xs) (firstn n ys).
  Proof. intros H. revert n. induction H; destruct n; simpl; eauto. Qed.

  Lemma rule_impl_request_hyps r R args R' args' hyps' :
    goodish_rule r (*very necessary, finally*)->
    rule_impl r (R, args) hyps' ->
    In (R', args') hyps' ->
    rule_impl (request_hyps r) (R', false, firstn (ins R') args')
      [(R, false, firstn (ins R) args)].
  Proof.
    intros Hgood H Hin. cbv [goodish_rule] in Hgood. fwd. cbv [request_hyps].
    rewrite Hgoodp0. simpl. unfold with_only_ins at 2. rewrite Hgoodp1. simpl.
    unfold fact_relmap at 2. simpl. invert H; simpl in *.
    - econstructor.
      + do 2 rewrite Exists_map. eapply Exists_impl. 2: eapply Forall2_In_r; eauto.
        simpl. intros f Hf. invert Hf. constructor. simpl. cbv [fact_ins].
        apply Forall2_firstn. eassumption.
      + constructor; [|solve[constructor]]. rewrite Hgoodp0 in H0. invert_list_stuff.
        invert H2. constructor. simpl. rewrite <- Hgoodp1. cbv [fact_ins].
        apply Forall2_firstn. assumption.
    - econstructor.
      + do 2 rewrite Exists_map. eapply Exists_impl. 2: eapply Forall2_In_r; eauto.
        simpl. intros f Hf. invert Hf. constructor. simpl. cbv [fact_ins].
        apply Forall2_firstn. eassumption.
      + constructor; [|solve[constructor]]. rewrite Hgoodp0 in H1. invert_list_stuff.
        invert H3. constructor. simpl. eapply Forall2_impl_strong.
        2: { rewrite <- Hgoodp1. cbv [fact_ins]. apply Forall2_firstn. eassumption. }
        intros x y Hxy Hx Hy. apply in_map_iff in Hx. clear Hy. fwd. invert Hxy.
        constructor. rewrite map.get_put_diff in H1; auto. intros ?. subst.
        apply Hgoodp2. eauto.
  Qed. Search fact'_relmap.

  
  Lemma invert_rule_impl_add_hyp r R b args' hyps' :
    goodish_rule r ->
    rule_impl (add_hyp r) ((R, b), args') hyps' ->
    b = true /\
      exists hyps0',
        hyps' = ((R, false), firstn (ins R) args') :: hyps0' /\
          Forall (fun x => snd (fst x) = true) hyps0' /\
          rule_impl r (R, args') (map (fact'_relmap (fun '(R, _) => R)) hyps0').
  Proof.
    intros Hgood H. cbv [goodish_rule] in Hgood. fwd. cbv [add_hyp] in H. invert H.
    - destruct (rule_agg r) eqn:E; simpl in H0; [discriminate H0|clear H0].
      clear Hgoodp2. rewrite Hgoodp0 in *. simpl in *. cbv [with_only_ins] in H6.
      rewrite Hgoodp1 in H6. invert_list_stuff. cbv [fact_relmap] in H1. simpl in H1.
      invert H1. simpl in *. invert H0.
      split; [reflexivity|]. apply interp_facts_relmap with (g := fst) in H3. fwd.
      rewrite map_map in H3p0. simpl in H3p0.
      eassert (H': forall x y, x = y -> map snd x = map snd y) by (intros; subst; reflexivity).
      apply H' in H3p0. clear H'. do 2 rewrite map_map in H3p0. simpl in H3p0.
      rewrite map_const in H3p0. eassert (H3p0': Forall _ _).
      { apply Forall_forall. intros x Hx. apply repeat_spec in Hx. exact Hx. }
      rewrite H3p0 in H3p0'. clear H3p0. apply Lists.List.Forall_map in H3p0'.
      assert (args'0 = firstn (ins (fact_R concl)) args').
      { move H at bottom. Search args'. move H4 at bottom. simpl in H4.
        cbv [fact_ins] in Hgoodp1. rewrite <- Hgoodp1 in H.
        eapply Forall2_firstn in H4. eapply Forall2_unique_r. 1: exact H. 1: exact H4.
        apply interp_expr_det. }
      subst.
      eexists. split; [reflexivity|]. split; [assumption|]. 
      destruct r; simpl in *. rewrite Hgoodp0, E in *. econstructor.
      { constructor. constructor. eassumption. }
      rewrite map_map in H3p1. erewrite map_ext with (g := fun x => x) in H3p1.
      2: { intros a. destruct a; reflexivity. }
      rewrite map_id in H3p1. apply H3p1.
    - symmetry in H0. destruct_option_map_Some. destruct p. invert H1.
      rewrite Hgoodp0 in *. simpl in *. cbv [with_only_ins] in H7.
      rewrite Hgoodp1 in H7. invert_list_stuff. cbv [fact_relmap] in H1. simpl in H1.
      invert H1. simpl in *. invert H0.
      split; [reflexivity|]. apply interp_facts_relmap with (g := fst) in H4. fwd.
      rewrite map_map in H4p0. simpl in H4p0.
      eassert (H': forall x y, x = y -> map snd x = map snd y) by (intros; subst; reflexivity).
      apply H' in H4p0. clear H'. do 2 rewrite map_map in H4p0. simpl in H4p0.
      rewrite map_const in H4p0. eassert (H4p0': Forall _ _).
      { apply Forall_forall. intros x Hx. apply repeat_spec in Hx. exact Hx. }
      rewrite H4p0 in H4p0'. clear H4p0. apply Lists.List.Forall_map in H4p0'.
      assert (args'0 = firstn (ins (fact_R concl)) args').
      { move H at bottom. Search args'. move H5 at bottom. simpl in H5.
        cbv [fact_ins] in Hgoodp1. rewrite <- Hgoodp1 in H. pose proof H5 as H5'.
        eapply Forall2_firstn in H5. eapply Forall2_unique_r.
        1: exact H. 2: apply interp_expr_det. eapply Forall2_impl_strong; [|eassumption].
        intros. rewrite Hgoodp1 in H1. apply in_map_iff in H1. fwd.
        invert H0. constructor. rewrite map.get_put_diff in H4; auto. intros H'.
        subst. apply Hgoodp2. eauto. }
      subst.
      eexists. split; [reflexivity|]. split; [assumption|].
      destruct r; simpl in *. rewrite Hgoodp0, E in *. destruct a. econstructor.
      { apply interp_agg_expr_relmap with (g := fst) in H3.
        cbv [agg_expr_relmap] in H3. simpl in H3. rewrite map_map in H3.
        rewrite map_ext with (g := fun x => x) in H3.
        2: { intros a. destruct a; reflexivity. }
        rewrite map_id in H3. apply H3. }
      { constructor. constructor. eassumption. }
      rewrite map_map in H4p1. erewrite map_ext with (g := fun x => x) in H4p1.
      2: { intros a. destruct a; reflexivity. }
      rewrite map_id in H4p1. apply H4p1.
  Qed.

  Lemma request_hyps_hyps_false r R b args hyps' :
    rule_impl (request_hyps r) (R, b, args) hyps' ->
    Forall (fun hyp' => snd (fst hyp') = false) hyps'.
  Proof.
    intros H. cbv [request_hyps] in H. invert H. apply Forall_forall.
    intros x Hx. eapply Forall2_In_r in H5. 2: eassumption.
    rewrite Exists_map in H5. apply Exists_exists in H5. fwd. invert H5p1. reflexivity.
  Qed.

  Lemma f_fixpoint' r S w :
    goodish_rule r ->
    fp (F [request_hyps r]) w ->
    fp (F [r]) S ->
    fp (F [request_hyps r; add_hyp r]) (f w S).
  Proof.
    cbv [fp F]. intros Hgood Wfp H [P [[R b] args]] Hx. simpl.
    destruct Hx as [Hx| [Hx|Hx]]; auto.
    { destruct b; auto. }
    fwd. invert Hxp0.
    - simpl. pose proof H1 as H1'.
      apply invert_rule_impl_request_hyps in H1. subst. apply Wfp. right. right.
      exists hyps'. split.
      { constructor. assumption. }
      apply request_hyps_hyps_false in H1'. rewrite Forall_forall in Hxp1, H1'.
      rewrite Forall_forall. intros x Hx. specialize (Hxp1 _ Hx). specialize (H1' _ Hx).
      destruct x as [ [R' b'] args']. simpl in Hxp1, H1'. subst. assumption.
    - invert_list_stuff. eapply invert_rule_impl_add_hyp in H2; eauto. fwd. simpl.
      apply H. right. right. eexists. split; eauto. apply Forall_map. eapply Forall_impl.
      2: { eapply Forall_and. 1: apply Hxp1p1. apply H2p1p1. }
      simpl. intros [[R' b'] args']. simpl. intros. fwd. assumption.
  Qed.

  Lemma g_fixpoint' (*P*) r S :
    goodish_rule r ->
    S_sane S ->
    fp (F [request_hyps r; add_hyp r]) S ->
    fp (F [r]) (g S).
  Proof.
    cbv [fp F]. intros Hgood (Sgood1&Sgood2) H [P x] Hx. destruct Hx as [Hx| [Hx|Hx]]; auto.
    { simpl. destruct x. apply Sgood1. assumption. }
    fwd. destruct x as [R args]. invert_list_stuff.
    pose proof rule_impl_add_hyp as H1'. specialize H1' with (1 := Hgood) (2 := H1).
    simpl. apply H. right. right. eexists. split.
    { apply Exists_cons_tl. constructor. eassumption. }
    constructor.
    { auto. }
    apply Forall_map. pose proof Hxp1 as H'. rewrite Forall_forall in H'.
    rewrite Forall_forall. intros [R' args'] Hx. specialize H' with (1 := Hx).
    simpl in H'. cbv [fact'_relmap]. eapply Sgood2; [eassumption|]. simpl.
    clear H'. intros y Hy. destruct y as [ [Ry By] argsy]. destruct By.
    { apply H; auto. }
    invert Hy. apply H. right. right. exists [(R, false, firstn (ins R) args)]. split.
    2: eauto. constructor. eapply rule_impl_request_hyps; eauto.
  Qed.

  Lemma f_sane w S :
    (forall x P, P x -> S (P, x)) ->
    (forall x P, P x -> w (P, x)) ->
    (forall x P, P x -> f w S (P, x)).
  Proof. intros H1 H2 [[R b] args] P. simpl. destruct b; eauto. Qed.

  Hint Resolve f_sane : core.
  Hint Unfold S_sane : core.

  Lemma f_fixpoint w p S :
    S_sane w ->
    S_sane S ->
    Forall goodish_rule p ->
    fp (F p) S ->
    fp (F (map request_hyps p)) w ->
    fp (F (make_good p)) (f w S).
  Proof.
    intros (Wgood1&Wgood2) (Sgood1&Sgood2) H1 H2 HP. pose proof f_fixpoint' as H'.
    rewrite Forall_forall in H1.
    assert (forall r, In r p -> fp (F [request_hyps r]) w).
    { intros r Hr. rewrite <- split_fixpoint in HP by auto. apply HP. apply in_map. assumption. }
    apply split_fixpoint; auto. cbv [make_good]. intros r Hr.
    apply in_app_iff in Hr. destruct Hr as [Hr|Hr]; apply in_map_iff in Hr; fwd.
    - apply split_fixpoint; auto. rewrite <- split_fixpoint in H2 by auto. 
      specialize (H' _ _ _ ltac:(eauto) ltac:(eauto) ltac:(eauto)).
      rewrite <- split_fixpoint in H' by auto. simpl in *. intros. apply H'. tauto.
    - apply split_fixpoint; auto. rewrite <- split_fixpoint in H2 by auto.
      specialize (H' _ _ _ ltac:(eauto) ltac:(eauto) ltac:(eauto)).
      rewrite <- split_fixpoint in H' by auto. simpl in *. intros. apply H'. tauto.
  Qed.

  Lemma g_sane S :
    (forall x P, P x -> S (P, x)) ->
    (forall x P, P x -> g S (P, x)).
  Proof. intros H [R args] P HP. simpl. auto. Qed.

  Hint Resolve g_sane : core.

  Lemma g_fixpoint p S :
    Forall goodish_rule p ->
    S_sane S ->
    fp (F (make_good p)) S ->
    fp (F p) (g S).
  Proof.
    intros H1 (Sgood1&Sgood2) H2. pose proof g_fixpoint' as H'. rewrite Forall_forall in H1.
    apply split_fixpoint; auto. cbv [make_good]. intros r Hr.
    apply H'; auto.
    apply split_fixpoint; auto.
    intros r' Hr'. rewrite <- split_fixpoint in H2 by auto.
    destruct Hr' as [Hr' | [Hr' | Hr'] ]; [| |exfalso; auto]; subst; apply H2; cbv [make_good]; apply in_app_iff; auto using in_map.
  Qed.

  Lemma g_mono S1 S2 :
    (forall x, S1 x -> S2 x) ->
    forall x, g S1 x -> g S2 x.
  Proof. cbv [g]. intros H [P [R args]] Hx. auto. Qed.
  
  Lemma gf_id w S :
    S_sane S ->
    equiv S (g (f w S)).
  Proof. (*note: here i just use weakening, which follows from Sgood1 and Sgood2, but Sgood1 and Sgood2 together are stronger than weakening*)
    intros (Sgood1&Sgood2). cbv [equiv g f]. intros [P [R args]].
    intuition eauto. (*because eauto doesn't know how to unfold <-> ?*)
  Qed.

  Hint Resolve fp_lfp F_mono S_sane_lfp : core.

  Lemma lfp_preimage p :
    Forall goodish_rule p ->
    equiv (g (lfp (F (make_good p)))) (lfp (F p)).
  Proof.
    intros Hgood. eapply lfp_preimage'.
    - exact g_mono.
    - apply f_fixpoint with (w := lfp (F (map request_hyps p))); eauto.
    - apply g_fixpoint; eauto.
    - apply gf_id; eauto.
  Qed.

  Lemma equiv_trans {U : Type} (A B C : U -> _) :
    equiv A B -> equiv B C -> equiv A C.
  Proof. cbv [equiv]. intros. rewrite H, <- H0. reflexivity. Qed.

  Lemma equiv_symm {U : Type} (A B : U -> _) :
    equiv A B -> equiv B A.
  Proof. cbv [equiv]. intros. rewrite H. reflexivity. Qed.

  Lemma g_ext A B : equiv A B -> equiv (g A) (g B).
  Proof. cbv [equiv g]. intros H [P [R args]]. apply H. Qed.
      
  Lemma phase_correct p :
    Forall goodish_rule p ->
    equiv (fun '(P, f) => prog_impl_implication p P f) (g (fun '(P, f) => prog_impl_implication (make_good p) P f)).
  Proof.
    intros. eapply equiv_trans.
    { apply prog_impl_fact_lfp. }
    eapply equiv_trans.
    { apply equiv_symm. apply lfp_preimage. assumption. }
    apply equiv_symm. apply g_ext. apply prog_impl_fact_lfp.
  Qed. 

  Lemma source_impl_target p Q R args :
    Forall goodish_rule p ->
    prog_impl_implication p Q (R, args) ->
    prog_impl_implication (make_good p)
      (fun '((R0, b0), args0) => if b0 then Q (R0, args0) else (R0, args0) = (R, firstn (ins R) args))
      ((R, true), args).
  Proof.
    intros H1 H2. pose proof phase_correct _ H1 as H3. cbv [equiv] in H3.
    rewrite (H3 (_, _)) in H2. clear H3. simpl in H2. assumption.
  Qed.

  Lemma target_impl_source p R args Q :
    Forall goodish_rule p ->
    prog_impl_implication (make_good p) Q ((R, true), args) ->
    prog_impl_implication p (fun '(R, args) => Q ((R, true), args)) (R, args).
  Proof.
    intros H1 H2. pose proof phase_correct _ H1 as H3. cbv [equiv] in H3.
    rewrite (H3 (_, _)). clear H3. simpl. remember (R, true, args) as x eqn:E.
    revert R args E. (*TODO factor following out into lemma*)induction H2; intros; subst.
    - apply partial_in. assumption.
    - eapply partial_step. 1: apply H. cbv [make_good] in H.
      apply Exists_app in H. destruct H as [H|H].
      { clear -H. exfalso. rewrite Exists_map in H. apply Exists_exists in H.
        fwd. invert Hp1. clear H4. rewrite Exists_map in H1. apply Exists_exists in H1.
        fwd. invert H1p1. }
      apply Exists_map in H. apply Exists_exists in H. fwd.
      rewrite Forall_forall in H1. apply invert_rule_impl_add_hyp in Hp1; auto.
      fwd. constructor.
      2: { rewrite Forall_forall in *. intros [[R' b'] args'] H.
           specialize (Hp1p1p1 _ ltac:(eassumption)). simpl in Hp1p1p1. subst.
           apply partial_pftree_trans. eapply partial_pftree_weaken.
           1: apply H2p1; eauto. intros [[Ry By] argsy]. intros Hy. destruct By.
           - apply partial_in. assumption.
           - clear H2p0. invert Hy. eapply partial_step.
             { cbv [make_good]. apply Exists_app. left. apply Exists_map.
               apply Exists_exists. exists x. split; [assumption|].
               eapply rule_impl_request_hyps; eauto.
               apply in_map_iff. eexists (_, _, _). simpl. eauto. }
             constructor; [|constructor]. apply partial_in. reflexivity. }
      apply partial_in. reflexivity.
  Qed.
End Transform.
