From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.

From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics.

From Datalog Require Import Map Tactics Fp List.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List.

Import ListNotations.

(*relations, variables, functions, and "aggregator functions" (e.g. min, max, sum, prod)*)
(* A datalog program talks about facts R(x1, ..., xn), where (R : rel) and (x1 : T), (x2 : T), etc. *)
Class signature {fn aggregator T : Type} : Type :=
  {
    (*returning None means inputs not in domain (e.g., number of args was wrong)*)
    interp_fun : fn -> list T -> option T;
    (*if x represents a finite set, then get_set x = Some ([x1; ...; xn]), where x1, ..., xn are the elements of the set*)
    get_set : T -> option (list T);
    (*agg_id sum = O, agg_id prod = 1, agg_id min = inf, etc*)
    agg_id : aggregator -> T;
    (*interp_agg takes an aggregator and returns the corresponding binop...
    arguably type should be aggregator -> T -> T -> option T,
    but i dont want to bother with that*)
    interp_agg : aggregator -> T -> T -> T; }.
Arguments signature : clear implicits.

Class query_signature {rel : Type} :=
  { ins : rel -> nat }.
Arguments query_signature : clear implicits.

Section __.
  Context {rel var fn aggregator T : Type}.
  Context `{sig : signature fn aggregator T} `{query_sig : query_signature rel}.
  Context {context : map.map var T} {context_ok : map.ok context}.
  Context {var_eqb : var -> var -> bool} {var_eqb_spec :  forall x0 y0 : var, BoolSpec (x0 = y0) (x0 <> y0) (var_eqb x0 y0)}.

  (*avoid generating useless induction principle*)
  Unset Elimination Schemes.
  Inductive expr :=
  | var_expr (v : var)
  | fun_expr (f : fn) (args : list expr).
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
  | mk_interp_agg_expr (a : aggregator) i vs s s' i's body's body hyps hyps's (result : T) :
    interp_expr ctx s s' ->
    get_set s' = Some i's ->
    Forall3 (fun i' body' hyps' =>
               exists vs' ctx',
                 map.of_list_zip vs vs' = Some ctx' /\
                   let ctx'' := map.putmany (map.put ctx i i') ctx' in
                   Forall2 (interp_fact ctx'') hyps hyps' /\
                     interp_expr ctx'' body body')
      i's body's hyps's ->
    result = fold_right (fun (x y : T) => interp_agg a x y) (agg_id a) body's ->
    interp_agg_expr _ {| agg_agg := a; agg_i := i; agg_vs := vs; agg_s := s; agg_body := body; agg_hyps := hyps |} result hyps's.

  Record rule := { rule_agg : option (var * agg_expr); rule_concls : list fact; rule_hyps : list fact }.

  (*semantics of rules*)
  Inductive interp_option_agg_expr : _ -> _ -> _ -> _ -> Prop :=
  | ioae_None ctx :
    interp_option_agg_expr ctx None ctx []
  | ioae_Some ctx res res' aexpr agg_hyps's :
    interp_agg_expr ctx aexpr res' agg_hyps's ->
    interp_option_agg_expr ctx (Some (res, aexpr)) (map.put ctx res res') agg_hyps's.
  
  Inductive rule_impl' : rule -> rel * list T -> list (rel * list T) -> list (list (rel * list T)) -> Prop :=
  | mk_rule_impl' r agg_hyps's ctx' f' hyps' ctx :
    interp_option_agg_expr ctx r.(rule_agg) ctx' agg_hyps's ->
    Exists (fun c => interp_fact ctx' c f') r.(rule_concls) ->
    Forall2 (interp_fact ctx) r.(rule_hyps) hyps' ->
    rule_impl' r f' hyps' agg_hyps's.

  Hint Constructors rule_impl' interp_option_agg_expr : core.

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
    - destruct e; simpl in He; auto.
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

  Definition appears_in_agg_expr v ae :=
    In v (vars_of_expr ae.(agg_s)) \/
      ~In v (ae.(agg_i) :: ae.(agg_vs)) /\
        (In v (vars_of_expr ae.(agg_body)) \/ In v (flat_map vars_of_fact ae.(agg_hyps))).

  Definition good_agg_expr ae :=
    Forall (fun v => In (var_expr v) (flat_map fact_args ae.(agg_hyps))) ae.(agg_vs).

  Hint Unfold appears_in_agg_expr : core.

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
        right. apply in_flat_map. eauto.
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
    In (var_expr v) f.(fact_args) ->
    agree_on ctx1 ctx2 v.
  Proof.
    intros H1 H2 Hv.
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
      intros v Hv. specialize (Hgood _ Hv). rewrite in_flat_map in Hgood.
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

  Definition appears_in_rule v r :=
    ~(exists ae, r.(rule_agg) = Some (v, ae)) /\
      In v (flat_map vars_of_fact r.(rule_concls)) \/
      In v (flat_map vars_of_fact r.(rule_hyps)) \/
      (exists w ae, r.(rule_agg) = Some (w, ae) /\ appears_in_agg_expr v ae).

  Definition good_rule (r : rule) :=
    (forall v, appears_in_rule v r ->
          In (var_expr v) (flat_map fact_args r.(rule_hyps))) /\
      match r.(rule_agg) with
      | None => True
      | Some (_, ae) => good_agg_expr ae
      end.

  Definition good_prog (p : list rule) := Forall good_rule p.

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
              In (var_expr v) (flat_map fact_args r.(rule_hyps)) \/
                In v invars) /\
        (forall v, In v (flat_map vars_of_expr (flat_map fact_ins (rule_hyps r))) ->
              In v invars) /\
        match r.(rule_agg) with
        | None => True
        | Some (_, aexpr) =>
            good_agg_expr aexpr /\
              forall v, In v (flat_map vars_of_expr (flat_map fact_ins aexpr.(agg_hyps))) ->
                   In v invars /\ ~In v aexpr.(agg_vs) /\ v <> aexpr.(agg_i)
        end.
  
  Definition rule_agg_hyps r :=
    match r.(rule_agg) with
    | None => []
    | Some (_, aexpr) => aexpr.(agg_hyps)
    end.

  Definition agg_hyps_elt_lengths r := length (rule_agg_hyps r).

  Lemma rule_impl_concl_relname_in r x hyps :
    rule_impl r x hyps ->
    In (fst x) (map fact_R (rule_concls r)).
  Proof.
    intros H. invert H. fwd. invert H0p1. apply Exists_exists in H0.
    fwd. invert H0p1. simpl. apply in_map. assumption.
  Qed.

  Lemma interp_agg_expr_hyp_relname_in ctx aexpr res' agg_hyps' :
    interp_agg_expr ctx aexpr res' agg_hyps' ->
    Forall (fun hyp => In (fst hyp) (map fact_R (agg_hyps aexpr))) (concat agg_hyps').
  Proof.
    intros H. invert H. simpl. apply Forall3_ignore12 in H2. apply Forall_concat.
    eapply Forall_impl; [|eassumption]. simpl. clear. intros. fwd.
    apply Forall2_forget_l in Hp1. eapply Forall_impl; [|eassumption].
    simpl. clear. intros. fwd. invert Hp1. simpl. apply in_map. assumption.
  Qed.

  Lemma rule_impl'_hyp_relname_in r x hyps agg_hyps' :
    rule_impl' r x hyps agg_hyps' ->
    Forall (fun hyp => In (fst hyp) (map fact_R (rule_hyps r))) hyps /\
      Forall (fun hyp => In (fst hyp) (map fact_R (rule_agg_hyps r)))
      (concat agg_hyps').
  Proof.
    intros H. invert H. split.
    - apply Forall2_forget_l in H2. eapply Forall_impl; [|eassumption].
      simpl. intros. fwd. invert Hp1. simpl. apply in_map. assumption.
    - cbv [rule_agg_hyps]. invert H0; auto. eapply interp_agg_expr_hyp_relname_in. eassumption.
  Qed.

  Lemma rule_impl_hyp_relname_in r x hyps :
    rule_impl r x hyps ->
    Forall (fun hyp => In (fst hyp) (map fact_R (rule_agg_hyps r ++ rule_hyps r))) hyps.
  Proof.
    cbv [rule_impl]. intros. fwd. apply rule_impl'_hyp_relname_in in Hp1.
    fwd. apply Forall_app. rewrite map_app.  split; eapply Forall_impl; eauto; intros; rewrite in_app_iff; simpl; eauto.
  Qed.
End __.
Arguments fact : clear implicits.
Arguments rule : clear implicits.
Arguments expr : clear implicits.
Arguments agg_expr : clear implicits.
