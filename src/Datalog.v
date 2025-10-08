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

From Datalog Require Import Forall3 Map Tactics Fp List.

From coqutil Require Import Map.Interface Map.Properties Tactics Tactics.fwd Datatypes.List.

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
    { agg : aggregator; i : var; vs : list var; s: expr; body: expr; hyps: list fact }.

  (*why is there flat_map but not flatten*)
  Inductive interp_agg_expr (ctx : context) : agg_expr -> T -> list (rel * list T) -> Prop :=
  | mk_interp_agg_expr a i vs s s' i's body's body hyps hyps's result :
    interp_expr ctx s s' ->
    get_set s' = Some i's ->
    Forall3 (fun i' body' hyps' =>
               exists vs',
                 let ctx' := map.putmany ctx (map.put (map.of_list (combine vs vs')) i i') in
                 Forall2 (interp_fact ctx') hyps hyps' /\
                   interp_expr ctx' body body')
      i's body's hyps's ->
    result = fold_right (interp_agg a) (agg_id a) body's ->
    interp_agg_expr _ {| agg := a; i := i; vs := vs; s := s; body := body; hyps := hyps |} result (concat hyps's).

  Record rule := { rule_agg : option (var * agg_expr); rule_concls : list fact; rule_hyps : list fact }.

  (*semantics of rules*)
  Inductive rule_impl : rule -> rel * list T -> list (rel * list T) -> Prop :=
  | normal_rule_impl hyps concls f' hyps' ctx :
    Exists (fun c => interp_fact ctx c f') concls ->
    Forall2 (interp_fact ctx) hyps hyps' ->
    rule_impl {| rule_agg := None; rule_hyps := hyps; rule_concls := concls|} f' hyps'
  | agg_rule_impl res res' agg_hyps' aexpr hyps concls f' hyps' ctx :
    interp_agg_expr ctx aexpr res' agg_hyps' ->
    Exists (fun c => interp_fact (map.put ctx res res') c f') concls ->
    Forall2 (interp_fact ctx) hyps hyps' ->
    rule_impl {| rule_agg := Some (res, aexpr); rule_hyps := hyps; rule_concls := concls|} f' hyps'.

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
  
  (*for any relation, we may think of some arguments to the relation as inputs, and others as outputs.  I think we do not actually care whether there is a functional dependence there.  by convention, we say that fact_args is always of the form outputs ++ inputs.  now, the function outs gives the number of outputs of a given relation. this suffices to determine the inputs, too.*)
    Inductive appears_in_expr (v : var) : expr -> Prop :=
  | app_in_fun_expr args f :
    Exists (appears_in_expr v) args ->
    appears_in_expr v (fun_expr f args)
  | app_in_var_expr : appears_in_expr v (var_expr v).

  Definition appears_in_fact (v : var) (f : fact) :=
    Exists (appears_in_expr v) f.(fact_args).
  Check eq. (*WHY*) Locate "=".
  Definition barely_appears_in_fact (v : var) (f : fact) :=
    In (var_expr v) f.(fact_args).

  Print agg_expr.
  Definition appears_in_agg_expr v ae :=
    appears_in_expr v ae.(s) \/
      ~In v (ae.(i) :: ae.(vs)) /\
        (appears_in_expr v ae.(body) \/ Exists (appears_in_fact v) ae.(hyps)).

  Definition appears_in_rule v r :=
    ~(exists ae, r.(rule_agg) = Some (v, ae)) /\ Exists (appears_in_fact v) r.(rule_concls) \/ Exists (appears_in_fact v) r.(rule_hyps) \/ (exists w ae, r.(rule_agg) = Some (w, ae) /\ appears_in_agg_expr v ae).

  Definition good_rule (r : rule) :=
    forall v, appears_in_rule v r ->
         Exists (barely_appears_in_fact v) r.(rule_hyps).

  Definition good_prog (p : list rule) := Forall good_rule p.

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
    intros H. cbv [appears_in_fact] in *. simpl in *. cbv [fact_ins] in H.
    rewrite Exists_exists in *. fwd. apply In_firstn_to_In in Hp0. eauto.
  Qed.

  Lemma barely_appears_with_only_ins v f :
    barely_appears_in_fact v (with_only_ins f) ->
    barely_appears_in_fact v f.
  Proof.
    intros H. cbv [barely_appears_in_fact] in *. simpl in *. cbv [fact_ins] in H.
    apply In_firstn_to_In in H. assumption.
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
    {| agg := ae.(agg); i := ae.(i); vs := ae.(vs);
                                     s := ae.(s);
                                     body := ae.(body);
                                     hyps := map fact_relmap ae.(hyps) |}.

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
    interp_agg_expr interp_fun get_set agg_id interp_agg ctx (agg_expr_relmap aexpr) res' (map fact'_relmap agg_hyps').
  Proof.
    intros H. invert H. cbv [agg_expr_relmap]. simpl.
    eassert (map _ (concat _) = _) as ->. 2: econstructor; eauto.
    { rewrite concat_map. reflexivity. }
    clear -H2. induction H2; simpl; eauto. constructor; eauto. simpl in *. fwd.
    exists vs'. intuition eauto. move Hp0 at bottom. clear -Hp0. induction Hp0; simpl; eauto.
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
      rewrite Hgoodp1 in H1. cbv [appears_in_fact] in H1. simpl in H1.
      rewrite Exists_exists in H1. fwd. apply in_map_iff in H1p0. fwd. invert H1p1.
      assumption.
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
    fwd. destruct x as [R args]. invert_list_stuff. Search rule_impl.
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
      apply Exists_map in H. apply Exists_exists in H. fwd. Search rule_impl add_hyp.
      rewrite Forall_forall in H1. apply invert_rule_impl_add_hyp in Hp1; auto.
      fwd. constructor.
      2: { rewrite Forall_forall in *. intros [[R' b'] args'] H.
           specialize (Hp1p1p1 _ ltac:(eassumption)). simpl in Hp1p1p1. subst.
           apply partial_pftree_trans. eapply partial_pftree_weaken.
           1: apply H2p1; eauto. intros [[Ry By] argsy]. intros Hy. destruct By.
           - apply partial_in. assumption.
           - clear H2p0. invert Hy. eapply partial_step.
             { cbv [make_good]. apply Exists_app. left. apply Exists_map.
               apply Exists_exists. exists x. split; [assumption|]. Search x.
               Check rule_impl_request_hyps. eapply rule_impl_request_hyps; eauto.
               apply in_map_iff. eexists (_, _, _). simpl. eauto. }
             constructor; [|constructor]. apply partial_in. reflexivity. }
      apply partial_in. reflexivity.
  Qed.
End Transform.
