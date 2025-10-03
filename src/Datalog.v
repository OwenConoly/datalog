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

From Datalog Require Import Forall3 Map Tactics.

From coqutil Require Import Map.Interface Map.Properties Tactics Tactics.fwd Datatypes.List.

Import ListNotations.

Section __.
  (*relations, variables, functions, and "aggregator functions" (e.g. min, max, sum, prod)*)
  Context (rel: Type) (var: Type) (fn: Type) (aggregator: Type).
  (* A datalog program talks about facts R(x1, ..., xn), where (R : rel) and (x1 : T), (x2 : T), etc. *)
  Context (T : Type).
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
    interp_agg_expr _ {| agg := a; i := i; vs := vs; s := s; body := body; hyps := hyps |} result (flat_map (fun x => x) hyps's).

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

  Inductive partial_pftree {T : Type} (P : T -> list T -> Prop) : T -> list T -> Prop :=
  | partial_in x l : In x l -> partial_pftree _ x l
  | partial_step x l ls :
    P x l ->
    Forall2 (partial_pftree _) l ls ->
    partial_pftree _ x (flat_map (fun x => x) ls).

  Definition prog_impl_implication (p : list rule) : rel * list T -> list (rel * list T) -> Prop :=
    partial_pftree (fun f' hyps' => Exists (fun r => rule_impl r f' hyps') p).
  
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
    eauto using Forall2_impl, interp_expr_subst_more.
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
  Context (outs: rel -> nat).
  Definition fact_outs f := firstn (outs f.(fact_R)) f.(fact_args).
  Definition fact_ins f := skipn (outs f.(fact_R)) f.(fact_args).

  Definition with_only_ins (f : fact) :=
    {| fact_R := f.(fact_R); fact_args := fact_ins f |}.
  
  (*if we get a message saying concls of r need to be computed, then send out messages
    saying premises of r need to be computed*)
  (*note: this is nonsensical if length r.(rule_concls) > 1*)
  Definition request_hyps (r : rule) : rule :=
    {| rule_agg := None;
      rule_hyps := map with_only_ins r.(rule_concls);
      rule_concls := map with_only_ins r.(rule_hyps) |}.

  (*add a hypothesis saying that the conclusion is something we need to compute*)
  (*note: this is fairly nonsensical (not semantically equivalent) if length r.(rule_concls) > 1*)
  Definition add_hyp (r : rule) : rule :=
    {| rule_agg := r.(rule_agg);
      rule_hyps := map with_only_ins r.(rule_concls) ++ r.(rule_hyps);
      rule_concls := r.(rule_concls) |}.

  (*semanticallly equivalent if each rule has concl length at most 1*)
  Definition make_good (p : list rule) : list rule :=
    map request_hyps p ++ map add_hyp p.

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

  (*2 conditions.
   * hyp_ins only depend on concl_ins, and
   * whole thing only depends on (concl_ins \cup vars_bare_in_hyps)
   (implicit conditions: every concl_in is of the form var_expr blah, where blah was not
   bound to the agg_expr)
   *)
  Definition goodish_rule r :=
    exists concl invars,
      r.(rule_concls) = [concl] /\
        fact_ins concl = map var_expr invars /\
        ~(exists invar ae, In invar invars /\ r.(rule_agg) = Some (invar, ae)) /\
        (forall v, (*alternatively, could write appears_in_outs here*)appears_in_rule v r ->
              Exists (barely_appears_in_fact v) r.(rule_hyps) \/
                In v invars) /\
        (forall v, Exists (appears_in_fact v) (map with_only_ins (rule_hyps r)) ->
              In v invars).
    
  (* Hint Unfold appears_in_fact fact_ins fact_outs : core. *)  

  Lemma In_skipn {A : Type} (x : A) n l :
    In x (skipn n l) ->
    In x l.
  Proof. intros. erewrite <- firstn_skipn. apply in_app_iff. eauto. Qed.
  
  Lemma appears_with_only_ins v f :
    appears_in_fact v (with_only_ins f) ->
    appears_in_fact v f.
  Proof.
    intros H. cbv [appears_in_fact] in *. simpl in *. cbv [fact_ins] in H.
    rewrite Exists_exists in *. fwd. Search In skipn. apply In_skipn in Hp0. eauto.
  Qed.

  Lemma barely_appears_with_only_ins v f :
    barely_appears_in_fact v (with_only_ins f) ->
    barely_appears_in_fact v f.
  Proof.
    intros H. cbv [barely_appears_in_fact] in *. simpl in *. cbv [fact_ins] in H.
    apply In_skipn in H. assumption.
  Qed.

  Lemma appears_in_rule_request_hyps v r :
    goodish_rule r ->
    appears_in_rule v (request_hyps r) ->
    appears_in_rule v r.
  Proof.
    clear. intros Hgood H. cbv [goodish_rule] in Hgood. fwd.
    cbv [appears_in_rule] in *. simpl in *. rewrite Hgoodp0 in *.
    destruct H as [H| [H|H]]; fwd.
    - right. left. rewrite Exists_map in Hp1. eapply Exists_impl; [|eassumption].
      simpl. intros. apply appears_with_only_ins. assumption.
    - left. split.
      2: { rewrite Exists_map in H. eapply Exists_impl; [|eassumption].
           simpl. intros. apply appears_with_only_ins. assumption. }
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
    - auto.
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
    cbv [appears_in_rule] in *. simpl in *. intros [Hv| [Hv|Hv]]; fwd; eauto.
    - invert Hv; eauto. left. cbv [with_only_ins] in H0. rewrite Hgoodp1 in H0.
      cbv [appears_in_fact] in H0. simpl in H0. apply Exists_exists in H0.
      fwd. split.
      + intros H'. fwd. apply in_map_iff in H0p0. fwd. invert H0p1. eauto.
      + rewrite <- Hgoodp1 in H0p0. constructor. cbv [appears_in_fact].
        apply Exists_exists. cbv [fact_ins] in H0p0. Search In firstn.
        apply In_skipn in H0p0. eauto.
    - right. right. eauto.
  Qed.

  Lemma add_hyp_good r :
    goodish_rule r ->
    good_rule (add_hyp r).
  Proof.
    intros H. pose proof H as HH. cbv [goodish_rule] in H. fwd.
    intros v Hv. simpl. rewrite Hp0. simpl.
    apply appears_in_rule_add_hyp in Hv; [|assumption].
    apply Hp3 in Hv. destruct Hv as [Hv|Hv].
    - apply Exists_cons_tl. assumption.
    - apply Exists_cons_hd. cbv [with_only_ins]. rewrite Hp1.
      cbv [barely_appears_in_fact]. simpl. apply in_map. assumption.
  Qed.


  (*[rs1 smaller than rs2] mod P*)
  Definition smaller_than_mod (rs1 rs2 : list rule) (P : rel * list T -> Prop) :=
    forall f fs1,
      prog_impl_implication rs1 f fs1 ->
      exists fs2,
        prog_impl_implication rs2 f fs2 /\
          Forall (fun f' => P f' \/ In f' fs1) fs2.

  Lemma rule_impl_add_hyp R r outs' ins' hyps' :
    goodish_rule r ->
    length outs' = outs R ->
    rule_impl r (R, outs' ++ ins') hyps' ->
    rule_impl (add_hyp r) (R, outs' ++ ins') ((R, ins') :: hyps').
  Proof.
    intros Hgood Hlen H. cbv [goodish_rule] in Hgood. fwd.
    invert H; cbv [add_hyp]; simpl in *; subst; repeat invert_list_stuff.
    - econstructor.
      + constructor. eassumption.
      + simpl. constructor; [|eassumption]. cbv [with_only_ins]. rewrite Hgoodp1.
        invert H2. eassert (fact_R concl = _) as ->. 2: econstructor. 1: reflexivity.
        simpl. cbv [fact_ins] in Hgoodp1. revert H3. eassert (fact_args concl = _) as ->.
        { erewrite <- (firstn_skipn _ (fact_args _)). rewrite Hgoodp1. reflexivity. }
        intros H2.  apply Forall2_app_inv_l in H2. fwd. assert (outs' = l1').
        { apply Forall2_length in H2p0. rewrite <- Hgoodp1 in H2p1.
          rewrite length_firstn in H2p0. apply Forall2_length in H2p1.
          rewrite length_skipn in H2p1.
          eassert (H: forall x y, x = y -> length x = length y) by (intros; subst; reflexivity).
          pose proof H2p2 as H'. apply H in H2p2. do 2 rewrite length_app in H2p2.
          assert (length outs' = length l1') by lia. clear -H' H0.
          revert l1' H' H0. induction outs'; destruct l1'; simpl; auto; try lia.
          intros H'. invert H'. intros. f_equal. auto. }
        subst. apply app_inv_head in H2p2. subst. assumption.
    - invert H3. econstructor.
      + eassumption.
      + constructor. constructor. assumption.
      + simpl. constructor; [|eassumption]. cbv [with_only_ins]. rewrite Hgoodp1.
        eassert (fact_R concl = _) as ->. 2: econstructor. 1: reflexivity.
        simpl. cbv [fact_ins] in Hgoodp1. revert H4. eassert (fact_args concl = _) as ->.
        { erewrite <- (firstn_skipn _ (fact_args _)). rewrite Hgoodp1. reflexivity. }
        intros H3.  apply Forall2_app_inv_l in H3. fwd. assert (outs' = l1').
        { apply Forall2_length in H3p0. rewrite <- Hgoodp1 in H3p1.
          rewrite length_firstn in H3p0. apply Forall2_length in H3p1.
          rewrite length_skipn in H3p1.
          eassert (H: forall x y, x = y -> length x = length y) by (intros; subst; reflexivity).
          pose proof H3p2 as H'. apply H in H3p2. do 2 rewrite length_app in H3p2.
          assert (length outs' = length l1') by lia. clear -H' H1.
          revert l1' H' H1. induction outs'; destruct l1'; simpl; auto; try lia.
          intros H'. invert H'. intros. f_equal. auto. }
        subst. apply app_inv_head in H3p2. subst. clear - H3p1 Hgoodp2 context_ok.
        revert l2' H3p1. induction invars; intros; simpl in *; repeat invert_list_stuff.
        -- constructor.
        -- constructor.
           ++ invert H1. constructor. rewrite map.get_put_diff in H0; auto.
              intros H'. subst. apply Hgoodp2. eauto.
           ++ eapply IHinvars; eauto. intros H'. apply Hgoodp2. fwd. eauto.
  Qed.
  
  Lemma good_rule_equiv datalog_ctx datalog_ctx' r :
    goodish_rule r ->
    (forall R ins' outs',
        length outs' = outs R ->
        prog_impl_fact datalog_ctx (R, outs' ++ ins') <->
          prog_impl_fact datalog_ctx' (R, outs' ++ ins') /\
            prog_impl_fact datalog_ctx' (R, ins')) ->
    (forall R ins' outs',
        length outs' = outs R ->
        prog_impl_fact (r :: datalog_ctx) (R, outs' ++ ins') <->
          prog_impl_fact (request_hyps r :: add_hyp r :: datalog_ctx') (R, outs' ++ ins') /\
            prog_impl_fact (request_hyps r :: add_hyp r :: datalog_ctx') (R, ins')).
  Proof.
    intros. split.
    - intros H'. remember (outs' ++ ins') as args' eqn:E. revert outs' ins' H1 E.
      remember (R2, args') as x eqn:Ex. revert args' R2 Ex.
      induction H'. intros. subst. split.
      + invert H1.
        -- econstructor.
           { apply Exists_cons_tl. apply Exists_cons_hd. apply rule_impl_add_hyp; eauto. }
           constructor.
           2: { eapply Forall_impl; [|eassumption]. simpl. intros (a1&a2) Ha.
                specialize (Ha _ _ ltac:(reflexivity)).
           
             cbv [add_hyp].
          2: { apply Exists_cons_
        

End __.
Arguments Build_rule {_ _ _ _}.
Arguments Build_fact {_ _ _}.
Arguments fun_expr {_ _}.
Arguments var_expr {_ _}.
Arguments rule_impl {_ _ _ _ _ _}.
Arguments prog_impl_fact {_ _ _ _ _ _}.
Arguments fact_args {_ _ _}.
Arguments interp_expr {_ _ _ _}.
Arguments interp_fact {_ _ _ _ _}.
Arguments fact_R {_ _ _}.
Arguments rule_concls {_ _ _ _}.
Arguments rule_hyps {_ _ _ _}.
Arguments vars_of_expr {_ _}.
