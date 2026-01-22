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

From Datalog Require Import Map Tactics Fp List Dag.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List.

Import ListNotations.

(*relations, variables, functions, and "aggregator functions" (e.g. min, max, sum, prod)*)
(* A datalog program talks about facts R(x1, ..., xn), where (R : rel) and (x1 : T), (x2 : T), etc. *)
Class signature {fn aggregator T : Type} : Type :=
  {
    (*returning None means inputs not in domain (e.g., number of args was wrong)*)
    interp_fun : fn -> list T -> option T;
    (*agg_id sum = O, agg_id prod = 1, agg_id min = inf, etc*)
    agg_id : aggregator -> T;
    (*interp_agg takes an aggregator and returns the corresponding binop...
    arguably type should be aggregator -> T -> T -> option T,
    but i dont want to bother with that*)
    interp_agg : aggregator -> T -> T -> T; }.
Arguments signature : clear implicits.

Section __.
  Context {rel var fn aggregator T : Type}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map var T} {context_ok : map.ok context}.
  Context {var_eqb : var -> var -> bool} {var_eqb_spec :  forall x0 y0 : var, BoolSpec (x0 = y0) (x0 <> y0) (var_eqb x0 y0)}.

  (*avoid generating useless induction principle*)
  Unset Elimination Schemes.
  Inductive expr :=
  | var_expr (v : var)
  | fun_expr (f : fn) (args : list expr).
  Set Elimination Schemes.

  Record clause :=
    { fact_R : rel;
      fact_args : list expr }.

  Record meta_clause :=
    { mc_rel : rel;
      mc_set : var }.

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

  Inductive fact :=
  | normal_fact (nf_rel : rel) (nf_args : list T)
  | meta_fact (mf_rel : rel) (mf_set : list T -> Prop).
  
  (*semantics of clauses*)
  Inductive interp_clause (ctx: context) : clause -> rel * list T  -> Prop :=
  | mk_interp_clause f args' :
    Forall2 (interp_expr ctx) f.(fact_args) args' ->
    interp_clause ctx f (f.(fact_R), args').

  (* target_rel, source_rel should both be unary, rule says that target_rule(x)
     holds if x = agg source_rel
   *)
  Inductive rule :=
  | normal_rule (rule_concls : list clause) (rule_hyps : list clause)
  | agg_rule (rule_agg : aggregator) (target_rel : rel) (source_rel : rel)
  | meta_rule (target_rel: rel) (target_set : list (list T -> Prop) -> (list T -> Prop))
      (source_rels : list rel).

  Definition is_list_set {X : Type} (S : X -> Prop) (l : list X) :=
    (forall x, S x <-> In x l) /\ NoDup l.

  Inductive rule_impl : rule -> fact -> list fact -> Prop :=
  | normal_rule_impl rule_concls rule_hyps ctx R args hyps' :
    Exists (fun c => interp_clause ctx c (R, args)) rule_concls ->
    Forall2 (interp_clause ctx) rule_hyps hyps' ->
    rule_impl (normal_rule rule_concls rule_hyps) (normal_fact R args)
      (map (fun '(R, args) => normal_fact R args) hyps')
  | agg_rule_impl rule_agg target_rel source_rel S vals :
    is_list_set (fun x => S [x]) vals ->
    rule_impl
      (agg_rule rule_agg target_rel source_rel)
      (normal_fact target_rel [fold_right (interp_agg rule_agg) (agg_id rule_agg) vals])
      (meta_fact source_rel S :: map (fun val => normal_fact source_rel [val]) vals)
  | meta_rule_impl target_rel target_set target_set' source_rels source_sets :
    length source_rels = length source_sets ->
    (forall x, target_set' x <-> target_set source_sets x) ->
    rule_impl
      (meta_rule target_rel target_set source_rels) 
      (meta_fact target_rel target_set')
      (zip meta_fact source_rels source_sets).

  Unset Elimination Schemes.
  Inductive pftree {T : Type} (P : T -> list T -> Prop) : T -> Prop :=
  | mkpftree x l :
    P x l ->
    Forall (pftree P) l ->
    pftree P x.
  Set Elimination Schemes.
  Hint Constructors pftree : core.
  
  (*semantics of programs*)
  Definition prog_impl_fact (p : list rule) : fact -> Prop :=
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

  Lemma pftree_weaken_strong {T1 T2 : Type}
    (P1 : T1 -> list T1 -> Prop) (P2 : T2 -> list T2 -> Prop) x f :
    pftree P1 x ->
    (forall x l, P1 x l -> P2 (f x) (map f l)) ->
    pftree P2 (f x).
  Proof.
    intros H1 H. induction H1. econstructor.
    2: { eapply Forall_map. eassumption. }
    apply H. assumption.
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

  Lemma pftree_partial_pftree {U : Type} P1 P2 Q (x : U) :
    pftree P1 x ->
    (forall y l, P1 y l -> P2 y l \/ Q y) ->
    partial_pftree P2 Q x.
  Proof.
    intros H1 H2. induction H1; eauto. apply H2 in H. destruct H; eauto.
  Qed.

  Lemma partial_pftree_pftree {U : Type} P (x : U) :
    partial_pftree P (fun y => False) x ->
    pftree P x.
  Proof. induction 1; eauto. contradiction. Qed.

  Lemma partial_pftree_trans {U : Type} P (x : U) Q :
    partial_pftree P (partial_pftree P Q) x ->
    partial_pftree P Q x.
  Proof. induction 1; eauto. Qed.
    
  Definition prog_impl_implication (p : list rule) : (fact -> Prop) -> fact -> Prop :=
    partial_pftree (fun f' hyps' => Exists (fun r => rule_impl r f' hyps') p).

  Lemma prog_impl_step p Q f hyps' :
    Exists (fun r : rule => rule_impl r f hyps') p ->
    Forall (prog_impl_implication p Q) hyps' ->
    prog_impl_implication p Q f.
  Proof. intros. eapply partial_step; eauto. Qed.

  Lemma prog_impl_fact_prog_impl_implication p1 p2 Q f :
    prog_impl_fact p1 f ->
    (forall r f hyps, In r p1 ->
                 rule_impl r f hyps ->
                 In r p2 \/ Q f) ->
    prog_impl_implication p2 Q f.
  Proof.
    intros. eapply pftree_partial_pftree; [eassumption|]. simpl.
    intros y l Hy. apply Exists_exists in Hy. fwd.
    eapply H0 in Hyp0; eauto. rewrite Exists_exists. destruct Hyp0 as [H'|H']; eauto.
  Qed.

  Lemma prog_impl_implication_prog_impl_fact p f :
    prog_impl_implication p (fun _ => False) f ->
    prog_impl_fact p f.
  Proof.
    cbv [prog_impl_implication prog_impl_fact].
    eauto using partial_pftree_pftree.
  Qed.
  
  Lemma partial_pftree_weaken_hyp {U : Type} P (x : U) Q1 Q2 :
    partial_pftree P Q1 x ->
    (forall y, Q1 y -> Q2 y) ->
    partial_pftree P Q2 x.
  Proof. intros H1 H2. induction H1; eauto. Qed.
  
  Lemma prog_impl_implication_weaken_hyp p x Q1 Q2 :
    prog_impl_implication p Q1 x ->
    (forall y, Q1 y -> Q2 y) ->
    prog_impl_implication p Q2 x.
  Proof. cbv [prog_impl_implication]. eauto using partial_pftree_weaken_hyp. Qed.    
  
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
    intros. apply Exists_exists in H1. apply Exists_exists. fwd. eauto.
  Qed.

  Fixpoint vars_of_expr (e : expr) : list var :=
    match e with
    | fun_expr _ args => flat_map vars_of_expr args
    | var_expr v => [v]
    end.
End __.
Arguments clause : clear implicits.
Arguments fact : clear implicits.
Arguments rule : clear implicits.
Arguments expr : clear implicits.
