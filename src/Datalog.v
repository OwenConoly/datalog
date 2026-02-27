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
    (*if x represents a finite set S then get_set x = Some S.
      note: suffices to have this be T -> option nat, for cardinality...
      should i do that? *)
    get_set : T -> option (T -> Prop);
    blank : T;
    interp_agg : aggregator -> list (T * T) -> T; }.
Arguments signature : clear implicits.

Class query_signature {rel : Type} :=
  { outs : rel -> nat }.
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

  (*help this needs better name*)
  Variant rel_type :=
    | normal (* R(x_1, ..., x_n) *)
    | meta   (* R(S, x_2, ..., x_n) means that S is the set of x_1's s.t. R(x_1, ..., x_n) *).

  (* Variant rel_type := *)
  (* | logical (_ : logical_rel_type) *)
  (* | done   (* R(_, x_2, _, _, x_5, ..., x_n) means that we are done deriving all R-facts with all the x_i's in their respsective positions *) *)
  (* . *)

  Record clause :=
    { clause_R : rel * rel_type;
      clause_args : list expr }.

  Record fact :=
    { fact_R : rel * rel_type;
      fact_args : list T }.

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

  (*semantics of clauses*)
  Definition interp_clause (ctx: context) (c : clause) (f : fact) : Prop :=
    c.(clause_R) = f.(fact_R) /\
      Forall2 (interp_expr ctx) c.(clause_args) f.(fact_args).

  Inductive rule :=
  | normal_rule (rule_concls : list clause) (rule_hyps : list clause)
  (* we deduce concl_rel(\sum_{i \in S} x_i, y_1, ..., y_n)
     from agg_rule concl_rel sum hyp_rel
     where S and x are s.t. the target_rel facts are of the form
     { target_rel(i, x_i, y_1, ..., y_n) : i \in S }.
   *)
  | agg_rule (concl_rel : rel) (agg : aggregator) (hyp_rel : rel).

  (*semantics of rules*) Check interp_agg.
  Inductive rule_impl : rule -> fact -> list fact -> Prop :=
  | normal_rule_impl rule_concls rule_hyps ctx f hyps :
    Exists (fun c => interp_clause ctx c f) rule_concls ->
    Forall2 (interp_clause ctx) rule_hyps hyps ->
    rule_impl (normal_rule rule_concls rule_hyps) f hyps
  | agg_rule_impl S S' vals concl_rel agg hyp_rel (args : list T) :
    get_set S = Some S' ->
    is_list_set S' (map fst vals) ->
    rule_impl
      (agg_rule concl_rel agg hyp_rel)
      {| fact_R := (concl_rel, normal);
        fact_args := interp_agg agg vals :: args |}
      ({| fact_R := (hyp_rel, meta); fact_args := S :: blank :: blank :: args |} ::
         map (fun '(i, x_i) => {| fact_R := (hyp_rel, normal); fact_args := i :: x_i :: args |}) vals).
  Hint Constructors rule_impl : core.

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
    pftree (fun f hyps => Exists (fun r => rule_impl r f hyps) p).

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
    partial_pftree (fun f hyps => Exists (fun r => rule_impl r f hyps) p).

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

  Lemma interp_expr_subst_more s s' v e :
    map.extends s' s ->
    interp_expr s e v ->
    interp_expr s' e v.
  Proof.
    intros Hext H. revert s s' Hext v H. induction e; intros s s' Hext v0 Hv0.
    - invert Hv0. constructor. auto. (*idk how it knows to unfold map.extends*)
    - invert Hv0. econstructor; eauto.
      eapply Forall2_impl_strong; [|eassumption]. intros. rewrite Forall_forall in H.
      eauto.
  Qed.

  Lemma interp_clause_subst_more s s' f f' :
    map.extends s' s ->
    interp_clause s f f' ->
    interp_clause s' f f'.
  Proof.
    cbv [interp_clause]. intros. fwd.
    eauto using interp_expr_subst_more.
  Qed.

  Fixpoint vars_of_expr (e : expr) : list var :=
    match e with
    | fun_expr _ args => flat_map vars_of_expr args
    | var_expr v => [v]
    end.

  Definition vars_of_clause (c : clause) : list var :=
    flat_map vars_of_expr c.(clause_args).

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

  Lemma interp_clause_agree_on ctx1 ctx2 c f :
    interp_clause ctx1 c f ->
    Forall (agree_on ctx1 ctx2) (vars_of_clause c) ->
    interp_clause ctx2 c f.
  Proof.
    intros [H1 H3] H2. split; auto. eapply Forall2_impl_strong; [|eassumption].
    intros. cbv [vars_of_clause] in H2. rewrite Forall_flat_map, Forall_forall in H2.
    eauto using interp_expr_agree_on.
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

  Lemma interp_clause_det ctx c f1 f2 :
    interp_clause ctx c f1 ->
    interp_clause ctx c f2 ->
    f1 = f2.
  Proof.
    intros [H1 H2] [H3 H4]. destruct f1, f2. simpl in *.
    f_equal; [congruence|].
    eapply Forall2_unique_r; eauto. apply interp_expr_det.
  Qed.

  Lemma interp_clause_det' c ctx1 ctx2 f1 f2 :
    interp_clause ctx1 c f1 ->
    interp_clause ctx2 c f2 ->
    Forall (agree_on ctx1 ctx2) (vars_of_clause c) ->
    f1 = f2.
  Proof. eauto using interp_clause_det, interp_clause_agree_on. Qed.

  Lemma interp_clause_same_agree ctx1 ctx2 c f v :
    interp_clause ctx1 c f ->
    interp_clause ctx2 c f ->
    In (var_expr v) c.(clause_args) ->
    agree_on ctx1 ctx2 v.
  Proof.
    intros [H1 H2] [H3 H4] Hv.
    eapply Forall2_and in H4; [|exact H2]. apply Forall2_forget_r in H4.
    rewrite Forall_forall in H4. apply H4 in Hv. fwd. invert Hvp1. invert Hvp2.
    cbv [agree_on]. congruence.
  Qed.

  Definition good_rule (r : rule) :=
    match r with
    | normal_rule rule_concls rule_hyps =>
        forall v,
          In v (flat_map vars_of_clause rule_concls) \/
            In v (flat_map vars_of_clause rule_hyps) ->
          In (var_expr v) (flat_map clause_args rule_hyps)
    | agg_rule _ _ _ => True
    end.

  Definition good_prog (p : list rule) := Forall good_rule p.

  Definition clause_outs (c : clause) := firstn (outs (fst c.(clause_R))) c.(clause_args).
  Definition clause_ins (c : clause) := skipn (outs (fst c.(clause_R))) c.(clause_args).

  Definition with_only_ins (c : clause) :=
    {| clause_R := c.(clause_R); clause_args := clause_ins c |}.

  (*2 conditions.
   * hyp_ins only depend on concl_ins, and
   * whole thing only depends on (concl_ins \cup vars_bare_in_hyps)
   (implicit conditions: every concl_in is of the form var_expr blah, where blah was not
   bound to the agg_expr)
   *)
  Definition goodish_rule (r : rule) :=
    match r with
    | normal_rule rule_concls rule_hyps =>
        exists concl,
        rule_concls = [concl] /\
          (forall v,
              In v (flat_map vars_of_clause rule_concls) \/
                In v (flat_map vars_of_clause rule_hyps) ->
              In (var_expr v) (flat_map clause_args rule_hyps) \/
                In (var_expr v) (clause_ins concl)) /\
          (forall v, In v (flat_map vars_of_expr (flat_map clause_ins rule_hyps)) ->
                In (var_expr v) (clause_ins concl)) /\
          (forall v, In v (flat_map vars_of_expr (clause_ins concl)) ->
                In (var_expr v) (clause_ins concl))
    | agg_rule _ _ _ => True
    end.

  Lemma rule_impl_concl_relname_in rule_concls rule_hyps f hyps :
    rule_impl (normal_rule rule_concls rule_hyps) f hyps ->
    In f.(fact_R) (map clause_R rule_concls).
  Proof.
    invert 1. apply Exists_exists in H2.
    cbv [interp_clause] in H2. fwd.
    apply in_map_iff. eauto.
  Qed.

  Lemma rule_impl_hyp_relname_in rule_concls rule_hyps f hyps :
    rule_impl (normal_rule rule_concls rule_hyps) f hyps ->
    Forall (fun hyp => In hyp.(fact_R) (map clause_R rule_hyps)) hyps.
  Proof.
    invert 1. eapply Forall_impl; [|eapply Forall2_forget_l; eassumption].
    simpl. cbv [interp_clause]. intros. fwd. apply in_map_iff. eauto.
  Qed.
End __.
Arguments clause : clear implicits.
Arguments fact : clear implicits.
Arguments rule : clear implicits.
Arguments expr : clear implicits.
