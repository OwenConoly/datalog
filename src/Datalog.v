From Stdlib Require Import Arith.Arith.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
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
    (*if x represents a finite set, then get_set x = Some ([x1; ...; xn]), where x1, ..., xn are the elements of the set*)
    agg_id : aggregator -> T;
    (*interp_agg takes an aggregator and returns the corresponding binop...
    arguably type should be aggregator -> T -> T -> option T,
    but i dont want to bother with that*)
    interp_agg : aggregator -> T -> T -> T; }.
Arguments signature : clear implicits.

Class query_signature {rel : Type} :=
  { outs : rel -> nat }.
Arguments query_signature : clear implicits.

Section __.
  Context {rel fn aggregator T : Type}.
  Context `{sig : signature fn aggregator T} `{query_sig : query_signature rel}.
  Definition var := tt.

  (*avoid generating useless induction principle*)
  Unset Elimination Schemes.
  Inductive expr {var} :=
  | Var (v : var)
  | FunExpr (f : fn) (args : list expr).
  Arguments expr : clear implicits.
  Set Elimination Schemes.

  Variant arg {var} := expr_arg (_ : expr var) | set_arg (_ : T -> Prop).
  Arguments arg : clear implicits.

  Record clause {var} := { clause_R : rel; clause_args : list (arg var) }.
  Arguments clause : clear implicits.

  Variant val := T_val (_ : T) | set_val (_ : T -> Prop).

  Record fact := { fact_R : rel; fact_args : list val }.

  Unset Elimination Schemes.
  (*semantics of expressions*)
  Inductive interp_expr : expr T -> T -> Prop :=
  | interp_var_expr v :
    interp_expr (Var v) v
  | interp_fun_expr f args args' x :
    Forall2 interp_expr args args' ->
    interp_fun f args' = Some x ->
    interp_expr (FunExpr f args) x.
  Set Elimination Schemes.

  Inductive interp_arg : arg T -> val -> Prop :=
  | interp_expr_arg e e' :
    interp_expr e e' ->
    interp_arg (expr_arg e) (T_val e')
  | interp_set_arg P Q :
    (forall x, P x <-> Q x) ->
    interp_arg (set_arg P) (set_val Q).

  Definition interp_clause (c : clause T) (f : fact) : Prop :=
    c.(clause_R) = f.(fact_R) /\
      Forall2 interp_arg c.(clause_args) f.(fact_args).

  Inductive normal_rule {var} :=
  | nr_nil (rule_concls : list (clause var)) (rule_hyps : list (clause var))
  | nr_cons_set (r : (T -> Prop) -> normal_rule)
  | nr_cons_var (r : var -> normal_rule).
  Arguments normal_rule : clear implicits.

  Inductive rule {var} :=
  | normal_rule_rule (r : normal_rule var)
  | agg_rule (target_rel : rel) (rule_agg : aggregator) (source_rel : rel).
  Arguments rule : clear implicits.

  Inductive normal_rule_impl : normal_rule T -> fact -> list fact -> Prop :=
  | nr_impl_nil rule_concls rule_hyps f hyps :
    Exists (fun c => interp_clause c f) rule_concls ->
    Forall2 interp_clause rule_hyps hyps ->
    normal_rule_impl (nr_nil rule_concls rule_hyps) f hyps
  | nr_impl_cons_set r P f hyps :
    normal_rule_impl (r P) f hyps ->
    normal_rule_impl (nr_cons_set r) f hyps
  | nr_impl_cons_var r x f hyps :
    normal_rule_impl (r x) f hyps ->
    normal_rule_impl (nr_cons_var r) f hyps.

  Inductive rule_impl : rule T -> fact -> list fact -> Prop :=
  | nr_rule_impl r f hyps :
    normal_rule_impl r f hyps ->
    rule_impl (normal_rule_rule r) f hyps
  | agg_rule_impl rule_agg target_rel source_rel S vals args :
    is_list_set (fun x => S x) vals ->
    rule_impl
      (agg_rule target_rel rule_agg source_rel)
      ({| fact_R := target_rel; fact_args := (fold_right (interp_agg rule_agg) (agg_id rule_agg) vals) :: args |})
      ({| fact_R := source_rel; fact_args := S args |} :: map (fun val => {| fact_R := source_rel; fact_args := (val :: args) |}) vals).

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
    - invert Hv0. constructor. auto.
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

  Lemma interp_clause_agree_on ctx1 ctx2 f f' :
    interp_clause ctx1 f f' ->
    Forall (agree_on ctx1 ctx2) (vars_of_clause f) ->
    interp_clause ctx2 f f'.
  Proof.
    cbv [interp_clause].
    intros H1 H2. fwd. split; auto. eapply Forall2_impl_strong; [|eassumption].
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

  Lemma interp_clause_det ctx f f1 f2 :
    interp_clause ctx f f1 ->
    interp_clause ctx f f2 ->
    f1 = f2.
  Proof.
    cbv [interp_clause]. intros. fwd. destruct f1, f2. simpl in *. subst.
    f_equal. eapply Forall2_unique_r; eauto. apply interp_expr_det.
  Qed.

  Lemma interp_clause_det' f ctx1 ctx2 f1 f2 :
    interp_clause ctx1 f f1 ->
    interp_clause ctx2 f f2 ->
    Forall (agree_on ctx1 ctx2) (vars_of_clause f) ->
    f1 = f2.
  Proof. eauto using interp_clause_det, interp_clause_agree_on. Qed.

  Lemma interp_clause_same_agree ctx1 ctx2 f f' v :
    interp_clause ctx1 f f' ->
    interp_clause ctx2 f f' ->
    In (var_expr v) f.(clause_args) ->
    agree_on ctx1 ctx2 v.
  Proof.
    cbv [interp_clause]. destruct f, f'. simpl.
    intros H1 H2 Hv. fwd.
    eapply Forall2_and in H1p1; eauto. apply Forall2_forget_r in H1p1.
    rewrite Forall_forall in H1p1. apply H1p1 in Hv. fwd. invert Hvp1. invert Hvp2.
    cbv [agree_on]. eauto using eq_trans.
  Qed.

  Definition in_set_hyps v set_hyps :=
    In v (flat_map vars_of_expr (map fst set_hyps)) \/
      In v (flat_map vars_of_expr (map snd set_hyps)).

  Lemma not_in_set_hyps_nil v :
    in_set_hyps v [] -> False.
  Proof.
    cbv [in_set_hyps]. simpl. destruct 1; assumption.
  Qed.

  Definition good_rule' concls hyps :=
    forall v,
      In v (flat_map vars_of_clause concls) \/ In v (flat_map vars_of_clause hyps) ->
      In (var_expr v) (flat_map clause_args hyps).

  Definition good_rule r :=
    match r with
    | normal_rule concls hyps => good_rule' concls hyps
    | agg_rule _ _ _ => True
    | meta_rule concl _ hyps => good_rule' [concl] hyps
    end.

  Definition good_prog (p : list rule) := Forall good_rule p.

  (* Definition fact_outs (f : fact) := firstn (outs f.(fact_R)) f.(fact_args). *)
  (* Definition fact_ins (f : fact) := skipn (outs f.(fact_R)) f.(fact_args). *)

  (* Definition with_only_ins (f : fact) := *)
  (*   {| fact_R := f.(fact_R); fact_args := fact_ins f |}. *)

  (*2 conditions.
   * hyp_ins only depend on concl_ins, and
   * whole thing only depends on (concl_ins \cup vars_bare_in_hyps)
   (implicit conditions: every concl_in is of the form var_expr blah, where blah was not
   bound to the agg_expr)
   *)
  Definition goodish_rule' concl hyps :=
    (forall v, (*alternatively, could write appears_in_outs here*)appears_in_rule v r ->
          In (var_expr v) (flat_map fact_args r.(rule_hyps)) \/
            In (var_expr v) (fact_ins concl)) /\
      (forall v, In v (flat_map vars_of_expr (flat_map fact_ins (rule_hyps r))) ->
            In (var_expr v) (fact_ins concl)) /\
      (forall v, In v (flat_map vars_of_expr (fact_ins concl)) ->
            In (var_expr v) (fact_ins concl)).
  Definition goodish_rule (r : rule) :=
    exists concl,
      r.(rule_concls) = [concl] /\
        .

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

  Lemma rule_impl'_hyp_relname_in ctx r x hyps agg_hyps' :
    rule_impl' ctx r x hyps agg_hyps' ->
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
