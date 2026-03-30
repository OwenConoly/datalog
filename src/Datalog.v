From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.

From Datalog Require Import Map Tactics Fp List Dag.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List Datatypes.Option.

Import ListNotations.

(*relations, variables, functions, and "aggregator functions" (e.g. min, max, sum, prod)*)
(* A datalog program talks about facts R(x1, ..., xn), where (R : rel) and (x1 : T), (x2 : T), etc. *)
Class signature {fn aggregator T : Type} : Type :=
  {
    (*returning None means inputs not in domain (e.g., number of args was wrong)*)
    interp_fun : fn -> list T -> option T;
    (* (*if x represents a finite set S then get_set x = Some S. *)
    (*   note: suffices to have this be T -> option nat, for cardinality... *)
    (*   should i do that? *) *)
    (* get_set : T -> option (T -> Prop); *)
    (* iter : T; *)
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

  Record clause :=
    { clause_rel : rel;
      clause_args : list expr }.

  Record meta_clause :=
    { meta_clause_rel : rel;
      meta_clause_args : list (option expr) }.

  Variant fact :=
    | normal_fact (nf_rel : rel) (nf_args : list T)
    | meta_fact (mf_rel : rel) (mf_args : list (option T)) (mf_set : list T -> Prop).

  Unset Elimination Schemes.
  Inductive interp_expr (ctx : context) : expr -> T -> Prop :=
  | interp_var_expr x v :
    map.get ctx x = Some v ->
    interp_expr ctx (var_expr x) v
  | interp_fun_expr f args args' x :
    Forall2 (interp_expr ctx) args args' ->
    interp_fun f args' = Some x ->
    interp_expr ctx (fun_expr f args) x.
  Set Elimination Schemes.

  Definition interp_clause (ctx: context) (c : clause) (f : fact) : Prop :=
    exists nf_args,
      Forall2 (interp_expr ctx) c.(clause_args) nf_args /\
        f = normal_fact c.(clause_rel) nf_args.

  Definition interp_meta_clause (ctx: context) (c : meta_clause) (f : fact) : Prop :=
    exists mf_args mf_set,
      Forall2 (option_relation (interp_expr ctx)) c.(meta_clause_args) mf_args /\
        f = meta_fact c.(meta_clause_rel) mf_args mf_set.

  Inductive rule :=
  | normal_rule (rule_concls : list clause) (rule_hyps : list clause)
  | meta_rule (rule_concls : list meta_clause) (rule_hyps : list meta_clause)
  (* we deduce concl_rel(\sum_{i \in S} x_i, y_1, ..., y_n)
     from agg_rule concl_rel sum hyp_rel
     where S and x are s.t. the target_rel facts are of the form
     { target_rel(i, x_i, y_1, ..., y_n) : i \in S }.
   *)
  | agg_rule (concl_rel : rel) (agg : aggregator) (hyp_rel : rel)
  (*TODO uncomment following*)
  (*hmm maybe this shoudl actually be some construct for injection of normlal facts into fmeta facsts, then could just do agg_over_rel?*)
  (*| agg_over_set (concl_rel : rel) (agg : aggregator) (cardinality : expr) (hyp_rel : rel) (hyp_args : list var)*).

  (*None is a wildcard*)
  Definition matches (x : option T) y :=
    match x with
    | None => True
    | Some x0 => x0 = y
    end.

  Definition fact_matches nf mf :=
    exists R nf_args mf_args mf_set,
      Forall2 matches mf_args nf_args /\
        mf_set nf_args /\
        nf = normal_fact R nf_args /\
        mf = meta_fact R mf_args mf_set.

  Inductive non_meta_rule_impl : rule -> rel -> list T -> list fact -> Prop :=
  | normal_rule_impl rule_concls rule_hyps ctx R args hyps :
    Exists (fun c => interp_clause ctx c (normal_fact R args)) rule_concls ->
    Forall2 (interp_clause ctx) rule_hyps hyps ->
    non_meta_rule_impl (normal_rule rule_concls rule_hyps) R args hyps
  | agg_rule_impl S vals concl_rel agg hyp_rel (args : list T) :
    is_list_set (fun '(i, x) => S (i :: x :: args)) vals ->
    non_meta_rule_impl
      (agg_rule concl_rel agg hyp_rel)
      concl_rel
      (interp_agg agg vals :: args)
      (meta_fact hyp_rel (None :: None :: map Some args) S ::
         map (fun '(i, x_i) => normal_fact hyp_rel (i :: x_i :: args)) vals).

  Unset Elimination Schemes.
  Inductive pftree {T : Type} (P : T -> list T -> Prop) (Q : T -> Prop) : T -> Prop :=
  | pftree_leaf x :
    Q x ->
    pftree _ _ x
  | pftree_step x l :
    P x l ->
    Forall (pftree _ _) l ->
    pftree _ _ x.
  Set Elimination Schemes.
  Hint Constructors pftree : core.

  Definition prog_impl_with_no_meta_rules (p : list rule) : (fact -> Prop) -> fact -> Prop :=
    pftree (fun f hyps => exists R args,
                f = normal_fact R args /\
                  Exists (fun r => non_meta_rule_impl r R args hyps) p).

  Inductive rule_impl p : rule -> fact -> list fact -> Prop :=
  | simple_rule_impl r R args hyps :
    non_meta_rule_impl r R args hyps ->
    rule_impl _ r (normal_fact R args) hyps
  | meta_rule_impl rule_concls rule_hyps ctx R args hyps S :
    Exists (fun c => interp_meta_clause ctx c (meta_fact R args (fun args' => S args'))) rule_concls ->
    Forall2 (interp_meta_clause ctx) rule_hyps hyps ->
    (forall args'',
        Forall2 matches args args'' ->
        S args'' <->
          prog_impl_with_no_meta_rules p (fun f' => Exists (fun hyp => f' = hyp \/ fact_matches f' hyp) hyps) (normal_fact R args'')) ->
    rule_impl _ (meta_rule rule_concls rule_hyps) (meta_fact R args S) hyps.
  Hint Constructors rule_impl : core.

  Lemma pftree_ind {U : Type} (P : U -> list U -> Prop) Q R :
    (forall x, Q x -> R x) ->
    (forall x l,
        P x l ->
        Forall (pftree P Q) l ->
        Forall R l ->
        R x) ->
    forall x, pftree P Q x -> R x.
  Proof.
    intros H1 H2. fix self 2.
    intros x Hx. invert Hx. 1: auto. eapply H2. 1,2: eassumption.
    clear -H0 self. induction H0; eauto.
  Qed.

  Lemma pftree_trans {U : Type} P (x : U) Q :
    pftree P (pftree P Q) x ->
    pftree P Q x.
  Proof. induction 1; eauto. Qed.

  Definition prog_impl (p : list rule) : (fact -> Prop) -> fact -> Prop :=
    pftree (fun f hyps => Exists (fun r => rule_impl p r f hyps) p).

  Lemma prog_impl_ind p Q R :
    (forall f, Q f -> R f) ->
    (forall f hyps,
        Exists (fun r => rule_impl p r f hyps) p ->
        Forall (prog_impl p Q) hyps ->
        Forall R hyps ->
        R f) ->
    forall f, prog_impl p Q f -> R f.
  Proof. apply pftree_ind. Qed.

  Lemma prog_impl_step p Q f hyps' :
    Exists (fun r : rule => rule_impl p r f hyps') p ->
    Forall (prog_impl p Q) hyps' ->
    prog_impl p Q f.
  Proof. intros. eapply pftree_step; eauto. Qed.

  Lemma prog_impl_leaf p Q f :
    Q f ->
    prog_impl p Q f.
  Proof. cbv [prog_impl]. eauto. Qed.
  Hint Resolve prog_impl_leaf : core.

  Lemma invert_prog_impl p Q f :
    prog_impl p Q f ->
    Q f \/
      exists hyps',
        Exists (fun r : rule => rule_impl p r f hyps') p /\
          Forall (prog_impl p Q) hyps'.
  Proof. invert 1; eauto. Qed.

  Lemma pftree_weaken_hyp {U : Type} P (x : U) Q1 Q2 :
    pftree P Q1 x ->
    (forall y, Q1 y -> Q2 y) ->
    pftree P Q2 x.
  Proof. intros H1 H2. induction H1; eauto. Qed.

  Lemma prog_impl_weaken_hyp p x Q1 Q2 :
    prog_impl p Q1 x ->
    (forall y, Q1 y -> Q2 y) ->
    prog_impl p Q2 x.
  Proof. cbv [prog_impl]. eauto using pftree_weaken_hyp. Qed.

  Lemma rule_impl_mf_ext p Q mf_rel mf_args hyps mf_set mf_set' :
    rule_impl p Q (meta_fact mf_rel mf_args mf_set) hyps ->
    (forall nf_args,
        Forall2 matches mf_args nf_args ->
        mf_set nf_args <-> mf_set' nf_args) ->
    rule_impl p Q (meta_fact mf_rel mf_args mf_set') hyps.
  Proof.
    invert 1. intros Heq.
    econstructor; [|eassumption|].
    { eapply Exists_impl; [|eassumption].
      simpl. cbv [interp_meta_clause]. intros. fwd. eauto. }
    intros. rewrite <- Heq by eassumption. auto.
  Qed.

  Lemma prog_impl_mf_ext p Q mf_rel mf_args mf_set mf_set' :
    prog_impl p Q (meta_fact mf_rel mf_args mf_set) ->
    (forall nf_args,
        Forall2 matches mf_args nf_args ->
        mf_set nf_args <-> mf_set' nf_args) ->
    Q (meta_fact mf_rel mf_args mf_set) \/
      prog_impl p Q (meta_fact mf_rel mf_args mf_set').
  Proof.
    intros H1 H2. apply invert_prog_impl in H1. destruct H1 as [H1|H1]; auto.
    fwd. right. eapply prog_impl_step; [|eassumption].
    eapply Exists_impl; [|eassumption]. simpl.
    eauto using rule_impl_mf_ext.
  Qed.

  Definition F p Q Px :=
    let '(P, x) := Px in
    P x \/ Q (P, x) \/ exists hyps', Exists (fun r => rule_impl p r x hyps') p /\ Forall (fun x => Q (P, x)) hyps'.

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

  Lemma pftree_lfp {U : Type} (P : U -> list U -> Prop) :
    equiv (fun '(Q0, x) => pftree P Q0 x)
      (lfp (fun Q '(Q0, x) => Q0 x \/ Q (Q0, x) \/ exists l, P x l /\ Forall (fun y => Q (Q0, y)) l)).
  Proof.
    cbv [equiv lfp fp]. intros [Q0 x]. split; intros; fwd.
    - apply H0. induction H; eauto.
      right. right. exists l. split; [assumption|]. eapply Forall_impl; [|eassumption].
      simpl. intros y. apply (H0 (_, _)).
    - apply (H (fun '(Q, x) => _)). clear. intros [Q x]. intros [Hx| [Hx |Hx] ]; eauto.
      fwd. eapply pftree_step; eassumption.
  Qed.

  Lemma prog_impl_lfp p :
    equiv (fun '(P, f) => prog_impl p P f) (lfp (F p)).
  Proof.
    cbv [equiv]. intros. cbv [prog_impl].
    epose proof pftree_lfp as H. cbv [equiv] in H. rewrite H.
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

  Hint Unfold prog_impl : core.

  Hint Extern 2 => eapply Forall_impl; [|eassumption]; cbv beta : core.
  Hint Extern 2 => eapply Forall2_impl; [|eassumption]; cbv beta : core.

  Lemma pftree_weaken {U : Type} P1 P2 Q (x : U) :
    pftree P1 Q x ->
    (forall y l, P1 y l -> P2 y l) ->
    pftree P2 Q x.
  Proof. induction 1; eauto. Qed.

  Lemma S_sane_lfp p : S_sane (lfp (F p)).
  Proof.
    eapply S_sane_ext; [apply prog_impl_lfp|]. cbv [S_sane]. split; intros; eauto.
    Fail Fail solve [induction H; eauto].
    eapply pftree_trans. eapply pftree_weaken_hyp; eauto.
  Qed.

  (*this gets more complicated due to meta rules :((( *)
  Lemma split_fixpoint (p : list rule) S :
    (forall P x, P x -> S (P, x)) ->
    (forall r, In r p -> fp (F [r]) S) <->
      fp (F p) S.
  Proof.
    intros Sgood1. cbv [fp F]. split.
    - intros H [P x] Hx. destruct Hx as [Hx| [Hx|Hx]]; eauto.
      fwd. apply Exists_exists in Hxp0. fwd. eapply H; eauto 6. admit.
    - intros H r Hr [P x] Hx. destruct Hx as [Hx| [Hx|Hx]]; eauto. fwd.
      invert_list_stuff.
      apply H. right. right. eexists. split; [|eassumption]. apply Exists_exists. eauto.
      admit.
  Abort.

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

  Definition consistent mf_rel mf_args mf_set S :=
    forall nf_args,
      Forall2 matches mf_args nf_args ->
      mf_set nf_args <-> S (normal_fact mf_rel nf_args).

  Definition doesnt_lie p Q :=
    forall mf_rel mf_args mf_set,
      prog_impl p Q (meta_fact mf_rel mf_args mf_set) ->
      consistent mf_rel mf_args mf_set (prog_impl p Q).

  (*ugh idk what to say here*)
  Lemma prog_impl_subset (p1 p2 : list rule) Q f :
    doesnt_lie p1 Q ->
    doesnt_lie p2 Q ->
    (forall x, In x p1 -> In x p2) ->
    prog_impl p1 Q f ->
    prog_impl p2 Q f.
  Proof.
    intros H1 H2 Hsub H. eapply pftree_weaken; simpl; eauto. simpl.
    intros ? ? Hr. apply Exists_exists in Hr. apply Exists_exists. fwd.
    eexists. split; [eauto|].
  Abort.

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

  Definition rel_of (f : fact) :=
    match f with
    | normal_fact R _ => R
    | meta_fact R _ _ => R
    end.

  Variant fact_args :=
    | normal_fact_args (nf_args : list T)
    | meta_fact_args (mf_args : list (option T)) (mf_set : list T -> Prop).

  Definition args_of f :=
    match f with
    | normal_fact _ nf_args => normal_fact_args nf_args
    | meta_fact _ mf_args mf_set => meta_fact_args mf_args mf_set
    end.

  Definition fact_of R args :=
    match args with
    | normal_fact_args nf_args => normal_fact R nf_args
    | meta_fact_args mf_args mf_set => meta_fact R mf_args mf_set
    end.

  Ltac invert_stuff :=
    match goal with
    | _ => progress cbn [matches rel_of fact_of args_of clause_rel clause_args meta_clause_rel meta_clause_args] in *
    | H : rule_impl _ _ _ _ |- _ => invert1 H || invert0 H
    | H : non_meta_rule_impl _ _ _ _ |- _ => progress (invert1 H) || invert0 H
    | H : interp_clause _ _ _ |- _ => cbv [interp_clause] in H; fwd
    | H : interp_meta_clause _ _ _ |- _ => cbv [interp_meta_clause] in H; fwd
    | H : interp_expr _ _ _ |- _ => invert1 H
    | H : In _ [_] |- _ => destruct H; [|contradiction]
    | H1: ?x = Some ?y, H2: ?x = Some ?z |- _ => first [is_var y | is_var z]; assert (y = z) by congruence; clear H1; subst
    | _ => progress subst
    | _ => progress invert_list_stuff
    | _ => progress fwd
    | _ => congruence
    end.

  Ltac interp_exprs :=
  repeat rewrite map_app; simpl;
  repeat match goal with
    | _ => progress simpl

    | |- Forall2 _ (_ ++ _) _ => apply Forall2_app
    | |- Forall2 _ (_ :: _) _ => constructor
    | |- Forall2 _ nil _ => constructor
    | |- Forall2 _ _ _ =>
        (eapply Forall2_impl; [|eassumption]; simpl; intros) ||
          idtac

    | |- Forall _ (_ :: _) => constructor; [interp_exprs|]
    | |- Forall _ [] => constructor

    | |- interp_expr _ _ _ => econstructor
    (* | |- interp_expr _ _ _ => *)
    (*     eapply interp_expr_subst_more; [|eassumption] *)
    | |- interp_clause _ _ _ =>
        eapply interp_clause_subst_more; [|eassumption]
    | |- interp_clause _ _ _ =>
        cbv [interp_clause]; eexists; split; [|reflexivity]; simpl
    | |- interp_meta_clause _ _ _ =>
        cbv [interp_meta_clause]; do 2 eexists; split; [|reflexivity]; simpl
    | |- _ /\ _ => split; [solve [interp_exprs] |]
    | |- Exists _ [_] => apply Exists_cons_hd

    | |- _ => rewrite map.get_put_diff by congruence
    | |- _ => rewrite map.get_put_same by reflexivity

    | |- _ => reflexivity
    | |- _ => eassumption (*hsould this just be assumption?*)
    end.

  Lemma interp_clause_agree_on ctx1 ctx2 c f :
    interp_clause ctx1 c f ->
    Forall (agree_on ctx1 ctx2) (vars_of_clause c) ->
    interp_clause ctx2 c f.
  Proof.
    cbv [interp_clause]. intros Hinterp Hagree. fwd.
    eexists. split; [|auto].
    eapply Forall2_impl_strong; [|eassumption].
    intros. cbv [vars_of_clause] in Hagree.
    rewrite Forall_flat_map, Forall_forall in Hagree.
    eauto using interp_expr_agree_on.
  Qed.

  Lemma interp_expr_det ctx e v1 v2 :
    interp_expr ctx e v1 ->
    interp_expr ctx e v2 ->
    v1 = v2.
  Proof.
    revert v1 v2. induction e; simpl; intros.
    - repeat invert_stuff.
    - repeat invert_stuff. enough (args' = args'0).
      { repeat invert_stuff. }
      clear -H3 H4 H. revert args'0 H3. induction H4; intros; invert_stuff.
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
    intros. repeat invert_stuff. f_equal.
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
    cbv [interp_clause]. intros H1 H2 Hv. fwd.
    eapply Forall2_and in H2p0; [|exact H1p0].
    apply Forall2_forget_r in H2p0.
    rewrite Forall_forall in H2p0. apply H2p0 in Hv.
    fwd. invert Hvp1. invert Hvp2.
    cbv [agree_on]. congruence.
  Qed.

  (* Definition good_rule (r : rule) := *)
  (*   match r with *)
  (*   | normal_rule rule_concls rule_hyps => *)
  (*       forall v, *)
  (*         In v (flat_map vars_of_clause rule_concls) \/ *)
  (*           In v (flat_map vars_of_clause rule_hyps) -> *)
  (*         In (var_expr v) (flat_map clause_args rule_hyps) *)
  (*   | agg_rule _ _ _ => True *)
  (*   end. *)

  (* Definition good_prog (p : list rule) := Forall good_rule p. *)

  (* Definition clause_outs (c : clause) := firstn (outs (fst c.(clause_R))) c.(clause_args). *)
  (* Definition clause_ins (c : clause) := skipn (outs (fst c.(clause_R))) c.(clause_args). *)

  (* Definition with_only_ins (c : clause) := *)
  (*   {| clause_R := c.(clause_R); clause_args := clause_ins c |}. *)

  (* (*2 conditions. *)
  (*  * hyp_ins only depend on concl_ins, and *)
  (*  * whole thing only depends on (concl_ins \cup vars_bare_in_hyps) *)
  (*  (implicit conditions: every concl_in is of the form var_expr blah, where blah was not *)
  (*  bound to the agg_expr) *)
  (*  *) *)
  (* Definition goodish_rule (r : rule) := *)
  (*   match r with *)
  (*   | normal_rule rule_concls rule_hyps => *)
  (*       exists concl, *)
  (*       rule_concls = [concl] /\ *)
  (*         (forall v, *)
  (*             In v (flat_map vars_of_clause rule_concls) \/ *)
  (*               In v (flat_map vars_of_clause rule_hyps) -> *)
  (*             In (var_expr v) (flat_map clause_args rule_hyps) \/ *)
  (*               In (var_expr v) (clause_ins concl)) /\ *)
  (*         (forall v, In v (flat_map vars_of_expr (flat_map clause_ins rule_hyps)) -> *)
  (*               In (var_expr v) (clause_ins concl)) /\ *)
  (*         (forall v, In v (flat_map vars_of_expr (clause_ins concl)) -> *)
  (*               In (var_expr v) (clause_ins concl)) *)
  (*   | agg_rule _ _ _ => True *)
  (*   end. *)

  Definition concl_rels (r : rule) : list rel :=
    match r with
    | normal_rule rule_concls _ => map clause_rel rule_concls
    | meta_rule rule_concls _ => map meta_clause_rel rule_concls
    | agg_rule concl_rel _ _ => [concl_rel]
    end.

  Definition hyp_rels (r : rule) : list rel :=
    match r with
    | normal_rule _ rule_hyps => map clause_rel rule_hyps
    | meta_rule _ rule_hyps => map meta_clause_rel rule_hyps
    | agg_rule _ _ hyp_rel => [hyp_rel]
    end.

  Lemma rule_impl_concl_relname_in p r f hyps :
    rule_impl p r f hyps ->
    In (rel_of f) (concl_rels r).
  Proof.
    invert 1.
    - match goal with
      | H: non_meta_rule_impl _ _ _ _ |- _ => invert H
      end.
      + rewrite Exists_exists in *. repeat invert_stuff.
        apply in_map_iff. eauto.
      + left. reflexivity.
    - rewrite Exists_exists in *. fwd. apply in_map_iff.
      repeat invert_stuff. eauto.
  Qed.

  Lemma rule_impl_hyp_relname_in p r f hyps :
    rule_impl p r f hyps ->
    Forall (fun hyp => In (rel_of hyp) (hyp_rels r)) hyps.
  Proof.
    invert 1.
    - match goal with
      | H: non_meta_rule_impl _ _ _ _ |- _ => invert H
      end.
      + simpl.
        eapply Forall_impl; [|eapply Forall2_forget_l; eassumption].
        intros. repeat invert_stuff.
        eauto using in_map.
      + simpl. constructor; eauto.
        apply Forall_map. apply Forall_forall.
        intros [? ?]. simpl. auto.
    - simpl.
      eapply Forall_impl; [|eapply Forall2_forget_l; eassumption].
      intros. repeat invert_stuff.
      eauto using in_map.
  Qed.

  Definition disjoint_lists {T} (l1 l2 : list T) :=
    forall x, In x l1 -> In x l2 -> False.

  Check rule_impl.
  Lemma staged_program_rule_impl p1 p2 r f hyps :
    disjoint_lists (flat_map concl_rels p1) (flat_map hyp_rels p2) ->
    rule_impl (p1 ++ p2) r f hyps ->
    rule_impl p2 r f hyps.
  Proof.
    Abort.


  Lemma staged_program p1 p2 Q f :
    disjoint_lists (flat_map concl_rels p1) (flat_map hyp_rels p2) ->
    prog_impl (p1 ++ p2) Q f ->
    prog_impl p1 (prog_impl p2 Q) f.
  Proof.
    intros Hdisj. induction 1 using prog_impl_ind.
    - apply pftree_leaf. apply pftree_leaf. assumption.
    - apply Exists_app in H. destruct H as [H|H].
      + eapply prog_impl_step. 2: eassumption. eapply Exists_impl; [|eassumption].
        simpl.
        ~In R (flat_map concl_rels p1) ->
        prog_impl (p1 ++ p2) hyps ->
        eapply prog_impl_step; [eassumption|]. assumption.
      + apply partial_in. eapply prog_impl_step; [eassumption|].
        rewrite Forall_forall in *. intros f Hf. specialize (H1 _ Hf).
        invert H1; auto. fold (prog_impl_implication p1) in *.
        apply Exists_exists in H, H2. fwd. apply rule_impl_hyp_relname_in in Hp1.
        apply rule_impl_concl_relname_in in H2p1. rewrite Forall_forall in Hp1.
        specialize (Hp1 _ Hf). exfalso. eapply Hdisj.
        -- apply in_flat_map. eauto.
        -- apply in_flat_map. eauto.
  Qed.

  Lemma prog_impl_trans p Q f :
    prog_impl p (prog_impl p Q) f ->
    prog_impl p Q f.
  Proof. apply pftree_trans. Qed.

  (* Lemma staged_program_iff p1 p2 Q f : *)
  (*   disjoint_lists (flat_map concl_rels p1) (flat_map hyp_rels p2) -> *)
  (*   prog_impl_implication (p1 ++ p2) Q f <-> *)
  (*   prog_impl_implication p1 (prog_impl_implication p2 Q) f. *)
  (* Proof. *)
  (*   split; auto using staged_program. intros. *)
  (*   apply prog_impl_trans. eapply prog_impl_implication_subset. *)
  (*   2: { eapply prog_impl_implication_weaken_hyp; [eassumption|]. *)
  (*        intros. eapply prog_impl_implication_subset; [|eassumption]. *)
  (*        intros. rewrite in_app_iff. auto. } *)
  (*   intros. rewrite in_app_iff. auto. *)
  (* Qed. *)

  (* Lemma loopless_program p Q f : *)
  (*   disjoint_lists (flat_map concl_rels p) (flat_map hyp_rels p) -> *)
  (*   prog_impl_implication p Q f -> *)
  (*   Q f \/ *)
  (*     exists hyps, *)
  (*       Forall Q hyps /\ *)
  (*         Exists (fun r => rule_impl r f hyps) p. *)
  (* Proof. *)
  (*   intros Hdisj. induction 1. *)
  (*   - auto. *)
  (*   - right. fold (prog_impl_implication p) in *. eexists. split; [|eassumption]. *)
  (*     rewrite Forall_forall in *. intros f Hf. specialize (H1 _ Hf). *)
  (*     destruct H1 as [H1|H1]; auto. fwd. rewrite Exists_exists in *. fwd. *)
  (*     apply rule_impl_hyp_relname_in in Hp1. apply rule_impl_concl_relname_in in H1p1p1. *)
  (*     rewrite Forall_forall in Hp1. specialize (Hp1 _ Hf). exfalso. eapply Hdisj. *)
  (*     + apply in_flat_map. eauto. *)
  (*     + apply in_flat_map. eauto. *)
  (* Qed. *)

  (* Lemma loopless_program_iff p Q f : *)
  (*   disjoint_lists (flat_map concl_rels p) (flat_map hyp_rels p) -> *)
  (*   prog_impl_implication p Q f <-> *)
  (*     (Q f \/ *)
  (*        exists hyps, *)
  (*          Forall Q hyps /\ *)
  (*            Exists (fun r => rule_impl r f hyps) p). *)
  (* Proof. *)
  (*   intros. split; auto using loopless_program. intros [H'|H']; fwd; eauto. *)
  (* Qed. *)
End __.
Arguments clause : clear implicits.
Arguments meta_clause : clear implicits.
Arguments fact : clear implicits.
Arguments fact_args : clear implicits.
Arguments rule : clear implicits.
Arguments expr : clear implicits.
