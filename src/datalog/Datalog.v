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

  Lemma fact_of_rel_of_args_of f :
    fact_of (rel_of f) (args_of f) = f.
  Proof. destruct f; reflexivity. Qed.

  Lemma rel_of_fact_of R args :
    rel_of (fact_of R args) = R.
  Proof. destruct args; reflexivity. Qed.

  Lemma args_of_fact_of R args :
    args_of (fact_of R args) = args.
  Proof. destruct args; reflexivity. Qed.

  Lemma fact_of_inj R args R' args' :
    fact_of R args = fact_of R' args' ->
    R = R' /\ args = args'.
  Proof.
    destruct args, args'; simpl; intros; congruence || fwd; auto.
  Qed.

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
  Hint Constructors non_meta_rule_impl : core.

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

  Definition extensionally_equal (f1 f2 : fact) : Prop :=
    match f1, f2 with
    | normal_fact R1 args1, normal_fact R2 args2 =>
        R1 = R2 /\ args1 = args2
    | meta_fact R1 mf_args1 mf_set1, meta_fact R2 mf_args2 mf_set2 =>
        R1 = R2 /\ mf_args1 = mf_args2 /\
        (forall args, Forall2 matches mf_args1 args -> (mf_set1 args <-> mf_set2 args))
    | _, _ => False
    end.

  (*TODO: meta_facts should have a type that restricts it to just being meta-facts?*)
  (*fact_supported is a goofy name*)
  Definition fact_supported (meta_facts : list fact) (f : fact) : Prop :=
    Exists (fun hyp => extensionally_equal f hyp \/ fact_matches f hyp) meta_facts.

  Definition one_step_derives0 fact_supported (p : list rule) (meta_facts : list fact) (R : rel) (args : list T) : Prop :=
    exists r hyps,
      In r p /\
        non_meta_rule_impl r R args hyps /\
        Forall (fact_supported meta_facts) hyps.
  Definition one_step_derives := one_step_derives0 fact_supported.
  Hint Unfold one_step_derives0 fact_supported : core.

  Inductive rule_impl (env : list fact -> rel -> list T -> Prop) : rule -> fact -> list fact -> Prop :=
  | simple_rule_impl r R args hyps :
    non_meta_rule_impl r R args hyps ->
    rule_impl _ r (normal_fact R args) hyps
  | meta_rule_impl rule_concls rule_hyps ctx R args hyps S :
    Exists (fun c => interp_meta_clause ctx c (meta_fact R args (fun args' => S args'))) rule_concls ->
      Forall2 (interp_meta_clause ctx) rule_hyps hyps ->
      (forall args'',
          Forall2 matches args args'' ->
          S args'' <-> env hyps R args'') ->
      rule_impl env (meta_rule rule_concls rule_hyps) (meta_fact R args S) hyps.
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
    pftree (fun f hyps => Exists (fun r => rule_impl (one_step_derives p) r f hyps) p).

  Lemma prog_impl_ind p Q R :
    (forall f, Q f -> R f) ->
    (forall f hyps,
        Exists (fun r => rule_impl (one_step_derives p) r f hyps) p ->
        Forall (prog_impl p Q) hyps ->
        Forall R hyps ->
        R f) ->
    forall f, prog_impl p Q f -> R f.
  Proof. apply pftree_ind. Qed.

  Lemma prog_impl_step p Q f hyps' :
    Exists (fun r => rule_impl (one_step_derives p) r f hyps') p ->
    Forall (prog_impl p Q) hyps' ->
    prog_impl p Q f.
  Proof. intros. eapply pftree_step; eauto. Qed.

  Lemma non_meta_rule_impl_ext r R args hyps hyps' :
    non_meta_rule_impl r R args hyps ->
    Forall2 extensionally_equal hyps hyps' ->
    non_meta_rule_impl r R args hyps'.
  Proof.
    intros H1 H2. invert H1.
    - econstructor; eauto. eapply Forall2_Forall2_Forall3 in H2; [|eassumption].
      apply Forall3_ignore2 in H2. eapply Forall2_impl; [|eassumption].
      simpl. intros. fwd. cbv [interp_clause extensionally_equal] in *. fwd. eauto.
    - invert H2. cbv [extensionally_equal] in H3. fwd.
      eassert (l' = _) as ->.
      2: { econstructor. eapply is_list_set_ext; [eassumption|].
           simpl. intros (?, ?). apply H3p2.
           constructor; try solve [cbv [matches]; auto].
           constructor; try solve [cbv [matches]; auto].
           rewrite <-  Forall2_map_l. apply Forall2_same.
           apply Forall_forall. simpl. auto. }
      apply Forall2_eq_eq. apply Forall2_flip.
      rewrite <- Forall2_map_l in *. eapply Forall2_impl; [|eassumption].
      simpl. intros (?, ?) ? ?. cbv [extensionally_equal] in *. fwd. reflexivity.
  Qed.

  Lemma fact_supported_ext hyps hyps' f :
    Forall2 extensionally_equal hyps hyps' ->
    fact_supported hyps f ->
    fact_supported hyps' f.
  Proof.
    intros H1 H2. cbv [fact_supported] in *. apply Exists_exists in H2. fwd.
    apply Forall2_forget_r in H1. rewrite Forall_forall in H1. apply H1 in H2p0.
    fwd. apply Exists_exists. eexists. split; [eassumption|].
    destruct f, x, y; destruct H2p1; simpl in *; fwd; contradiction || eauto.
    - right. cbv [fact_matches] in H. fwd. cbv [fact_matches].
      do 4 eexists. ssplit; try reflexivity; auto. apply H2p0p1p2; auto.
    - left. ssplit; auto. intros. rewrite <- H2p0p1p2 by assumption. apply Hp2.
      assumption.
    - exfalso. cbv [fact_matches] in H. fwd. congruence.
  Qed.

  Lemma one_step_derives_ext p hyps hyps' R args'' :
    Forall2 extensionally_equal hyps hyps' ->
    one_step_derives p hyps R args'' -> one_step_derives p hyps' R args''.
  Proof.
    intros H1 H2. cbv [one_step_derives one_step_derives0] in *. fwd.
    do 2 eexists. split; [eassumption|]. split; [eassumption|].
    eapply Forall_impl; [|eassumption].
    intros f Hf. eapply fact_supported_ext; eassumption.
  Qed.

  Definition is_meta f :=
    match f with
    | meta_fact _ _ _ => True
    | normal_fact _ _ => False
    end.

  Lemma extensionally_equal_sym f1 f2 :
    extensionally_equal f1 f2 -> extensionally_equal f2 f1.
  Proof.
    destruct f1, f2; cbv [extensionally_equal] in *; try contradiction; fwd.
    - auto.
    - repeat split; auto. intros. symmetry. auto.
  Qed.

  Lemma rule_impl_ext p r f hyps hyps' :
    rule_impl (one_step_derives p) r f hyps ->
    Forall2 extensionally_equal hyps hyps' ->
    rule_impl (one_step_derives p) r f hyps'.
  Proof.
    intros H1 H2. invert H1.
    - constructor. eauto using non_meta_rule_impl_ext.
    - econstructor.
      + eassumption.
      + eapply Forall2_Forall2_Forall3 in H2; [|eassumption].
        apply Forall3_ignore2 in H2. eapply Forall2_impl; [|eassumption].
        simpl. intros. fwd. cbv [interp_meta_clause extensionally_equal] in *. fwd. eauto.
      + intros. rewrite H3 by assumption. split; intros; eapply one_step_derives_ext; eauto.
        apply Forall2_flip. eapply Forall2_impl; [|eassumption].
        auto using extensionally_equal_sym.
  Qed.

  Lemma prog_impl_step_strong p Q f hyps' :
    Exists (fun r => rule_impl (one_step_derives p) r f hyps') p ->
    Forall (fun hyp => exists hyp', extensionally_equal hyp hyp' /\ prog_impl p Q hyp') hyps' ->
    prog_impl p Q f.
  Proof.
    intros H1 H2. apply Forall_exists_r_Forall2 in H2.
    fwd.
    eapply prog_impl_step.
    - eapply Exists_impl; [|eassumption]. simpl. intros. eapply rule_impl_ext; try eassumption.
      eapply Forall2_impl; [|eassumption].
      simpl. intros. fwd. auto using extensionally_equal_sym.
    - eapply Forall2_forget_l in H2. eapply Forall_impl; [|eassumption].
      simpl. intros. fwd. assumption.
  Qed.

  Lemma prog_impl_leaf p Q f :
    Q f ->
    prog_impl p Q f.
  Proof. cbv [prog_impl]. eauto. Qed.
  Hint Resolve prog_impl_leaf : core.

  Lemma invert_prog_impl p Q f :
    prog_impl p Q f ->
    Q f \/
      exists hyps',
        Exists (fun r : rule => rule_impl (one_step_derives p) r f hyps') p /\
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

  Lemma prog_impl_hyp_ext p f Q1 Q2 :
    (forall f', Q1 f' <-> Q2 f') ->
    prog_impl p Q1 f <-> prog_impl p Q2 f.
  Proof.
    intros H.
    split; intros; eapply prog_impl_weaken_hyp; try eassumption.
    - intros. apply H. assumption.
    - intros. apply H. assumption.
  Qed.

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
    P x \/ Q (P, x) \/ exists hyps', Exists (fun r => rule_impl (one_step_derives p) r x hyps') p /\ Forall (fun x => Q (P, x)) hyps'.

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

  Lemma pftree_equiv {U} (P1 P2 : U -> list U -> Prop) Q (x:U) :
    (forall y l, P1 y l <-> P2 y l) ->
    pftree P1 Q x <-> pftree P2 Q x.
  Proof.
    intros H. split; intros Htree.
    - eapply pftree_weaken; [exact Htree | intros y l Hyl; apply H; exact Hyl].
    - eapply pftree_weaken; [exact Htree | intros y l Hyl; apply H; exact Hyl].
  Qed.

  Lemma S_sane_lfp p : S_sane (lfp (F p)).
  Proof.
    eapply S_sane_ext; [apply prog_impl_lfp|]. cbv [S_sane]. split; intros; eauto.
    eapply pftree_trans. eapply pftree_weaken_hyp; eauto.
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
    cbv [interp_clause]. intros Hinterp Hagree. fwd.
    eexists. split; [|auto].
    eapply Forall2_impl_strong; [|eassumption].
    intros. cbv [vars_of_clause] in Hagree.
    rewrite Forall_flat_map, Forall_forall in Hagree.
    eauto using interp_expr_agree_on.
  Qed.

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

  Definition concl_rels (r : rule) : list rel :=
    match r with
    | normal_rule rule_concls _ => map clause_rel rule_concls
    | meta_rule rule_concls _ => map meta_clause_rel rule_concls
    | agg_rule concl_rel _ _ => [concl_rel]
    end.

  Definition meta_concl_rels (r : rule) : list rel :=
    match r with
    | normal_rule _ _ => []
    | meta_rule rule_concls _ => map meta_clause_rel rule_concls
    | agg_rule _ _ _ => []
    end.

  Definition all_rels (r : rule) : list rel :=
    match r with
    | normal_rule rule_concls rule_hyps =>
        map clause_rel rule_concls ++ map clause_rel rule_hyps
    | meta_rule rule_concls rule_hyps =>
        map meta_clause_rel rule_concls ++ map meta_clause_rel rule_hyps
    | agg_rule concl_rel _ hyp_rel => [concl_rel; hyp_rel]
    end.

    (*not equivalent to hyp_rels_alt*)
  Definition hyp_rels (r : rule) : list rel :=
    match r with
    | normal_rule _ rule_hyps => map clause_rel rule_hyps
    | meta_rule rule_concls rule_hyps => map meta_clause_rel rule_hyps
    | agg_rule _ _ hyp_rel => [hyp_rel]
    end.

  Lemma non_meta_rule_impl_concl_relname_in r R args hyps :
    non_meta_rule_impl r R args hyps ->
    In R (concl_rels r).
  Proof.
    invert 1.
    - rewrite Exists_exists in *. repeat invert_stuff.
      apply in_map_iff. eauto.
    - left. reflexivity.
  Qed.

  Lemma rule_impl_concl_relname_in p r f hyps :
    rule_impl p r f hyps ->
    In (rel_of f) (concl_rels r).
  Proof.
    invert 1.
    - eapply  non_meta_rule_impl_concl_relname_in. eassumption.
    - rewrite Exists_exists in *. fwd. apply in_map_iff.
      repeat invert_stuff. eauto.
  Qed.

  Lemma non_meta_rule_impl_hyp_relname_in r R args hyps :
    non_meta_rule_impl r R args hyps ->
    Forall (fun hyp => In (rel_of hyp) (hyp_rels r)) hyps.
  Proof.
    invert 1.
    - simpl.
      eapply Forall_impl; [|eapply Forall2_forget_l; eassumption].
      intros. repeat invert_stuff.
      eauto using in_map.
    - simpl. constructor; eauto.
      apply Forall_map. apply Forall_forall.
      intros [? ?]. simpl. auto.
  Qed.

  Lemma rule_impl_hyp_relname_in p r f hyps :
    rule_impl p r f hyps ->
    Forall (fun hyp => In (rel_of hyp) (hyp_rels r)) hyps.
  Proof.
    invert 1.
    - eapply non_meta_rule_impl_hyp_relname_in. eassumption.
    - simpl.
      eapply Forall_impl; [|eapply Forall2_forget_l; eassumption].
      intros. repeat invert_stuff.
      eauto using in_map.
  Qed.

  Lemma pftree_weaken_hyp_strong {U : Type} (P : U -> list U -> Prop) Q1 Q2 (x : U) (Inv : U -> Prop) :
    (Q1 x -> Q2 x) ->
    (forall y l, P y l -> Forall Inv l) ->
    (forall y, Inv y -> Q1 y -> Q2 y) ->
    pftree P Q1 x -> pftree P Q2 x.
  Proof.
    intros Hx Hstep Hinv Htree.
    assert (Hgen: forall y, pftree P Q1 y -> (Q1 y -> Q2 y) \/ Inv y -> pftree P Q2 y).
    { intros y Hy. induction Hy.
      - intros Hcond. apply pftree_leaf. destruct Hcond as [Hcond | Hcond].
        + apply Hcond. exact H.
        + apply Hinv; auto.
      - intros _. eapply pftree_step; [exact H |].
        pose proof (Hstep _ _ H) as Hinv_l.
        rewrite Forall_forall in H1, Hinv_l |- *.
        intros z Hz. apply H1; [exact Hz |].
        right. apply Hinv_l. exact Hz. }
    apply Hgen; auto.
  Qed.

  Lemma pftree_hyp_ext_framed {U : Type} (P : U -> list U -> Prop) Q1 Q2 (x : U) (Inv : U -> Prop) :
    (Q1 x <-> Q2 x) ->
    (forall y l, P y l -> Forall Inv l) ->
    (forall y, Inv y -> Q1 y <-> Q2 y) ->
    pftree P Q1 x <-> pftree P Q2 x.
  Proof.
    intros Hx Hstep Hinv. split; apply pftree_weaken_hyp_strong with (Inv := Inv).
    - apply Hx.
    - exact Hstep.
    - intros; apply Hinv; auto.
    - apply Hx.
    - exact Hstep.
    - intros; apply Hinv; auto.
  Qed.

  Lemma prog_impl_hyp_ext_strong p Q1 Q2 f :
    (Q1 f <-> Q2 f) ->
    (forall f', In (rel_of f') (flat_map hyp_rels p) -> Q1 f' <-> Q2 f') ->
    prog_impl p Q1 f <-> prog_impl p Q2 f.
  Proof.
    intros Hf Hhyps.
    apply pftree_hyp_ext_framed with (Inv := fun f' => In (rel_of f') (flat_map hyp_rels p)).
    - exact Hf.
    - intros y l Hex.
      apply Exists_exists in Hex. fwd.
      apply rule_impl_hyp_relname_in in Hexp1.
      eapply Forall_impl; [|exact Hexp1].
      simpl. intros hyp Hhyp.
      apply in_flat_map. eexists; split; eauto.
    - exact Hhyps.
  Qed.

  Lemma staged_program_rule_impl p1 p2 r f hyps :
    disjoint_lists (meta_concl_rels r) (flat_map concl_rels p2) ->
    rule_impl (one_step_derives (p1 ++ p2)) r f hyps ->
    rule_impl (one_step_derives p1) r f hyps.
  Proof.
    intros Hout. invert 1.
    - invert H0.
      + constructor. econstructor; eassumption.
      + constructor. econstructor; eassumption.
    - econstructor; try eassumption.
      intros args'' Hargs''. rewrite H2 by assumption.
      cbv [one_step_derives one_step_derives0]. split; intros H'.
      + fwd. rewrite in_app_iff in H'p0. destruct H'p0 as [H'p0|H'p0]; eauto 6.
        apply non_meta_rule_impl_concl_relname_in in H'p1.
        rewrite Exists_exists in H0. fwd. repeat invert_stuff.
        exfalso. eapply Hout.
        -- apply in_map. eassumption.
        -- apply in_flat_map. eauto.
      + fwd. do 2 eexists. rewrite in_app_iff. eauto.
  Qed.

  Lemma staged_program_rule_impl_bw p1 p2 r f hyps :
    disjoint_lists (meta_concl_rels r) (flat_map concl_rels p2) ->
    rule_impl (one_step_derives p1) r f hyps ->
    rule_impl (one_step_derives (p1 ++ p2)) r f hyps.
  Proof.
    intros Hout. invert 1.
    - invert H0.
      + constructor. econstructor; eassumption.
      + constructor. econstructor; eassumption.
    - econstructor; try eassumption.
      intros args'' Hargs''. rewrite H2 by assumption.
      cbv [one_step_derives one_step_derives0]. split; intros H'.
      + fwd. do 2 eexists. rewrite in_app_iff. eauto.
      + fwd. do 2 eexists. eauto. rewrite in_app_iff in H'p0. destruct H'p0 as [H'p0|H'p0]; eauto.
        apply non_meta_rule_impl_concl_relname_in in H'p1.
        rewrite Exists_exists in H0. fwd. repeat invert_stuff.
        exfalso. eapply Hout.
        -- apply in_map. eassumption.
        -- apply in_flat_map. eauto.
  Qed.

  Lemma prog_impl_subset' p1 p2 Q f :
    disjoint_lists (flat_map meta_concl_rels p1) (flat_map concl_rels p2) ->
    prog_impl p1 Q f ->
    prog_impl (p1 ++ p2) Q f.
  Proof.
    intros Hdisj H. induction H using prog_impl_ind.
    - apply prog_impl_leaf. assumption.
    - eapply prog_impl_step; [|eassumption].
      rewrite Exists_exists in *. fwd. eexists.
      rewrite in_app_iff. split; [eauto|].
      eapply staged_program_rule_impl_bw; [|eassumption].
      eapply disjoint_lists_incl_l; [eassumption|].
      apply incl_flat_map_r. assumption.
  Qed.

  Lemma rule_impl_list_set p1 p2 r f hyps :
    rule_impl (one_step_derives p1) r f hyps ->
    same_set p1 p2 ->
    rule_impl (one_step_derives p2) r f hyps.
  Proof.
    intros H Hiff. invert H.
    - constructor. assumption.
    - econstructor; try eassumption. intros. rewrite H2 by assumption.
      clear -Hiff. cbv [one_step_derives one_step_derives0].
      split; intros; fwd; do 2 eexists; edestruct Hiff; eauto.
  Qed.

  Lemma prog_impl_same_set p1 p2 Q f :
    prog_impl p1 Q f ->
    same_set p1 p2 ->
    prog_impl p2 Q f.
  Proof.
    intros H Hiff. induction H using prog_impl_ind.
    - apply prog_impl_leaf. assumption.
    - eapply prog_impl_step; [|eassumption].
      rewrite Exists_exists in *. fwd.
      edestruct Hiff; eauto using rule_impl_list_set.
  Qed.

  Lemma incl_exists_app_eq_set' {U} (eq_prop : forall x y : U, x = y \/ x <> y)
      (l1 l2 : list U) :
    incl l1 l2 ->
    exists l3, disjoint_lists l1 l3 /\ same_set (l1 ++ l3) l2.
  Proof.
    intros H_incl.
    assert (In_dec : forall (a : U) (l : list U), {In a l} + {~ In a l}).
    { intros a l. induction l as [|x l' [IH|IH]].
      - right; auto.
      - left; right; auto.
      - destruct (eq_prop a x); [left; left; auto | right; intros [->|]; auto]. }
    exists (filter (fun x => if In_dec x l1 then false else true) l2).
    split.
    - intros x Hx1 Hx2. apply filter_In in Hx2 as [_ Hx2].
      destruct (In_dec x l1); discriminate.
    - intros x. rewrite in_app_iff, filter_In. split.
      + intros [Hx | [Hx _]]; auto using H_incl.
      + intros Hx. destruct (In_dec x l1).
        * left; auto.
        * right; split; [auto | destruct (In_dec x l1); auto].
  Qed.

  From Stdlib Require Import Classical.
  Lemma incl_exists_app_eq_set {U} (l1 l2 : list U) :
    incl l1 l2 ->
    exists l3, disjoint_lists l1 l3 /\ same_set (l1 ++ l3) l2.
  Proof.
    apply incl_exists_app_eq_set'.
    intros x y. apply classic.
  Qed.

  Lemma prog_impl_subset p1 p2 Q f :
    incl p1 p2 ->
    (forall r, In r p2 ->
          In r p1 \/
            disjoint_lists (flat_map meta_concl_rels p1) (concl_rels r)) ->
    prog_impl p1 Q f ->
    prog_impl p2 Q f.
  Proof.
    intros H12 H21 H1. apply incl_exists_app_eq_set in H12. fwd.
    eapply prog_impl_same_set; [|eassumption].
    apply prog_impl_subset'; [|assumption].
    intros R HR1 HR2. apply in_flat_map in HR1, HR2. fwd.
    epose_dep H21. specialize' H21.
    { apply H12p1. apply in_app_iff. right. eassumption. }
    destruct H21 as [H21|H21]; eauto.
    eapply H21; eauto. apply in_flat_map. eauto.
  Qed.

  Lemma staged_program p1 p2 Q f :
    disjoint_lists (flat_map concl_rels p1) (flat_map hyp_rels p2) ->
    disjoint_lists (flat_map meta_concl_rels p1) (flat_map concl_rels p2) ->
    disjoint_lists (flat_map meta_concl_rels p2) (flat_map concl_rels p1) ->
    prog_impl (p1 ++ p2) Q f ->
    prog_impl p1 (prog_impl p2 Q) f.
  Proof.
    intros Hdisj Hmr1 Hmr2. induction 1 using prog_impl_ind.
    - apply pftree_leaf. apply pftree_leaf. assumption.
    - apply Exists_app in H. destruct H as [H|H].
      + eapply prog_impl_step. 2: eassumption.
        rewrite Exists_exists in *. fwd.
        eexists. split; [eassumption|].
        eapply staged_program_rule_impl; [|eassumption].
        eapply disjoint_lists_incl_l; [eassumption|].
        apply incl_flat_map_r. assumption.
      + apply pftree_leaf. eapply prog_impl_step.
        -- rewrite Exists_exists in *. fwd. eexists. split; [eassumption|].
           eapply staged_program_rule_impl with (p2 := p1).
           2: { eapply rule_impl_list_set; [eassumption|].
                apply same_set_app_comm. }
           eapply disjoint_lists_incl_l; [eassumption|].
           apply incl_flat_map_r. assumption.
        -- rewrite Exists_exists in H. fwd.
           apply rule_impl_hyp_relname_in in Hp1.
           eapply Forall_impl.
           2: { eapply Forall_and; [apply Hp1|apply H1]. }
           simpl. intros f' [Hf'1 Hf'2].
           invert Hf'2; [assumption|].
           apply Exists_exists in H. fwd.
           apply rule_impl_concl_relname_in in Hp3.
           exfalso.
           eapply Hdisj; apply in_flat_map; eauto.
  Qed.

  Lemma meta_concl_rels_incl_concl_rels r :
    incl (meta_concl_rels r) (concl_rels r).
  Proof. destruct r; simpl; auto with incl. Qed.
  Hint Resolve meta_concl_rels_incl_concl_rels : incl.

  Lemma concl_rels_incl_all_rels r :
    incl (concl_rels r) (all_rels r).
  Proof. destruct r; simpl; auto with incl. Qed.
  Hint Resolve concl_rels_incl_all_rels : incl.

  Lemma hyp_rels_incl_all_rels r :
    incl (hyp_rels r) (all_rels r).
  Proof. destruct r; simpl; auto with incl. Qed.
  Hint Resolve hyp_rels_incl_all_rels : incl.

  Lemma staged_program_weak p1 p2 Q f :
    disjoint_lists (flat_map concl_rels p1) (flat_map all_rels p2) ->
    prog_impl (p1 ++ p2) Q f ->
    prog_impl p1 (prog_impl p2 Q) f.
  Proof.
    intros Hdisj H. apply staged_program; auto.
    1,2: eapply disjoint_lists_incl; [eassumption| |]; auto with incl.
    apply disjoint_lists_comm.
    eapply disjoint_lists_incl; [eassumption| |]; auto with incl.
    apply incl_flat_map_strong; auto with incl. intros.
    eapply incl_tran; auto with incl.
  Qed.

  Lemma prog_impl_trans p Q f :
    prog_impl p (prog_impl p Q) f ->
    prog_impl p Q f.
  Proof. apply pftree_trans. Qed.

  Lemma staged_program_iff p1 p2 Q f :
    disjoint_lists (flat_map concl_rels p1) (flat_map all_rels p2) ->
    prog_impl (p1 ++ p2) Q f <->
    prog_impl p1 (prog_impl p2 Q) f.
  Proof.
    split; auto using staged_program_weak. intros.
    apply prog_impl_trans. eapply prog_impl_subset'.
    { eapply disjoint_lists_incl; [eassumption| |]; auto with incl. }
    eapply prog_impl_weaken_hyp; [eassumption|].
    intros.
    eapply prog_impl_same_set. 2: apply same_set_app_comm.
    eapply prog_impl_subset'; [|eassumption].
    apply disjoint_lists_comm.
    eapply disjoint_lists_incl; [eassumption | |]; auto with incl.
    apply incl_flat_map_strong; auto with incl.
    intros. eapply incl_tran; auto with incl.
  Qed.

  Lemma prog_impl_rel_of p Q f :
    prog_impl p Q f ->
    Q f \/ In (rel_of f) (flat_map concl_rels p).
  Proof.
    intros H. apply invert_prog_impl in H. destruct H as [Hq | [hyps' [Hex _]]].
    - left. exact Hq.
    - right. apply Exists_exists in Hex. destruct Hex as [r [Hrin Hrule]].
      apply in_flat_map. exists r. split; [exact Hrin |].
      eapply rule_impl_concl_relname_in. exact Hrule.
  Qed.

  Definition meta_rules_valid p :=
    forall R mf_args mf_set mhyps mr,
      In mr p ->
      rule_impl (one_step_derives p) mr (meta_fact R mf_args mf_set) mhyps ->
      forall nr args hyps,
        In nr p ->
        rule_impl (one_step_derives p) nr (normal_fact R args) hyps ->
        Forall2 matches mf_args args ->
        Forall (fun f =>
                  match f with
                  | normal_fact R' nf_args' =>
                      exists mf_args' mf_set',
                      In (meta_fact R' mf_args' mf_set') mhyps /\
                        Forall2 matches mf_args' nf_args'
                  | meta_fact R' mf_args' _ =>
                      exists mf_set',
                      In (meta_fact R' mf_args' mf_set') mhyps
                  end) hyps.

  Definition consistent mf_rel mf_args mf_set S :=
    forall nf_args,
      Forall2 matches mf_args nf_args ->
      mf_set nf_args <-> S (normal_fact mf_rel nf_args).

  Lemma extensionally_equal_refl f :
    extensionally_equal f f.
  Proof. destruct f; cbv [extensionally_equal]; repeat split; intros; tauto. Qed.

  Lemma meta_rules_valid_step' p Q mf_rel mf_args mf_set mr mhyps :
    (forall f, Q f -> ~ In (rel_of f) (flat_map concl_rels p)) ->
    meta_rules_valid p ->
    In mr p ->
    rule_impl (one_step_derives p) mr (meta_fact mf_rel mf_args mf_set) mhyps ->
    (forall mf_rel' mf_args' mf_set',
        In (meta_fact mf_rel' mf_args' mf_set') mhyps ->
        consistent mf_rel' mf_args' mf_set' (prog_impl p Q)) ->
    (forall mf_rel' mf_args' mf_set' mf_set'0,
        In (meta_fact mf_rel' mf_args' mf_set') mhyps ->
        prog_impl p Q (meta_fact mf_rel' mf_args' mf_set'0) ->
        forall nf_args',
          Forall2 matches mf_args' nf_args' ->
          mf_set' nf_args' <-> mf_set'0 nf_args') ->
    Forall (prog_impl p Q) mhyps ->
    consistent mf_rel mf_args mf_set (prog_impl p Q).
  Proof.
    intros Hinp H1 H2 Hmr_impl H4 H5 H6.
    pose proof Hmr_impl as Hvalid. apply H1 in Hvalid; [|assumption].
    cbv [consistent]. intros nf_args Hmatch. split; intros Hnf_args.
    - clear H5 Hvalid. invert Hmr_impl. rewrite H10 in Hnf_args by assumption.
      cbv [one_step_derives one_step_derives0] in Hnf_args. fwd.
      eapply prog_impl_step_strong.
      { apply Exists_exists. eauto. }
      eapply Forall_impl; [|eassumption]. intros f' Hf'.

      cbv [fact_supported] in Hf'. apply Exists_exists in Hf'. fwd.
      destruct Hf'p1 as [Hf'p1|Hf'p1].
      { eexists. split; [eassumption|]. rewrite Forall_forall in H6. auto. }
      exists f'. split. { apply extensionally_equal_refl. }
      cbv [fact_matches] in Hf'p1. fwd.
      apply H4 in Hf'p0. cbv [consistent] in Hf'p0. apply Hf'p0; eassumption.
    - apply invert_prog_impl in Hnf_args. destruct Hnf_args as [Hnf_args|Hnf_args].
      { exfalso. eapply Hinp; [eassumption|]. simpl.
        apply in_flat_map. apply rule_impl_concl_relname_in in Hmr_impl. simpl in Hmr_impl. eauto. }
      clear H1 H2.
      fwd. apply Exists_exists in Hnf_argsp0. fwd.
      specialize (Hvalid _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
      invert Hmr_impl. rewrite H9 by assumption.
      invert Hnf_argsp0p1. cbv [one_step_derives one_step_derives0].
      do 2 eexists. split; [eassumption|]. split; [eassumption|].
      eapply Forall_impl.
      2: { apply Forall_and; [exact Hvalid|exact Hnf_argsp1]. }
      clear hyps' Hvalid Hnf_argsp1 H7.
      simpl. intros f Hf. fwd. destruct f; fwd.
      + cbv [fact_supported]. apply Exists_exists. eexists. split; [eassumption|].
        right. cbv [fact_matches]. do 4 eexists. ssplit; try reflexivity.
        1: assumption. apply H4 in Hfp0p0. cbv [consistent] in Hfp0p0.
        rewrite Hfp0p0 by assumption. assumption.
      + cbv [fact_supported]. apply Exists_exists. eexists. split; [eassumption|].
        left. simpl. ssplit; auto. intros args Hargs.
        symmetry. eapply H5; eassumption.
  Qed.

  Definition doesnt_lie S :=
    forall mf_rel mf_args mf_set,
      S (meta_fact mf_rel mf_args mf_set) ->
      consistent mf_rel mf_args mf_set S.

  Definition args_consistent mf_args mf_set (S_args : fact_args -> Prop) :=
    forall nf_args,
      Forall2 matches mf_args nf_args ->
      mf_set nf_args <-> S_args (normal_fact_args nf_args).

  Definition honest_args (S_args : fact_args -> Prop) :=
    forall mf_args mf_set,
      S_args (meta_fact_args mf_args mf_set) ->
      args_consistent mf_args mf_set S_args.

  Lemma doesnt_lie_honest_args S R :
    doesnt_lie S ->
    honest_args (fun args => S (fact_of R args)).
  Proof.
    cbv [doesnt_lie honest_args args_consistent consistent fact_of]. eauto.
  Qed.

  Lemma honest_args_ext S1 S2 :
    (forall args, S1 args <-> S2 args) ->
    honest_args S1 ->
    honest_args S2.
  Proof.
    intros Heq H1 mf_args mf_set Hmeta nf_args Hmatch.
    cbv [honest_args args_consistent] in *.
    apply (proj2 (Heq _)) in Hmeta.
    pose proof (H1 _ _ Hmeta _ Hmatch) as H. rewrite Heq. exact H.
  Qed.

  (*this is a lemma about pairwise properties, because that is all that i need to reasona baout.
    it is also true for n-wise properties, or even properties of arbitrary-length finite lists.
   it is not true for infinite sets. *)

  Inductive is_dag_ish {U} Q (P : U -> list U -> _) : list U -> Prop :=
  | is_dag_ish_nil : is_dag_ish _ _ []
  | is_dag_ish_cons x xs :
    Q x \/ (exists l, P x l /\ incl l xs) ->
    is_dag_ish _ _ xs ->
    is_dag_ish _ _ (x :: xs).
  Hint Constructors is_dag_ish : core.

  Lemma is_dag_ish_app U (Q : U -> _) P xs1 xs2 :
    is_dag_ish Q P xs1 ->
    is_dag_ish Q P xs2 ->
    is_dag_ish Q P (xs1 ++ xs2).
  Proof.
    intros H1 H2. induction H1; simpl; auto.
    constructor; auto. destruct H as [H|H]; auto.
    fwd. right. eexists. split; [eassumption|].
    auto with incl.
  Qed.

  Lemma is_dag_ish_concat U (Q : U -> _) P xss :
    Forall (is_dag_ish Q P) xss ->
    is_dag_ish Q P (concat xss).
  Proof. induction 1; simpl; auto using is_dag_ish_app. Qed.

  Lemma pftree_something_idk U (P : U -> list U -> _) Q x :
    pftree P Q x ->
    exists xs,
      is_dag_ish Q P xs /\ In x xs.
  Proof.
    induction 1.
    - exists [x]. simpl. auto.
    - apply Forall_exists_r_Forall2 in H1. fwd.
      exists (x :: concat ys). simpl. split; auto. constructor.
      + right. eexists. split; [eassumption|].
        apply Forall2_forget_r in H1. cbv [incl]. apply Forall_forall.
        eapply Forall_impl; [|eassumption].
        simpl. intros. fwd. rewrite in_concat. eauto.
      + apply is_dag_ish_concat.
        apply Forall2_forget_l in H1. eapply Forall_impl; [|eassumption].
        simpl. intros. fwd. assumption.
  Qed.

  Lemma is_dag_ish_pftree U (P : U -> _ -> _) Q xs :
    is_dag_ish Q P xs ->
    Forall (pftree P Q) xs.
  Proof.
    induction 1; constructor; auto.
    destruct H; fwd; auto.
    eapply pftree_step; [eassumption|].
    Search Forall incl. eauto using incl_Forall.
  Qed.

  Hint Unfold In : core.
  Lemma stepping_induction' U (P : U -> list U -> _) R Q :
    (forall x1 x2, R x1 x2 <-> R x2 x1) ->
    (forall xs,
        (forall x1 x2, In x1 xs -> In x2 xs -> R x1 x2) ->
        forall x,
        is_dag_ish Q P (x :: xs) ->
        (forall y, In y (x :: xs) -> R x y)) ->
    forall xs,
      is_dag_ish Q P xs ->
      forall x1 x2,
        In x1 xs ->
        In x2 xs ->
        R x1 x2.
  Proof.
    intros Hcomm Hstep xs Hxs.
    induction Hxs.
    - simpl. contradiction.
    - specialize (Hstep _ IHHxs).
      intros x1 x2 [H1|H1] [H2|H2]; subst; auto.
      apply Hcomm. auto.
  Qed.

  Lemma stepping_induction U (P : U -> list U -> _) R Q :
    (forall x1 x2, R x1 x2 <-> R x2 x1) ->
    (forall xs,
        (forall x1 x2, In x1 xs -> In x2 xs -> R x1 x2) ->
        forall x,
        is_dag_ish Q P (x :: xs) ->
        (forall y, In y (x :: xs) -> R x y)) ->
    forall x1 x2,
      pftree P Q x1 ->
      pftree P Q x2 ->
      R x1 x2.
  Proof.
    intros ? ? x1 x2 H1 H2. apply pftree_something_idk in H1, H2.
    fwd. eapply is_dag_ish_app in H1p0; [|exact H2p0].
    clear H2p0. eapply stepping_induction'; try eassumption.
    1,2: apply in_app_iff; auto.
  Qed.

  Lemma is_dag_ish_idk U (P : U -> _ -> _) Q xs :
    is_dag_ish Q P xs ->
    Forall (fun x => Q x \/ (exists l : list U, P x l /\ incl l xs)) xs.
  Proof.
    induction 1; auto. constructor.
    - destruct H; fwd; auto. right. eexists. split; [eassumption|].
      auto with incl.
    - eapply Forall_impl; [|eassumption]. simpl. intros ? [?|?]; fwd; eauto 6 with incl.
  Qed.

  Lemma meta_hyps_are_meta_facts env r mf_rel mf_args mf_set hyps :
    rule_impl env r (meta_fact mf_rel mf_args mf_set) hyps ->
    Forall is_meta hyps.
  Proof.
    invert 1. eapply Forall_impl.
    2: { eapply Forall2_forget_l. eassumption. }
    simpl. intros. fwd. cbv [interp_meta_clause] in *. fwd.
    exact I.
  Qed.

  Lemma meta_facts_consistent' p Q f1 f2 :
    (forall f, Q f -> ~ In (rel_of f) (flat_map concl_rels p)) ->
    (forall mf_rel mf_args1 mf_args2 mf_set1 mf_set2,
        Q (meta_fact mf_rel mf_args1 mf_set1) ->
        Q (meta_fact mf_rel mf_args2 mf_set2) ->
        forall nf_args : list T,
          Forall2 matches mf_args1 nf_args ->
          Forall2 matches mf_args2 nf_args ->
          mf_set1 nf_args <-> mf_set2 nf_args) ->
    meta_rules_valid p ->
    prog_impl p Q f1 ->
    prog_impl p Q f2 ->
    match f1, f2 with
    | meta_fact mf_rel1 mf_args1 mf_set1, meta_fact mf_rel2 mf_args2 mf_set2 =>
        mf_rel1 = mf_rel2 ->
        (forall nf_args,
            Forall2 matches mf_args1 nf_args ->
            Forall2 matches mf_args2 nf_args ->
            mf_set1 nf_args <-> mf_set2 nf_args)
    | _, _ => True
    end.
  Proof.
    intros Hinp Hinp2 Hvalid H1 H2. eapply stepping_induction with (x1 := f1) (x2 := f2).
    3,4: eassumption.
    { intros x1 x2. destruct x1, x2; split; intros; subst; auto; symmetry; auto. }
    clear f1 f2 H1 H2.
    intros fs Hfs1.
    assert (Hfs1': forall mf_rel mf_args1 mf_args2 mf_set1 mf_set2,
               In (meta_fact mf_rel mf_args1 mf_set1) fs ->
               In (meta_fact mf_rel mf_args2 mf_set2) fs ->
               forall nf_args : list T,
                 Forall2 matches mf_args1 nf_args ->
                 Forall2 matches mf_args2 nf_args ->
                 mf_set1 nf_args <-> mf_set2 nf_args).
    { intros mf_rel mf_args1 mf_args2 mf_set1 mf_set2 H1 H2.
      specialize (Hfs1 _ _ H1 H2). simpl in Hfs1. auto. }
    clear Hfs1.
    intros f1 Hfs2 f2 Hf2. invert Hfs2. rename H1 into Hf1. rename H2 into Hfs2.
    destruct f1, f2; try exact I. intros. subst.
    destruct Hf2 as [Hf2|Hf2].
    { fwd. reflexivity. }
    destruct Hf1 as [Hf1|Hf1].
    { apply is_dag_ish_pftree in Hfs2. rewrite Forall_forall in Hfs2.
      apply Hfs2 in Hf2.
      apply invert_prog_impl in Hf2. destruct Hf2 as [Hf2|Hf2]; eauto.
      exfalso. fwd. apply Exists_exists in Hf2p0. fwd.
      apply rule_impl_concl_relname_in in Hf2p0p1. simpl in Hf2p0p1.
      eapply Hinp; eauto. simpl. apply in_flat_map. eauto. }
    apply is_dag_ish_idk in Hfs2. rewrite Forall_forall in Hfs2.
    specialize (Hfs2 _ Hf2).
    fwd. apply Exists_exists in Hf1p0. fwd.
    destruct Hfs2 as [Hfs2|Hfs2].
    { exfalso. eapply Hinp; eauto. simpl. apply rule_impl_concl_relname_in in Hf1p0p1.
      simpl in Hf1p0p1. apply in_flat_map. eauto. }
    fwd. apply Exists_exists in Hfs2p0. fwd.
    pose proof Hf1p0p1 as Hmr1. pose proof Hfs2p0p1 as Hmr2.
    invert Hf1p0p1. invert Hfs2p0p1.
    rewrite H11 by assumption. rewrite H8 by assumption.
    clear H11 H8. clear H5 H6 H7 H10 ctx ctx0.
    assert (Forall is_meta l) as Hml.
    { eapply meta_hyps_are_meta_facts. eassumption. }
    assert (Forall is_meta l0) as Hml0.
    { eapply meta_hyps_are_meta_facts. eassumption. }
    apply Hvalid in Hmr1, Hmr2; try assumption.
    cbv [one_step_derives one_step_derives0]. split; intros Hderiv.
    - fwd. specialize (Hmr2 _ _ _ ltac:(eassumption) ltac:(eauto) ltac:(eassumption)).
      do 2 eexists. split; [eassumption|]. split; [eassumption|].
      eapply Forall_impl.
      2: { apply Forall_and; [apply Hmr2|apply Hderivp2]. }
      simpl. intros f Hf. fwd. destruct f; fwd.
      + cbv [fact_supported]. apply Exists_exists.
        eexists. split; [eassumption|].
        cbv [fact_supported] in Hfp1. apply Exists_exists in Hfp1. fwd.
        destruct Hfp1p1 as [Hfp1p1|Hfp1p1].
        { exfalso. cbv [extensionally_equal] in Hfp1p1. fwd.
          rewrite Forall_forall in Hml. apply Hml in Hfp1p0. exact Hfp1p0. }
        cbv [fact_matches] in Hfp1p1. fwd. right.
        cbv [fact_matches]. do 4 eexists. ssplit; try reflexivity.
        -- assumption.
        -- move Hfs1' at bottom.
           epose_dep Hfs1'. specialize' Hfs1'.
           { apply Hf1p1. eassumption. }
           specialize' Hfs1'.
           { apply Hfs2p1. eassumption. }
           apply Hfs1'; assumption.
      + cbv [fact_supported]. apply Exists_exists.
        eexists. split; [eassumption|].
        cbv [fact_supported] in Hfp1. apply Exists_exists in Hfp1. fwd.
        destruct Hfp1p1 as [Hfp1p1|Hfp1p1].
        2: { cbv [fact_matches] in Hfp1p1. fwd. discriminate. }
        left. cbv [extensionally_equal]. ssplit; auto.
        cbv [extensionally_equal] in Hfp1p1. fwd.
        intros. rewrite Hfp1p1p2 by assumption.
        move Hfs1' at bottom.
        epose_dep Hfs1'. specialize' Hfs1'.
        { apply Hf1p1. eassumption. }
        specialize' Hfs1'.
        { apply Hfs2p1. eassumption. }
        apply Hfs1'; assumption.
    - fwd. specialize (Hmr1 _ _ _ ltac:(eassumption) ltac:(eauto) ltac:(eassumption)).
      do 2 eexists. split; [eassumption|]. split; [eassumption|].
      eapply Forall_impl.
      2: { apply Forall_and; [apply Hmr1|apply Hderivp2]. }
      simpl. intros f Hf. fwd. destruct f; fwd.
      + cbv [fact_supported]. apply Exists_exists.
        eexists. split; [eassumption|].
        cbv [fact_supported] in Hfp1. apply Exists_exists in Hfp1. fwd.
        destruct Hfp1p1 as [Hfp1p1|Hfp1p1].
        { exfalso. cbv [extensionally_equal] in Hfp1p1. fwd.
          rewrite Forall_forall in Hml0. apply Hml0 in Hfp1p0. exact Hfp1p0. }
        cbv [fact_matches] in Hfp1p1. fwd. right.
        cbv [fact_matches]. do 4 eexists. ssplit; try reflexivity.
        -- assumption.
        -- move Hfs1' at bottom.
           epose_dep Hfs1'. specialize' Hfs1'.
           { apply Hf1p1. eassumption. }
           specialize' Hfs1'.
           { apply Hfs2p1. eassumption. }
           apply Hfs1'; assumption.
      + cbv [fact_supported]. apply Exists_exists.
        eexists. split; [eassumption|].
        cbv [fact_supported] in Hfp1. apply Exists_exists in Hfp1. fwd.
        destruct Hfp1p1 as [Hfp1p1|Hfp1p1].
        2: { cbv [fact_matches] in Hfp1p1. fwd. discriminate. }
        left. cbv [extensionally_equal]. ssplit; auto.
        cbv [extensionally_equal] in Hfp1p1. fwd.
        intros. rewrite Hfp1p1p2 by assumption.
        move Hfs1' at bottom.
        epose_dep Hfs1'. specialize' Hfs1'.
        { apply Hf1p1. eassumption. }
        specialize' Hfs1'.
        { apply Hfs2p1. eassumption. }
        symmetry. apply Hfs1'; assumption.
  Qed.

  Lemma meta_facts_consistent p Q mf_rel mf_args1 mf_args2 mf_set1 mf_set2 :
    (forall f, Q f -> ~ In (rel_of f) (flat_map concl_rels p)) ->
    (forall mf_rel mf_args1 mf_args2 mf_set1 mf_set2,
        Q (meta_fact mf_rel mf_args1 mf_set1) ->
        Q (meta_fact mf_rel mf_args2 mf_set2) ->
        forall nf_args : list T,
          Forall2 matches mf_args1 nf_args ->
          Forall2 matches mf_args2 nf_args ->
          mf_set1 nf_args <-> mf_set2 nf_args) ->
    meta_rules_valid p ->
    prog_impl p Q (meta_fact mf_rel mf_args1 mf_set1) ->
    prog_impl p Q (meta_fact mf_rel mf_args2 mf_set2) ->
    forall nf_args,
      Forall2 matches mf_args1 nf_args ->
      Forall2 matches mf_args2 nf_args ->
      mf_set1 nf_args <-> mf_set2 nf_args.
  Proof.
    intros H1 H2 H3 H4 H5 ? H6 H7. pose proof meta_facts_consistent' as H'.
    epose proof (H' _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) H4 H5) as H''.
    simpl in H''. apply H''; auto.
  Qed.

  Definition honest_prog p :=
    forall Q,
      (forall f, Q f -> ~ In (rel_of f) (flat_map concl_rels p)) ->
      doesnt_lie Q ->
      doesnt_lie (prog_impl p Q).

  Lemma valid_impl_honest p :
    meta_rules_valid p ->
    honest_prog p.
  Proof.
    intros Hvalid Q Hdisj Q_honest.
    cbv [honest_prog doesnt_lie].
    intros mf_rel mf_args mf_set H_prog_M.
    remember (meta_fact mf_rel mf_args mf_set) as f eqn:Ef.
    revert mf_rel mf_args mf_set Ef.
    induction H_prog_M using prog_impl_ind;
      intros mf_rel mf_args mf_set Ef;
      subst.
    - intros nf_args Hargs. cbv [doesnt_lie consistent] in Q_honest.
      rewrite Q_honest by eassumption. split; intros H'.
      -- apply prog_impl_leaf. assumption.
      -- apply invert_prog_impl in H'. destruct H' as [H'|H']; [assumption|].
         exfalso. fwd. apply Exists_exists in H'p0. fwd.
         eapply Hdisj; [eassumption|]. simpl.
         apply in_flat_map. eexists. split; [eassumption|].
         apply rule_impl_concl_relname_in in H'p0p1.
         exact H'p0p1.
    - apply Exists_exists in H. destruct H as [mr1 [Hmr1_in Hmr1_impl]].
      eapply meta_rules_valid_step'; try eassumption.
      * intros mf_rel' mf_args' mf_set' Hin.
        rewrite Forall_forall in H1. specialize (H1 _ Hin _ _ _ eq_refl).
        exact H1.
      * intros.
        eapply meta_facts_consistent; try eassumption.
        2: { rewrite Forall_forall in H0. auto. }
        clear -Q_honest.
        cbv [doesnt_lie] in Q_honest.
        intros mf_rel mf_args1 mf_args2 mf_set1 mf_set2 H1 H2 nf_args Hargs1 Hargs2.
        apply Q_honest in H1, H2.
        cbv [consistent] in H1, H2. rewrite H1, H2 by assumption. reflexivity.
  Qed.

End __.
Arguments clause : clear implicits.
Arguments meta_clause : clear implicits.
Arguments fact : clear implicits.
Arguments fact_args : clear implicits.
Arguments rule : clear implicits.
Arguments expr : clear implicits.
Hint Constructors non_meta_rule_impl : core.
Hint Constructors rule_impl : core.

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
    (* | |- interp_clause _ _ _ => *)
    (*     eapply interp_clause_subst_more; [|eassumption] *)
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

(*TODO this is reproduced within the section, and idk how to get it out*)
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
