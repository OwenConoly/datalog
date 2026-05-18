From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import Classical_Prop.
From Stdlib Require Import Relations.Relation_Operators Relations.Operators_Properties.

From Datalog Require Import Map Tactics Fp List Dag.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List Datatypes.Option.

Import ListNotations.

Notation "R ^*" := (clos_refl_trans_1n _ R) (format "R ^*").
#[global] Hint Constructors clos_refl_trans_1n : core.

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
      nf = normal_fact R nf_args /\
        mf = meta_fact R mf_args mf_set /\
        Forall2 matches mf_args nf_args /\
        mf_set nf_args.

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
    exists hyps,
      Exists (fun r => non_meta_rule_impl r R args hyps) p /\
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

  Print non_meta_rule_impl.
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
    eexists. split; [eassumption|]. eapply Forall_impl; [|eassumption].
    intros f Hf. eapply fact_supported_ext; eassumption.
  Qed.

  Definition is_meta f :=
    match f with
    | meta_fact _ _ _ => True
    | normal_fact _ _ => False
    end.

  Lemma extensionally_equal_sym f1 f2 :
    extensionally_equal f1 f2 ->
    extensionally_equal f2 f1.
  Proof.
    cbv [extensionally_equal]. intros.
    destruct f1, f2; fwd; auto.
    ssplit; auto. symmetry. auto.
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
        simpl. intros. fwd. cbv [interp_meta_clause extensionally_equal] in *.
        fwd. eauto.
      + intros. rewrite H3 by assumption.
        split; intros; eapply one_step_derives_ext; eauto.
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
    - eapply Exists_impl; [|eassumption]. simpl. intros.
      eapply rule_impl_ext; try eassumption.
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
    eauto using prog_impl_weaken_hyp.
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

  Lemma prog_impl_mf_ext' p Q mf_rel mf_args mf_set mf_set' :
    prog_impl p Q (meta_fact mf_rel mf_args mf_set) ->
    (forall nf_args,
        Forall2 matches mf_args nf_args ->
        mf_set nf_args <-> mf_set' nf_args) ->
    ~Q (meta_fact mf_rel mf_args mf_set) ->
    prog_impl p Q (meta_fact mf_rel mf_args mf_set').
  Proof.
    intros H1 H2 H3. eapply prog_impl_mf_ext in H1. 2: exact H2.
    destruct H1; eauto. exfalso. auto.
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

  Definition vars_of_meta_clause (c : meta_clause) : list var :=
    flat_map vars_of_expr (keep_Some c.(meta_clause_args)).

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
    | H : Exists _ _ |- _ => apply Exists_exists in H; fwd
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

  Definition hyp_rels (r : rule) : list rel :=
    match r with
    | normal_rule _ rule_hyps => map clause_rel rule_hyps
    | meta_rule rule_concls rule_hyps => map meta_clause_rel rule_hyps
    | agg_rule _ _ hyp_rel => [hyp_rel]
    end.

  Definition all_rels (r : rule) : list rel :=
    concl_rels r ++ hyp_rels r.

  Definition concl_vars r :=
    match r with
    | normal_rule rule_concls rule_hyps =>
        flat_map vars_of_clause rule_concls
    | meta_rule rule_concls rule_hyps =>
        flat_map vars_of_meta_clause rule_concls
    | agg_rule _ _ _ => []
    end.

  Definition hyp_vars (r : rule) : list var. Admitted.

  Definition all_vars r := concl_vars r ++ hyp_vars r.

  Definition rule_hyp_args r :=
    match r with
    | normal_rule _ rule_hyps =>
        flat_map clause_args rule_hyps
    | meta_rule _ rule_hyps =>
        keep_Some (flat_map meta_clause_args rule_hyps)
    | agg_rule _ _ _ => []
    end.

  Definition good_rule (r : rule) :=
    forall v, In v (all_vars r) -> In (var_expr v) (rule_hyp_args r).

  Definition good_prog (p : list rule) := Forall good_rule p.

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

  Lemma non_meta_rule_impl_concl_relname_in r R args hyps :
    non_meta_rule_impl r R args hyps ->
    In R (concl_rels r).
  Proof.
    invert 1.
    - repeat invert_stuff. apply in_map_iff. eauto.
    - left. reflexivity.
  Qed.

  Lemma rule_impl_concl_relname_in p r f hyps :
    rule_impl p r f hyps ->
    In (rel_of f) (concl_rels r).
  Proof.
    invert 1.
    - eapply non_meta_rule_impl_concl_relname_in. eassumption.
    - repeat invert_stuff. apply in_map_iff. eauto.
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

  (* Lemma staged_program_prog_impl_with_no_meta_rules p1 p2 Q f : *)
  (*   disjoint_lists (flat_map concl_rels p1) (flat_map hyp_rels p2) -> *)
  (*   prog_impl_with_no_meta_rules (p1 ++ p2) Q f -> *)
  (*   prog_impl_with_no_meta_rules p1 (prog_impl_with_no_meta_rules p2 Q) f. *)
  (* Proof. *)
  (*   intros Hdisj H. induction H. *)
  (*   - apply pftree_leaf. apply pftree_leaf. assumption. *)
  (*   - rename H into Hr. fwd. rewrite Exists_app in Hrp1. *)
  (*     destruct Hrp1 as [Hr|Hr]. *)
  (*     { eapply pftree_step; eauto. } *)
  (*     apply pftree_leaf. eapply pftree_step; eauto. *)
  (*     apply Exists_exists in Hr. fwd. *)
  (*     apply non_meta_rule_impl_hyp_relname_in in Hrp1. *)
  (*     eapply Forall_impl. *)
  (*     2: { apply Forall_and; [apply Hrp1|apply H1]. } *)
  (*     simpl. intros f [Hf1 Hf2]. *)
  (*     invert Hf2; [assumption|]. *)
  (*     exfalso. rename H into HR. fwd. simpl in Hf1. *)
  (*     apply (Hdisj R0). *)
  (*     2: { apply in_flat_map. simpl in Hf1. eauto. } *)
  (*     apply Exists_exists in HRp1. fwd. *)
  (*     apply non_meta_rule_impl_concl_relname_in in HRp1p1. *)
  (*     apply in_flat_map. eauto. *)
  (* Qed. *)

  (* Lemma prog_impl_with_no_meta_rules_subset p1 p2 Q f : *)
  (*   incl p1 p2 -> *)
  (*   prog_impl_with_no_meta_rules p1 Q f -> *)
  (*   prog_impl_with_no_meta_rules p2 Q f. *)
  (* Proof. *)
  (*   intros Hincl H. eapply pftree_weaken; [eassumption|]. *)
  (*   simpl. intros. fwd. eauto using incl_Exists. *)
  (* Qed. *)

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
      + fwd. apply Exists_app in H'p0. destruct H'p0 as [H'p0|H'p0]; eauto 6.
        apply Exists_exists in H'p0. fwd.
        apply non_meta_rule_impl_concl_relname_in in H'p0p1.
        repeat invert_stuff. exfalso. eapply Hout.
        -- apply in_map. eassumption.
        -- apply in_flat_map. eauto.
      + fwd. eexists. rewrite Exists_app. eauto.
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
      + fwd. eexists. rewrite Exists_app. eauto.
      + fwd. eexists. rewrite Exists_app in H'p0. destruct H'p0 as [H'p0|H'p0]; eauto.
        apply Exists_exists in H'p0. fwd.
        apply non_meta_rule_impl_concl_relname_in in H'p0p1.
        repeat invert_stuff. exfalso. eapply Hout.
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
      split; intros; fwd.
      + eexists. split; eauto. rewrite Exists_exists in *. fwd. edestruct Hiff; eauto.
      + eexists. split; eauto. rewrite Exists_exists in *. fwd. edestruct Hiff; eauto.
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

  Lemma one_step_derives_subset p1 p2 hyps R args :
    incl p1 p2 ->
    (forall r', In r' p2 -> In r' p1 \/ disjoint_lists (flat_map meta_concl_rels p1) (concl_rels r')) ->
    In R (flat_map meta_concl_rels p1) ->
    one_step_derives p1 hyps R args <-> one_step_derives p2 hyps R args.
  Proof.
    intros Hincl Hdisj HR. cbv [one_step_derives one_step_derives0].
    split; intros; fwd.
    - eexists. split; eauto. eapply incl_Exists; eassumption.
    - apply Exists_exists in Hp0. fwd.
      destruct (Hdisj _ ltac:(eassumption)) as [Hr_in_p1 | Hdisj_r'].
      + eexists. rewrite Exists_exists. eauto.
      + exfalso. eapply Hdisj_r'; [exact HR |].
        eapply non_meta_rule_impl_concl_relname_in; eassumption.
  Qed.

  Lemma rule_impl_subset p1 p2 r f hyps :
    incl p1 p2 ->
    (forall r', In r' p2 -> In r' p1 \/ disjoint_lists (flat_map meta_concl_rels p1) (concl_rels r')) ->
    In r p1 ->
    rule_impl (one_step_derives p1) r f hyps ->
    rule_impl (one_step_derives p2) r f hyps.
  Proof.
    intros Hincl Hdisj Hrin Hrule.
    inversion Hrule; subst.
    - constructor. assumption.
    - econstructor; [eassumption | eassumption |].
      intros args'' Hargs''.
      rewrite H1 by assumption.
      apply one_step_derives_subset; auto.
      apply in_flat_map. exists (meta_rule rule_concls rule_hyps).
      split; [exact Hrin |].
      simpl. apply Exists_exists in H. destruct H as [c [Hcin Hc]].
      cbv [interp_meta_clause] in Hc.
      destruct Hc as [mf_args [mf_set [H_forall2 H_eq]]].
      inversion H_eq; subst.
      apply in_map_iff. exists c. split; [reflexivity | exact Hcin].
  Qed.

  Lemma prog_impl_subset p1 p2 Q f :
    incl p1 p2 ->
    (forall r, In r p2 ->
          In r p1 \/
            disjoint_lists (flat_map meta_concl_rels p1) (concl_rels r)) ->
    prog_impl p1 Q f ->
    prog_impl p2 Q f.
  Proof.
    intros Hincl Hdisj Hprog.
    induction Hprog using prog_impl_ind.
    - apply prog_impl_leaf. assumption.
    - apply Exists_exists in H. destruct H as [r [Hrin Hrule]].
      eapply prog_impl_step.
      + apply Exists_exists. exists r. split.
        * apply Hincl. exact Hrin.
        * eapply rule_impl_subset; eassumption.
      + assumption.
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
  Proof. cbv [all_rels]. auto with incl. Qed.
  Hint Resolve concl_rels_incl_all_rels : incl.

  Lemma hyp_rels_incl_all_rels r :
    incl (hyp_rels r) (all_rels r).
  Proof. cbv [all_rels]. auto with incl. Qed.
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

  (*just like fact_supported, except it puts no constraint on the sets*)
  Definition fact_potentially_supported (mhyps : list fact) (f : fact) : Prop :=
    match f with
    | normal_fact R' nf_args' =>
        exists mf_args' mf_set',
        In (meta_fact R' mf_args' mf_set') mhyps /\
          Forall2 matches mf_args' nf_args'
    | meta_fact R' mf_args' _ =>
        exists mf_set',
        In (meta_fact R' mf_args' mf_set') mhyps
    end.

  Definition meta_rules_valid p :=
    forall R mf_args mf_set mhyps mr,
      In mr p ->
      rule_impl (one_step_derives p) mr (meta_fact R mf_args mf_set) mhyps ->
      forall nr args hyps,
        In nr p ->
        rule_impl (one_step_derives p) nr (normal_fact R args) hyps ->
        Forall2 matches mf_args args ->
        Forall (fact_potentially_supported mhyps) hyps.

  Definition consistent mf_rel mf_args mf_set S :=
    forall nf_args,
      Forall2 matches mf_args nf_args ->
      mf_set nf_args <-> S (normal_fact mf_rel nf_args).

  Hint Unfold extensionally_equal : core.
  Lemma extensionally_equal_refl : forall f,
    extensionally_equal f f.
  Proof. destruct f; auto. Qed.

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
      { eapply Exists_impl; [|eassumption]. simpl. eauto. }
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
      eexists. rewrite Exists_exists. split; [eauto|].
      eapply Forall_impl.
      2: { apply Forall_and; [exact Hvalid|exact Hnf_argsp1]. }
      clear hyps' Hvalid Hnf_argsp1 H7.
      simpl. intros f Hf. fwd.
      cbv [fact_potentially_supported] in Hfp0. destruct f; fwd.
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
  Proof. cbv [doesnt_lie honest_args consistent args_consistent]. eauto. Qed.

  (*this is a lemma about pairwise properties, because that is all that i need to reasona baout.
    it is also true for n-wise properties, or even properties of arbitrary-length finite lists.
   it is not true for infinite sets. *)

  Inductive is_flat_pftree {U} Q (P : U -> list U -> _) : list U -> Prop :=
  | is_flat_pftree_nil : is_flat_pftree _ _ []
  | is_flat_pftree_cons x xs :
    Q x \/ (exists l, P x l /\ incl l xs) ->
    is_flat_pftree _ _ xs ->
    is_flat_pftree _ _ (x :: xs).
  Hint Constructors is_flat_pftree : core.

  Lemma is_flat_pftree_app U (Q : U -> _) P xs1 xs2 :
    is_flat_pftree Q P xs1 ->
    is_flat_pftree Q P xs2 ->
    is_flat_pftree Q P (xs1 ++ xs2).
  Proof.
    intros H1 H2. induction H1; simpl; auto.
    constructor; auto. destruct H as [H|H]; auto.
    fwd. right. eexists. split; [eassumption|].
    auto with incl.
  Qed.

  Lemma is_flat_pftree_concat U (Q : U -> _) P xss :
    Forall (is_flat_pftree Q P) xss ->
    is_flat_pftree Q P (concat xss).
  Proof. induction 1; simpl; auto using is_flat_pftree_app. Qed.

  Lemma pftree_impl_exists_flat_pftree U (P : U -> list U -> _) Q x :
    pftree P Q x ->
    exists xs,
      is_flat_pftree Q P xs /\ In x xs.
  Proof.
    induction 1.
    - exists [x]. simpl. auto.
    - apply Forall_exists_r_Forall2 in H1. fwd.
      exists (x :: concat ys). simpl. split; auto. constructor.
      + right. eexists. split; [eassumption|].
        apply Forall2_forget_r in H1. cbv [incl]. apply Forall_forall.
        eapply Forall_impl; [|eassumption].
        simpl. intros. fwd. rewrite in_concat. eauto.
      + apply is_flat_pftree_concat.
        apply Forall2_forget_l in H1. eapply Forall_impl; [|eassumption].
        simpl. intros. fwd. assumption.
  Qed.

  Lemma is_flat_pftree_pftree U (P : U -> _ -> _) Q xs :
    is_flat_pftree Q P xs ->
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
        is_flat_pftree Q P (x :: xs) ->
        (forall y, In y (x :: xs) -> R x y)) ->
    forall xs,
      is_flat_pftree Q P xs ->
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
        is_flat_pftree Q P (x :: xs) ->
        (forall y, In y (x :: xs) -> R x y)) ->
    forall x1 x2,
      pftree P Q x1 ->
      pftree P Q x2 ->
      R x1 x2.
  Proof.
    intros ? ? x1 x2 H1 H2. apply pftree_impl_exists_flat_pftree in H1, H2.
    fwd. eapply is_flat_pftree_app in H1p0; [|exact H2p0].
    clear H2p0. eapply stepping_induction'; try eassumption.
    1,2: apply in_app_iff; auto.
  Qed.

  Lemma is_flat_pftree_forall_step U (P : U -> _ -> _) Q xs :
    is_flat_pftree Q P xs ->
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
    { apply is_flat_pftree_pftree in Hfs2. rewrite Forall_forall in Hfs2.
      apply Hfs2 in Hf2.
      apply invert_prog_impl in Hf2. destruct Hf2 as [Hf2|Hf2]; eauto.
      exfalso. fwd. apply Exists_exists in Hf2p0. fwd.
      apply rule_impl_concl_relname_in in Hf2p0p1. simpl in Hf2p0p1.
      eapply Hinp; eauto. simpl. apply in_flat_map. eauto. }
    apply is_flat_pftree_forall_step in Hfs2. rewrite Forall_forall in Hfs2.
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
    - fwd. apply Exists_exists in Hderivp0. fwd.
      specialize (Hmr2 _ _ _ ltac:(eassumption) ltac:(eauto) ltac:(eassumption)).
      eexists. rewrite Exists_exists. split; [eauto|].
      eapply Forall_impl.
      2: { apply Forall_and; [apply Hmr2|apply Hderivp1]. }
      simpl. intros f Hf.
      cbv [fact_potentially_supported] in Hf. fwd. destruct f; fwd.
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
    - fwd. apply Exists_exists in Hderivp0. fwd.
      specialize (Hmr1 _ _ _ ltac:(eassumption) ltac:(eauto) ltac:(eassumption)).
      eexists. rewrite Exists_exists. split; [eauto|].
      eapply Forall_impl.
      2: { apply Forall_and; [apply Hmr1|apply Hderivp1]. }
      simpl. intros f Hf.
      cbv [fact_potentially_supported] in Hf. fwd. destruct f; fwd.
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

  Definition good_inputs p Q :=
    (forall f, Q f -> ~ In (rel_of f) (flat_map concl_rels p)) /\
      doesnt_lie Q.


  Definition honest_prog p :=
    forall Q,
      good_inputs p Q ->
      doesnt_lie (prog_impl p Q).

  Lemma valid_impl_honest p :
    meta_rules_valid p ->
    honest_prog p.
  Proof.
    intros Hvalid Q [Hdisj Q_honest].
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
        Check meta_facts_consistent.
        eapply meta_facts_consistent; try eassumption.
        2: { rewrite Forall_forall in H0. auto. }
        clear -Q_honest.
        cbv [doesnt_lie] in Q_honest.
        intros mf_rel mf_args1 mf_args2 mf_set1 mf_set2 H1 H2 nf_args Hargs1 Hargs2.
        apply Q_honest in H1, H2.
        cbv [consistent] in H1, H2. rewrite H1, H2 by assumption. reflexivity.
  Qed.

  Lemma use_honest_prog p Q mf_rel mf_args mf_set :
    honest_prog p ->
    good_inputs p Q ->
    prog_impl p Q (meta_fact mf_rel mf_args mf_set) ->
    Q (meta_fact mf_rel mf_args mf_set) \/
      prog_impl p Q (meta_fact mf_rel mf_args (fun args => prog_impl p Q (normal_fact mf_rel args))).
  Proof.
    intros H1 H2 H3.
    eapply prog_impl_mf_ext; [eassumption|].
    cbv [honest_prog] in H1. apply H1; assumption.
  Qed.

  (*ugh idk what to say here*)
  (* Lemma prog_impl_subset'' (p1 p2 : list rule) Q f : *)
  (*   doesnt_lie p1 Q -> *)
  (*   doesnt_lie p2 Q -> *)
  (*   (forall x, In x p1 -> In x p2) -> *)
  (*   prog_impl p1 Q f -> *)
  (*   prog_impl p2 Q f. *)
  (* Proof. *)
  (*   intros H1 H2 Hsub H. eapply pftree_weaken; simpl; eauto. simpl. *)
  (*   intros ? ? Hr. apply Exists_exists in Hr. apply Exists_exists. fwd. *)
  (*   eexists. split; [eauto|]. *)
  (* Abort. *)


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

  Inductive non_meta_rule :=
  | nmr_normal (_ _ : list clause)
  | nmr_agg (_ : rel) (_ : aggregator) (_ : rel).

  Definition rule_of nmr :=
    match nmr with
    | nmr_normal concls hyps => normal_rule concls hyps
    | nmr_agg concl_rel agg hyp_rel => agg_rule concl_rel agg hyp_rel
    end.

  Inductive dfact :=
  | normal_dfact (nf_rel : rel) (nf_args : list T)
  | meta_dfact (mf_rel : rel) (mf_args : list (option T)) (source : option nat) (expected_msgs : nat) (*number of messages that node "source" will ever send about mf_rel*).

  Record prog :=
    { meta_rules : list (list meta_clause * list meta_clause);
      non_meta_rules : list non_meta_rule }.

  Record rule_state :=
    { known_facts : list dfact;
      waiting_facts : list dfact;
      sent_facts : list dfact }.

  Definition state :=
    list rule_state.

  Context (is_input : rel -> bool).
  Context (p : prog).

  Definition rules_of : list rule :=
    map (fun '(c, h) => meta_rule c h) p.(meta_rules) ++ map rule_of p.(non_meta_rules).

  Definition stepOne {T} (do_step : T -> T -> Prop) : list T -> list T -> Prop :=
    fun start finish =>
      exists l1 x y l2,
        start = l1 ++ x :: l2 /\
          finish = l1 ++ y :: l2 /\
          do_step x y.

  Definition stepWithLabel {T U} (do_step : U -> T -> T -> Prop) (labels : list U) : list T -> list T -> Prop :=
    fun start finish =>
      exists l1 n x y l2,
        combine labels start = l1 ++ (n, x) :: l2 /\
          finish = map snd l1 ++ y :: map snd l2 /\
          do_step n x y.

  Definition learn_fact_at_rule (s1 s2 : rule_state) : Prop :=
    exists l1 x l2,
      s2.(known_facts) = x :: s1.(known_facts) /\
        s1.(waiting_facts) = l1 ++ x :: l2 /\
        s2.(waiting_facts) = l1 ++ l2 /\
        s2.(sent_facts) = s1.(sent_facts).

  Definition expect_num_R_facts R mf_args known_facts num :=
    if is_input R then
      In (meta_dfact R mf_args None num) known_facts
    else
      exists expected_msgss,
        Forall2 (fun n expected_msgs => In (meta_dfact R mf_args (Some n) expected_msgs) known_facts) (seq O (length p.(non_meta_rules))) expected_msgss /\
          num = fold_left Nat.add expected_msgss O.

  Definition dfact_matches mf_rel mf_args nf :=
    exists nf_args,
      nf = normal_dfact mf_rel nf_args /\
        Forall2 matches mf_args nf_args.

  Definition knows_datalog_fact (dfacts : list dfact) (f : fact) :=
    match f with
    | normal_fact nf_rel nf_args =>
        In (normal_dfact nf_rel nf_args) dfacts
    | meta_fact mf_rel mf_args mf_set =>
        exists num,
        expect_num_R_facts mf_rel mf_args dfacts num /\
          Existsn (dfact_matches mf_rel mf_args) num dfacts /\
          (forall nf_args,
              Forall2 matches mf_args nf_args ->
              mf_set nf_args <-> In (normal_dfact mf_rel nf_args) dfacts)
    end.

  Definition can_deduce_normal_fact (r : non_meta_rule) (known_facts : list dfact) nf_rel nf_args :=
    exists hyps,
      non_meta_rule_impl (rule_of r) nf_rel nf_args hyps /\
        Forall (knows_datalog_fact known_facts) hyps.

  Definition can_deduce_meta_fact (mf_concls mf_hyps : list meta_clause) (r : non_meta_rule) (source : nat) (sent_facts : list dfact) (known_facts : list dfact) (result : dfact) :=
    exists ctx hyps mf_rel mf_args mf_cnt,
      result = meta_dfact mf_rel mf_args (Some source) mf_cnt /\
        Existsn (dfact_matches mf_rel mf_args) mf_cnt sent_facts /\
        Exists (fun c => interp_meta_clause ctx c (meta_fact mf_rel mf_args (fun _ => False))) mf_concls /\
        Forall2 (interp_meta_clause ctx) mf_hyps hyps /\
        Forall (knows_datalog_fact known_facts) hyps /\
        (forall nf_args,
            can_deduce_normal_fact r known_facts mf_rel nf_args ->
            Forall2 matches mf_args nf_args ->
            In (normal_dfact mf_rel nf_args) known_facts).

  Definition meta_facts_correct_at_rule mrs n rs r :=
    forall R mf_args num,
      In (meta_dfact R mf_args (Some n) num) rs.(sent_facts) ->
      exists mf_concls mf_hyps,
        In (mf_concls, mf_hyps) mrs /\
          can_deduce_meta_fact mf_concls mf_hyps r n rs.(sent_facts) rs.(known_facts) (meta_dfact R mf_args (Some n) num).

  Definition meta_facts_correct (s : state) :=
    Forall3 (fun r rs n =>
               meta_facts_correct_at_rule p.(meta_rules) n rs r)
            p.(non_meta_rules) s (seq 0 (length s)).

  Definition add_waiting_fact f (rs : rule_state) :=
    {| known_facts := rs.(known_facts);
      waiting_facts := f :: rs.(waiting_facts);
      sent_facts := rs.(sent_facts); |}.

  Definition send_fact f rs :=
    {| known_facts := rs.(known_facts);
      waiting_facts := rs.(waiting_facts);
      sent_facts := f :: rs.(sent_facts) |}.

  Inductive comp_step : state -> state -> Prop :=
  | learn_fact s1 s2 :
    stepOne learn_fact_at_rule s1 s2 ->
    comp_step s1 s2
  | fire_normal_rule nf_rel nf_args s1 s2 :
    stepWithLabel (fun '(r, n) rs rs' =>
                     can_deduce_normal_fact r rs.(known_facts) nf_rel nf_args /\
                       (forall mf_args num,
                           In (meta_dfact nf_rel mf_args (Some n) num) rs.(sent_facts) ->
                           Forall2 matches mf_args nf_args ->
                           False) /\
                       rs' = send_fact (normal_dfact nf_rel nf_args) rs)
      (combine p.(non_meta_rules) (seq O (length s1))) s1 s2 ->
    comp_step s1 (map (add_waiting_fact (normal_dfact nf_rel nf_args)) s2)
  | fire_meta_rule mf_concls mf_hyps new_fact s1 s2 :
    In (mf_concls, mf_hyps) p.(meta_rules) ->
    stepWithLabel (fun '(r, n) rs rs' =>
                     can_deduce_meta_fact mf_concls mf_hyps r n rs.(sent_facts) rs.(known_facts) new_fact /\
                       rs' = send_fact new_fact rs)
      (combine p.(non_meta_rules) (seq O (length s1))) s1 s2 ->
    comp_step s1 (map (add_waiting_fact new_fact) s2).

  Definition is_input_fact f :=
    match f with
    | normal_dfact R _ => is_input R
    | meta_dfact R _ None _ => is_input R
    | meta_dfact _ _ (Some _) _ => false
    end.

  Definition inputs := list dfact.

  Inductive inp_step : state -> inputs -> state -> inputs -> Prop :=
  | Receive s1 inps1 new_fact :
    is_input_fact new_fact = true ->
    inp_step s1 inps1 (map (add_waiting_fact new_fact) s1) (new_fact :: inps1).

  Context (Hmeta_rules : meta_rules_valid rules_of).

  Definition good_non_meta_rule (r : non_meta_rule) : Prop :=
    match r with
    | nmr_normal cs _ => Forall (fun c => is_input c.(clause_rel) = false) cs
    | nmr_agg concl _ _ => is_input concl = false
    end.

  Context (Hp_input : Forall good_non_meta_rule p.(non_meta_rules)).

  Definition good_meta_rule_inputs (mr : list meta_clause * list meta_clause) : Prop :=
    let '(concls, _) := mr in
    Forall (fun c => is_input c.(meta_clause_rel) = false) concls.

  Context (Hp_meta_input : Forall good_meta_rule_inputs p.(meta_rules)).

  Definition rule_has_dfact rs f :=
    In f rs.(known_facts) \/ In f rs.(waiting_facts).

  Definition knows_dfact (s : state) f :=
    Exists (fun rs => rule_has_dfact rs f) s.

  Definition nth_sat {T} (l : list T) n (P : T -> Prop) :=
    match nth_error l n with
    | Some x => P x
    | None => False
    end.

  Definition good_input_facts input_facts :=
    Forall (fun f => is_input_fact f = true) input_facts /\
      (forall R mf_args num,
          In (meta_dfact R mf_args None num) input_facts ->
          (forall num0, In (meta_dfact R mf_args None num0) input_facts -> num0 = num) /\
            exists num',
              num' <= num /\
                Existsn (dfact_matches R mf_args) num' input_facts).

  Definition sane_state (input_facts : list dfact) (s : state) :=
    length s = length p.(non_meta_rules) /\
    (forall R mf_args num,
        knows_dfact s (meta_dfact R mf_args None num) ->
        In (meta_dfact R mf_args None num) input_facts) /\
      (forall R mf_args n num,
          knows_dfact s (meta_dfact R mf_args (Some n) num) ->
          nth_sat s n (fun rs =>
                         Existsn (dfact_matches R mf_args) num rs.(sent_facts) /\
                         In (meta_dfact R mf_args (Some n) num) rs.(sent_facts))) /\
      (forall f,
          knows_dfact s f ->
          Forall (fun rs => rule_has_dfact rs f) s) /\
      (forall R mf_args,
        exists msgs_sents num_inp,
          Forall2 (fun rs msgs_sent =>
                     Existsn (dfact_matches R mf_args) msgs_sent rs.(sent_facts))
            s msgs_sents /\
            Existsn (dfact_matches R mf_args) num_inp input_facts /\
            Forall (fun rs_n =>
                      exists num_known num_wait,
                        Existsn (dfact_matches R mf_args) num_known rs_n.(known_facts) /\
                          Existsn (dfact_matches R mf_args) num_wait rs_n.(waiting_facts) /\
                          num_known + num_wait = num_inp + fold_left Nat.add msgs_sents O) s) /\
      (forall R,
          is_input R = true ->
          (forall mf_args, Forall (fun rs => Existsn (dfact_matches R mf_args) O rs.(sent_facts)) s) /\
            (forall mf_args n num, ~knows_dfact s (meta_dfact R mf_args (Some n) num))).

  Lemma learn_fact_at_rule_rule_has_dfact rs1 rs2 :
    learn_fact_at_rule rs1 rs2 ->
    forall f, rule_has_dfact rs1 f <-> rule_has_dfact rs2 f.
  Proof.
    cbv [learn_fact_at_rule rule_has_dfact]. intros H f. fwd.
    rewrite Hp0, Hp1, Hp2. simpl. repeat rewrite in_app_iff. simpl.
    intuition congruence.
  Qed.

  Lemma learn_fact_at_rule_sent rs1 rs2 :
    learn_fact_at_rule rs1 rs2 ->
    rs2.(sent_facts) = rs1.(sent_facts).
  Proof. cbv [learn_fact_at_rule]. intros H. fwd. assumption. Qed.

  Lemma exists_swap A (P : A -> Prop) l1 x y l2 :
    (P x -> P y) ->
    Exists P (l1 ++ x :: l2) -> Exists P (l1 ++ y :: l2).
  Proof.
    intros H Hex.
    apply Exists_app in Hex. apply Exists_app. destruct Hex as [Hex|Hex]; auto.
    right. apply Exists_cons in Hex. apply Exists_cons.
    destruct Hex as [Hx|Hl2]; auto.
  Qed.

  Lemma forall_swap A (P : A -> Prop) l1 x y l2 :
    (P x -> P y) ->
    Forall P (l1 ++ x :: l2) -> Forall P (l1 ++ y :: l2).
  Proof.
    intros H Hf.
    apply Forall_app in Hf. apply Forall_app. destruct Hf as [Hf1 Hf2]. split; auto.
    apply Forall_cons_iff in Hf2. apply Forall_cons_iff.
    destruct Hf2 as [Hx Hl2]. auto.
  Qed.

  Lemma nth_sat_swap A l1 (x y : A) l2 (P : A -> Prop) k :
    (P x -> P y) ->
    nth_sat (l1 ++ x :: l2) k P -> nth_sat (l1 ++ y :: l2) k P.
  Proof.
    intros H. cbv [nth_sat].
    destruct (Nat.lt_ge_cases k (length l1)) as [Hk|Hk].
    - rewrite ! nth_error_app1 by assumption. auto.
    - rewrite ! nth_error_app2 by assumption.
      destruct (k - length l1) eqn:E; simpl; auto.
  Qed.

  Lemma forall2_swap_l A B l1 (x y : A) l2 (ms : list B) (P : A -> B -> Prop) :
    (forall m, P x m -> P y m) ->
    Forall2 P (l1 ++ x :: l2) ms ->
    Forall2 P (l1 ++ y :: l2) ms.
  Proof.
    intros H Hf.
    apply Forall2_app_inv_l in Hf. fwd. invert_list_stuff.
    apply Forall2_app; [assumption|]. constructor; auto.
  Qed.

  Lemma learn_fact_at_rule_perm rs1 rs2 :
    learn_fact_at_rule rs1 rs2 ->
    Permutation (rs1.(known_facts) ++ rs1.(waiting_facts))
                (rs2.(known_facts) ++ rs2.(waiting_facts)).
  Proof.
    cbv [learn_fact_at_rule]. intros H. fwd.
    rewrite Hp0, Hp1, Hp2. simpl.
    eapply perm_trans.
    - apply Permutation_app_head. apply Permutation_sym. apply Permutation_middle.
    - apply Permutation_sym. apply Permutation_middle.
  Qed.

  Lemma learn_fact_at_rule_existsn_split (P : dfact -> Prop) rs1 rs2 :
    learn_fact_at_rule rs1 rs2 ->
    forall num_k num_w,
      Existsn P num_k rs1.(known_facts) ->
      Existsn P num_w rs1.(waiting_facts) ->
      exists num_k' num_w',
        Existsn P num_k' rs2.(known_facts) /\
        Existsn P num_w' rs2.(waiting_facts) /\
        num_k' + num_w' = num_k + num_w.
  Proof.
    intros H num_k num_w Hk Hw.
    pose proof (learn_fact_at_rule_perm _ _ H) as Hperm.
    pose proof (Existsn_app _ _ _ _ _ Hk Hw) as Hcat.
    eapply Existsn_perm in Hcat. 2: exact Hperm.
    apply Existsn_split in Hcat. fwd. eauto.
  Qed.

  Lemma nth_error_app_middle A (l1 : list A) x l2 n :
    nth_error (l1 ++ x :: l2) n =
    match Nat.compare n (length l1) with
    | Lt => nth_error l1 n
    | Eq => Some x
    | Gt => nth_error l2 (n - length l1 - 1)
    end.
  Proof.
    destruct (Nat.compare_spec n (length l1)) as [-> | Hlt | Hgt].
    - rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
    - rewrite nth_error_app1 by assumption. reflexivity.
    - rewrite nth_error_app2 by lia.
      destruct (n - length l1) eqn:E; [exfalso; lia|].
      simpl. f_equal. lia.
  Qed.

  Lemma nth_sat_app_middle A (l1 : list A) x l2 n P :
    nth_sat (l1 ++ x :: l2) n P =
    match Nat.compare n (length l1) with
    | Lt => nth_sat l1 n P
    | Eq => P x
    | Gt => nth_sat l2 (n - length l1 - 1) P
    end.
  Proof.
    cbv [nth_sat]. rewrite nth_error_app_middle.
    destruct (Nat.compare_spec n (length l1)) as [-> | Hlt | Hgt]; reflexivity.
  Qed.

  Lemma nth_sat_map A B (f : A -> B) l n (P : B -> Prop) :
    nth_sat (map f l) n P <-> nth_sat l n (fun x => P (f x)).
  Proof.
    cbv [nth_sat]. rewrite nth_error_map.
    destruct (nth_error l n); reflexivity.
  Qed.

  Lemma knows_dfact_add_waiting F s f :
    knows_dfact (map (add_waiting_fact F) s) f -> f = F \/ knows_dfact s f.
  Proof.
    cbv [knows_dfact rule_has_dfact]. intros HE. apply Exists_exists in HE.
    destruct HE as (rs' & Hin' & [Hk | Hw]).
    - apply in_map_iff in Hin'. destruct Hin' as (rs & Heq & Hin); subst rs'.
      cbv [add_waiting_fact] in Hk; simpl in Hk.
      right. apply Exists_exists. exists rs. auto.
    - apply in_map_iff in Hin'. destruct Hin' as (rs & Heq & Hin); subst rs'.
      cbv [add_waiting_fact] in Hw; simpl in Hw.
      destruct Hw as [<-|Hw]; auto.
      right. apply Exists_exists. exists rs. auto.
  Qed.

  Lemma knows_dfact_after_step F l1 x l2 f :
    knows_dfact (map (add_waiting_fact F) (l1 ++ send_fact F x :: l2)) f ->
    f = F \/ knows_dfact (l1 ++ x :: l2) f.
  Proof.
    intros HE. apply knows_dfact_add_waiting in HE.
    destruct HE as [|HE]; [auto|]. right.
    cbv [knows_dfact rule_has_dfact send_fact] in *.
    rewrite Exists_app in HE |- *. simpl in HE |- *.
    rewrite Exists_cons in HE |- *. intuition.
  Qed.

  Lemma rule_has_dfact_afw F rs f :
    rule_has_dfact rs f -> rule_has_dfact (add_waiting_fact F rs) f.
  Proof. cbv [rule_has_dfact add_waiting_fact]; simpl; intuition. Qed.

  Lemma rule_has_dfact_afw_F F rs :
    rule_has_dfact (add_waiting_fact F rs) F.
  Proof. cbv [rule_has_dfact add_waiting_fact]; simpl; auto. Qed.

  Lemma fold_left_add_from_0 (l : list nat) (n : nat) :
    fold_left Nat.add l n = fold_left Nat.add l 0 + n.
  Proof.
    revert n. induction l as [|a l IH]; intros n; simpl; [reflexivity|].
    rewrite IH, (IH a). lia.
  Qed.

  Lemma can_deduce_implies_not_input r kf nf_rel nf_args :
    good_non_meta_rule r ->
    can_deduce_normal_fact r kf nf_rel nf_args ->
    is_input nf_rel = false.
  Proof.
    intros Hgood (hyps & Himpl & _).
    destruct r as [cs hs | concl agg hyp]; simpl in Himpl, Hgood.
    - invert Himpl.
      match goal with
      | H : Exists _ _ |- _ =>
        apply Exists_exists in H; destruct H as (c & Hin_c & Hint)
      end.
      cbv [interp_clause] in Hint. destruct Hint as (nfargs & _ & Heq).
      injection Heq as -> ->.
      rewrite Forall_forall in Hgood. apply Hgood; exact Hin_c.
    - invert Himpl. exact Hgood.
  Qed.

  Lemma step_preserves_sane inputs s1 s2 :
    good_input_facts inputs ->
    sane_state inputs s1 ->
    comp_step s1 s2 ->
    sane_state inputs s2.
  Proof.
    intros Hinp Hsane Hstep.
    destruct Hsane as (Hlen & Hmf_inp & Hmf_sent & Heverywhere & Hcount & Hinp_sane).
    invert Hstep.
    - cbv [stepOne] in H. fwd.
      pose proof (learn_fact_at_rule_rule_has_dfact _ _ Hp2) as Hpres_rhd.
      pose proof (learn_fact_at_rule_sent _ _ Hp2) as Hpres_sent.
      assert (Hkd_bw : forall f, knows_dfact (l1 ++ y :: l2) f -> knows_dfact (l1 ++ x :: l2) f).
      { intros f. cbv [knows_dfact]. apply exists_swap. apply Hpres_rhd. }
      cbv [sane_state]. ssplit.
      + rewrite ! length_app in *. simpl in *. lia.
      + intros R mf_args num Hk. apply Hkd_bw in Hk. eapply Hmf_inp. eassumption.
      + intros R mf_args n num Hk. apply Hkd_bw in Hk.
        specialize (Hmf_sent _ _ _ _ Hk).
        eapply nth_sat_swap; [|exact Hmf_sent].
        intros. fwd. rewrite Hpres_sent. split; assumption.
      + intros f Hk. pose proof Hk as Hk0. apply Hkd_bw in Hk0.
        specialize (Heverywhere _ Hk0).
        eapply forall_swap; [|exact Heverywhere].
        cbv beta. apply Hpres_rhd.
      + intros R mf_args.
        specialize (Hcount R mf_args). fwd.
        exists msgs_sents, num_inp. ssplit.
        * eapply forall2_swap_l; [|exact Hcountp0].
          intros msg He. rewrite Hpres_sent. assumption.
        * assumption.
        * eapply forall_swap; [|exact Hcountp2].
          cbv beta. intros (num_k & num_w & Hk_x & Hw_x & Hsum_x).
          pose proof (learn_fact_at_rule_existsn_split _ _ _ Hp2 _ _ Hk_x Hw_x)
            as (num_k' & num_w' & Hk_y & Hw_y & Hsum_y).
          do 2 eexists. ssplit; eauto. lia.
      + intros R HR. specialize (Hinp_sane R HR). fwd.
        split.
        * intros mf_args. specialize (Hinp_sanep0 mf_args).
          eapply forall_swap; [|exact Hinp_sanep0].
          cbv beta. intros He. rewrite Hpres_sent. assumption.
        * intros mf_args n num Hk. apply Hkd_bw in Hk.
          exact (Hinp_sanep1 _ _ _ Hk).
    - cbv [stepWithLabel] in H. fwd. destruct n as [r k].
      destruct Hp2 as (Hcan & Hnometa & Hyq). subst y.
      assert (Hlc : length (combine (non_meta_rules p) (seq 0 (length s1))) = length s1).
      { rewrite length_combine, length_seq. lia. }
      assert (Hs1_eq : s1 = map snd l1 ++ x :: map snd l2).
      { apply (f_equal (map snd)) in Hp0.
        rewrite map_combine_snd in Hp0 by assumption.
        rewrite map_app in Hp0. simpl in Hp0. exact Hp0. }
      assert (Hlen_lt : length l1 < length s1).
      { rewrite Hs1_eq, length_app, ! length_map. simpl. lia. }
      assert (Hk_eq : k = length l1).
      { assert (Hlen_seq : length (non_meta_rules p) = length (seq 0 (length s1))).
        { rewrite length_seq. lia. }
        pose proof Hp0 as Hp0a.
        apply (f_equal (map fst)) in Hp0a.
        rewrite map_app in Hp0a. simpl in Hp0a.
        rewrite map_combine_fst in Hp0a by assumption.
        apply (f_equal (map snd)) in Hp0a.
        rewrite map_app in Hp0a. simpl in Hp0a.
        rewrite map_combine_snd in Hp0a by assumption.
        pose proof (f_equal (fun ll => nth_error ll (length l1)) Hp0a) as HnE.
        cbv beta in HnE.
        rewrite nth_error_app_middle in HnE.
        rewrite ! length_map in HnE.
        rewrite Nat.compare_refl in HnE.
        rewrite nth_error_seq in HnE.
        assert (E : length l1 <? length s1 = true) by (apply Nat.ltb_lt; lia).
        rewrite E in HnE.
        injection HnE as ->. lia. }
      assert (Hin_r : In r p.(non_meta_rules)).
      { assert (Hin_outer : In (r, k, x) (combine (combine (non_meta_rules p) (seq 0 (length s1))) s1)).
        { rewrite Hp0. apply in_or_app. right. simpl. auto. }
        apply in_combine_l in Hin_outer.
        apply in_combine_l in Hin_outer. exact Hin_outer. }
      assert (Hnf_noninput : is_input nf_rel = false).
      { rewrite Forall_forall in Hp_input. apply Hp_input in Hin_r.
        eapply can_deduce_implies_not_input; eassumption. }
      rewrite Hs1_eq in Hmf_inp, Hmf_sent, Heverywhere, Hcount, Hinp_sane, Hlen.
      cbv [sane_state]. ssplit.
      + rewrite length_map, length_app in *. cbn [length] in *.
        rewrite ! length_map in *. lia.
      + intros R mf_args num Hk.
        apply knows_dfact_after_step in Hk.
        destruct Hk as [Hk | Hk]; [discriminate|].
        eapply Hmf_inp; eassumption.
      + intros R mf_args n' num Hk.
        apply knows_dfact_after_step in Hk.
        destruct Hk as [Hk | Hk]; [discriminate|].
        specialize (Hmf_sent _ _ _ _ Hk).
        rewrite nth_sat_map. cbv beta.
        rewrite nth_sat_app_middle. rewrite length_map.
        rewrite nth_sat_app_middle in Hmf_sent. rewrite length_map in Hmf_sent.
        destruct (Nat.compare_spec n' (length l1)) as [Hl' | Hl' | Hl'].
        * subst n'.
          destruct Hmf_sent as (HE & HI).
          cbv [add_waiting_fact send_fact]; simpl.
          assert (Hnmatch : ~ dfact_matches R mf_args (normal_dfact nf_rel nf_args)).
          { intros (nf_args0 & Heqf & Hmatch).
            injection Heqf as H_rel H_args. subst R nf_args0.
            eapply Hnometa with (mf_args := mf_args) (num := num).
            - rewrite Hk_eq. exact HI.
            - exact Hmatch. }
          split.
          -- apply Existsn_no; assumption.
          -- right. exact HI.
        * cbv [add_waiting_fact]; simpl. exact Hmf_sent.
        * cbv [add_waiting_fact]; simpl. exact Hmf_sent.
      + intros f Hk.
        apply Forall_map.
        pose proof Hk as Hk0.
        apply knows_dfact_after_step in Hk0.
        destruct Hk0 as [Hk0 | Hk0].
        * subst f.
          apply Forall_forall. intros y _. apply rule_has_dfact_afw_F.
        * specialize (Heverywhere _ Hk0).
          apply Forall_app in Heverywhere. destruct Heverywhere as (HF1 & HF2).
          apply Forall_cons_iff in HF2. destruct HF2 as (Hxf & HF2).
          apply Forall_app. split.
          -- eapply Forall_impl; [|exact HF1]. intros. apply rule_has_dfact_afw; assumption.
          -- constructor.
             ++ apply rule_has_dfact_afw.
                cbv [rule_has_dfact send_fact]; simpl. exact Hxf.
             ++ eapply Forall_impl; [|exact HF2]. intros. apply rule_has_dfact_afw; assumption.
      + intros R mf_args.
        specialize (Hcount R mf_args). fwd.
        apply Forall2_app_inv_l in Hcountp0.
        destruct Hcountp0 as (ms_pre & ms_rest & Hms_pre & Hms_rest & ?). subst.
        inversion Hms_rest; subst.
        rename y into ms_x. rename l' into ms_post.
        rename H1 into Hms_x. rename H3 into Hms_post.
        apply Forall_app in Hcountp2. destruct Hcountp2 as (Hcountp2_pre & Hcountp2_rest).
        apply Forall_cons_iff in Hcountp2_rest.
        destruct Hcountp2_rest as (Hcountp2_x & Hcountp2_post).
        destruct (classic (dfact_matches R mf_args (normal_dfact nf_rel nf_args))) as [Hdf | Hdf].
        * exists (ms_pre ++ S ms_x :: ms_post), num_inp. ssplit.
          -- rewrite <- Forall2_map_l.
             apply Forall2_app; [|constructor].
             ++ eapply Forall2_impl; [|exact Hms_pre]. intros y m Hy.
                cbv [add_waiting_fact]; simpl. exact Hy.
             ++ cbv [add_waiting_fact send_fact]; simpl.
                apply Existsn_yes; assumption.
             ++ eapply Forall2_impl; [|exact Hms_post]. intros y m Hy.
                cbv [add_waiting_fact]; simpl. exact Hy.
          -- assumption.
          -- apply Forall_map.
             apply Forall_app; split.
             ++ eapply Forall_impl; [|exact Hcountp2_pre].
                intros y (num_k & num_w & Hk_y & Hw_y & Hsum).
                exists num_k, (S num_w). cbv [add_waiting_fact]; simpl. ssplit.
                ** exact Hk_y.
                ** apply Existsn_yes; assumption.
                ** rewrite ! fold_left_app in *. simpl in *.
                   rewrite (fold_left_add_from_0 ms_post _) in Hsum.
                   rewrite (fold_left_add_from_0 ms_post _).
                   lia.
             ++ constructor.
                ** destruct Hcountp2_x as (num_k & num_w & Hk_x & Hw_x & Hsum).
                   exists num_k, (S num_w). cbv [add_waiting_fact send_fact]; simpl. ssplit.
                   --- exact Hk_x.
                   --- apply Existsn_yes; assumption.
                   --- rewrite ! fold_left_app in *. simpl in *.
                       rewrite (fold_left_add_from_0 ms_post _) in Hsum.
                       rewrite (fold_left_add_from_0 ms_post _).
                       lia.
                ** eapply Forall_impl; [|exact Hcountp2_post].
                   intros y (num_k & num_w & Hk_y & Hw_y & Hsum).
                   exists num_k, (S num_w). cbv [add_waiting_fact]; simpl. ssplit.
                   --- exact Hk_y.
                   --- apply Existsn_yes; assumption.
                   --- rewrite ! fold_left_app in *. simpl in *.
                       rewrite (fold_left_add_from_0 ms_post _) in Hsum.
                       rewrite (fold_left_add_from_0 ms_post _).
                       lia.
        * exists (ms_pre ++ ms_x :: ms_post), num_inp. ssplit.
          -- rewrite <- Forall2_map_l.
             apply Forall2_app; [|constructor].
             ++ eapply Forall2_impl; [|exact Hms_pre]. intros y m Hy.
                cbv [add_waiting_fact]; simpl. exact Hy.
             ++ cbv [add_waiting_fact send_fact]; simpl. apply Existsn_no; assumption.
             ++ eapply Forall2_impl; [|exact Hms_post]. intros y m Hy.
                cbv [add_waiting_fact]; simpl. exact Hy.
          -- assumption.
          -- apply Forall_map.
             apply Forall_app; split.
             ++ eapply Forall_impl; [|exact Hcountp2_pre].
                intros y (num_k & num_w & Hk_y & Hw_y & Hsum).
                exists num_k, num_w. cbv [add_waiting_fact]; simpl. ssplit.
                ** exact Hk_y.
                ** apply Existsn_no; assumption.
                ** assumption.
             ++ constructor.
                ** destruct Hcountp2_x as (num_k & num_w & Hk_x & Hw_x & Hsum).
                   exists num_k, num_w. cbv [add_waiting_fact send_fact]; simpl. ssplit.
                   --- exact Hk_x.
                   --- apply Existsn_no; assumption.
                   --- assumption.
                ** eapply Forall_impl; [|exact Hcountp2_post].
                   intros y (num_k & num_w & Hk_y & Hw_y & Hsum).
                   exists num_k, num_w. cbv [add_waiting_fact]; simpl. ssplit.
                   --- exact Hk_y.
                   --- apply Existsn_no; assumption.
                   --- assumption.
      + intros R HR.
        specialize (Hinp_sane R HR). fwd.
        split.
        * intros mf_args. specialize (Hinp_sanep0 mf_args).
          apply Forall_map.
          eapply forall_swap with (x := x); cycle 1.
          -- eapply Forall_impl; [|exact Hinp_sanep0]. intros y Hy.
             cbv [add_waiting_fact]; simpl. exact Hy.
          -- cbv [add_waiting_fact send_fact]; simpl. intros Hx_zero.
             apply Existsn_no; [|exact Hx_zero].
             intros (nf_args0 & Heqf & Hmatch).
             inversion Heqf as [[H_rel H_args]]. subst.
             congruence.
        * intros mf_args n num Hk.
          apply knows_dfact_after_step in Hk.
          destruct Hk as [Hk | Hk]; [discriminate|].
          apply (Hinp_sanep1 _ _ _ Hk).
    - cbv [stepWithLabel] in H0. fwd. destruct n as [r k].
      destruct H0p2 as (Hcdmf & Hyq). subst y.
      cbv [can_deduce_meta_fact] in Hcdmf.
      destruct Hcdmf as (ctx & hyps & mf_rel & mf_args_new & mf_cnt & Hnf_eq
                          & HsentExistsn & Hmc_concl & Hmc_hyps & Hknow_hyps & Hclosure).
      assert (Hlc : length (combine (non_meta_rules p) (seq 0 (length s1))) = length s1).
      { rewrite length_combine, length_seq. lia. }
      assert (Hs1_eq : s1 = map snd l1 ++ x :: map snd l2).
      { apply (f_equal (map snd)) in H0p0.
        rewrite map_combine_snd in H0p0 by assumption.
        rewrite map_app in H0p0. simpl in H0p0. exact H0p0. }
      assert (Hlen_lt : length l1 < length s1).
      { rewrite Hs1_eq, length_app, ! length_map. simpl. lia. }
      assert (Hk_eq : k = length l1).
      { assert (Hlen_seq : length (non_meta_rules p) = length (seq 0 (length s1))).
        { rewrite length_seq. lia. }
        pose proof H0p0 as Hp0a.
        apply (f_equal (map fst)) in Hp0a.
        rewrite map_app in Hp0a. simpl in Hp0a.
        rewrite map_combine_fst in Hp0a by assumption.
        apply (f_equal (map snd)) in Hp0a.
        rewrite map_app in Hp0a. simpl in Hp0a.
        rewrite map_combine_snd in Hp0a by assumption.
        pose proof (f_equal (fun ll => nth_error ll (length l1)) Hp0a) as HnE.
        cbv beta in HnE.
        rewrite nth_error_app_middle in HnE.
        rewrite ! length_map in HnE.
        rewrite Nat.compare_refl in HnE.
        rewrite nth_error_seq in HnE.
        assert (E : length l1 <? length s1 = true) by (apply Nat.ltb_lt; lia).
        rewrite E in HnE.
        injection HnE as ->. lia. }
      assert (Hmf_rel_noninput : is_input mf_rel = false).
      { rewrite Forall_forall in Hp_meta_input.
        specialize (Hp_meta_input _ H). simpl in Hp_meta_input.
        rewrite Forall_forall in Hp_meta_input.
        apply Exists_exists in Hmc_concl.
        destruct Hmc_concl as (c & Hin_c & Hint).
        cbv [interp_meta_clause] in Hint.
        destruct Hint as (mfa & mfs & _ & Heq).
        injection Heq as -> _ _.
        apply (Hp_meta_input _ Hin_c). }
      subst new_fact.
      rewrite Hs1_eq in Hmf_inp, Hmf_sent, Heverywhere, Hcount, Hinp_sane, Hlen.
      cbv [sane_state]. ssplit.
      + rewrite length_map, length_app in *. cbn [length] in *.
        rewrite ! length_map in *. lia.
      + intros R mf_args num Hk.
        apply knows_dfact_after_step in Hk.
        destruct Hk as [Hk | Hk]; [discriminate|].
        eapply Hmf_inp; eassumption.
      + intros R mf_args n' num Hk.
        apply knows_dfact_after_step in Hk.
        rewrite nth_sat_map. cbv beta.
        rewrite nth_sat_app_middle. rewrite length_map.
        destruct Hk as [Hk | Hk].
        * injection Hk as -> -> -> ->.
          rewrite <- Hk_eq. rewrite Nat.compare_refl.
          cbv [add_waiting_fact send_fact]; simpl. split.
          -- apply Existsn_no; [|exact HsentExistsn].
             intros (? & Heq & _). discriminate.
          -- left. reflexivity.
        * specialize (Hmf_sent _ _ _ _ Hk).
          rewrite nth_sat_app_middle in Hmf_sent. rewrite length_map in Hmf_sent.
          destruct (Nat.compare_spec n' (length l1)) as [Hl' | Hl' | Hl'].
          -- subst n'.
             destruct Hmf_sent as (HE & HI).
             cbv [add_waiting_fact send_fact]; simpl. split.
             ++ apply Existsn_no; [|exact HE].
                intros (? & Heq & _). discriminate.
             ++ right. exact HI.
          -- cbv [add_waiting_fact]; simpl. exact Hmf_sent.
          -- cbv [add_waiting_fact]; simpl. exact Hmf_sent.
      + intros f Hk.
        apply Forall_map.
        pose proof Hk as Hk0.
        apply knows_dfact_after_step in Hk0.
        destruct Hk0 as [Hk0 | Hk0].
        * subst f.
          apply Forall_forall. intros y _. apply rule_has_dfact_afw_F.
        * specialize (Heverywhere _ Hk0).
          apply Forall_app in Heverywhere. destruct Heverywhere as (HF1 & HF2).
          apply Forall_cons_iff in HF2. destruct HF2 as (Hxf & HF2).
          apply Forall_app. split.
          -- eapply Forall_impl; [|exact HF1]. intros. apply rule_has_dfact_afw; assumption.
          -- constructor.
             ++ apply rule_has_dfact_afw.
                cbv [rule_has_dfact send_fact]; simpl. exact Hxf.
             ++ eapply Forall_impl; [|exact HF2]. intros. apply rule_has_dfact_afw; assumption.
      + intros R mf_args.
        specialize (Hcount R mf_args). fwd.
        apply Forall2_app_inv_l in Hcountp0.
        destruct Hcountp0 as (ms_pre & ms_rest & Hms_pre & Hms_rest & ?). subst.
        inversion Hms_rest; subst.
        rename y into ms_x. rename l' into ms_post.
        rename H2 into Hms_x. rename H4 into Hms_post.
        apply Forall_app in Hcountp2. destruct Hcountp2 as (Hcountp2_pre & Hcountp2_rest).
        apply Forall_cons_iff in Hcountp2_rest.
        destruct Hcountp2_rest as (Hcountp2_x & Hcountp2_post).
        exists (ms_pre ++ ms_x :: ms_post), num_inp. ssplit.
        * rewrite <- Forall2_map_l.
          apply Forall2_app; [|constructor].
          -- eapply Forall2_impl; [|exact Hms_pre]. intros y m Hy.
             cbv [add_waiting_fact]; simpl. exact Hy.
          -- cbv [add_waiting_fact send_fact]; simpl.
             apply Existsn_no; [|exact Hms_x].
             intros (? & Heq & _). discriminate.
          -- eapply Forall2_impl; [|exact Hms_post]. intros y m Hy.
             cbv [add_waiting_fact]; simpl. exact Hy.
        * assumption.
        * apply Forall_map.
          apply Forall_app; split.
          -- eapply Forall_impl; [|eassumption].
             intros y (num_k & num_w & Hk_y & Hw_y & Hsum).
             exists num_k, num_w. cbv [add_waiting_fact]; simpl. ssplit.
             ++ exact Hk_y.
             ++ apply Existsn_no; [|exact Hw_y].
                intros (? & Heq & _). discriminate.
             ++ assumption.
          -- constructor.
             ++ destruct Hcountp2_x as (num_k & num_w & Hk_x & Hw_x & Hsum).
                exists num_k, num_w. cbv [add_waiting_fact send_fact]; simpl. ssplit.
                ** exact Hk_x.
                ** apply Existsn_no; [|exact Hw_x].
                   intros (? & Heq & _). discriminate.
                ** assumption.
             ++ eapply Forall_impl; [|exact Hcountp2_post].
                intros y (num_k & num_w & Hk_y & Hw_y & Hsum).
                exists num_k, num_w. cbv [add_waiting_fact]; simpl. ssplit.
                ** exact Hk_y.
                ** apply Existsn_no; [|exact Hw_y].
                   intros (? & Heq & _). discriminate.
                ** assumption.
      + intros R HR.
        specialize (Hinp_sane R HR). fwd.
        split.
        * intros mf_args. specialize (Hinp_sanep0 mf_args).
          apply Forall_map.
          eapply forall_swap with (x := x); cycle 1.
          -- eapply Forall_impl; [|exact Hinp_sanep0]. intros y Hy.
             cbv [add_waiting_fact]; simpl. exact Hy.
          -- cbv [add_waiting_fact send_fact]; simpl. intros Hx_zero.
             apply Existsn_no; [|exact Hx_zero].
             intros (? & Heq & _). discriminate.
        * intros mf_args n num Hk.
          apply knows_dfact_after_step in Hk.
          destruct Hk as [Hk | Hk].
          -- injection Hk as -> _ _ _. congruence.
          -- apply (Hinp_sanep1 _ _ _ Hk).
  Qed.

  Lemma fold_left_add_zero (l : list nat) :
    Forall (eq 0) l ->
    fold_left Nat.add l 0 = 0.
  Proof.
    induction 1; simpl; auto. subst. simpl. assumption.
  Qed.

  Lemma Forall2_nth_error_fwd {A B} (R : A -> B -> Prop) xs ys :
    Forall2 R xs ys ->
    forall n x y,
      nth_error xs n = Some x ->
      nth_error ys n = Some y ->
      R x y.
  Proof.
    induction 1; intros [|n] x' y' Hx Hy; simpl in *; try discriminate.
    - injection Hx as ->. injection Hy as ->. assumption.
    - eapply IHForall2; eassumption.
  Qed.

  (* For the count argument to close (analog of SimpleDataflow's
     expect_num_R_facts_no_travellers using msgs_received = num), we need
     the local count of matching normal facts in known.  SimpleDataflow gets
     this for free because there is no waiting in that model.  Here we
     require it explicitly --- it matches the second conjunct of
     [knows_datalog_fact dfacts (meta_fact R mf_args _)]. *)
  Lemma expect_num_R_facts_no_waiting inputs s rs R mf_args nf_args num :
    good_input_facts inputs ->
    sane_state inputs s ->
    In rs s ->
    expect_num_R_facts R mf_args rs.(known_facts) num ->
    Existsn (dfact_matches R mf_args) num rs.(known_facts) ->
    In (normal_dfact R nf_args) rs.(waiting_facts) ->
    Forall2 matches mf_args nf_args ->
    False.
  Proof.
    intros Hinp Hsane Hin Hexp Hex_kn Hwait Hmatch.
    destruct Hsane as (Hlen & Hmf_inp & Hmf_sent & Heverywhere & Hcount & Hinp_sane).
    specialize (Hcount R mf_args). fwd.
    rewrite Forall_forall in Hcountp2.
    specialize (Hcountp2 _ Hin).
    destruct Hcountp2 as (num_known & num_wait & Hex_known & Hex_wait & Hsum).
    pose proof (Existsn_unique _ _ _ _ Hex_kn Hex_known) as Hnk_eq.
    subst num_known.
    cbv [expect_num_R_facts] in Hexp.
    destruct (is_input R) eqn:ER.
    - (* input: meta_dfact in rs.known --> in inputs.  num_inp <= num.
         All rules have sent_facts count = 0 for input R.  Per-rule sum
         then forces num_wait <= 0; In matching contradicts. *)
      assert (Hk : knows_dfact s (meta_dfact R mf_args None num)).
      { cbv [knows_dfact]. apply Exists_exists. exists rs. split; auto.
        cbv [rule_has_dfact]. left. exact Hexp. }
      specialize (Hmf_inp _ _ _ Hk).
      destruct Hinp as (_ & Hinp_cnt).
      specialize (Hinp_cnt _ _ _ Hmf_inp).
      destruct Hinp_cnt as (_ & num' & Hle & Hexists_inp).
      pose proof (Existsn_unique _ _ _ _ Hexists_inp Hcountp1) as Hni_eq.
      subst num'.
      specialize (Hinp_sane R ER). destruct Hinp_sane as (Hinp_sane_zero & _).
      specialize (Hinp_sane_zero mf_args).
      assert (Hms_zero : Forall (eq 0) msgs_sents).
      { clear -Hcountp0 Hinp_sane_zero.
        induction Hcountp0; constructor.
        - apply Forall_cons_iff in Hinp_sane_zero. destruct Hinp_sane_zero as (Hzero & _).
          symmetry. eapply Existsn_unique; eassumption.
        - apply IHHcountp0.
          apply Forall_cons_iff in Hinp_sane_zero. apply (proj2 Hinp_sane_zero). }
      rewrite (fold_left_add_zero _ Hms_zero) in Hsum.
      assert (num_wait = 0) by lia.
      subst num_wait.
      apply Existsn_0_Forall_not in Hex_wait.
      rewrite Forall_forall in Hex_wait.
      apply (Hex_wait _ Hwait).
      exists nf_args. split; auto.
    - (* non-input: each per-rule meta_dfact in rs.known is consistent with
         that rule's sent_facts count, so msgs_sents = expected_msgss
         pointwise; sum equals num.  num_inp = 0 (non-input means no
         matching normals in inputs).  Per-rule sum forces num_wait = 0. *)
      fwd.
      assert (Hni_zero : num_inp = 0).
      { destruct Hinp as (Hrel & _).
        assert (Hno : Existsn (dfact_matches R mf_args) 0 inputs).
        { apply Forall_not_Existsn_0.
          apply Forall_forall. intros f Hin_f Hdf.
          destruct Hdf as (nf_args0 & Heq & _). subst f.
          rewrite Forall_forall in Hrel. specialize (Hrel _ Hin_f).
          simpl in Hrel. congruence. }
        symmetry. eapply Existsn_unique; eassumption. }
      subst num_inp.
      assert (Hms_eq : msgs_sents = expected_msgss).
      { apply nth_error_ext. intros k.
        pose proof (Forall2_length Hcountp0) as Hlen_ms.
        pose proof (Forall2_length Hexpp0) as Hlen_es.
        rewrite length_seq in Hlen_es.
        destruct (Nat.lt_ge_cases k (length msgs_sents)) as [Hkk | Hkk].
        + destruct (nth_error msgs_sents k) as [ms|] eqn:Hms; [|apply nth_error_None in Hms; lia].
          destruct (nth_error expected_msgss k) as [es|] eqn:Hes; [|apply nth_error_None in Hes; lia].
          f_equal.
          destruct (nth_error s k) as [rs_k|] eqn:Hrs_k; [|apply nth_error_None in Hrs_k; lia].
          pose proof (Forall2_nth_error_fwd _ _ _ Hcountp0 _ _ _ Hrs_k Hms) as HE_ms.
          cbv beta in HE_ms.
          assert (Hseq_k : nth_error (seq 0 (length (non_meta_rules p))) k = Some k).
          { rewrite nth_error_seq.
            assert (Hltb : (k <? length (non_meta_rules p)) = true) by (apply Nat.ltb_lt; lia).
            rewrite Hltb. reflexivity. }
          pose proof (Forall2_nth_error_fwd _ _ _ Hexpp0 _ _ _ Hseq_k Hes) as HE_es_in.
          cbv beta in HE_es_in.
          assert (Hknows : knows_dfact s (meta_dfact R mf_args (Some k) es)).
          { cbv [knows_dfact]. apply Exists_exists. exists rs. split; auto.
            cbv [rule_has_dfact]. left. exact HE_es_in. }
          specialize (Hmf_sent _ _ _ _ Hknows).
          cbv [nth_sat] in Hmf_sent. rewrite Hrs_k in Hmf_sent.
          destruct Hmf_sent as (HE_es & _).
          eapply Existsn_unique; eassumption.
        + rewrite (proj2 (nth_error_None _ _)) by lia.
          rewrite (proj2 (nth_error_None _ _)) by lia.
          reflexivity. }
      subst expected_msgss.
      assert (num_wait = 0) by lia.
      subst num_wait.
      apply Existsn_0_Forall_not in Hex_wait.
      rewrite Forall_forall in Hex_wait.
      apply (Hex_wait _ Hwait).
      exists nf_args. split; auto.
  Qed.
  
  Lemma Forall3_nth_error_fwd {A B C} (R : A -> B -> C -> Prop) xs ys zs :
    Forall3 R xs ys zs ->
    forall n x y z,
      nth_error xs n = Some x ->
      nth_error ys n = Some y ->
      nth_error zs n = Some z ->
      R x y z.
  Proof.
    induction 1; intros [|n] x' y' z' Hx Hy Hz; simpl in *; try discriminate.
    - injection Hx as ->. injection Hy as ->. injection Hz as ->. assumption.
    - eapply IHForall3; eassumption.
  Qed.

  Lemma Forall3_nth_error_bwd {A B C} (R : A -> B -> C -> Prop) xs ys zs :
    length xs = length ys ->
    length ys = length zs ->
    (forall n x y z,
        nth_error xs n = Some x ->
        nth_error ys n = Some y ->
        nth_error zs n = Some z ->
        R x y z) ->
    Forall3 R xs ys zs.
  Proof.
    revert ys zs.
    induction xs as [|x xs IH]; intros [|y ys] [|z zs] Hl1 Hl2 H;
      simpl in *; try discriminate; try constructor.
    - apply (H 0); reflexivity.
    - apply IH; auto. intros n x' y' z' Hx Hy Hz. apply (H (S n)); auto.
  Qed.

  (* With sent-based meta_facts_correct, the only nontrivial known-growth
     issue is in the learn_fact case at the firing rule (where wf moves
     from waiting to known).  This helper lifts a witness across that
     known-growth, encapsulating the saturation arguments. *)
  Lemma can_deduce_meta_fact_learn_fact inputs s x wf mf_concls mf_hyps r n result :
    good_input_facts inputs ->
    sane_state inputs s ->
    In x s ->
    In wf x.(waiting_facts) ->
    In (mf_concls, mf_hyps) p.(meta_rules) ->
    In r p.(non_meta_rules) ->
    can_deduce_meta_fact mf_concls mf_hyps r n x.(sent_facts) x.(known_facts) result ->
    can_deduce_meta_fact mf_concls mf_hyps r n x.(sent_facts) (wf :: x.(known_facts)) result.
  Proof.
    intros Hinp Hsane Hxs_in Hwf_in_wait Hmr_in Hr_in Hcdm.
    cbv [can_deduce_meta_fact] in Hcdm |- *.
    destruct Hcdm as (ctx & hyps & mf_rel' & mf_args' & mf_cnt' & Hres & HEx & Hconcl & Hinterp & Hknown_hyps & Hclo).
    exists ctx, hyps, mf_rel', mf_args', mf_cnt'. split; [exact Hres|].
    split; [exact HEx|]. split; [exact Hconcl|]. split; [exact Hinterp|].
    split.
    { (* Forall (knows_datalog_fact (wf :: x.known)) hyps *)
      eapply Forall_impl; [|exact Hknown_hyps].
      intros h Hold. destruct h as [R_h nf_args_h | R_h mf_args_h mf_set_h].
      + simpl in Hold |- *. apply in_cons. exact Hold.
      + simpl in Hold |- *.
        destruct Hold as (num_h & Hexp_h & Hex_h & Hsetcorr_h).
        exists num_h. split; [|split].
        * cbv [expect_num_R_facts] in Hexp_h |- *.
          destruct (is_input R_h) eqn:Hin_R.
          -- right. exact Hexp_h.
          -- destruct Hexp_h as (expected_msgss & Hf2 & Hsum).
             exists expected_msgss. split; [|exact Hsum].
             eapply Forall2_impl_strong; [|exact Hf2].
             intros n_pos exp_n Hin_old _ _. apply in_cons. exact Hin_old.
        * apply Existsn_no; [|exact Hex_h].
          intros [nf_args_w [Hwf_eq Hmatch_w]].
          eapply expect_num_R_facts_no_waiting; try eassumption.
          rewrite Hwf_eq in Hwf_in_wait. exact Hwf_in_wait.
        * intros nf_args0 Hmatch.
          specialize (Hsetcorr_h _ Hmatch).
          split.
          -- intros Hset. apply in_cons. apply Hsetcorr_h. exact Hset.
          -- intros Hin. simpl in Hin. destruct Hin as [Hwf_eq | Hin_old].
             ++ exfalso. eapply expect_num_R_facts_no_waiting; try eassumption.
                rewrite Hwf_eq in Hwf_in_wait. exact Hwf_in_wait.
             ++ apply Hsetcorr_h. exact Hin_old. }
    { (* closure at (wf :: x.known) *)
      intros nf_args0 Hded Hmatch.
      destruct Hded as (hyps_d & Himpl & Hkn_d_new).
      (* Build rule_impl for the meta-rule with a constructed set *)
      pose (S_constr := fun args'' => one_step_derives rules_of hyps mf_rel' args'').
      assert (Hri_meta : rule_impl (one_step_derives rules_of) (meta_rule mf_concls mf_hyps)
                          (meta_fact mf_rel' mf_args' S_constr) hyps).
      { eapply meta_rule_impl with (ctx := ctx).
        - eapply Exists_impl; [|exact Hconcl]. intros c (mf_args0 & mf_set0 & Hf2 & Heq).
          injection Heq as Hrel Hargs _. subst.
          exists mf_args0, S_constr. split; [exact Hf2|]. reflexivity.
        - exact Hinterp.
        - intros args'' _. subst S_constr. simpl. reflexivity. }
      (* Build rule_impl for r *)
      assert (Hri_normal : rule_impl (one_step_derives rules_of) (rule_of r)
                            (normal_fact mf_rel' nf_args0) hyps_d).
      { apply simple_rule_impl. exact Himpl. }
      (* Apply meta_rules_valid *)
      assert (HFPS : Forall (fact_potentially_supported hyps) hyps_d).
      { eapply Hmeta_rules with (mr := meta_rule mf_concls mf_hyps)
                                 (nr := rule_of r); try eassumption.
        - cbv [rules_of]. apply in_app_iff. left.
          apply in_map_iff. exists (mf_concls, mf_hyps). split; [reflexivity|]. exact Hmr_in.
        - cbv [rules_of]. apply in_app_iff. right.
          apply in_map_iff. exists r. split; [reflexivity|]. exact Hr_in. }
      (* Now transfer Hkn_d_new (at NEW) to Hkn_d_old (at OLD) *)
      assert (Hkn_d_old : Forall (knows_datalog_fact x.(known_facts)) hyps_d).
      { rewrite Forall_forall in Hkn_d_new, HFPS, Hknown_hyps |- *.
        intros h Hh_in. specialize (Hkn_d_new _ Hh_in). specialize (HFPS _ Hh_in).
        destruct h as [R_h nf_args_h | R_h mf_args_h mf_set_h].
        - (* normal_fact h: use saturation to rule out h = wf *)
          cbv [fact_potentially_supported] in HFPS.
          destruct HFPS as (mf_args_h' & mf_set_h' & Hin_mhyp & Hmatch_h).
          specialize (Hknown_hyps _ Hin_mhyp).
          simpl in Hkn_d_new, Hknown_hyps |- *.
          destruct Hkn_d_new as [Hwf_is | Hkn_old]; [|exact Hkn_old].
          exfalso. destruct Hknown_hyps as (num_h & Hexp_h & Hex_h & _).
          eapply expect_num_R_facts_no_waiting; try eassumption.
          rewrite <- Hwf_is. exact Hwf_in_wait.
        - (* meta_fact h: use mhyps's knows_datalog_fact via Hknown_hyps *)
          cbv [fact_potentially_supported] in HFPS.
          destruct HFPS as (mf_set_h' & Hin_mhyp).
          specialize (Hknown_hyps _ Hin_mhyp).
          simpl in Hkn_d_new, Hknown_hyps |- *.
          destruct Hkn_d_new as (num & Hexp_new & Hex_new & Hsetcorr_new).
          destruct Hknown_hyps as (num_old & Hexp_old & Hex_old & _).
          exists num_old. split; [exact Hexp_old|]. split; [exact Hex_old|].
          intros nf_args1 Hmatch1.
          specialize (Hsetcorr_new _ Hmatch1).
          split.
          + intros Hs. apply Hsetcorr_new in Hs. simpl in Hs.
            destruct Hs as [Hwf_eq | Hold_in]; [|exact Hold_in].
            exfalso. eapply expect_num_R_facts_no_waiting; try eassumption.
            rewrite Hwf_eq in Hwf_in_wait. exact Hwf_in_wait.
          + intros Hin. apply Hsetcorr_new. apply in_cons. exact Hin. }
      (* Apply Hclo to get In ... at OLD *)
      assert (Hded_old : can_deduce_normal_fact r x.(known_facts) mf_rel' nf_args0).
      { cbv [can_deduce_normal_fact]. exists hyps_d. split; assumption. }
      specialize (Hclo _ Hded_old Hmatch).
      apply in_cons. exact Hclo. }
  Qed.

  Lemma step_preserves_mfs_correct inputs s s' :
    good_input_facts inputs ->
    sane_state inputs s ->
    meta_facts_correct s ->
    comp_step s s' ->
    meta_facts_correct s'.
  Proof.
    intros Hinp Hsane Hmfc Hstep.
    pose proof Hsane as Hsane'.
    destruct Hsane as (Hlen & Hmf_inp & Hmf_sent & Heverywhere & Hcount & Hinp_sane).
    invert Hstep.
    - (* learn_fact *)
      cbv [stepOne learn_fact_at_rule] in H.
      destruct H as (l1 & x & y & l2 & Hseq & Hs'eq & Hlfr).
      destruct Hlfr as (lw1 & wf & lw2 & Hyknown & Hxwait & Hywait & Hysent).
      assert (Hlen_lt : length l1 < length s).
      { rewrite Hseq, length_app. simpl. lia. }
      cbv [meta_facts_correct] in Hmfc |- *.
      apply Forall3_nth_error_bwd.
      + rewrite Hs'eq, ! length_app. simpl. rewrite Hseq, length_app in Hlen. simpl in Hlen. lia.
      + rewrite Hs'eq, length_seq, length_app. reflexivity.
      + intros n r rs k_seq Hk_r Hk_rs Hk_k.
        rewrite nth_error_seq in Hk_k.
        rewrite Hs'eq in Hk_k. rewrite length_app in Hk_k. simpl in Hk_k.
        destruct (n <? _) eqn:Hltb in Hk_k; [|discriminate].
        injection Hk_k as <-. apply Nat.ltb_lt in Hltb.
        assert (Hold_get : forall n0 r0 rs0,
                   nth_error (non_meta_rules p) n0 = Some r0 ->
                   nth_error s n0 = Some rs0 ->
                   meta_facts_correct_at_rule (meta_rules p) n0 rs0 r0).
        { intros n0 r0 rs0 Hr0 Hrs0.
          eapply (Forall3_nth_error_fwd _ _ _ _ Hmfc); try eassumption.
          rewrite nth_error_seq.
          assert (Hltb' : n0 <? length s = true).
          { apply Nat.ltb_lt. apply nth_error_Some_bound_index in Hrs0. assumption. }
          rewrite Hltb'. reflexivity. }
        rewrite Hs'eq, nth_error_app_middle in Hk_rs.
        destruct (Nat.compare_spec n (length l1)) as [Heq | Hlt | Hgt].
        * (* n = length l1: rule where learn_fact happened *)
          subst n.
          replace ((length l1 ?= length l1)) with Eq in Hk_rs by (symmetry; apply Nat.compare_refl).
          injection Hk_rs as <-.
          assert (Hxs : nth_error s (length l1) = Some x).
          { rewrite Hseq, nth_error_app2 by lia.
            rewrite Nat.sub_diag. reflexivity. }
          specialize (Hold_get _ _ _ Hk_r Hxs).
          cbv [meta_facts_correct_at_rule] in Hold_get |- *.
          intros R mf_args num HIn.
          (* HIn is in sent_facts y = sent_facts x (unchanged by learn_fact) *)
          rewrite Hysent in HIn.
          specialize (Hold_get _ _ _ HIn).
          fwd. exists mf_concls, mf_hyps. split; [assumption|].
          rewrite Hyknown, Hysent.
          eapply can_deduce_meta_fact_learn_fact; try eassumption.
          { eapply nth_error_In; eassumption. }
          { rewrite Hxwait. apply in_app_iff. right. left. reflexivity. }
          { eapply nth_error_In; eassumption. }
        * (* n < length l1 *)
          replace ((n ?= length l1)) with Lt in Hk_rs by (symmetry; apply Nat.compare_lt_iff; lia).
          assert (Hsn : nth_error s n = Some rs).
          { rewrite Hseq, nth_error_app1 by lia. assumption. }
          specialize (Hold_get _ _ _ Hk_r Hsn). exact Hold_get.
        * (* n > length l1 *)
          replace ((n ?= length l1)) with Gt in Hk_rs by (symmetry; apply Nat.compare_gt_iff; lia).
          assert (Hsn : nth_error s n = Some rs).
          { rewrite Hseq, nth_error_app2 by lia.
            assert (Hoff : n - length l1 = S (n - length l1 - 1)) by lia.
            rewrite Hoff. simpl. assumption. }
          specialize (Hold_get _ _ _ Hk_r Hsn). exact Hold_get.
    - (* fire_normal_rule *)
      cbv [stepWithLabel] in H. fwd. destruct n as [r_fire k_fire].
      destruct Hp2 as (Hcan & Hnometa & Hyq). subst y.
      assert (Hlc : length (combine (non_meta_rules p) (seq 0 (length s))) = length s).
      { rewrite length_combine, length_seq. lia. }
      assert (Hs_eq : s = map snd l1 ++ x :: map snd l2).
      { apply (f_equal (map snd)) in Hp0.
        rewrite map_app in Hp0. simpl in Hp0.
        rewrite map_combine_snd in Hp0 by exact Hlc.
        exact Hp0. }
      assert (Hlen_lt : length l1 < length s).
      { rewrite Hs_eq, length_app, ! length_map. simpl. lia. }
      assert (Hk_eq : k_fire = length l1).
      { assert (Hlen_seq : length (non_meta_rules p) = length (seq 0 (length s))).
        { rewrite length_seq. lia. }
        pose proof Hp0 as Hp0a.
        apply (f_equal (map fst)) in Hp0a.
        rewrite map_app in Hp0a. simpl in Hp0a.
        rewrite map_combine_fst in Hp0a by exact Hlc.
        apply (f_equal (map snd)) in Hp0a.
        rewrite map_app in Hp0a. simpl in Hp0a.
        rewrite map_combine_snd in Hp0a by exact Hlen_seq.
        pose proof (f_equal (fun ll => nth_error ll (length l1)) Hp0a) as HnE.
        cbv beta in HnE.
        rewrite nth_error_app_middle in HnE.
        rewrite ! length_map in HnE.
        rewrite Nat.compare_refl in HnE.
        rewrite nth_error_seq in HnE.
        assert (E : length l1 <? length s = true) by (apply Nat.ltb_lt; lia).
        rewrite E in HnE.
        injection HnE as ->. lia. }
      cbv [meta_facts_correct] in Hmfc |- *.
      apply Forall3_nth_error_bwd.
      + rewrite Hs_eq, length_app, ! length_map in Hlen. simpl in Hlen.
        rewrite ! length_map in Hlen.
        rewrite length_map, length_app, length_map. simpl. rewrite length_map. lia.
      + rewrite length_map, length_seq, length_app, ! length_map. reflexivity.
      + intros n r rs k_seq Hk_r Hk_rs Hk_k.
        rewrite nth_error_seq in Hk_k.
        destruct (n <? _) eqn:Hltb in Hk_k; [|discriminate].
        injection Hk_k as <-. apply Nat.ltb_lt in Hltb.
        rewrite nth_error_map in Hk_rs.
        destruct (nth_error (map snd l1 ++ send_fact (normal_dfact nf_rel nf_args) x :: map snd l2) n)
          as [rs_inner|] eqn:Hk_rsi; [|discriminate].
        simpl in Hk_rs. injection Hk_rs as <-.
        (* Get old meta_facts_correct_at_rule from Hmfc *)
        assert (Hold_get : forall n0 r0 rs0,
                   nth_error (non_meta_rules p) n0 = Some r0 ->
                   nth_error s n0 = Some rs0 ->
                   meta_facts_correct_at_rule (meta_rules p) n0 rs0 r0).
        { intros n0 r0 rs0 Hr0 Hrs0.
          eapply (Forall3_nth_error_fwd _ _ _ _ Hmfc); try eassumption.
          rewrite nth_error_seq.
          assert (Hltb' : n0 <? length s = true).
          { apply Nat.ltb_lt. apply nth_error_Some_bound_index in Hrs0. assumption. }
          rewrite Hltb'. reflexivity. }
        rewrite nth_error_app_middle, length_map in Hk_rsi.
        destruct (Nat.compare_spec n (length l1)) as [Heq | Hlt | Hgt].
        * (* n = length l1: firing rule *)
          subst n.
          replace ((length l1 ?= length l1)) with Eq in Hk_rsi by (symmetry; apply Nat.compare_refl).
          injection Hk_rsi as <-.
          assert (Hxs : nth_error s (length l1) = Some x).
          { rewrite Hs_eq, nth_error_app2 by (rewrite length_map; lia).
            rewrite length_map, Nat.sub_diag. reflexivity. }
          specialize (Hold_get _ _ _ Hk_r Hxs).
          cbv [meta_facts_correct_at_rule] in Hold_get |- *.
          intros R mf_args num HIn. simpl in HIn.
          destruct HIn as [Heq_F | HIn_old]; [discriminate|].
          specialize (Hold_get _ _ _ HIn_old).
          fwd. exists mf_concls, mf_hyps. split; [assumption|].
          cbv [can_deduce_meta_fact] in Hold_getp1 |- *.
          destruct Hold_getp1 as (ctx & hyps & mf_rel' & mf_args' & mf_cnt' & Hres & HEx & Hconcl & Hinterp & Hknown_hyps & Hclo).
          injection Hres as Heq1 Heq2 Heq3.
          subst mf_rel' mf_args' mf_cnt'.
          exists ctx, hyps, R, mf_args, num. split; [reflexivity|].
          split.
          { (* Existsn count over (F :: x.sent) — need to show F doesn't match *)
            simpl.
            assert (Hnomatch : ~ dfact_matches R mf_args (normal_dfact nf_rel nf_args)).
            { intros [nf_args2 [Heq Hmatch]]. injection Heq as -> ->.
              eapply Hnometa; [|eassumption].
              rewrite Hk_eq. exact HIn_old. }
            apply Existsn_no; assumption. }
          split; [assumption|]. split; [assumption|]. split; [assumption|].
          assumption.
        * (* n < length l1: unchanged rule *)
          replace ((n ?= length l1)) with Lt in Hk_rsi by (symmetry; apply Nat.compare_lt_iff; lia).
          rewrite nth_error_map in Hk_rsi.
          destruct (nth_error l1 n) as [pair_n|] eqn:Hl1n; [|discriminate].
          simpl in Hk_rsi. injection Hk_rsi as Hri.
          assert (Hsn : nth_error s n = Some rs_inner).
          { rewrite Hs_eq, nth_error_app1 by (rewrite length_map; lia).
            rewrite nth_error_map, Hl1n. simpl. f_equal. assumption. }
          specialize (Hold_get _ _ _ Hk_r Hsn). exact Hold_get.
        * (* n > length l1: unchanged rule *)
          replace ((n ?= length l1)) with Gt in Hk_rsi by (symmetry; apply Nat.compare_gt_iff; lia).
          rewrite nth_error_map in Hk_rsi.
          destruct (nth_error l2 (n - length l1 - 1)) as [pair_n|] eqn:Hl2n; [|discriminate].
          simpl in Hk_rsi. injection Hk_rsi as Hri.
          assert (Hsn : nth_error s n = Some rs_inner).
          { rewrite Hs_eq, nth_error_app2 by (rewrite length_map; lia).
            rewrite length_map.
            assert (Hoff : n - length l1 = S (n - length l1 - 1)) by lia.
            rewrite Hoff. simpl. rewrite nth_error_map, Hl2n. simpl. f_equal. assumption. }
          specialize (Hold_get _ _ _ Hk_r Hsn). exact Hold_get.
    - (* fire_meta_rule *)
      rename H into Hmr_in.
      cbv [stepWithLabel] in H0. fwd. destruct n as [r_fire k_fire].
      destruct H0p2 as (Hcan & Hyq). subst y.
      assert (Hnf_meta : exists mf_rel0 mf_args0 mf_cnt0, new_fact = meta_dfact mf_rel0 mf_args0 (Some k_fire) mf_cnt0).
      { cbv [can_deduce_meta_fact] in Hcan. destruct Hcan as (_ & _ & ?r & ?a & ?c & ? & _). eauto. }
      destruct Hnf_meta as (new_mfr & new_mfa & new_mfc & Hnf_eq).
      assert (Hlc : length (combine (non_meta_rules p) (seq 0 (length s))) = length s).
      { rewrite length_combine, length_seq. lia. }
      assert (Hs_eq : s = map snd l1 ++ x :: map snd l2).
      { apply (f_equal (map snd)) in H0p0.
        rewrite map_app in H0p0. simpl in H0p0.
        rewrite map_combine_snd in H0p0 by exact Hlc.
        exact H0p0. }
      assert (Hlen_lt : length l1 < length s).
      { rewrite Hs_eq, length_app, ! length_map. simpl. lia. }
      assert (Hk_eq : k_fire = length l1).
      { assert (Hlen_seq : length (non_meta_rules p) = length (seq 0 (length s))).
        { rewrite length_seq. lia. }
        pose proof H0p0 as Hp0a.
        apply (f_equal (map fst)) in Hp0a.
        rewrite map_app in Hp0a. simpl in Hp0a.
        rewrite map_combine_fst in Hp0a by exact Hlc.
        apply (f_equal (map snd)) in Hp0a.
        rewrite map_app in Hp0a. simpl in Hp0a.
        rewrite map_combine_snd in Hp0a by exact Hlen_seq.
        pose proof (f_equal (fun ll => nth_error ll (length l1)) Hp0a) as HnE.
        cbv beta in HnE.
        rewrite nth_error_app_middle in HnE.
        rewrite ! length_map in HnE.
        rewrite Nat.compare_refl in HnE.
        rewrite nth_error_seq in HnE.
        assert (E : length l1 <? length s = true) by (apply Nat.ltb_lt; lia).
        rewrite E in HnE.
        injection HnE as ->. lia. }
      cbv [meta_facts_correct] in Hmfc |- *.
      apply Forall3_nth_error_bwd.
      + rewrite Hs_eq, length_app, ! length_map in Hlen. simpl in Hlen.
        rewrite ! length_map in Hlen.
        rewrite length_map, length_app, length_map. simpl. rewrite length_map. lia.
      + rewrite length_map, length_seq, length_app, ! length_map. reflexivity.
      + intros n r rs k_seq Hk_r Hk_rs Hk_k.
        rewrite nth_error_seq in Hk_k.
        destruct (n <? _) eqn:Hltb in Hk_k; [|discriminate].
        injection Hk_k as <-. apply Nat.ltb_lt in Hltb.
        rewrite nth_error_map in Hk_rs.
        destruct (nth_error (map snd l1 ++ send_fact new_fact x :: map snd l2) n)
          as [rs_inner|] eqn:Hk_rsi; [|discriminate].
        simpl in Hk_rs. injection Hk_rs as <-.
        assert (Hold_get : forall n0 r0 rs0,
                   nth_error (non_meta_rules p) n0 = Some r0 ->
                   nth_error s n0 = Some rs0 ->
                   meta_facts_correct_at_rule (meta_rules p) n0 rs0 r0).
        { intros n0 r0 rs0 Hr0 Hrs0.
          eapply (Forall3_nth_error_fwd _ _ _ _ Hmfc); try eassumption.
          rewrite nth_error_seq.
          assert (Hltb' : n0 <? length s = true).
          { apply Nat.ltb_lt. apply nth_error_Some_bound_index in Hrs0. assumption. }
          rewrite Hltb'. reflexivity. }
        rewrite nth_error_app_middle, length_map in Hk_rsi.
        destruct (Nat.compare_spec n (length l1)) as [Heq | Hlt | Hgt].
        * (* n = length l1: firing rule *)
          subst n.
          replace ((length l1 ?= length l1)) with Eq in Hk_rsi by (symmetry; apply Nat.compare_refl).
          injection Hk_rsi as <-.
          assert (Hxs : nth_error s (length l1) = Some x).
          { rewrite Hs_eq, nth_error_app2 by (rewrite length_map; lia).
            rewrite length_map, Nat.sub_diag. reflexivity. }
          specialize (Hold_get _ _ _ Hk_r Hxs).
          cbv [meta_facts_correct_at_rule] in Hold_get |- *.
          intros R mf_args num HIn. simpl in HIn.
          destruct HIn as [Heq_nf | HIn_old].
          { (* HIn picks new_fact = meta_dfact R mf_args (Some (length l1)) num *)
            assert (Hr_eq : r = r_fire).
            { assert (Hlen_seq : length (non_meta_rules p) = length (seq 0 (length s))).
              { rewrite length_seq. lia. }
              pose proof H0p0 as Hp0a.
              apply (f_equal (map fst)) in Hp0a.
              rewrite map_app in Hp0a. simpl in Hp0a.
              rewrite map_combine_fst in Hp0a by exact Hlc.
              apply (f_equal (map fst)) in Hp0a.
              rewrite map_app in Hp0a. simpl in Hp0a.
              rewrite map_combine_fst in Hp0a by exact Hlen_seq.
              pose proof (f_equal (fun ll => nth_error ll (length l1)) Hp0a) as HnE.
              cbv beta in HnE.
              rewrite nth_error_app_middle in HnE.
              rewrite ! length_map in HnE.
              rewrite Nat.compare_refl in HnE.
              rewrite HnE in Hk_r. injection Hk_r as ->. reflexivity. }
            subst r.
            exists mf_concls, mf_hyps. split; [exact Hmr_in|].
            cbv [can_deduce_meta_fact] in Hcan |- *.
            destruct Hcan as (ctx & hyps & mf_rel' & mf_args' & mf_cnt' & Hres & HEx & Hconcl & Hinterp & Hknown_hyps & Hclo).
            rewrite Heq_nf in Hres. injection Hres as <- <- _ <-.
            exists ctx, hyps, R, mf_args, num. split; [reflexivity|].
            split.
            { simpl. rewrite Heq_nf. apply Existsn_no; [|assumption].
              intros [nf_args2 [Heq Hmatch]]. discriminate. }
            split; [exact Hconcl|]. split; [exact Hinterp|]. split; [exact Hknown_hyps|].
            exact Hclo. }
          { (* HIn picks an old (Some length l1) meta-fact in x.sent *)
            specialize (Hold_get _ _ _ HIn_old).
            fwd. exists mf_concls0, mf_hyps0. split; [exact Hold_getp0|].
            cbv [can_deduce_meta_fact] in Hold_getp1 |- *.
            destruct Hold_getp1 as (ctx & hyps & mf_rel' & mf_args' & mf_cnt' & Hres & HEx & Hconcl & Hinterp & Hknown_hyps & Hclo).
            injection Hres as Heq1 Heq2 Heq3.
            subst mf_rel' mf_args' mf_cnt'.
            exists ctx, hyps, R, mf_args, num. split; [reflexivity|].
            split.
            { simpl. rewrite Hnf_eq. apply Existsn_no; [|assumption].
              intros [nf_args2 [Heq Hmatch]]. discriminate. }
            split; [exact Hconcl|]. split; [exact Hinterp|]. split; [exact Hknown_hyps|].
            exact Hclo. }
        * (* n < length l1 *)
          replace ((n ?= length l1)) with Lt in Hk_rsi by (symmetry; apply Nat.compare_lt_iff; lia).
          rewrite nth_error_map in Hk_rsi.
          destruct (nth_error l1 n) as [pair_n|] eqn:Hl1n; [|discriminate].
          simpl in Hk_rsi. injection Hk_rsi as Hri.
          assert (Hsn : nth_error s n = Some rs_inner).
          { rewrite Hs_eq, nth_error_app1 by (rewrite length_map; lia).
            rewrite nth_error_map, Hl1n. simpl. f_equal. assumption. }
          specialize (Hold_get _ _ _ Hk_r Hsn). exact Hold_get.
        * (* n > length l1 *)
          replace ((n ?= length l1)) with Gt in Hk_rsi by (symmetry; apply Nat.compare_gt_iff; lia).
          rewrite nth_error_map in Hk_rsi.
          destruct (nth_error l2 (n - length l1 - 1)) as [pair_n|] eqn:Hl2n; [|discriminate].
          simpl in Hk_rsi. injection Hk_rsi as Hri.
          assert (Hsn : nth_error s n = Some rs_inner).
          { rewrite Hs_eq, nth_error_app2 by (rewrite length_map; lia).
            rewrite length_map.
            assert (Hoff : n - length l1 = S (n - length l1 - 1)) by lia.
            rewrite Hoff. simpl. rewrite nth_error_map, Hl2n. simpl. f_equal. assumption. }
          specialize (Hold_get _ _ _ Hk_r Hsn). exact Hold_get.
  Qed.

  Lemma steps_preserves_sane inputs s s' :
    good_input_facts inputs ->
    sane_state inputs s ->
    comp_step^* s s' ->
    sane_state inputs s'.
  Proof.
    intros Hinp Hsane Hsteps. induction Hsteps; auto.
    apply IHHsteps; auto.
    eapply step_preserves_sane; eassumption.
  Qed.

  Lemma steps_preserves_mfs_correct inputs s s' :
    good_input_facts inputs ->
    sane_state inputs s ->
    meta_facts_correct s ->
    comp_step^* s s' ->
    meta_facts_correct s'.
  Proof.
    intros Hinp Hsane Hmfc Hsteps. induction Hsteps; auto.
    apply IHHsteps; auto.
    - eapply step_preserves_sane; eassumption.
    - eapply step_preserves_mfs_correct; eassumption.
  Qed.

  Definition has_derived_datalog_fact (s : state) (f : fact) :=
    match f with
    | normal_fact R args => knows_dfact s (normal_dfact R args)
    | meta_fact R mf_args mf_set =>
        if is_input R then
          exists num, knows_dfact s (meta_dfact R mf_args None num)
        else
          forall k, k < length p.(non_meta_rules) ->
            exists num,
              knows_dfact s (meta_dfact R mf_args (Some k) num)
    end.

  Definition mf_consistent_state (s : state) (f : fact) :=
    match f with
    | normal_fact _ _ => True
    | meta_fact R mf_args mf_set =>
        forall nf_args,
          Forall2 matches mf_args nf_args ->
          mf_set nf_args <-> knows_dfact s (normal_dfact R nf_args)
    end.

  Definition state_correct (inputs : list dfact) (s : state) :=
    forall f,
      has_derived_datalog_fact s f /\ mf_consistent_state s f ->
      prog_impl rules_of (knows_datalog_fact inputs) f.

  (* Lift a per-rule [knows_datalog_fact rs.known h] to [has_derived_datalog_fact s h]
     for any rs in s.  For normal facts this is just "exists rs with the dfact".  For
     meta facts the input branch uses the [expect_num_R_facts] count directly; the
     non-input branch extracts the per-source-rule count witness from the Forall2. *)
  Lemma knows_datalog_fact_local_lift_has_derived inputs s rs h :
    good_input_facts inputs ->
    sane_state inputs s ->
    In rs s ->
    knows_datalog_fact rs.(known_facts) h ->
    has_derived_datalog_fact s h.
  Proof.
    intros _ Hsane Hin Hkdf.
    destruct h as [R0 args0 | R0 mf_args0 mf_set0]; simpl in Hkdf |- *.
    - cbv [knows_dfact]. apply Exists_exists. exists rs. split; [exact Hin|].
      left. exact Hkdf.
    - destruct Hkdf as (num & Hsat & _ & _).
      cbv [expect_num_R_facts] in Hsat.
      destruct (is_input R0) eqn:HER0.
      + exists num. cbv [knows_dfact]. apply Exists_exists.
        exists rs. split; [exact Hin|]. left. exact Hsat.
      + intros k Hk. destruct Hsat as (msgss & Hf2 & _).
        pose proof (Forall2_length Hf2) as Hlen_msgs. rewrite length_seq in Hlen_msgs.
        assert (Hk_seq : nth_error (seq 0 (length p.(non_meta_rules))) k = Some k).
        { rewrite nth_error_seq.
          assert (E : k <? length p.(non_meta_rules) = true) by (apply Nat.ltb_lt; exact Hk).
          rewrite E. reflexivity. }
        assert (Hk_msg : exists m, nth_error msgss k = Some m).
        { destruct (nth_error msgss k) eqn:E; [eauto|].
          apply nth_error_None in E. lia. }
        destruct Hk_msg as (m & Hkm).
        pose proof (Forall2_nth_error_fwd _ _ _ Hf2 k k m Hk_seq Hkm) as Hin_m.
        exists m. cbv [knows_dfact]. apply Exists_exists. exists rs.
        split; [exact Hin|]. left. exact Hin_m.
  Qed.

  Lemma knows_datalog_fact_local_lift_mf_consistent inputs s rs h :
    good_input_facts inputs ->
    sane_state inputs s ->
    In rs s ->
    knows_datalog_fact rs.(known_facts) h ->
    mf_consistent_state s h.
  Proof.
    intros Hinp Hsane Hin Hkdf.
    destruct h as [R0 args0 | R0 mf_args0 mf_set0]; simpl; [exact I|].
    intros nf_args Hmatch.
    destruct Hkdf as (num & Hsat & Hexn & Hbic).
    specialize (Hbic _ Hmatch). rewrite Hbic. split.
    - intros Hin_k. cbv [knows_dfact]. apply Exists_exists. exists rs.
      split; [exact Hin|]. left. exact Hin_k.
    - intros Hkd.
      pose proof Hsane as (_ & _ & _ & Heverywhere & _ & _).
      pose proof (Heverywhere _ Hkd) as Hev. rewrite Forall_forall in Hev.
      specialize (Hev _ Hin). cbv [rule_has_dfact] in Hev.
      destruct Hev as [Hin_k | Hin_w]; [exact Hin_k|].
      exfalso. eapply expect_num_R_facts_no_waiting; eassumption.
  Qed.

  Lemma send_fact_rule_has_dfact F rs f :
    rule_has_dfact (send_fact F rs) f <-> rule_has_dfact rs f.
  Proof. cbv [send_fact rule_has_dfact]. simpl. reflexivity. Qed.

  Lemma knows_dfact_send_fact_in_middle F l1 x l2 f :
    knows_dfact (l1 ++ send_fact F x :: l2) f <-> knows_dfact (l1 ++ x :: l2) f.
  Proof.
    cbv [knows_dfact]. split; apply exists_swap; cbv [send_fact rule_has_dfact]; simpl; auto.
  Qed.

  Lemma knows_dfact_add_waiting_mono F s g :
    knows_dfact s g -> knows_dfact (map (add_waiting_fact F) s) g.
  Proof.
    cbv [knows_dfact]. intros HE. apply Exists_exists in HE. apply Exists_exists.
    destruct HE as (rs & Hin & Hd). exists (add_waiting_fact F rs).
    split; [apply in_map; exact Hin|].
    cbv [add_waiting_fact rule_has_dfact] in *. simpl. intuition.
  Qed.

  Lemma knows_dfact_after_step_bw F l1 x l2 f :
    f = F \/ knows_dfact (l1 ++ x :: l2) f ->
    knows_dfact (map (add_waiting_fact F) (l1 ++ send_fact F x :: l2)) f.
  Proof.
    intros [Heq|Hkd].
    - subst f. cbv [knows_dfact rule_has_dfact add_waiting_fact send_fact].
      rewrite map_app. simpl. apply Exists_app. right.
      apply Exists_cons_hd. simpl. right. left. reflexivity.
    - rewrite <- knows_dfact_send_fact_in_middle in Hkd.
      cbv [knows_dfact] in *.
      apply Exists_exists in Hkd. apply Exists_exists.
      destruct Hkd as (rs & Hin & Hd). exists (add_waiting_fact F rs).
      split.
      + apply in_map_iff. exists rs. split; [reflexivity|exact Hin].
      + cbv [add_waiting_fact rule_has_dfact] in *. simpl. intuition.
  Qed.

  Lemma learn_fact_preserves_knows_dfact s s' f :
    stepOne learn_fact_at_rule s s' ->
    knows_dfact s f <-> knows_dfact s' f.
  Proof.
    intros (l1 & x & y & l2 & Hs & Hs' & Hlfr).
    pose proof (learn_fact_at_rule_rule_has_dfact _ _ Hlfr f) as Hpres.
    subst. cbv [knows_dfact]. split; apply exists_swap; apply Hpres.
  Qed.

  Lemma learn_fact_preserves_has_derived_datalog_fact s s' f :
    stepOne learn_fact_at_rule s s' ->
    has_derived_datalog_fact s f <-> has_derived_datalog_fact s' f.
  Proof.
    intros Hstep. cbv [has_derived_datalog_fact].
    destruct f as [R args | R mf_args mf_set]; [apply learn_fact_preserves_knows_dfact; assumption|].
    destruct (is_input R).
    - split; intros (num & Hk); exists num;
        apply (learn_fact_preserves_knows_dfact _ _ _ Hstep); assumption.
    - split; intros H k Hk; specialize (H k Hk);
        destruct H as (num & Hk_d); exists num;
        apply (learn_fact_preserves_knows_dfact _ _ _ Hstep); assumption.
  Qed.

  Lemma learn_fact_preserves_mf_consistent_state s s' f :
    stepOne learn_fact_at_rule s s' ->
    mf_consistent_state s f <-> mf_consistent_state s' f.
  Proof.
    intros Hstep. cbv [mf_consistent_state].
    destruct f as [|R mf_args mf_set]; [reflexivity|].
    split; intros H nf_args Hmatch; specialize (H nf_args Hmatch); rewrite H.
    - apply learn_fact_preserves_knows_dfact. assumption.
    - symmetry. apply learn_fact_preserves_knows_dfact. assumption.
  Qed.

  Lemma good_inputs_knows_datalog_fact_inputs inputs :
    good_input_facts inputs ->
    0 < length p.(non_meta_rules) ->
    good_inputs rules_of (knows_datalog_fact inputs).
  Proof.
    intros Hinp Hlt. split.
    - intros f Hf. destruct f as [R0 args0 | R0 mf_args0 mf_set0]; simpl in Hf.
      + destruct Hinp as (Hinp_all & _). rewrite Forall_forall in Hinp_all.
        specialize (Hinp_all _ Hf). simpl in Hinp_all.
        intros Hin_concl. apply in_flat_map in Hin_concl.
        destruct Hin_concl as (r0 & Hin_r0 & Hin_rel).
        unfold rules_of in Hin_r0. apply in_app_or in Hin_r0.
        destruct Hin_r0 as [Hin_meta | Hin_nm].
        * apply in_map_iff in Hin_meta.
          destruct Hin_meta as ((c0, h0) & Heq & Hin_mr0). subst r0.
          simpl in Hin_rel. apply in_map_iff in Hin_rel.
          destruct Hin_rel as (mc & Hrel_eq & Hin_mc).
          rewrite Forall_forall in Hp_meta_input.
          specialize (Hp_meta_input _ Hin_mr0). simpl in Hp_meta_input.
          rewrite Forall_forall in Hp_meta_input.
          specialize (Hp_meta_input _ Hin_mc).
          rewrite Hrel_eq in Hp_meta_input. congruence.
        * apply in_map_iff in Hin_nm.
          destruct Hin_nm as (nmr & Heq & Hin_nmr). subst r0.
          rewrite Forall_forall in Hp_input.
          specialize (Hp_input _ Hin_nmr).
          destruct nmr as [cs hs | cr ag hr]; simpl in Hin_rel, Hp_input.
          -- apply in_map_iff in Hin_rel.
             destruct Hin_rel as (c & Hrel_eq & Hin_c).
             rewrite Forall_forall in Hp_input. specialize (Hp_input _ Hin_c).
             rewrite Hrel_eq in Hp_input. congruence.
          -- destruct Hin_rel as [Hrel_eq|[]]. subst cr. congruence.
      + destruct Hf as (num0 & Hexp & _ & _).
        cbv [expect_num_R_facts] in Hexp.
        destruct (is_input R0) eqn:HER0.
        * intros Hin_concl. apply in_flat_map in Hin_concl.
          destruct Hin_concl as (r0 & Hin_r0 & Hin_rel).
          unfold rules_of in Hin_r0. apply in_app_or in Hin_r0.
          destruct Hin_r0 as [Hin_meta | Hin_nm].
          -- apply in_map_iff in Hin_meta.
             destruct Hin_meta as ((c0, h0) & Heq & Hin_mr0). subst r0.
             simpl in Hin_rel. apply in_map_iff in Hin_rel.
             destruct Hin_rel as (mc & Hrel_eq & Hin_mc).
             rewrite Forall_forall in Hp_meta_input.
             specialize (Hp_meta_input _ Hin_mr0). simpl in Hp_meta_input.
             rewrite Forall_forall in Hp_meta_input.
             specialize (Hp_meta_input _ Hin_mc).
             rewrite Hrel_eq in Hp_meta_input. simpl in Hp_meta_input. congruence.
          -- apply in_map_iff in Hin_nm.
             destruct Hin_nm as (nmr & Heq & Hin_nmr). subst r0.
             rewrite Forall_forall in Hp_input.
             specialize (Hp_input _ Hin_nmr).
             destruct nmr as [cs hs | cr ag hr]; simpl in Hin_rel, Hp_input.
             ++ apply in_map_iff in Hin_rel.
                destruct Hin_rel as (c & Hrel_eq & Hin_c).
                rewrite Forall_forall in Hp_input. specialize (Hp_input _ Hin_c).
                rewrite Hrel_eq in Hp_input. simpl in Hp_input. congruence.
             ++ destruct Hin_rel as [Hrel_eq|[]]. subst cr. simpl in Hp_input.
                congruence.
        * destruct Hexp as (msgss & Hf2_msgs & _).
          pose proof (Forall2_length Hf2_msgs) as Hlen_msgs.
          rewrite length_seq in Hlen_msgs.
          assert (H0_seq : nth_error (seq 0 (length p.(non_meta_rules))) 0 = Some 0).
          { rewrite nth_error_seq.
            assert (E : 0 <? length p.(non_meta_rules) = true)
              by (apply Nat.ltb_lt; exact Hlt).
            rewrite E. reflexivity. }
          assert (H0_msg : exists m, nth_error msgss 0 = Some m).
          { destruct (nth_error msgss 0) eqn:Em; [eauto|].
            apply nth_error_None in Em. lia. }
          destruct H0_msg as (m0 & Hm0).
          pose proof (Forall2_nth_error_fwd _ _ _ Hf2_msgs 0 0 m0 H0_seq Hm0)
            as Hin_m0.
          destruct Hinp as (Hinp_all & _). rewrite Forall_forall in Hinp_all.
          specialize (Hinp_all _ Hin_m0). simpl in Hinp_all. congruence.
    - cbv [doesnt_lie consistent]. intros mfr0 mfa0 mfs0 Hin nf_args0 Hmatch_nf.
      simpl in Hin. destruct Hin as (num0 & _ & _ & Hbic).
      simpl. apply Hbic. exact Hmatch_nf.
  Qed.

  Lemma use_meta_facts_correct (R : rel) (mf_args : list (option T))
    (inputs : list dfact) (s : state) :
    good_input_facts inputs ->
    sane_state inputs s ->
    meta_facts_correct s ->
    is_input R = false ->
    (forall mf_rel' mf_args' mf_set',
        (R, mf_args) <> (mf_rel', mf_args') ->
        has_derived_datalog_fact s (meta_fact mf_rel' mf_args' mf_set') /\
        mf_consistent_state s (meta_fact mf_rel' mf_args' mf_set') ->
        prog_impl rules_of (knows_datalog_fact inputs) (meta_fact mf_rel' mf_args' mf_set')) ->
    has_derived_datalog_fact s (meta_fact R mf_args (fun _ => True)) ->
    forall nf_args,
      Forall2 matches mf_args nf_args ->
      prog_impl rules_of (knows_datalog_fact inputs) (normal_fact R nf_args) ->
      knows_dfact s (normal_dfact R nf_args).
  Proof.
    intros Hinp Hsane Hmf HER HRs HR nf_args Hmatch Hprog.
    invert Hprog.
    - (* Q-leaf: contradicts is_input R = false *)
      simpl in H.
      destruct Hinp as (Hinp_all & _). rewrite Forall_forall in Hinp_all.
      specialize (Hinp_all _ H). simpl in Hinp_all. congruence.
    - (* rule_step: rule r in rules_of derives normal_fact R nf_args from hyps *)
      rename H into Hrule_exists. rename H0 into Hhyps. rename l into hyps.
      apply Exists_exists in Hrule_exists.
      destruct Hrule_exists as (r & Hin_r & Hrule_impl).
      invert Hrule_impl.
      (* After invert, we have a non_meta_rule_impl hypothesis (named by Coq) *)
      match goal with H : non_meta_rule_impl _ _ _ _ |- _ => rename H into Hnmri end.
      (* Find k such that r = rule_of r_k *)
      unfold rules_of in Hin_r. apply in_app_or in Hin_r.
      destruct Hin_r as [Hin_meta_r | Hin_nonmeta_r].
      { (* r is a meta_rule, but non_meta_rule_impl r requires r = normal_rule or agg_rule *)
        apply in_map_iff in Hin_meta_r. destruct Hin_meta_r as ((c & h) & Heq_r & _).
        subst r. invert Hnmri. }
      apply in_map_iff in Hin_nonmeta_r.
      destruct Hin_nonmeta_r as (r_k & Heq_r & Hin_rk).
      subst r.
      pose proof Hin_rk as Hin_rk_save.
      apply In_nth_error in Hin_rk. destruct Hin_rk as (k & Hnth_k).
      rename Hin_rk_save into Hin_rk.
      apply nth_error_Some_bound_index in Hnth_k as Hk_lt.
      (* Extract meta-fact knowledge for index k *)
      simpl in HR. rewrite HER in HR.
      specialize (HR _ Hk_lt). destruct HR as (num_k & Hkknows).
      pose proof Hsane as (Hlen & Hmf_inp & Hmf_sent & Heverywhere & Hcount & Hinp_sane).
      pose proof (Hmf_sent _ _ _ _ Hkknows) as Hsent_k.
      cbv [nth_sat] in Hsent_k.
      destruct (nth_error s k) as [rs_k|] eqn:Hnth_s; [|contradiction].
      destruct Hsent_k as (Hexn_k & Hin_k_sent).
      (* By meta_facts_correct, can_deduce_meta_fact witness at index k *)
      cbv [meta_facts_correct] in Hmf.
      assert (Hk_seq : nth_error (seq 0 (length s)) k = Some k).
      { rewrite nth_error_seq.
        assert (E : k <? length s = true) by (apply Nat.ltb_lt; lia).
        rewrite E. reflexivity. }
      assert (Hmf_k : meta_facts_correct_at_rule p.(meta_rules) k rs_k r_k).
      { eapply (Forall3_nth_error_fwd _ _ _ _ Hmf); eassumption. }
      cbv [meta_facts_correct_at_rule] in Hmf_k.
      specialize (Hmf_k _ _ _ Hin_k_sent).
      destruct Hmf_k as (mf_concls & mf_hyps & Hin_mr & Hcan).
      cbv [can_deduce_meta_fact] in Hcan.
      destruct Hcan as (ctx & hyps_d & mf_rel_c & mf_args_c & mf_cnt_c
                       & Heq_F & Hexn_F & Hconcl & Hf2_h & Hkdf_h & Hsound_can).
      injection Heq_F as Hr_eq Ha_eq Hc_eq.
      subst mf_rel_c mf_args_c mf_cnt_c.
      (* Build can_deduce_normal_fact: hyps are in rs_k.known *)
      assert (Hcan_nf : can_deduce_normal_fact r_k rs_k.(known_facts) R nf_args).
      { cbv [can_deduce_normal_fact]. exists hyps. split; [exact Hnmri|].
        (* Build prog_impl ... (meta_fact R mf_args S_constr) for use with
           meta_rules_valid to get fact_potentially_supported. *)
        pose (S_constr := fun args'' => one_step_derives rules_of hyps_d R args'').
        assert (Hmr_impl :
                  rule_impl (one_step_derives rules_of) (meta_rule mf_concls mf_hyps)
                    (meta_fact R mf_args S_constr) hyps_d).
        { apply meta_rule_impl with (ctx := ctx).
          - eapply Exists_impl; [|exact Hconcl].
            intros c Hclause. cbv [interp_meta_clause] in Hclause |- *.
            destruct Hclause as (mfa_v & mfs_v & Hf2_v & Heq_v).
            injection Heq_v as Hcrel Hcargs _.
            exists mfa_v, S_constr. rewrite Hcargs. split; [exact Hf2_v|].
            rewrite <- Hcrel. reflexivity.
          - exact Hf2_h.
          - intros args'' Hmatch_args''. subst S_constr. reflexivity. }
        assert (Hnr_impl :
                  rule_impl (one_step_derives rules_of) (rule_of r_k)
                    (normal_fact R nf_args) hyps).
        { apply simple_rule_impl. exact Hnmri. }
        assert (Hin_mr_rules : In (meta_rule mf_concls mf_hyps) rules_of).
        { unfold rules_of. apply in_or_app. left. apply in_map_iff.
          exists (mf_concls, mf_hyps). split; [reflexivity|exact Hin_mr]. }
        assert (Hin_nr_rules : In (rule_of r_k) rules_of).
        { unfold rules_of. apply in_or_app. right. apply in_map. exact Hin_rk. }
        pose proof (Hmeta_rules _ _ _ _ _ Hin_mr_rules Hmr_impl _ _ _
                                Hin_nr_rules Hnr_impl Hmatch) as Hpot.
        (* For each hyp h, fact_potentially_supported hyps_d h.  Lift to
           knows_datalog_fact rs_k.known h via the meta-fact in hyps_d. *)
        rewrite Forall_forall. intros h Hh.
        rewrite Forall_forall in Hpot, Hkdf_h, Hhyps.
        pose proof (Hpot _ Hh) as Hpot_h.
        pose proof (Hhyps _ Hh) as Hprog_h.
        assert (Hgood_inputs_Q : good_inputs rules_of (knows_datalog_fact inputs)).
        { apply good_inputs_knows_datalog_fact_inputs; [exact Hinp|]. lia. }
        pose proof (valid_impl_honest _ Hmeta_rules _ Hgood_inputs_Q) as Hhonest.
        cbv [doesnt_lie] in Hhonest.
        assert (Hin_rs_k : In rs_k s) by (eapply nth_error_In; eassumption).
        (* Now handle h based on its shape *)
        destruct h as [R' args' | R' mf_args' mf_set'_h].
        + (* normal hyp *)
          cbv [fact_potentially_supported] in Hpot_h.
          destruct Hpot_h as (mf_args' & mf_set'_m & Hin_m & Hmatch_m).
          pose proof (Hkdf_h _ Hin_m) as Hkd_m.
          destruct (classic ((R, mf_args) = (R', mf_args'))) as [Heq | Hne].
          * (* self-recursive case: admit (needs recursion or stronger invariant) *)
            admit.
          * (* non-self-recursive case *)
            pose proof (knows_datalog_fact_local_lift_has_derived _ _ _ _ Hinp Hsane Hin_rs_k Hkd_m) as Hhd_m.
            pose proof (knows_datalog_fact_local_lift_mf_consistent _ _ _ _ Hinp Hsane Hin_rs_k Hkd_m) as Hmc_m.
            pose proof (HRs _ _ _ Hne (conj Hhd_m Hmc_m)) as Hprog_m.
            pose proof (Hhonest _ _ _ Hprog_m) as Hcon_m.
            cbv [consistent] in Hcon_m.
            specialize (Hcon_m _ Hmatch_m).
            apply Hcon_m in Hprog_h.
            simpl in Hkd_m. destruct Hkd_m as (num_m & _ & _ & Hbic_m).
            specialize (Hbic_m _ Hmatch_m).
            simpl. apply Hbic_m. exact Hprog_h.
        + (* meta hyp *)
          cbv [fact_potentially_supported] in Hpot_h.
          destruct Hpot_h as (mf_set'_m & Hin_m).
          pose proof (Hkdf_h _ Hin_m) as Hkd_m.
          destruct (classic ((R, mf_args) = (R', mf_args'))) as [Heq | Hne].
          * (* self-recursive case: admit *)
            admit.
          * (* non-self-recursive *)
            pose proof (knows_datalog_fact_local_lift_has_derived _ _ _ _ Hinp Hsane Hin_rs_k Hkd_m) as Hhd_m.
            pose proof (knows_datalog_fact_local_lift_mf_consistent _ _ _ _ Hinp Hsane Hin_rs_k Hkd_m) as Hmc_m.
            pose proof (HRs _ _ _ Hne (conj Hhd_m Hmc_m)) as Hprog_m.
            pose proof (Hhonest _ _ _ Hprog_m) as Hcon_m.
            pose proof (Hhonest _ _ _ Hprog_h) as Hcon_h.
            cbv [consistent] in Hcon_m, Hcon_h.
            (* Both consistent: mf_set'_h and mf_set'_m agree with prog_impl_normal *)
            simpl in Hkd_m |- *.
            destruct Hkd_m as (num_m & Hexp_m & Hexn_m & Hbic_m).
            exists num_m. split; [exact Hexp_m|]. split; [exact Hexn_m|].
            intros nf_args0 Hmatch_nf.
            specialize (Hbic_m _ Hmatch_nf).
            specialize (Hcon_m _ Hmatch_nf).
            specialize (Hcon_h _ Hmatch_nf).
            rewrite Hcon_h, <- Hcon_m. exact Hbic_m. }
      (* Apply soundness clause *)
      specialize (Hsound_can _ Hcan_nf Hmatch).
      cbv [knows_dfact]. apply Exists_exists. exists rs_k. split.
      + apply nth_error_In with k. exact Hnth_s.
      + left. exact Hsound_can.
  Admitted.

  Lemma comp_step_sound inputs s s' :
    good_input_facts inputs ->
    sane_state inputs s ->
    meta_facts_correct s ->
    state_correct inputs s ->
    comp_step s s' ->
    state_correct inputs s'.
  Proof.
    intros Hinp Hsane Hmfc Hsound Hstep f (Hf1 & Hf2).
    invert Hstep.
    - (* learn_fact: waiting -> known at some rule.  Nothing new known. *)
      apply Hsound. split.
      + apply (learn_fact_preserves_has_derived_datalog_fact _ _ _ H); assumption.
      + apply (learn_fact_preserves_mf_consistent_state _ _ _ H); assumption.
    - (* fire_normal_rule: new normal fact F = normal_dfact nf_rel nf_args added to
         waiting at all rules; one rule additionally has F in its sent_facts. *)
      rename H into HstepL.
      set (F := normal_dfact nf_rel nf_args) in *.
      cbv [stepWithLabel] in HstepL.
      destruct HstepL as (l1 & label_fire & x & y & l2 & Hcomb & Hs2_eq & Hstepfire).
      destruct label_fire as (r_fire & k_fire).
      destruct Hstepfire as (Hded & Hno_sent & Hy_eq). subst y.
      assert (Hlen_s : length s = length p.(non_meta_rules))
        by (destruct Hsane as (H0&_); exact H0).
      assert (Hlc : length (combine (non_meta_rules p) (seq 0 (length s))) = length s).
      { rewrite length_combine, length_seq. lia. }
      assert (Hs_eq : s = map snd l1 ++ x :: map snd l2).
      { apply (f_equal (map snd)) in Hcomb.
        rewrite map_combine_snd in Hcomb by assumption.
        rewrite map_app in Hcomb. simpl in Hcomb. exact Hcomb. }
      (* knows_dfact s' g <-> g = F \/ knows_dfact s g *)
      assert (Hkd_iff : forall g,
                 knows_dfact (map (add_waiting_fact F) s2) g <-> g = F \/ knows_dfact s g).
      { intros g. rewrite Hs2_eq, Hs_eq. split.
        - apply knows_dfact_after_step.
        - apply knows_dfact_after_step_bw. }
      (* knows_dfact s' (meta_dfact ...) iff knows_dfact s (meta_dfact ...) since F is normal *)
      assert (Hkd_meta : forall R0 mf_args0 opt num,
                 knows_dfact (map (add_waiting_fact F) s2) (meta_dfact R0 mf_args0 opt num) <->
                 knows_dfact s (meta_dfact R0 mf_args0 opt num)).
      { intros. rewrite Hkd_iff. split; [intros [Heq|Hkd]|tauto].
        - subst F. discriminate.
        - assumption. }
      destruct f as [R args | R mf_args mf_set].
      + (* f = normal_fact R args *)
        simpl in Hf1. apply Hkd_iff in Hf1. destruct Hf1 as [Heq|Hf1].
        * (* args is the newly fired fact's args *)
          subst F. injection Heq as -> ->.
          (* Use the firing rule to derive prog_impl ... (normal_fact nf_rel nf_args) *)
          assert (Hin_r : In r_fire p.(non_meta_rules)).
          { assert (Hin_out : In (r_fire, k_fire, x)
                             (combine (combine (non_meta_rules p) (seq 0 (length s))) s)).
            { rewrite Hcomb. apply in_or_app. right. simpl. auto. }
            apply in_combine_l in Hin_out. apply in_combine_l in Hin_out. exact Hin_out. }
          destruct Hded as (hyps & Hnmri & Hkdf_hyps).
          eapply prog_impl_step.
          -- apply Exists_exists. exists (rule_of r_fire). split.
             ++ unfold rules_of. apply in_or_app. right. apply in_map. exact Hin_r.
             ++ apply simple_rule_impl. exact Hnmri.
          -- (* Forall (prog_impl rules_of (knows_datalog_fact inputs)) hyps *)
             rewrite Forall_forall in Hkdf_hyps |- *. intros h Hin_h.
             specialize (Hkdf_hyps _ Hin_h).
             destruct h as [R' args' | R' mf_args' mf_set'].
             ++ (* normal hyp: lift via helper *)
                apply Hsound. split.
                ** eapply knows_datalog_fact_local_lift_has_derived; try eassumption.
                   rewrite Hs_eq. apply in_or_app. right. apply in_eq.
                ** eapply knows_datalog_fact_local_lift_mf_consistent; try eassumption.
                   rewrite Hs_eq. apply in_or_app. right. apply in_eq.
             ++ (* meta hyp: lift via helper *)
                apply Hsound. split.
                ** eapply knows_datalog_fact_local_lift_has_derived; try eassumption.
                   rewrite Hs_eq. apply in_or_app. right. apply in_eq.
                ** eapply knows_datalog_fact_local_lift_mf_consistent; try eassumption.
                   rewrite Hs_eq. apply in_or_app. right. apply in_eq.
        * (* old normal fact; apply Hsound on s *)
          apply Hsound. simpl. split; [exact Hf1|exact I].
      + (* f = meta_fact R mf_args mf_set.  Lift Hf1 from s' to s via Hkd_meta.
           For Hf2: when R != nf_rel, F = normal_dfact nf_rel ... can't equal
           normal_dfact R nf_args, so knows_dfact unchanged; lift directly.
           When R = nf_rel, the new fact may force mf_set nf_args_fire = true
           even though knows_dfact s (normal nf_rel nf_args_fire) might be false.
           That sub-case is admitted below. *)
        simpl in Hf1, Hf2.
        assert (Hf1_s : has_derived_datalog_fact s (meta_fact R mf_args mf_set)).
        { simpl. destruct (is_input R) eqn:HER.
          - destruct Hf1 as (num & Hk). exists num. apply Hkd_meta in Hk. exact Hk.
          - intros k Hk. specialize (Hf1 k Hk). destruct Hf1 as (num & Hknk).
            exists num. apply Hkd_meta in Hknk. exact Hknk. }
        destruct (classic (R = nf_rel)) as [HReq | HRneq].
        * (* R = nf_rel: Hf2 says mf_set nf_args <-> (nf_args = nf_args_fire) OR
             knows_dfact s (normal nf_rel nf_args).  Lift to mf_consistent_state s f
             succeeds EXCEPT when nf_args_fire matches mf_args AND
             ~knows_dfact s (normal nf_rel nf_args_fire) — case (iii) below.  In
             that sub-case mf_consistent_state s f is genuinely violated and
             Hsound is unusable; the derivation must come from the firing rule. *)
          subst R.
          assert (Hf2_s : mf_consistent_state s (meta_fact nf_rel mf_args mf_set)).
          { simpl. intros nf_args0 Hmatch0. specialize (Hf2 _ Hmatch0).
            destruct (classic (nf_args0 = nf_args)) as [-> | HNe].
            - (* nf_args0 = nf_args (the newly fired fact's args).  Need
                 mf_set nf_args <-> knows_dfact s (normal nf_rel nf_args). *)
              destruct (classic (knows_dfact s (normal_dfact nf_rel nf_args)))
                as [Hk | Hnk].
              + (* case (ii) knows_dfact s = true: Hf2 RHS reduces to true *)
                split; intros _; [exact Hk|].
                rewrite Hf2, Hkd_iff. right. exact Hk.
              + (* case (iii): knows_dfact s = false.  In fact this case is
                   IMPOSSIBLE: has_derived_datalog_fact s f (which holds via
                   Hf1_s, but we don't have it here in the consistent assert)
                   would force a (Some k_fire) meta_dfact in s for (nf_rel,
                   mf_args), and by Hmf_sent it'd be in x.sent_facts, which
                   contradicts the fire_normal_rule precondition Hno_sent.
                   We derive False directly from Hf1_s. *)
                exfalso.
                assert (Hin_r : In r_fire (non_meta_rules p)).
                { assert (Hin_out : In (r_fire, k_fire, x)
                    (combine (combine (non_meta_rules p) (seq 0 (length s))) s)).
                  { rewrite Hcomb. apply in_or_app. right. simpl. auto. }
                  apply in_combine_l in Hin_out.
                  apply in_combine_l in Hin_out. exact Hin_out. }
                assert (Hgood_r : good_non_meta_rule r_fire).
                { rewrite Forall_forall in Hp_input. apply Hp_input. exact Hin_r. }
                assert (HNI : is_input nf_rel = false).
                { eapply can_deduce_implies_not_input; eassumption. }
                assert (Hk_eq : k_fire = length l1).
                { assert (Hlen_seq : length (non_meta_rules p) = length (seq 0 (length s))).
                  { rewrite length_seq. lia. }
                  pose proof Hcomb as Hp0a.
                  apply (f_equal (map fst)) in Hp0a.
                  rewrite map_app in Hp0a. simpl in Hp0a.
                  rewrite map_combine_fst in Hp0a by assumption.
                  apply (f_equal (map snd)) in Hp0a.
                  rewrite map_app in Hp0a. simpl in Hp0a.
                  rewrite map_combine_snd in Hp0a by assumption.
                  pose proof (f_equal (fun ll => nth_error ll (length l1)) Hp0a) as HnE.
                  cbv beta in HnE.
                  rewrite nth_error_app_middle in HnE.
                  rewrite ! length_map in HnE.
                  rewrite Nat.compare_refl in HnE.
                  rewrite nth_error_seq in HnE.
                  assert (E : length l1 <? length s = true).
                  { apply Nat.ltb_lt.
                    rewrite Hs_eq, length_app, ! length_map. simpl. lia. }
                  rewrite E in HnE.
                  injection HnE as ->. lia. }
                cbv [has_derived_datalog_fact] in Hf1_s.
                rewrite HNI in Hf1_s.
                assert (Hk_lt : k_fire < length p.(non_meta_rules)).
                { rewrite Hk_eq. rewrite <- Hlen_s.
                  rewrite Hs_eq, length_app, ! length_map. simpl. lia. }
                specialize (Hf1_s _ Hk_lt). destruct Hf1_s as (num & Hknows).
                pose proof Hsane as (_ & _ & Hmf_sent & _ & _ & _).
                specialize (Hmf_sent _ _ _ _ Hknows).
                cbv [nth_sat] in Hmf_sent.
                assert (Hnth : nth_error s k_fire = Some x).
                { rewrite Hs_eq, Hk_eq.
                  rewrite nth_error_app2 by (rewrite length_map; lia).
                  rewrite length_map, Nat.sub_diag. reflexivity. }
                rewrite Hnth in Hmf_sent.
                destruct Hmf_sent as (_ & Hin_x).
                eapply Hno_sent; [exact Hin_x | exact Hmatch0].
            - (* case (i) nf_args0 != nf_args: lift Hf2 directly *)
              rewrite Hf2, Hkd_iff. split.
              + intros [Heq | Hk]; [|exact Hk].
                subst F. injection Heq as Heq2. contradiction.
              + intros Hk. right. exact Hk. }
          apply Hsound. split; assumption.
        * (* R != nf_rel: knows_dfact unchanged for (normal R _); lift Hf2 *)
          assert (Hf2_s : mf_consistent_state s (meta_fact R mf_args mf_set)).
          { simpl. intros args0 Hmatch. specialize (Hf2 _ Hmatch).
            rewrite Hf2, Hkd_iff. split.
            - intros [Heq | Hk]; [|exact Hk].
              subst F. injection Heq as Heq1 _. contradiction.
            - intros Hk. right. exact Hk. }
          apply Hsound. split; assumption.
    - (* fire_meta_rule: new meta_fact new_fact added to waiting at all rules;
         one rule additionally has new_fact in its sent_facts. *)
      rename H into Hin_mr.
      rename H0 into HstepL.
      pose proof HstepL as HstepL_save.
      cbv [stepWithLabel] in HstepL.
      destruct HstepL as (l1 & label_fire & x & y & l2 & Hcomb & Hs2_eq & Hstepfire).
      destruct label_fire as (r_fire & k_fire).
      destruct Hstepfire as (Hcan & Hy_eq). subst y.
      set (F := new_fact) in *.
      assert (Hlen_s : length s = length p.(non_meta_rules))
        by (destruct Hsane as (H0&_); exact H0).
      assert (Hlc : length (combine (non_meta_rules p) (seq 0 (length s))) = length s).
      { rewrite length_combine, length_seq. lia. }
      assert (Hs_eq : s = map snd l1 ++ x :: map snd l2).
      { apply (f_equal (map snd)) in Hcomb.
        rewrite map_combine_snd in Hcomb by assumption.
        rewrite map_app in Hcomb. simpl in Hcomb. exact Hcomb. }
      assert (Hkd_iff : forall g,
                 knows_dfact (map (add_waiting_fact F) s2) g <-> g = F \/ knows_dfact s g).
      { intros g. rewrite Hs2_eq, Hs_eq. split.
        - apply knows_dfact_after_step.
        - apply knows_dfact_after_step_bw. }
      (* F is a meta_dfact (from can_deduce_meta_fact), so knows_dfact s'
         (normal _ _) = knows_dfact s (normal _ _). *)
      assert (HF_meta : exists mf_rel mf_args mf_cnt,
                 F = meta_dfact mf_rel mf_args (Some k_fire) mf_cnt).
      { cbv [can_deduce_meta_fact] in Hcan.
        destruct Hcan as (ctx & hyps & mf_rel & mf_args & mf_cnt & Heq & _).
        exists mf_rel, mf_args, mf_cnt. subst F. exact Heq. }
      assert (Hkd_normal : forall R0 args0,
                 knows_dfact (map (add_waiting_fact F) s2) (normal_dfact R0 args0) <->
                 knows_dfact s (normal_dfact R0 args0)).
      { intros. rewrite Hkd_iff. split; [intros [Heq|Hkd]|tauto].
        - destruct HF_meta as (? & ? & ? & ->). discriminate.
        - assumption. }
      destruct f as [R args | R mf_args mf_set].
      + (* f = normal_fact R args: new fact is meta, so Hf1 lifts directly *)
        simpl in Hf1. apply Hkd_normal in Hf1.
        apply Hsound. simpl. split; [exact Hf1|exact I].
      + (* f = meta_fact R mf_args mf_set *)
        simpl in Hf1, Hf2.
        assert (Hf2_s : mf_consistent_state s (meta_fact R mf_args mf_set)).
        { simpl. intros args0 Hmatch. specialize (Hf2 _ Hmatch).
          rewrite Hf2. exact (Hkd_normal R args0). }
        destruct (is_input R) eqn:HER.
        * (* is_input R: F = meta_dfact ... (Some k_fire) can't equal (None _).
             Lift Hf1 and apply Hsound. *)
          destruct Hf1 as (num & Hk).
          rewrite Hkd_iff in Hk.
          destruct Hk as [Heq | Hk_s].
          -- destruct HF_meta as (? & ? & ? & HFeq). rewrite HFeq in Heq. discriminate.
          -- apply Hsound. simpl. split; [|exact Hf2_s].
             simpl. rewrite HER. exists num. exact Hk_s.
        * (* not is_input R.  Case-split on whether F matches the target meta-fact:
             - Case B (F doesn't match): F = meta_dfact mf_rel0 mf_args0 ..., and
               (R, mf_args) != (mf_rel0, mf_args0), so for every k the new fact
               doesn't match meta_dfact R mf_args (Some k) num.  Hf1 lifts to s.
             - Case A (F matches): R = mf_rel0 and mf_args = mf_args0.  Then F is
               the witness for k = k_fire, and s may have no other witness.
               Requires deriving prog_impl ... f via the firing meta-rule. *)
          destruct HF_meta as (mf_rel0 & mf_args0 & mf_cnt0 & HFeq).
          destruct (classic (R = mf_rel0 /\ mf_args = mf_args0)) as [[HReq HMeq] | HNeq].
          -- (* Case A: R = mf_rel0, mf_args = mf_args0.  Further split on whether
                s has a pre-existing witness for k = k_fire:
                  A.1: lift Hf1 to s entirely, apply Hsound.
                  A.2: F is the only witness, must derive via meta_rule_impl
                       + bridge (~100 lines, needs use_meta_facts_correct analog). *)
             subst R mf_args.
             destruct (classic (exists num0,
                          knows_dfact s (meta_dfact mf_rel0 mf_args0 (Some k_fire) num0)))
                as [HA1 | HA2].
             { (* A.1: lift Hf1 to s for all k *)
               assert (Hf1_s : has_derived_datalog_fact s
                                 (meta_fact mf_rel0 mf_args0 mf_set)).
               { simpl. rewrite HER. intros k Hk.
                 destruct (classic (k = k_fire)) as [-> | Hk_ne]; [exact HA1|].
                 specialize (Hf1 k Hk). destruct Hf1 as (num & Hk_s').
                 rewrite Hkd_iff in Hk_s'.
                 destruct Hk_s' as [Heq | Hk_s]; [|exists num; exact Hk_s].
                 exfalso. rewrite HFeq in Heq.
                 injection Heq as Heq_k _. apply Hk_ne. assumption. }
               apply Hsound. split; assumption. }
             (* A.2 below: no pre-existing witness *)
             cbv [can_deduce_meta_fact] in Hcan.
             destruct Hcan as (ctx & hyps_d & mf_rel_c & mf_args_c & mf_cnt_c
                              & Heq_F & Hexn_F & Hexists_concl & Hf2_h & Hkdf_h & Hsound_can).
             rewrite HFeq in Heq_F. injection Heq_F as Hr_eq Ha_eq Hc_eq.
             subst mf_rel_c mf_args_c mf_cnt_c.
             pose (S_constr := fun args'' => one_step_derives rules_of hyps_d mf_rel0 args'').
             assert (Hprog_constr :
                       prog_impl rules_of (knows_datalog_fact inputs)
                         (meta_fact mf_rel0 mf_args0 S_constr)).
             { eapply prog_impl_step.
               - apply Exists_exists. exists (meta_rule mf_concls mf_hyps). split.
                 + unfold rules_of. apply in_or_app. left. apply in_map_iff.
                   exists (mf_concls, mf_hyps). split; [reflexivity|exact Hin_mr].
                 + apply meta_rule_impl with (ctx := ctx).
                   * eapply Exists_impl; [|exact Hexists_concl].
                     intros c Hclause. cbv [interp_meta_clause] in Hclause |- *.
                     destruct Hclause as (mfa_v & mfs_v & Hf2_v & Heq_v).
                     injection Heq_v as Hcrel Hcargs _.
                     exists mfa_v, S_constr. rewrite Hcargs. split; [exact Hf2_v|].
                     rewrite <- Hcrel. reflexivity.
                   * exact Hf2_h.
                   * intros args'' Hmatch_args''. subst S_constr. reflexivity.
               - rewrite Forall_forall in Hkdf_h |- *. intros h Hin_h.
                 specialize (Hkdf_h _ Hin_h).
                 apply Hsound. split.
                 + eapply knows_datalog_fact_local_lift_has_derived; try eassumption.
                   rewrite Hs_eq. apply in_or_app. right. apply in_eq.
                 + eapply knows_datalog_fact_local_lift_mf_consistent; try eassumption.
                   rewrite Hs_eq. apply in_or_app. right. apply in_eq. }
             eapply prog_impl_mf_ext'; [exact Hprog_constr | | ].
             ++ (* iff: S_constr nf_args <-> mf_set nf_args, via use_meta_facts_correct *)
                intros nf_args1 Hmatch1.
                (* Direction setup: use Hhonest to convert S_constr to prog_impl_normal *)
                pose proof Hsane as Hsane'.
                assert (Hstep_comp : comp_step s (map (add_waiting_fact F) s2)).
                { subst F. econstructor; eassumption. }
                assert (Hsane_s' : sane_state inputs (map (add_waiting_fact F) s2)).
                { eapply step_preserves_sane; eassumption. }
                assert (Hmfc_s' : meta_facts_correct (map (add_waiting_fact F) s2)).
                { eapply step_preserves_mfs_correct; [exact Hinp|exact Hsane|exact Hmfc|exact Hstep_comp]. }
                (* HRs for use_meta_facts_correct: state_correct restricted to s'-side *)
                assert (HRs_umfc :
                  forall mf_rel' mf_args' mf_set',
                    (mf_rel0, mf_args0) <> (mf_rel', mf_args') ->
                    has_derived_datalog_fact (map (add_waiting_fact F) s2)
                      (meta_fact mf_rel' mf_args' mf_set') /\
                    mf_consistent_state (map (add_waiting_fact F) s2)
                      (meta_fact mf_rel' mf_args' mf_set') ->
                    prog_impl rules_of (knows_datalog_fact inputs)
                      (meta_fact mf_rel' mf_args' mf_set')).
                { intros mfr' mfa' mfs' Hne (Hhd' & Hmc').
                  (* Lift Hhd' and Hmc' from s' to s *)
                  apply Hsound. split.
                  - (* has_derived_datalog_fact s (meta_fact mfr' mfa' mfs') *)
                    simpl. destruct (is_input mfr') eqn:HERmfr'.
                    + simpl in Hhd'. rewrite HERmfr' in Hhd'.
                      destruct Hhd' as (num & Hk). exists num.
                      rewrite Hkd_iff in Hk. destruct Hk as [Heq | Hk_s]; [|exact Hk_s].
                      exfalso. rewrite HFeq in Heq. discriminate.
                    + simpl in Hhd'. rewrite HERmfr' in Hhd'.
                      intros k Hk. specialize (Hhd' k Hk).
                      destruct Hhd' as (num & Hknk).
                      rewrite Hkd_iff in Hknk.
                      destruct Hknk as [Heq | Hk_s]; [|exists num; exact Hk_s].
                      rewrite HFeq in Heq. injection Heq as -> -> _ _.
                      exfalso. apply Hne. reflexivity.
                  - (* mf_consistent_state s f' *)
                    simpl. intros nf_args2 Hmatch2.
                    simpl in Hmc'. specialize (Hmc' _ Hmatch2).
                    rewrite Hmc'. apply Hkd_normal. }
                assert (Hf1_True : has_derived_datalog_fact (map (add_waiting_fact F) s2)
                                     (meta_fact mf_rel0 mf_args0 (fun _ => True))).
                { simpl. rewrite HER. exact Hf1. }
                pose proof (use_meta_facts_correct mf_rel0 mf_args0 inputs
                              (map (add_waiting_fact F) s2)
                              Hinp Hsane_s' Hmfc_s' HER HRs_umfc
                              Hf1_True nf_args1 Hmatch1) as Humfc.
                assert (Hlen_pos_p : 0 < length p.(non_meta_rules)).
                { rewrite <- Hlen_s, Hs_eq, length_app, ! length_map. simpl. lia. }
                assert (Hgood_inputs_Q : good_inputs rules_of (knows_datalog_fact inputs))
                  by (apply good_inputs_knows_datalog_fact_inputs; assumption).
                pose proof (valid_impl_honest _ Hmeta_rules _ Hgood_inputs_Q) as Hhonest.
                cbv [doesnt_lie] in Hhonest.
                (* Humfc : prog_impl ... (normal_fact mf_rel0 nf_args1) ->
                           knows_dfact s' (normal_dfact mf_rel0 nf_args1) *)
                pose proof (Hhonest _ _ _ Hprog_constr) as Hcon_constr.
                cbv [consistent] in Hcon_constr.
                specialize (Hcon_constr _ Hmatch1).
                rewrite Hcon_constr.
                (* Goal: prog_impl ... (normal_fact mf_rel0 nf_args1) <-> mf_set nf_args1 *)
                split.
                ** (* prog_impl -> mf_set *)
                   intros Hprog. apply Humfc in Hprog.
                   apply (proj2 (Hf2 _ Hmatch1)). exact Hprog.
                ** (* mf_set -> prog_impl *)
                   intros Hms.
                   apply (proj1 (Hf2 _ Hmatch1)) in Hms.
                   apply Hkd_normal in Hms.
                   apply Hsound. simpl. split; [exact Hms|exact I].
             ++ (* ~Q (meta_fact mf_rel0 mf_args0 S_constr): inputs has no
                   (Some k) meta-facts (by good_input_facts), so expect_num_R_facts
                   fails for non-input mf_rel0. *)
                intros HQ. simpl in HQ. destruct HQ as (num & Hexp & _ & _).
                cbv [expect_num_R_facts] in Hexp. rewrite HER in Hexp.
                destruct Hexp as (msgss & Hf2_msgs & _).
                pose proof (Forall2_length Hf2_msgs) as Hlen_msgs.
                rewrite length_seq in Hlen_msgs.
                assert (Hlen_pos : 0 < length p.(non_meta_rules)).
                { rewrite <- Hlen_s. rewrite Hs_eq, length_app. simpl. lia. }
                assert (H0_seq : nth_error (seq 0 (length p.(non_meta_rules))) 0 = Some 0).
                { rewrite nth_error_seq.
                  assert (E : 0 <? length p.(non_meta_rules) = true)
                    by (apply Nat.ltb_lt; exact Hlen_pos).
                  rewrite E. reflexivity. }
                assert (H0_msg : exists m, nth_error msgss 0 = Some m).
                { destruct (nth_error msgss 0) eqn:E; [eauto|].
                  apply nth_error_None in E. lia. }
                destruct H0_msg as (m & H0m).
                pose proof (Forall2_nth_error_fwd _ _ _ Hf2_msgs 0 0 m H0_seq H0m)
                  as Hin_m.
                destruct Hinp as (Hinp_all & _). rewrite Forall_forall in Hinp_all.
                specialize (Hinp_all _ Hin_m). simpl in Hinp_all. congruence.
          -- (* Case B: lift Hf1 to s entirely *)
             assert (Hf1_s : has_derived_datalog_fact s (meta_fact R mf_args mf_set)).
             { simpl. rewrite HER. intros k Hk. specialize (Hf1 k Hk).
               destruct Hf1 as (num & Hk_s'). rewrite Hkd_iff in Hk_s'.
               destruct Hk_s' as [Heq | Hk_s]; [|exists num; exact Hk_s].
               exfalso. rewrite HFeq in Heq. injection Heq as -> -> _ _.
               apply HNeq. split; reflexivity. }
             apply Hsound. split; assumption.
  Admitted.


End __.
Arguments clause : clear implicits.
Arguments meta_clause : clear implicits.
Arguments fact : clear implicits.
Arguments fact_args : clear implicits.
Arguments rule : clear implicits.
Arguments expr : clear implicits.
Hint Constructors non_meta_rule_impl : core.
Hint Constructors rule_impl : core.
Hint Immediate extensionally_equal_refl : core.
Hint Unfold extensionally_equal : core.

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
  | _ => progress cbn [matches rel_of fact_of args_of clause_rel clause_args meta_clause_rel meta_clause_args fact_supported extensionally_equal] in *
  | H : one_step_derives _ _ _ _ |- _ => cbv [one_step_derives one_step_derives0] in H; fwd
  | H : fact_matches _ _ |- _ => cbv [fact_matches] in H; fwd
  | H : fact_supported _ _ |- _ => cbv [fact_supported] in H
  | H : rule_impl _ _ _ _ |- _ => invert1 H || invert0 H
  | H : non_meta_rule_impl _ _ _ _ |- _ => progress (invert1 H) || invert0 H
  | H : interp_clause _ _ _ |- _ => cbv [interp_clause] in H; fwd
  | H : interp_meta_clause _ _ _ |- _ => cbv [interp_meta_clause] in H; fwd
  | H : interp_expr _ _ _ |- _ => invert1 H
  | H1: ?x = Some ?y, H2: ?x = Some ?z |- _ => first [is_var y | is_var z]; assert (y = z) by congruence; clear H1; subst
  | _ => progress subst
  | _ => progress invert_list_stuff
  | _ => progress fwd
  | _ => congruence
  end.
