From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import Classical_Prop RelationClasses Morphisms.
From Datalog.Util Require Import Autodestr Autocbn Pftree.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List Datatypes.Option Eqb.

From Datalog Require Import Map Tactics Fp List Eqb.
From GraphSearch Require Import Dag.

Import ListNotations.

Definition relT := Type. Existing Class relT.
Definition rel `{relT} := (_ : relT).

Definition exprvarT := Type. Existing Class exprvarT.
Definition exprvar `{exprvarT} := (_ : exprvarT).

Definition fnT := Type. Existing Class fnT.
Definition fn `{fnT} := (_ : fnT).

Definition aggregatorT := Type. Existing Class aggregatorT.
Definition aggregator `{aggregatorT} := (_ : aggregatorT).

Definition valueT := Type. Existing Class valueT.
Definition value `{valueT} := (_ : valueT).

Class datalog_semantics {_fn : fnT} {_aggregator : aggregatorT} {_value : valueT} : Type :=
  {
    interp_fun : _fn -> list _value -> option _value;
    (* (*if x represents a finite set S then get_set x = Some S. *)
    (*   note: suffices to have this be T -> option nat, for cardinality... *)
    (*   should i do that? *) *)
    (* get_set : T -> option (T -> Prop); *)
    get_nat : _value -> nat;
    agg_bop : _aggregator -> _value -> _value -> _value;
    agg_id : _aggregator -> _value; }.
Arguments datalog_semantics : clear implicits.

Class datalog_params {_rel : relT} {_exprvar : exprvarT} `{semantics : datalog_semantics} {context : map.map _exprvar value} {context_ok : map.ok context} := {}.

Definition interp_agg `{datalog_semantics} agg (vals : list (value * value)) :=
  fold_right (agg_bop agg) (agg_id agg) (map snd vals).

Class query_signature {rel : Type} :=
  { outs : rel -> nat }.
Arguments query_signature : clear implicits.

Goal forall {exprvar : exprvarT} {var_eqb : Eqb exprvar} {var_eqb_ok : Eqb_ok var_eqb} (v v0 : exprvar),
    BoolSpec (v = v0) (v <> v0) (var_eqb v v0).
Proof. intros. Fail typeclasses eauto. Abort.

#[global] Typeclasses Transparent relT exprvarT fnT aggregatorT valueT.

Goal forall {exprvar : exprvarT} {var_eqb : Eqb exprvar} {var_eqb_ok : Eqb_ok var_eqb} (v v0 : exprvar),
    BoolSpec (v = v0) (v <> v0) (var_eqb v v0).
Proof. intros. typeclasses eauto. Abort.

Module expr.
  Section __.
    Context `{params: datalog_params}.

    Unset Elimination Schemes.
    Inductive expr :=
    | var (v : exprvar)
    | app (f : fn) (args : list expr).

    Inductive interp (ctx : context) : expr -> value -> Prop :=
    | interp_var_expr x v :
      map.get ctx x = Some v ->
      interp ctx (var x) v
    | interp_fun_expr f args args' x :
      Forall2 (interp ctx) args args' ->
      interp_fun f args' = Some x ->
      interp ctx (app f args) x.
    Set Elimination Schemes.

    Fixpoint size (e : expr) :=
      match e with
      | var _ => O
      | app _ args => S (fold_right Nat.max O (map size args))
      end.

    Lemma expr_ind P :
      (forall v, P (var v)) ->
      (forall f args,
          Forall P args ->
          P (app f args)) ->
      forall e, P e.
    Proof.
      intros. remember (size e) as sz eqn:E.
      assert (He: (size e < Datatypes.S sz)%nat) by lia.
      clear E. revert e He. induction (Datatypes.S sz); intros.
      - lia.
      - destruct e; simpl in He; auto.
        + apply H0. clear -IHn He. induction args; [constructor|].
          simpl in *. constructor; [|apply IHargs; lia]. apply IHn. lia.
    Qed.
    Register Scheme expr_ind as ind_nodep for expr.

    Lemma interp_subst_more s s' v e :
      map.extends s' s ->
      interp s e v ->
      interp s' e v.
    Proof.
      intros Hext H. revert s s' Hext v H. induction e; intros s s' Hext v0 Hv0.
      - invert Hv0. constructor. auto.
      - invert Hv0. econstructor; eauto.
        eapply Forall2_impl_strong; [eassumption|]. intros. rewrite Forall_forall in H.
        eauto.
    Qed.

    Fixpoint vars (e : expr) : list exprvar :=
      match e with
      | app _ args => flat_map vars args
      | var v => [v]
      end.

    Lemma interp_agree_on ctx1 ctx2 e v :
      interp ctx1 e v ->
      Forall (agree_on ctx1 ctx2) (vars e) ->
      interp ctx2 e v.
    Proof.
      revert v. induction e; intros v0 H0 H1; simpl in *.
      - invert H1. invert H4. invert H0. rewrite H3 in H1. constructor. assumption.
      - invert H0. econstructor; eauto. clear -H H1 H4. apply Forall_flat_map in H1.
        revert H H1. induction H4.
        + constructor.
        + intros H1 H2. invert H1. invert H2. auto.
    Qed.

    Lemma interp_det ctx e v1 v2 :
      interp ctx e v1 ->
      interp ctx e v2 ->
      v1 = v2.
    Proof.
      revert v1 v2. induction e; simpl; intros.
      - invert1_any. map_func. reflexivity.
      - invert1_any. enough (args' = args'0) by congruence.
        eapply Forall2_unique_r; try eassumption.
        rewrite Forall_forall in H. eauto.
    Qed.

    Lemma interp_det' e ctx1 ctx2 v1 v2 :
      interp ctx1 e v1 ->
      interp ctx2 e v2 ->
      Forall (agree_on ctx1 ctx2) (vars e) ->
      v1 = v2.
    Proof. eauto using interp_det, interp_agree_on. Qed.
  End __.
End expr. Export expr (expr).

Module normal_fact.
  Record normal_fact {relt : relT} {value : valueT} :=
    { rel : relt;
      args : list value }.
  (*i don't actually want this to be global; i'd prefer to instead export it along with normal_fact.  but the Import/Export commands aren't granular enough for me to do that.*)
  #[global] Ltac2 Set to_destruct as prev := fun _ => pattern_pred pat:(@normal_fact _ _) :: prev ().
  #[global] Ltac2 Set to_cbn as prev := fun _ => reference:(rel) :: reference:(args) :: prev ().
End normal_fact. Export normal_fact (normal_fact).
#[export] Hint Unfold normal_fact.rel normal_fact.args : core.

Module value_pattern.
  Section __.
    Context {value : valueT}.
    (*could consider extending this?*)
    Variant value_pattern {value : valueT} :=
      | exactly (v : value)
      | any.

    Definition matches (p : value_pattern) v :=
      match p with
      | exactly v0 => v0 = v
      | any => True
      end.

    Lemma matches_map_exactly vs :
      Forall2 matches (map exactly vs) vs.
    Proof.
      rewrite <- Forall2_map_l. apply Forall2_same. apply Forall_forall. simpl. auto.
    Qed.
End __.

End value_pattern. Export value_pattern (value_pattern).
#[export] Hint Unfold value_pattern.matches : core.
#[export] Hint Resolve value_pattern.matches_map_exactly : core.

Module fact_pattern.
  Record fact_pattern {relt : relT} {value : valueT} :=
    { rel : relt;
      args : list value_pattern }.
  #[global] Ltac2 Set to_destruct as prev := fun _ => pattern_pred pat:(@fact_pattern _ _) :: prev ().
  #[global] Ltac2 Set to_cbn as prev := fun _ => reference:(rel) :: reference:(args) :: prev ().

  Section __.
    Context {relt : relT} {value : valueT}.
    Definition matches (fp : fact_pattern) f :=
      fp.(rel) = f.(normal_fact.rel) /\
        Forall2 value_pattern.matches fp.(args) f.(normal_fact.args).
  End __.
End fact_pattern. Export fact_pattern (fact_pattern).

Module meta_fact.
  Record meta_fact {relt : relT} {value : valueT} :=
    { pattern : fact_pattern;
      set : list value -> Prop }.
  #[global] Ltac2 Set to_destruct as prev := fun _ => pattern_pred pat:(@meta_fact _ _) :: prev ().
  #[global] Ltac2 Set to_cbn as prev := fun _ => reference:(pattern) :: reference:(set) :: prev ().
  Section __.
    Context {relt : relT} {value : valueT}.

    Definition matches mf nf :=
      fact_pattern.matches mf.(pattern) nf /\ mf.(set) nf.(normal_fact.args).

    Definition equiv (mf1 mf2 : meta_fact) :=
      mf1.(pattern) = mf2.(pattern) /\
        forall args,
          Forall2 value_pattern.matches mf1.(pattern).(fact_pattern.args) args ->
          mf1.(set) args <-> mf2.(set) args.

    Lemma matches_ext mf nf mf' :
      matches mf nf ->
      equiv mf mf' ->
      matches mf' nf.
    Proof.
      cbv [matches equiv]. intros H1 H2. fwd. simp.
      cbv [fact_pattern.matches] in *. fwd. simp. edestruct H2p1; eauto.
    Qed.

    Lemma equiv_Equivalence : Equivalence equiv.
    Proof.
      cbv [equiv]. constructor.
      - intros. split; [reflexivity|]. intros. reflexivity.
      - intros mf1 mf2 H. fwd. split; [congruence|]. intros.
        symmetry. apply Hp1. congruence.
      - intros mf1 mf2 mf3 H1 H2. fwd. split; [congruence|]. intros.
        etransitivity; [now apply H1p1|]. apply H2p1. congruence.
    Qed.

    Definition rel mf := mf.(pattern).(fact_pattern.rel).
  End __.
End meta_fact. Export meta_fact (meta_fact).
#[export] Hint Resolve meta_fact.matches_ext : core.
#[export] Existing Instance meta_fact.equiv_Equivalence.

#[local] Hint Resolve Forall2_impl : core.
#[local] Hint Resolve Forall_impl : core.

Module clause.
  Record clause {relt : relT} {exprvar : exprvarT} {fn : fnT} :=
    { rel : relt;
      args : list expr }.
  #[global] Ltac2 Set to_destruct as prev := fun _ => pattern_pred pat:(@clause _ _ _) :: prev ().
  #[global] Ltac2 Set to_cbn as prev := fun _ => reference:(rel) :: reference:(args) :: prev ().

  Section __.
    Context `{params : datalog_params}.

    Definition interp (ctx: context) (c : clause) (f : normal_fact) :=
      c.(rel) = f.(normal_fact.rel) /\
        Forall2 (expr.interp ctx) c.(args) f.(normal_fact.args).

    Lemma interp_subst_more s s' f f' :
      map.extends s' s ->
      interp s f f' ->
      interp s' f f'.
    Proof.
      cbv [interp]. intros. fwd. eauto using expr.interp_subst_more.
    Qed.

    Definition vars (c : clause) : list exprvar :=
      flat_map expr.vars c.(args).

    Lemma interp_agree_on ctx1 ctx2 c f :
      interp ctx1 c f ->
      Forall (agree_on ctx1 ctx2) (vars c) ->
      interp ctx2 c f.
    Proof.
      cbv [interp]. intros Hinterp Hagree.
      fwd. split; auto.
      eapply Forall2_impl_strong; [eassumption|].
      intros. cbv [vars] in Hagree.
      rewrite Forall_flat_map, Forall_forall in Hagree.
      eauto using expr.interp_agree_on.
    Qed.

    Lemma interp_det ctx c f1 f2 :
      interp ctx c f1 ->
      interp ctx c f2 ->
      f1 = f2.
    Proof.
      intros. cbv [interp] in *. fwd. simp. f_equal.
      eapply Forall2_unique_r; eauto using expr.interp_det.
    Qed.

    Lemma interp_det' c ctx1 ctx2 f1 f2 :
      interp ctx1 c f1 ->
      interp ctx2 c f2 ->
      Forall (agree_on ctx1 ctx2) (vars c) ->
      f1 = f2.
    Proof. eauto using interp_det, interp_agree_on. Qed.

    Lemma interp_same_agree ctx1 ctx2 c f v :
      interp ctx1 c f ->
      interp ctx2 c f ->
      In (expr.var v) c.(args) ->
      agree_on ctx1 ctx2 v.
    Proof.
      cbv [interp]. intros H1 H2 Hv. fwd.
      eapply Forall2_and in H2p1; [|exact H1p1].
      apply Forall2_forget_r in H2p1.
      rewrite Forall_forall in H2p1. apply H2p1 in Hv.
      fwd. invert1_any. cbv [agree_on]. congruence.
    Qed.
End __.
End clause. Export clause (clause).
#[export] Hint Unfold clause.rel clause.args : core.

Module expr_pattern.
  Section __.
    Context `{params : datalog_params}.

    (*could reuse the value_pattern type idk*)
    Variant expr_pattern :=
      | exactly (e : expr)
      | any.

    Variant interp (ctx : context) : expr_pattern -> value_pattern -> Prop :=
      | interp_exactly p v :
        expr.interp ctx p v ->
        interp _ (exactly p) (value_pattern.exactly v)
      | interp_any :
        interp _ any value_pattern.any.

    Definition vars p :=
      match p with
      | exactly e => expr.vars e
      | any => []
      end.
  End __.
End expr_pattern. Export expr_pattern (expr_pattern).

Module clause_pattern.
  Record clause_pattern {relt : relT} {exprvar : exprvarT} {fn : fnT} :=
    { rel : relt;
      args : list expr_pattern }.
  #[global] Ltac2 Set to_destruct as prev := fun _ => pattern_pred pat:(@clause_pattern _ _ _) :: prev ().
  #[global] Ltac2 Set to_cbn as prev := fun _ => reference:(rel) :: reference:(args) :: prev ().

  Section __.
    Context `{params : datalog_params}.

    Definition interp (ctx: context) (cp : clause_pattern) (fp : fact_pattern) :=
      cp.(rel) = fp.(fact_pattern.rel) /\
        Forall2 (expr_pattern.interp ctx) cp.(args) fp.(fact_pattern.args).

    Definition vars (c : clause_pattern) : list exprvar :=
      flat_map expr_pattern.vars c.(args).
  End __.
End clause_pattern. Export clause_pattern (clause_pattern).

Module fact.
  Section __.
    Context `{params : datalog_params}.
    Variant fact :=
      | normal (_ : normal_fact)
      | meta (_ : meta_fact).

    Definition rel_of (f : fact) :=
      match f with
      | normal nf => nf.(normal_fact.rel)
      | meta mf => mf.(meta_fact.pattern).(fact_pattern.rel)
      end.

    Variant args :=
      | normal_args (nf_args : list value)
      | meta_args (mf_args : list value_pattern) (mf_set : list value -> Prop).

    Definition args_of f :=
      match f with
      | normal nf => normal_args nf.(normal_fact.args)
      | meta {| meta_fact.pattern := pat; meta_fact.set := st |} =>
          meta_args pat.(fact_pattern.args) st
      end.

    Definition of_args R args : fact :=
      match args with
      | normal_args nf_args =>
          normal {| normal_fact.rel := R;
                   normal_fact.args := nf_args |}
      | meta_args mf_args mf_set =>
          meta {| meta_fact.pattern :=
                   {| fact_pattern.rel := R;
                     fact_pattern.args := mf_args |};
                 meta_fact.set := mf_set |}
      end.

    Lemma of_args_args_of f :
      of_args (rel_of f) (args_of f) = f.
    Proof. destruct f; fwd; simp; reflexivity. Qed.

    Lemma rel_of_of_args R args :
      rel_of (of_args R args) = R.
    Proof. destruct args; reflexivity. Qed.

    Lemma args_of_of_args R args :
      args_of (of_args R args) = args.
    Proof. destruct args; reflexivity. Qed.

    Lemma fact_of_inj R args R' args' :
      of_args R args = of_args R' args' ->
      R = R' /\ args = args'.
    Proof.
      destruct args, args'; simpl; intros; congruence || fwd; auto.
    Qed.

    Definition equiv (f1 f2 : fact) :=
      match f1, f2 with
      | normal nf1, normal nf2 => nf1 = nf2
      | meta mf1, meta mf2 => meta_fact.equiv mf1 mf2
      | _, _ => False
      end.

    Lemma equiv_Equivalence : Equivalence equiv.
    Proof.
      constructor.
      - intros f. destruct f; simpl; reflexivity.
      - intros f1 f2. destruct f1, f2; simpl; intros; contradiction || now symmetry.
      - intros f1 f2 f3. destruct f1, f2, f3; simpl; intros;
          contradiction || (etransitivity; eassumption).
    Qed.

    Lemma equiv_map_meta mfs fs :
      Forall2 equiv (map meta mfs) fs ->
      exists mfs', fs = map meta mfs' /\ Forall2 meta_fact.equiv mfs mfs'.
    Proof.
      revert fs. induction mfs; simpl; intros fs H; invert H.
      - exists []. auto.
      - destruct y; simpl in *; [contradiction|]. apply IHmfs in H4. fwd.
        exists (m :: mfs'). auto.
    Qed.

    (*if we know only mfs and the normal_facts that mfs include, then do we know f?*)
    Definition implied_by_mfs (mfs : list meta_fact) (f : fact) :=
      match f with
      | normal nf => Exists (fun hyp => meta_fact.matches hyp nf) mfs
      | meta mf => Exists (meta_fact.equiv mf) mfs
      end.

    Lemma implied_by_mfs_ext hyps hyps' f :
      Forall2 meta_fact.equiv hyps hyps' ->
      implied_by_mfs hyps f ->
      implied_by_mfs hyps' f.
    Proof.
      intros H1 H2. apply Forall2_forget_r in H1. rewrite Forall_forall in H1.
      destruct f; simpl in *.
      - rewrite Exists_exists in *. fwd. especialize H1; eauto. fwd. eauto.
      - rewrite Exists_exists in *. fwd. especialize H1; eauto. fwd. eexists.
        split; [eassumption|]. etransitivity; eassumption.
    Qed.

    Definition is_meta f :=
      match f with
      | meta _ => True
      | normal _ => False
      end.

    Definition rel f :=
      match f with
      | meta mf => meta_fact.rel mf
      | normal nf => normal_fact.rel nf
      end.
  End __.
End fact. Export fact (fact).
#[export] Hint Resolve fact.implied_by_mfs_ext : core.
#[export] Existing Instance fact.equiv_Equivalence.

Module rule.
  Section __.
    Context `{params : datalog_params}.

    Variant rule :=
      | impl (concls : list clause) (hyps : list clause)
      | agg (concl : rel) (agg : aggregator) (hyp : rel).
        (*hmm maybe this shoudl actually be some construct for injection of normlal facts into fmeta facsts, then could just do agg_over_rel?*)
        (*| agg_over_set (concl_rel : rel) (agg : aggregator) (cardinality : expr) (hyp_rel : rel) (hyp_args : list var)*)

    Variant interp : rule -> normal_fact -> list fact -> Prop :=
      | interp_impl rule_concls rule_hyps ctx nf hyps :
        Exists (fun c => clause.interp ctx c nf) rule_concls ->
        Forall2 (clause.interp ctx) rule_hyps hyps ->
        interp (impl rule_concls rule_hyps) nf (map fact.normal hyps)
      | interp_agg S vals concl_rel a hyp_rel (args : list value) :
        is_list_set (fun '(i, x) => S (i :: x :: args)) vals ->
        interp
          (agg concl_rel a hyp_rel)
          {| normal_fact.rel := concl_rel;
            normal_fact.args := interp_agg a vals :: args |}
          (fact.meta {| meta_fact.pattern :=
                         {| fact_pattern.rel := hyp_rel;
                           fact_pattern.args := value_pattern.any :: value_pattern.any :: map value_pattern.exactly args |};
                       meta_fact.set := S |}
             ::
             map (fun '(i, x_i) => fact.normal {| normal_fact.rel := hyp_rel; normal_fact.args := (i :: x_i :: args) |}) vals).

    Lemma interp_ext r f hyps hyps' :
      interp r f hyps ->
      Forall2 fact.equiv hyps hyps' ->
      interp r f hyps'.
    Proof.
      intros H1 H2. invert H1.
      - apply Forall2_map_l in H2. eapply Forall2_impl in H2.
        1: apply Forall2_eq_map in H2.
        2: { simpl. intros. fwd. reflexivity. }
        subst. econstructor; eassumption.
      - invert H2. cbv [fact.equiv] in H3. fwd. cbv [meta_fact.equiv] in *. simp. fwd.
        invert H3p0. (*<- i thought fwd should have done this?*)
        apply Forall2_map_l in H5. eapply Forall2_impl in H5.
        1: apply Forall2_eq_map in H5.
        2: { cbv [fact.equiv]. intros. simp. fwd. instantiate (1 := fun '(_, _) => _). reflexivity. }
        subst. econstructor. eapply is_list_set_ext; [eassumption|].
        simpl. intros. simp. apply H3p1. auto.
    Qed.

    (*if we know only mfs and the normal facts that mfs include, then can we derive f with exactly one rule application?*)
    Definition one_step_derives (p : list rule) (mfs : list meta_fact) (nf : normal_fact) :=
      exists hyps,
        Exists (fun r => interp r nf hyps) p /\
          Forall (fact.implied_by_mfs mfs) hyps.

    Lemma one_step_derives_ext p hyps hyps' nf :
      Forall2 meta_fact.equiv hyps hyps' ->
      one_step_derives p hyps nf ->
      one_step_derives p hyps' nf.
    Proof.
      intros H1 H2. cbv [one_step_derives] in *. fwd. eauto 6.
    Qed.

    Definition concl_rels (r : rule) :=
      match r with
      | impl rule_concls _ => map clause.rel rule_concls
      | agg concl_rel _ _ => [concl_rel]
      end.

    Definition hyp_rels (r : rule) : list rel :=
      match r with
      | impl _ rule_hyps => map clause.rel rule_hyps
      | agg _ _ hyp_rel => [hyp_rel]
      end.

    Definition all_rels (r : rule) : list rel :=
      concl_rels r ++ hyp_rels r.

    Definition concl_vars r :=
      match r with
      | impl rule_concls _ => flat_map clause.vars rule_concls
      | agg _ _ _ => []
      end.

    Definition hyp_vars r :=
      match r with
      | impl _ rule_hyps => flat_map clause.vars rule_hyps
      | agg _ _ _ => []
      end.

    Definition all_vars r := concl_vars r ++ hyp_vars r.

    Definition hyp_args r :=
      match r with
      | impl _ rule_hyps => flat_map clause.args rule_hyps
      | agg _ _ _ => []
      end.

    (*is rule r conducive to bottom-up evaluation?*)
    Definition is_bottomup (r : rule) :=
      forall v, In v (all_vars r) -> In (expr.var v) (hyp_args r).

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

    Lemma interp_concl_relname_in r f hyps :
      interp r f hyps ->
      In f.(normal_fact.rel) (concl_rels r).
    Proof.
      invert 1.
      - fwd. simpl. apply in_map_iff. simp. invert H0p1. simp. eexists. split; eauto.
        reflexivity.
      - left. reflexivity.
    Qed.

    Lemma interp_hyp_relname_in r f hyps :
      interp r f hyps ->
      Forall (fun hyp => In (fact.rel hyp) (hyp_rels r)) hyps.
    Proof.
      invert 1.
      - simpl. apply Forall_forall. intros x Hx. apply in_map_iff in Hx. fwd.
        simpl. apply in_map_iff. simp. cbv [clause.interp] in *. simp. fwd.
        apply Forall2_forget_l in H1. rewrite Forall_forall in H1. especialize H1; eauto.
        fwd. simp. eexists. split; [|eassumption]. reflexivity.
      - simpl. constructor; [simpl; auto|]. apply List.Forall_map.
        apply Forall_forall. intros. simp. simpl. auto.
    Qed.

    Lemma one_step_derives_app p1 p2 mfs nf :
      ~ In nf.(normal_fact.rel) (flat_map concl_rels p2) ->
      one_step_derives (p1 ++ p2) mfs nf <-> one_step_derives p1 mfs nf.
    Proof.
      cbv [one_step_derives]. intros Hout. split; intros H; fwd; eauto 6.
      apply in_app_iff in Hp0p0. destruct Hp0p0; eauto.
      exfalso. apply Hout. apply in_flat_map. eauto using interp_concl_relname_in.
    Qed.

    Lemma one_step_derives_incl p1 p2 mfs nf :
      incl p1 p2 ->
      one_step_derives p1 mfs nf ->
      one_step_derives p2 mfs nf.
    Proof. cbv [one_step_derives]. intros Hincl H. fwd. eauto 6. Qed.

    Lemma one_step_derives_same_set p1 p2 mfs nf :
      same_set p1 p2 ->
      one_step_derives p1 mfs nf <-> one_step_derives p2 mfs nf.
    Proof.
      intros Hiff. split; apply one_step_derives_incl.
      - intros x Hx. apply Hiff. assumption.
      - intros x Hx. apply Hiff. assumption.
    Qed.
  End __.
End rule. Export rule (rule).
#[export] Hint Resolve rule.one_step_derives_ext : core.

Module meta_rule.
  Record meta_rule {relt : relT} {exprvar : exprvarT} {fn : fnT} :=
    { concls : list clause_pattern;
      hyps : list clause_pattern }.
  #[global] Ltac2 Set to_destruct as prev := fun _ => pattern_pred pat:(@meta_rule _ _ _) :: prev ().
  #[global] Ltac2 Set to_cbn as prev := fun _ => reference:(concls) :: reference:(hyps) :: prev ().

  Section __.
    Context `{params : datalog_params}.

    Definition pattern_interp r p ps :=
      exists ctx,
        Exists (fun c => clause_pattern.interp ctx c p) r.(concls) /\
          Forall2 (clause_pattern.interp ctx) r.(hyps) ps.

    Definition interp prog r mf hyps :=
      exists pat,
        pattern_interp r pat (map meta_fact.pattern hyps) /\
          meta_fact.equiv mf
            ({| meta_fact.pattern := pat;
               meta_fact.set :=
                 fun args =>
                   rule.one_step_derives prog hyps
                                         {| normal_fact.rel := pat.(fact_pattern.rel);
                                           normal_fact.args := args |} |}).

    Lemma interp_ext_hyps p r f hyps hyps' :
      interp p r f hyps ->
      Forall2 meta_fact.equiv hyps hyps' ->
      interp p r f hyps'.
    Proof.
      intros H1 H2. cbv [interp] in *. fwd.
      erewrite <- Forall2_map_eq.
      2: { eapply Forall2_impl; [eassumption|]. cbv [meta_fact.equiv]. intros. fwd. eassumption. }
      eexists. split; [eassumption|]. etransitivity; [eassumption|].
      cbv [meta_fact.equiv]. simpl. split; auto. intros.
      split; eauto. symmetry in H2. eauto.
    Qed.

    Lemma interp_ext_concl p r mf mf' hyps :
      interp p r mf hyps ->
      meta_fact.equiv mf mf' ->
      interp p r mf' hyps.
    Proof.
      cbv [interp]. intros. fwd. eexists. split; [eassumption|].
      etransitivity; eauto. symmetry. eassumption.
    Qed.

    Definition concl_rels (r : meta_rule) :=
      map clause_pattern.rel r.(concls).

    Definition hyp_rels (r : meta_rule) :=
      map clause_pattern.rel r.(hyps).

    Lemma pattern_interp_concl_relname_in r pat ps :
      pattern_interp r pat ps ->
      In pat.(fact_pattern.rel) (concl_rels r).
    Proof.
      cbv [pattern_interp concl_rels clause_pattern.interp]. intros. fwd.
      apply in_map_iff. eauto.
    Qed.

    Lemma interp_concl_relname_in p r f hyps :
      interp p r f hyps ->
      In (meta_fact.rel f) (concl_rels r).
    Proof.
      cbv [interp meta_fact.equiv meta_fact.rel]. intros H. fwd. simp.
      apply pattern_interp_concl_relname_in in Hp0. simp. assumption.
    Qed.

    Lemma interp_hyp_relname_in p r f hyps :
      interp p r f hyps ->
      Forall (fun hyp => In (meta_fact.rel hyp) (hyp_rels r)) hyps.
    Proof.
      cbv [interp]. intros H. fwd. simp.
      cbv [pattern_interp clause_pattern.interp] in *. fwd. simp.
      apply Forall2_map_r in Hp0p1.
      eapply Forall_impl; [eapply Forall2_forget_l; eassumption|].
      simpl. intros. fwd. simp. cbv [meta_fact.rel hyp_rels]. simpl.
      apply in_map_iff. eexists. split; [|eassumption]. reflexivity.
    Qed.

    Lemma interp_prog_ext p1 p2 r mf hyps :
      (forall mfs nf,
          In nf.(normal_fact.rel) (concl_rels r) ->
          rule.one_step_derives p1 mfs nf <-> rule.one_step_derives p2 mfs nf) ->
      interp p1 r mf hyps <-> interp p2 r mf hyps.
    Proof.
      cbv [interp]. intros H. split; intros H'; fwd.
      - eexists. split; [eassumption|]. etransitivity; [eassumption|].
        cbv [meta_fact.equiv]. simpl. split; [reflexivity|]. intros.
        apply H. simpl. eauto using pattern_interp_concl_relname_in.
      - eexists. split; [eassumption|]. etransitivity; [eassumption|].
        cbv [meta_fact.equiv]. simpl. split; [reflexivity|]. intros.
        symmetry. apply H. simpl. eauto using pattern_interp_concl_relname_in.
    Qed.

    Lemma interp_app p1 p2 r mf hyps :
      disjoint_lists (concl_rels r) (flat_map rule.concl_rels p2) ->
      interp (p1 ++ p2) r mf hyps <-> interp p1 r mf hyps.
    Proof.
      intros Hdisj. apply interp_prog_ext. intros.
      apply rule.one_step_derives_app. eauto.
    Qed.

    Lemma interp_same_set p1 p2 r mf hyps :
      same_set p1 p2 ->
      interp p1 r mf hyps <-> interp p2 r mf hyps.
    Proof.
      intros. apply interp_prog_ext. intros. apply rule.one_step_derives_same_set. assumption.
    Qed.
  End __.
End meta_rule. Export meta_rule (meta_rule).
#[export] Hint Resolve meta_rule.interp_ext_concl : core.

Module program.
  Record program {relt : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} :=
    { rules : list rule;
      meta_rules : list meta_rule }.
  #[global] Ltac2 Set to_destruct as prev := fun _ => pattern_pred pat:(@program _ _ _ _) :: prev ().
  #[global] Ltac2 Set to_cbn as prev := fun _ => reference:(rules) :: reference:(meta_rules) :: prev ().

  Section __.
    Context `{params : datalog_params}.

    Variant interp_step (p : program) : fact -> list fact -> Prop :=
      | rule_step f hyps :
        Exists (fun r => rule.interp r f hyps) p.(rules) ->
        interp_step _ (fact.normal f) hyps
      | meta_rule_step f hyps :
        Exists (fun mr => meta_rule.interp p.(rules) mr f hyps) p.(meta_rules) ->
        interp_step _ (fact.meta f) (map fact.meta hyps).

    (*making this an abbreviation allows directly using lemmas about pftree "without unfolding" interp *)
    Abbreviation interp p := (pftree (interp_step p)).

    Lemma interp_step_ext_hyps p f hyps hyps' :
      interp_step p f hyps ->
      Forall2 fact.equiv hyps hyps' ->
      interp_step p f hyps'.
    Proof.
      intros H1 H2. invert H1.
      - constructor. rewrite Exists_exists in *. fwd. eauto using rule.interp_ext.
      - apply fact.equiv_map_meta in H2. fwd. constructor.
        rewrite Exists_exists in *. fwd. eauto using meta_rule.interp_ext_hyps.
    Qed.

    Lemma interp_step_ext_concl p f f' hyps :
      interp_step p f hyps ->
      fact.equiv f f' ->
      interp_step p f' hyps.
    Proof.
      intros H1 H2. invert H1; destruct f'; simpl in H2; try contradiction; subst.
      - constructor. assumption.
      - constructor. rewrite Exists_exists in *. fwd. eauto.
    Qed.

    Lemma interp_step_strong p Q f hyps :
      interp_step p f hyps ->
      Forall (fun hyp => exists hyp', fact.equiv hyp hyp' /\ interp p Q hyp') hyps ->
      interp p Q f.
    Proof.
      intros H1 H2. apply Forall_exists_r_Forall2 in H2.
      fwd. eapply pftree.step.
      - eapply interp_step_ext_hyps; [eassumption|].
        eapply Forall2_impl; [eassumption|]. simpl. intros. fwd. assumption.
      - eapply Forall_impl. 1: eapply Forall2_forget_l; eassumption. simpl.
        intros. fwd. assumption.
    Qed.

    Lemma interp_ext p Q f f' :
      interp p Q f ->
      fact.equiv f f' ->
      Q f \/ interp p Q f'.
    Proof.
      intros H1 H2. invert H1; auto.
      right. eapply pftree.step; [|eassumption].
      eauto using interp_step_ext_concl.
    Qed.

    Lemma interp_ext' p Q :
      Proper (fact.equiv ==> iff) Q ->
      Proper (fact.equiv ==> iff) (interp p Q).
    Proof.
      intros H f1 f2 Hfs. split; intros H'.
      - eapply interp_ext in H'; eauto. destruct H'; eauto. apply pftree.leaf.
        eapply H; try eassumption. symmetry. assumption.
      - eapply interp_ext in H'. 2: symmetry; eassumption.
        destruct H'; eauto. apply pftree.leaf.
        eapply H; eassumption.
    Qed.

    Definition hyp_rels (p : program) :=
      flat_map rule.hyp_rels p.(rules) ++ flat_map meta_rule.hyp_rels p.(meta_rules).

    Lemma interp_step_hyp_relname_in p f hyps :
      interp_step p f hyps ->
      Forall (fun hyp => In (fact.rel hyp) (hyp_rels p)) hyps.
    Proof.
      cbv [hyp_rels]. invert 1.
      - fwd. eapply Forall_impl; [eapply rule.interp_hyp_relname_in; eassumption|].
        simpl. intros. apply in_or_app. left. apply in_flat_map. eauto.
      - fwd. apply List.Forall_map.
        eapply Forall_impl; [eapply meta_rule.interp_hyp_relname_in; eassumption|].
        simpl. intros. apply in_or_app. right. apply in_flat_map. eauto.
    Qed.
    #[local] Hint Resolve interp_step_hyp_relname_in.

    Lemma interp_invariant p Q f :
      interp p Q f <->
        interp p (fun f' => Q f' /\ (f' = f \/ In (fact.rel f') (hyp_rels p))) f.
    Proof.
      split; intros H.
      - apply pftree.invariant; eauto.
      - eapply pftree.weaken_hyp; [eassumption|]. simpl. intros. fwd. assumption.
    Qed.

    Lemma interp_hyp_ext_strong p Q1 Q2 f :
      (Q1 f <-> Q2 f) ->
      (forall f', In (fact.rel f') (hyp_rels p) -> Q1 f' <-> Q2 f') ->
      interp p Q1 f <-> interp p Q2 f.
    Proof.
      intros Hf Hhyps.
      assert (Hequiv: forall f', f' = f \/ In (fact.rel f') (hyp_rels p) -> Q1 f' <-> Q2 f').
      { intros f' [-> | Hin]; auto. }
      rewrite (interp_invariant p Q1 f), (interp_invariant p Q2 f).
      apply pftree.hyp_ext. intros f'. split.
      - intros. fwd. split; auto. apply Hequiv; auto.
      - intros. fwd. split; auto. apply Hequiv; auto.
    Qed.

    Definition union (p1 p2 : program) :=
      {| rules := p1.(rules) ++ p2.(rules);
        meta_rules := p1.(meta_rules) ++ p2.(meta_rules) |}.

    Lemma interp_step_union p1 p2 f hyps :
      disjoint_lists (flat_map meta_rule.concl_rels p1.(meta_rules))
        (flat_map rule.concl_rels p2.(rules)) ->
      interp_step p1 f hyps ->
      interp_step (union p1 p2) f hyps.
    Proof.
      intros Hdisj H. invert H; constructor; cbv [union]; simpl; apply Exists_app; left.
      - assumption.
      - rewrite Exists_exists in *. fwd. eexists. split; [eassumption|].
        apply meta_rule.interp_app; [|assumption].
        eapply disjoint_lists_incl_l; [eassumption|]. apply incl_flat_map_r. assumption.
    Qed.

    Lemma interp_union p1 p2 Q f :
      disjoint_lists (flat_map meta_rule.concl_rels p1.(meta_rules))
        (flat_map rule.concl_rels p2.(rules)) ->
      interp p1 Q f ->
      interp (union p1 p2) Q f.
    Proof. intros. eapply pftree.weaken; eauto using interp_step_union. Qed.

    Lemma interp_step_same_set p1 p2 f hyps :
      same_set p1.(rules) p2.(rules) ->
      same_set p1.(meta_rules) p2.(meta_rules) ->
      interp_step p1 f hyps ->
      interp_step p2 f hyps.
    Proof.
      intros Hr Hmr H. invert H; constructor; rewrite Exists_exists in *; fwd.
      - eexists. split; [|eassumption]. apply Hr. assumption.
      - eexists. split.
        + apply Hmr. eassumption.
        + apply meta_rule.interp_same_set with (p1 := rules p1); assumption.
    Qed.

    Lemma interp_same_set p1 p2 Q f :
      same_set p1.(rules) p2.(rules) ->
      same_set p1.(meta_rules) p2.(meta_rules) ->
      interp p1 Q f ->
      interp p2 Q f.
    Proof. intros. eapply pftree.weaken; eauto using interp_step_same_set. Qed.

  (* Ltac invert_stuff := *)
  (*   match goal with *)
  (*   | _ => progress cbn [matches rel_of fact_of args_of clause.rel clause.args meta_clause.rel meta_clause.args] in * *)
  (*   | H : rule_impl _ _ _ _ |- _ => invert1 H || invert0 H *)
  (*   | H : non_meta_rule_impl _ _ _ _ |- _ => progress (invert1 H) || invert0 H *)
  (*   | H : clause.interp _ _ _ |- _ => cbv [clause.interp] in H; fwd *)
  (*   | H : meta_clause.interp _ _ _ |- _ => cbv [meta_clause.interp] in H; fwd *)
  (*   | H : expr.interp _ _ _ |- _ => invert1 H *)
  (*   | H : In _ [_] |- _ => destruct H; [|contradiction] *)
  (*   | H : Exists _ _ |- _ => apply Exists_exists in H; fwd *)
  (*   | H1: ?x = Some ?y, H2: ?x = Some ?z |- _ => first [is_var y | is_var z]; assert (y = z) by congruence; clear H1; subst *)
  (*   | _ => progress subst *)
  (*   | _ => progress invert_list_stuff *)
  (*   | _ => progress fwd *)
  (*   | _ => congruence *)
  (*   end. *)

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

  Lemma staged_program p1 p2 Q f :
    disjoint_lists (flat_map concl_rels p1) (flat_map hyp_rels p2) ->
    disjoint_lists (flat_map meta_concl_rels p1) (flat_map concl_rels p2) ->
    disjoint_lists (flat_map meta_concl_rels p2) (flat_map concl_rels p1) ->
    prog_impl (p1 ++ p2) Q f ->
    prog_impl p1 (prog_impl p2 Q) f.
  Proof.
    intros Hdisj Hmr1 Hmr2. induction 1 using prog_impl_ind.
    - apply pftree.leaf. apply pftree.leaf. assumption.
    - apply Exists_app in H. destruct H as [H|H].
      + eapply prog_impl_step. 2: eassumption.
        rewrite Exists_exists in *. fwd.
        eexists. split; [eassumption|].
        eapply staged_program_rule_impl; [|eassumption].
        eapply disjoint_lists_incl_l; [eassumption|].
        apply incl_flat_map_r. assumption.
      + apply pftree.leaf. eapply prog_impl_step.
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
  Definition fact_potentially_supported (mhyps : list fact) (f : fact) :=
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

  Definition consistent (mf_rel : rel) mf_args mf_set S :=
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
    eapply pftree.step; [eassumption|].
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
    simpl. intros. fwd. cbv [meta_clause.interp] in *. fwd.
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

End __.

Fixpoint expr_varmap {var1 var2 : exprvarT} {fn : fnT}
  (f : var1 -> var2) (e : @expr var1 fn) : @expr var2 fn :=
  match e with
  | expr.var v => expr.var (f v)
  | expr.app fu args => expr.app fu (map (expr_varmap f) args)
  end.

Definition clause_varmap {rel : relT} {var1 var2 : exprvarT} {fn : fnT}
  (f : var1 -> var2) (c : @clause rel var1 fn) : @clause rel var2 fn :=
  {| clause.rel := c.(clause.rel);
     clause.args := map (expr_varmap f) c.(clause.args) |}.

Definition meta_clause_varmap {rel : relT} {var1 var2 : exprvarT} {fn : fnT}
  (f : var1 -> var2) (c : @meta_clause rel var1 fn) : @meta_clause rel var2 fn :=
  {| meta_clause.rel := c.(meta_clause.rel);
     meta_clause.args := map (option_map (expr_varmap f)) c.(meta_clause.args) |}.

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
        (eapply Forall2_impl; [eassumption|]; simpl; intros) ||
          idtac

    | |- Forall _ (_ :: _) => constructor; [interp_exprs|]
    | |- Forall _ [] => constructor

    | |- expr.interp _ _ _ => econstructor
    (* | |- interp_expr _ _ _ => *)
    (*     eapply interp_expr_subst_more; [|eassumption] *)
    (* | |- interp_clause _ _ _ => *)
    (*     eapply interp_clause_subst_more; [|eassumption] *)
    | |- clause.interp _ _ _ =>
        cbv [clause.interp]; eexists; split; [|reflexivity]; simpl
    | |- meta_clause.interp _ _ _ =>
        cbv [meta_clause.interp]; do 2 eexists; split; [|reflexivity]; simpl
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
  | _ => progress cbn [matches rel_of fact_of args_of clause.rel clause.args meta_clause.rel meta_clause.args fact_supported extensionally_equal] in *
  | H : one_step_derives _ _ _ _ |- _ => cbv [one_step_derives one_step_derives0] in H; fwd
  | H : fact_matches _ _ |- _ => cbv [fact_matches] in H; fwd
  | H : fact_supported _ _ |- _ => cbv [fact_supported] in H
  | H : rule_impl _ _ _ _ |- _ => invert1 H || invert0 H
  | H : non_meta_rule_impl _ _ _ _ |- _ => progress (invert1 H) || invert0 H
  | H : clause.interp _ _ _ |- _ => cbv [clause.interp] in H; fwd
  | H : meta_clause.interp _ _ _ |- _ => cbv [meta_clause.interp] in H; fwd
  | H : expr.interp _ _ _ |- _ => invert1 H
  | H1: ?x = Some ?y, H2: ?x = Some ?z |- _ => first [is_var y | is_var z]; assert (y = z) by congruence; clear H1; subst
  | _ => progress subst
  | _ => progress invert_list_stuff
  | _ => progress fwd
  | _ => congruence
  end.
