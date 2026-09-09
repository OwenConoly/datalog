From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import RelationClasses Morphisms.
From Datalog.Util Require Import Autodestr Autocbn Pftree.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List Datatypes.Option Eqb.

From Datalog Require Import Map Tactics Fp List Eqb.
From GraphSearch Require Import Dag.

Import ListNotations.

Definition relT := Type. Existing Class relT.
Abbreviation rel := (_ : relT).

Definition exprvarT := Type. Existing Class exprvarT.
Abbreviation exprvar := (_ : exprvarT).

Definition fnT := Type. Existing Class fnT.
Abbreviation fn := (_ : fnT).

Definition aggregatorT := Type. Existing Class aggregatorT.
Abbreviation aggregator := (_ : aggregatorT).

Definition valueT := Type. Existing Class valueT.
Abbreviation value := (_ : valueT).

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

    Definition agree (mf1 mf2 : meta_fact) :=
      forall nf,
        fact_pattern.matches mf1.(pattern) nf ->
        fact_pattern.matches mf2.(pattern) nf ->
        mf1.(set) nf.(normal_fact.args) <-> mf2.(set) nf.(normal_fact.args).

    Lemma agree_sym mf1 mf2 :
      agree mf1 mf2 ->
      agree mf2 mf1.
    Proof. cbv [agree]. intros H nf H1 H2. symmetry. auto. Qed.

    Lemma equiv_of_agree mf1 mf2 :
      mf1.(pattern) = mf2.(pattern) ->
      agree mf1 mf2 ->
      equiv mf1 mf2.
    Proof.
      cbv [equiv agree]. intros Hpat Hagree. split; [assumption|]. intros args Hargs.
      rewrite <- Hpat in *.
      eapply (Hagree (normal_fact.Build_normal_fact _ _ _ _));
      cbv [fact_pattern.matches]; simpl; auto.
    Qed.
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

    (*if we know hyp and the normal_facts that hyp includes, then do we know f?*)
    Definition implied_by_mf (f : fact) (hyp : meta_fact) :=
      match f with
      | normal nf => meta_fact.matches hyp nf
      | meta mf => meta_fact.equiv mf hyp
      end.

    Definition implied_by_mfs (mfs : list meta_fact) (f : fact) :=
      Exists (implied_by_mf f) mfs.

    (*the pattern half of implied_by_mf: does fp cover f, ignoring sets?*)
    Definition covered_by (f : fact) (fp : fact_pattern) :=
      match f with
      | normal nf => fact_pattern.matches fp nf
      | meta mf => fp = mf.(meta_fact.pattern)
      end.

    Definition covered_by_pats (pats : list fact_pattern) (f : fact) :=
      Exists (covered_by f) pats.

    Lemma implied_by_mfs_ext hyps hyps' f :
      Forall2 meta_fact.equiv hyps hyps' ->
      implied_by_mfs hyps f ->
      implied_by_mfs hyps' f.
    Proof.
      cbv [implied_by_mfs implied_by_mf]. intros H1 H2.
      apply Forall2_forget_r in H1. rewrite Forall_forall in H1.
      destruct f; simpl in *.
      - rewrite Exists_exists in *. fwd. especialize H1; eauto. fwd. eauto.
      - rewrite Exists_exists in *. fwd. especialize H1; eauto. fwd. eexists.
        split; [eassumption|]. etransitivity; eassumption.
    Qed.

    Lemma implied_by_mfs_pats mfs f :
      implied_by_mfs mfs f ->
      covered_by_pats (map meta_fact.pattern mfs) f.
    Proof.
      cbv [implied_by_mfs covered_by_pats implied_by_mf covered_by]. destruct f; intros H.
      - rewrite Exists_map. eapply Exists_impl; [|eassumption].
        cbv [meta_fact.matches]. simpl. intros. fwd. assumption.
      - rewrite Exists_map. eapply Exists_impl; [|eassumption].
        cbv [meta_fact.equiv]. simpl. intros. fwd. symmetry. assumption.
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

    Definition set_consistent_with (mf : meta_fact) (S : fact -> Prop) :=
      forall nf,
        fact_pattern.matches mf.(meta_fact.pattern) nf ->
        mf.(meta_fact.set) nf.(normal_fact.args) <-> S (normal nf).

    Definition set_doesnt_lie (S : fact -> Prop) :=
      forall mf, S (meta mf) -> set_consistent_with mf S.

    Lemma set_doesnt_lie_agree (S : fact -> Prop) mf1 mf2 :
      set_doesnt_lie S ->
      S (meta mf1) ->
      S (meta mf2) ->
      meta_fact.agree mf1 mf2.
    Proof.
      cbv [set_doesnt_lie set_consistent_with meta_fact.agree].
      intros H H1 H2 nf Hm1 Hm2.
      rewrite (H _ H1) by assumption. rewrite (H _ H2) by assumption. reflexivity.
    Qed.

    Definition args_consistent mf_args mf_set (S_args : args -> Prop) :=
      forall nf_args,
        Forall2 value_pattern.matches mf_args nf_args ->
        mf_set nf_args <-> S_args (normal_args nf_args).

    Definition honest_args (S_args : args -> Prop) :=
      forall mf_args mf_set,
        S_args (meta_args mf_args mf_set) ->
        args_consistent mf_args mf_set S_args.

    Lemma set_doesnt_lie_honest_args (S : fact -> Prop) R :
      set_doesnt_lie S ->
      honest_args (fun a => S (of_args R a)).
    Proof.
      cbv [set_doesnt_lie honest_args args_consistent].
      intros H mf_args mf_set Hmeta nf_args Hargs. apply H in Hmeta.
      cbv [set_consistent_with] in Hmeta. simpl in Hmeta.
      apply (Hmeta {| normal_fact.rel := R; normal_fact.args := nf_args |}).
      cbv [fact_pattern.matches]. simpl. auto.
    Qed.
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

    Lemma pattern_interp_hyp_relname_in r pat ps :
      pattern_interp r pat ps ->
      Forall (fun fp => In fp.(fact_pattern.rel) (hyp_rels r)) ps.
    Proof.
      cbv [pattern_interp clause_pattern.interp]. intros H. fwd.
      eapply Forall_impl; [eapply Forall2_forget_l; eassumption|].
      simpl. intros. fwd. cbv [hyp_rels]. apply in_map_iff. eauto.
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

    (*whenever r's conclusion pattern covers a conclusion of nr,
      r's hypothesis patterns cover nr's hypotheses*)
    Definition valid_for (r : meta_rule) (nr : rule) :=
      forall pat pats nf hyps,
        pattern_interp r pat pats ->
        rule.interp nr nf hyps ->
        fact_pattern.matches pat nf ->
        Forall (fact.covered_by_pats pats) hyps.
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

    Definition concl_rels (p : program) :=
      flat_map rule.concl_rels p.(rules) ++ flat_map meta_rule.concl_rels p.(meta_rules).

    Lemma interp_step_concl_relname_in p f hyps :
      interp_step p f hyps ->
      In (fact.rel f) (concl_rels p).
    Proof.
      cbv [concl_rels]. invert 1; fwd; simpl; apply in_or_app.
      - left. apply in_flat_map. eauto using rule.interp_concl_relname_in.
      - right. apply in_flat_map. eauto using meta_rule.interp_concl_relname_in.
    Qed.
    #[local] Hint Resolve interp_step_concl_relname_in.

    Definition all_rels (p : program) := concl_rels p ++ hyp_rels p.

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

    (*p2's rules conclude nothing p1's meta-rules aggregate over*)
    Definition meta_indep (p1 p2 : program) :=
      disjoint_lists (flat_map meta_rule.concl_rels p1.(meta_rules))
        (flat_map rule.concl_rels p2.(rules)).

    (*p2 reads nothing p1 concludes, and neither one's rules disturb the other's meta-rules*)
    Definition stratified (p1 p2 : program) :=
      disjoint_lists (concl_rels p1) (hyp_rels p2) /\ meta_indep p1 p2 /\ meta_indep p2 p1.
    #[local] Hint Unfold stratified : core.

    Lemma interp_step_union p1 p2 f hyps :
      meta_indep p1 p2 ->
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
      meta_indep p1 p2 ->
      interp p1 Q f ->
      interp (union p1 p2) Q f.
    Proof. intros. eapply pftree.weaken; eauto using interp_step_union. Qed.

    Lemma interp_step_union_inv p1 p2 f hyps :
      meta_indep p1 p2 ->
      meta_indep p2 p1 ->
      interp_step (union p1 p2) f hyps ->
      interp_step p1 f hyps \/ interp_step p2 f hyps.
    Proof.
      intros H12 H21 H. invert H; cbv [union] in *; simpl in *;
        apply Exists_app in H0; destruct H0; rewrite Exists_exists in *; fwd.
      - left. constructor. apply Exists_exists. eauto.
      - right. constructor. apply Exists_exists. eauto.
      - left. constructor. apply Exists_exists. eexists. split; [eassumption|].
        apply meta_rule.interp_app with (p2 := rules p2); [|assumption].
        eapply disjoint_lists_incl_l; [eassumption|]. apply incl_flat_map_r. assumption.
      - right. constructor. apply Exists_exists. eexists. split; [eassumption|].
        apply meta_rule.interp_app with (p2 := rules p1).
        + eapply disjoint_lists_incl_l; [eassumption|]. apply incl_flat_map_r. assumption.
        + apply meta_rule.interp_same_set with (p1 := rules p1 ++ rules p2);
            auto using same_set_app_comm.
    Qed.

    Lemma stratify p1 p2 Q f :
      stratified p1 p2 ->
      interp (union p1 p2) Q f ->
      interp p1 (interp p2 Q) f.
    Proof.
      intros (H1 & H12 & H21) H. apply pftree.stratify.
      - intros y l z l' Hy Hz Hz'. eapply H1.
        + eapply interp_step_concl_relname_in. eassumption.
        + apply interp_step_hyp_relname_in in Hy. rewrite Forall_forall in Hy. auto.
      - eapply pftree.weaken; [eassumption|]. simpl. intros.
        eauto using interp_step_union_inv.
    Qed.

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

    Lemma unstratify p1 p2 Q f :
      meta_indep p1 p2 ->
      meta_indep p2 p1 ->
      interp p1 (interp p2 Q) f ->
      interp (union p1 p2) Q f.
    Proof.
      intros H12 H21 H. apply pftree.trans.
      apply interp_union with (p2 := p2) in H; [|assumption].
      eapply pftree.weaken_hyp; [eassumption|]. simpl. intros y Hy.
      apply interp_union with (p2 := p1) in Hy; [|assumption].
      eapply interp_same_set; [| |eassumption]; cbv [union]; simpl;
        apply same_set_app_comm.
    Qed.

    Lemma stratified_of_disjoint p1 p2 :
      disjoint_lists (concl_rels p1) (all_rels p2) ->
      stratified p1 p2.
    Proof.
      intros H. cbv [stratified meta_indep]. ssplit.
      - eapply disjoint_lists_incl; [eassumption| |]; cbv [all_rels]; auto with incl.
      - eapply disjoint_lists_incl; [eassumption| |]; cbv [all_rels concl_rels];
          auto with incl.
      - apply disjoint_lists_comm in H.
        eapply disjoint_lists_incl; [eassumption| |]; cbv [all_rels concl_rels];
          auto with incl.
    Qed.

    Lemma stratify_iff p1 p2 Q f :
      stratified p1 p2 ->
      interp (union p1 p2) Q f <-> interp p1 (interp p2 Q) f.
    Proof.
      cbv [stratified]. intros. fwd. auto 6 using stratify, unstratify.
    Qed.

    Lemma interp_rel_of p Q f :
      interp p Q f ->
      Q f \/ In (fact.rel f) (concl_rels p).
    Proof. invert 1; eauto. Qed.

    Definition meta_rules_valid (p : program) :=
      forall mr nr,
        In mr p.(meta_rules) ->
        In nr p.(rules) ->
        meta_rule.valid_for mr nr.

    Definition good_input_set (p : program) (Q : fact -> Prop) :=
      (forall f, Q f -> ~ In (fact.rel f) (concl_rels p)) /\ fact.set_doesnt_lie Q.

    Definition honest (p : program) :=
      forall Q, good_input_set p Q -> fact.set_doesnt_lie (interp p Q).

    Lemma meta_rules_valid_step p Q mf mhyps :
      (forall f, Q f -> ~ In (fact.rel f) (concl_rels p)) ->
      meta_rules_valid p ->
      Exists (fun mr => meta_rule.interp p.(rules) mr mf mhyps) p.(meta_rules) ->
      Forall (fun mhyp => fact.set_consistent_with mhyp (interp p Q)) mhyps ->
      (forall mhyp mf',
          In mhyp mhyps ->
          interp p Q (fact.meta mf') ->
          mhyp.(meta_fact.pattern) = mf'.(meta_fact.pattern) ->
          meta_fact.equiv mhyp mf') ->
      Forall (fun mhyp => interp p Q (fact.meta mhyp)) mhyps ->
      fact.set_consistent_with mf (interp p Q).
    Proof.
      intros Hinp Hvalid Hex Hcons Hagree Hderiv.
      rewrite Exists_exists in Hex. destruct Hex as [mr [Hmr Hinterp]].
      rewrite Forall_forall in Hcons, Hderiv. cbv [fact.set_consistent_with] in Hcons.
      pose proof Hinterp as Hpat. cbv [meta_rule.interp meta_fact.equiv] in Hpat. fwd. simp.
      cbv [fact.set_consistent_with]. intros nf Hmatch.
      pose proof Hmatch as Hm. cbv [fact_pattern.matches] in Hm. fwd. simp.
      rewrite Hpatp2 by assumption. split; intros H.
      - cbv [rule.one_step_derives] in H. fwd.
        eapply interp_step_strong.
        + constructor. apply Exists_exists. eauto.
        + eapply Forall_impl; [eassumption|]. simpl. intros f Hf.
          cbv [fact.implied_by_mfs] in Hf. rewrite Exists_exists in Hf. fwd.
          destruct f.
          * eexists. split; [reflexivity|].
            cbv [fact.implied_by_mf meta_fact.matches] in Hfp1. fwd.
            rewrite <- Hcons by eassumption. assumption.
          * eexists (fact.meta _). split; [eassumption|]. auto.
      - invert H.
        + exfalso. apply meta_rule.pattern_interp_concl_relname_in in Hpatp0. simp.
          eapply Hinp; [eassumption|]. simpl.
          cbv [concl_rels]. apply in_or_app. right. apply in_flat_map. eauto.
        + invert H0. rewrite Exists_exists in H2. fwd.
          specialize (Hvalid _ _ Hmr H2p0 _ _ _ _ Hpatp0 H2p1 Hmatch).
          cbv [rule.one_step_derives]. eexists.
          split; [apply Exists_exists; eauto|].
          eapply Forall_impl; [eapply Forall_and; [exact Hvalid | exact H1]|].
          simpl. intros f Hf. fwd. apply in_map_iff in Hfp0p0. fwd.
          cbv [fact.implied_by_mfs]. apply Exists_exists. eexists.
          split; [eassumption|].
          cbv [fact.covered_by] in Hfp0p1. destruct f.
          * cbv [fact.implied_by_mf meta_fact.matches].
            split; [assumption|]. rewrite Hcons by eassumption. assumption.
          * cbv [fact.implied_by_mf]. symmetry. apply Hagree; auto.
    Qed.

    Lemma one_step_derives_mhyps p mh1 mh2 mr2 pat2 nf :
      meta_rules_valid p ->
      In mr2 p.(meta_rules) ->
      meta_rule.pattern_interp mr2 pat2 (map meta_fact.pattern mh2) ->
      fact_pattern.matches pat2 nf ->
      (forall mhyp1 mhyp2, In mhyp1 mh1 -> In mhyp2 mh2 -> meta_fact.agree mhyp1 mhyp2) ->
      rule.one_step_derives p.(rules) mh1 nf ->
      rule.one_step_derives p.(rules) mh2 nf.
    Proof.
      intros Hvalid Hmr2 Hpat2 Hmatch Hagree Hderiv.
      cbv [rule.one_step_derives] in *. fwd.
      specialize (Hvalid _ _ Hmr2 Hderivp0p0 _ _ _ _ Hpat2 Hderivp0p1 Hmatch).
      eexists. split; [apply Exists_exists; eauto|].
      eapply Forall_impl; [eapply Forall_and; [exact Hvalid|exact Hderivp1]|].
      simpl. intros f [Hcov Himp].
      cbv [fact.covered_by_pats] in Hcov. cbv [fact.implied_by_mfs] in Himp |- *.
      rewrite Exists_exists in Hcov, Himp |- *. fwd.
      apply in_map_iff in Hcovp0. fwd.
      eexists. split; [eassumption|].
      cbv [fact.covered_by] in Hcovp1. destruct f.
      - cbv [fact.implied_by_mf meta_fact.matches] in *. fwd.
        split; [assumption|]. eapply Hagree with (mhyp1 := x0); eauto.
      - cbv [fact.implied_by_mf] in *.
        etransitivity; [eassumption|].
        apply meta_fact.equiv_of_agree.
        + cbv [meta_fact.equiv] in Himpp1. fwd. congruence.
        + eapply Hagree; eassumption.
    Qed.

  Lemma meta_facts_consistent' p Q f1 f2 :
      (forall f, Q f -> ~ In (fact.rel f) (concl_rels p)) ->
      (forall mf1 mf2, Q (fact.meta mf1) -> Q (fact.meta mf2) -> meta_fact.agree mf1 mf2) ->
      meta_rules_valid p ->
      interp p Q f1 ->
      interp p Q f2 ->
      match f1, f2 with
      | fact.meta mf1, fact.meta mf2 => meta_fact.agree mf1 mf2
      | _, _ => True
      end.
    Proof.
      intros Hinp Hinp2 Hvalid Hf1 Hf2.
      eapply pftree.pairwise_ind with (x1 := f1) (x2 := f2).
      3,4: eassumption.
      - intros x1 x2. destruct x1, x2; simpl; try tauto.
        split; apply meta_fact.agree_sym.
      - intros x xs IH Hderiv Hstep.
        rewrite Forall_forall in Hderiv, Hstep.
        apply Forall_forall. intros y Hy.
        destruct x as [nf1|mf1]; [exact I|].
        destruct y as [nf2|mf2]; [exact I|].
        destruct Hy as [Hy|Hy].
        { invert Hy. cbv [meta_fact.agree]. intros. reflexivity. }
        intros nf Hm1 Hm2.
        pose proof (Hstep (fact.meta mf1) ltac:(simpl; auto)) as Hx.
        pose proof (Hstep (fact.meta mf2) ltac:(simpl; auto)) as Hz.
        pose proof Hm1 as Hr1. pose proof Hm2 as Hr2.
        cbv [fact_pattern.matches] in Hr1, Hr2. fwd.
        destruct Hx as [Hx|Hx]; destruct Hz as [Hz|Hz].
        + exact (Hinp2 _ _ Hx Hz nf Hm1 Hm2).
        + exfalso. fwd. apply interp_step_concl_relname_in in Hzp0.
          eapply Hinp; [eassumption|]. cbv [fact.rel meta_fact.rel] in *. congruence.
        + exfalso. fwd. apply interp_step_concl_relname_in in Hxp0.
          eapply Hinp; [eassumption|]. cbv [fact.rel meta_fact.rel] in *. congruence.
        + fwd. invert Hxp0. invert Hzp0.
          rewrite Exists_exists in H0, H1. fwd.
          assert (Hagree: forall mhyp1 mhyp2, In mhyp1 hyps -> In mhyp2 hyps0 ->
                     meta_fact.agree mhyp1 mhyp2).
          { intros mhyp1 mhyp2 Ha Hb.
            apply (IH (fact.meta mhyp1) (fact.meta mhyp2));
              [apply Hxp1 | apply Hzp1]; apply in_map; assumption. }
          pose proof H0p1 as E1. pose proof H1p1 as E2.
          cbv [meta_rule.interp meta_fact.equiv] in E1, E2. fwd.
          rewrite E1p2 by assumption. rewrite E2p2 by assumption. simp.
          split; intros Hd.
          * eapply one_step_derives_mhyps in Hvalid.
            3: exact E2p0. all: eassumption.
          * eapply one_step_derives_mhyps in Hvalid.
            3: exact E1p0. all: try eassumption.
            intros. apply meta_fact.agree_sym. auto.
    Qed.

    Lemma meta_facts_consistent p Q mf1 mf2 :
      (forall f, Q f -> ~ In (fact.rel f) (concl_rels p)) ->
      (forall mf1 mf2, Q (fact.meta mf1) -> Q (fact.meta mf2) -> meta_fact.agree mf1 mf2) ->
      meta_rules_valid p ->
      interp p Q (fact.meta mf1) ->
      interp p Q (fact.meta mf2) ->
      meta_fact.agree mf1 mf2.
    Proof.
      intros. eapply (meta_facts_consistent' p Q (fact.meta mf1) (fact.meta mf2)); eassumption.
    Qed.

    Lemma valid_impl_honest p :
      meta_rules_valid p ->
      honest p.
    Proof.
      intros Hvalid Q [Hdisj Q_honest] mf Hderiv.
      assert (HQagree: forall mf1 mf2,
                 Q (fact.meta mf1) -> Q (fact.meta mf2) -> meta_fact.agree mf1 mf2).
      { eauto using fact.set_doesnt_lie_agree. }
      remember (fact.meta mf) as f eqn:Ef. revert mf Ef.
      induction Hderiv; intros mf Ef; subst.
      - pose proof H as HQ. apply Q_honest in H.
        cbv [fact.set_consistent_with] in H |- *. intros nf Hmatch.
        rewrite H by assumption. split; intros H'.
        + apply pftree.leaf. assumption.
        + invert H'; [assumption|].
          exfalso. apply interp_step_concl_relname_in in H0.
          eapply Hdisj; [exact HQ|].
          cbv [fact.rel meta_fact.rel] in *. cbv [fact_pattern.matches] in Hmatch. fwd.
          congruence.
      - invert H. rewrite Forall_forall in H0, H1.
        eapply meta_rules_valid_step; try eassumption.
        + rewrite Forall_forall. intros mhyp Hin.
          apply (H1 (fact.meta mhyp)); auto using in_map.
        + intros mhyp mf' Hin Hd Hpat.
          apply meta_fact.equiv_of_agree; [assumption|].
          eapply meta_facts_consistent; try eassumption.
          apply H0. apply in_map. assumption.
        + rewrite Forall_forall. intros mhyp Hin.
          apply H0. apply in_map. assumption.
    Qed.

    Lemma use_honest p Q mf :
      honest p ->
      good_input_set p Q ->
      interp p Q (fact.meta mf) ->
      Q (fact.meta mf) \/
        interp p Q (fact.meta {| meta_fact.pattern := mf.(meta_fact.pattern);
                                meta_fact.set :=
                                  fun args =>
                                    interp p Q
                                      (fact.normal {| normal_fact.rel := meta_fact.rel mf;
                                                     normal_fact.args := args |}) |}).
    Proof.
      intros Hhonest Hgood H. eapply interp_ext; [eassumption|].
      cbv [fact.equiv]. apply meta_fact.equiv_of_agree; [reflexivity|].
      pose proof (Hhonest Q Hgood mf H) as Hc. cbv [fact.set_consistent_with] in Hc.
      cbv [meta_fact.agree]. simpl. intros nf Hm1 Hm2.
      rewrite Hc by assumption. cbv [meta_fact.rel].
      cbv [fact_pattern.matches] in Hm1. fwd. simp. reflexivity.
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
  Abbreviation interp p := (pftree (interp_step p)).
End program. Export program (program).
Fixpoint expr_varmap {var1 var2 : exprvarT} {fn : fnT}
  (f : var1 -> var2) (e : @expr var1 fn) : @expr var2 fn :=
  match e with
  | expr.var v => expr.var (f v)
  | expr.app fu args => expr.app fu (map (expr_varmap f) args)
  end.

Definition expr_pattern_varmap {var1 var2 : exprvarT} {fn : fnT}
  (f : var1 -> var2) (e : @expr_pattern var1 fn) : @expr_pattern var2 fn :=
  match e with
  | expr_pattern.exactly e => expr_pattern.exactly (expr_varmap f e)
  | expr_pattern.any => expr_pattern.any
  end.

Definition clause_varmap {rel : relT} {var1 var2 : exprvarT} {fn : fnT}
  (f : var1 -> var2) (c : @clause rel var1 fn) : @clause rel var2 fn :=
  {| clause.rel := c.(clause.rel);
     clause.args := map (expr_varmap f) c.(clause.args) |}.

Definition clause_pattern_varmap {rel : relT} {var1 var2 : exprvarT} {fn : fnT}
  (f : var1 -> var2) (c : @clause_pattern rel var1 fn) : @clause_pattern rel var2 fn :=
  {| clause_pattern.rel := c.(clause_pattern.rel);
     clause_pattern.args := map (expr_pattern_varmap f) c.(clause_pattern.args) |}.

#[export] Hint Constructors rule.interp : core.
#[export] Hint Unfold fact.equiv : core.

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
    | |- expr_pattern.interp _ _ _ => econstructor
    | |- clause.interp _ _ _ => cbv [clause.interp]; simpl
    | |- clause_pattern.interp _ _ _ => cbv [clause_pattern.interp]; simpl
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
  | _ => progress cbn [value_pattern.matches fact.rel fact.of_args fact.args_of
                       clause.rel clause.args clause_pattern.rel clause_pattern.args
                       fact.implied_by_mfs fact.implied_by_mf fact.equiv] in *
  | H : rule.one_step_derives _ _ _ |- _ => cbv [rule.one_step_derives] in H; fwd
  | H : meta_fact.matches _ _ |- _ => cbv [meta_fact.matches] in H; fwd
  | H : fact.implied_by_mfs _ _ |- _ => cbv [fact.implied_by_mfs] in H
  | H : rule.interp _ _ _ |- _ => invert1 H || invert0 H
  | H : clause.interp _ _ _ |- _ => cbv [clause.interp] in H; fwd
  | H : clause_pattern.interp _ _ _ |- _ => cbv [clause_pattern.interp] in H; fwd
  | H : expr.interp _ _ _ |- _ => invert1 H
  | H1: ?x = Some ?y, H2: ?x = Some ?z |- _ =>
      first [is_var y | is_var z]; assert (y = z) by congruence; clear H1; subst
  | _ => progress subst
  | _ => progress invert_list_stuff
  | _ => progress fwd
  | _ => progress simp
  | _ => congruence
  end.
