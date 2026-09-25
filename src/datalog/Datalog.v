From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Eqdep_dec.
From Stdlib Require Import RelationClasses Morphisms.
From Datalog.Util Require Import Autodestr Autocbn Pftree.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List Datatypes.Option Eqb.

From Datalog Require Import Map Tactics Fp List Eqb Decidable Default.
From GraphSearch Require Import Dag.

Import ListNotations.
Open Scope bool_scope.

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

Class datalog_semantics {_fn : fnT} {_aggregator: aggregatorT} {_value : valueT} : Type :=
  {
    interp_fun : fn -> list value -> option value;
    (* (*if x represents a finite set S then get_set x = Some S. *)
    (*   note: suffices to have this be T -> option nat, for cardinality... *)
    (*   should i do that? *) *)
    (* get_set : T -> option (T -> Prop); *)
    get_nat : value -> nat;
    agg_bop : aggregator -> value -> value -> value;
    agg_id : aggregator -> value; }.
Arguments datalog_semantics : clear implicits.

Class datalog_params {_rel : relT} {_exprvar : exprvarT} `{semantics : datalog_semantics} {context : map.map _exprvar value} {context_ok : map.ok context} {value_eqb : Eqb value} {value_eqb_ok : Eqb_ok value_eqb} {value_set : map.map (list value) unit} {value_set_ok : map.ok value_set} := {}.

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

    Context {var_eqb : Eqb exprvar} {var_eqb_ok : Eqb_ok var_eqb}.
    Context {fn_eqb : Eqb fn} {fn_eqb_ok : Eqb_ok fn_eqb}.

    #[global] Instance eqb : Eqb expr :=
      fix expr_eqb e1 e2 :=
        match e1, e2 with
        | var v1, var v2 => var_eqb v1 v2
        | app f1 args1, app f2 args2 =>
            fn_eqb f1 f2 && forallb2 expr_eqb args1 args2
        | _, _ => false
        end.

    #[global] Instance eqb_ok : Eqb_ok eqb.
    Proof.
      intros e1. induction e1 as [v|f args IH]; intros [v0|f0 args0]; cbv [Eqb.eqb] in *; simpl; try congruence.
      - destr (var_eqb v v0); congruence.
      - destr (fn_eqb f f0); simpl; [|congruence].
        pose proof (forallb2_eqb_ok_strong _ eqb args args0 IH) as Hargs.
        destruct (forallb2 eqb args args0); congruence.
    Qed.
  End __.
End expr. Abbreviation expr := expr.expr.
#[export] Hint Constructors expr.interp : core.

Module normal_fact.
  Record normal_fact {relt : relT} {value : valueT} :=
    { rel : relt;
      args : list value }.
  (*i don't actually want this to be global; i'd prefer to instead export it along with normal_fact.  but the Import/Export commands aren't granular enough for me to do that.*)
  #[global] Ltac2 Set to_destruct as prev := fun _ => pattern_pred pat:(@normal_fact _ _) :: prev ().
  #[global] Ltac2 Set to_cbn as prev := fun _ => reference:(rel) :: reference:(args) :: prev ().

  Section __.
    Context {relt : relT} {value : valueT}.
    Context {rel_eqb : Eqb relt} {rel_eqb_ok : Eqb_ok rel_eqb}.
    Context {value_eqb : Eqb value} {value_eqb_ok : Eqb_ok value_eqb}.

    #[global] Instance eqb : Eqb normal_fact :=
      fun f1 f2 => eqb f1.(rel) f2.(rel) && eqb f1.(args) f2.(args).

    #[global] Instance eqb_ok : Eqb_ok eqb.
    Proof.
      intros [R1 args1] [R2 args2]. cbv [Eqb.eqb eqb]. simpl.
      destr (rel_eqb R1 R2); [|congruence]. destr (list_eqb args1 args2); congruence.
    Qed.
  End __.
End normal_fact. Abbreviation normal_fact := normal_fact.normal_fact.
#[export] Hint Unfold normal_fact.rel normal_fact.args : core.

Module value_pattern.
  Section __.
    Context {value : valueT} {value_eqb : Eqb value} {value_eqb_ok : Eqb_ok value_eqb}.
    (*could consider extending this?*)
    Variant value_pattern {value : valueT} :=
      | exactly (v : value)
      | any.

    Definition matches (p : value_pattern) v :=
      match p with
      | exactly v0 => v0 = v
      | any => True
      end.

    Definition matchesb (p : value_pattern) v :=
      match p with
      | exactly v0 => eqb v0 v
      | any => true
      end.

    Definition value_of (p : value_pattern) : option value :=
      match p with
      | exactly v => Some v
      | any => None
      end.

    Lemma matchesb_matches p v :
      matchesb p v = true <-> matches p v.
    Proof.
      destruct p; simpl.
      - pose proof (eqb_spec v0 v) as Hs. cbv [eqb] in *.
        destruct (value_eqb v0 v); intuition congruence.
      - intuition auto.
    Qed.

    #[global] Instance matchesb_spec p v :
      Reflects (matches p v) (matchesb p v).
    Proof.
      destruct p; simpl.
      - exact _.
      - constructor. constructor.
    Qed.

    Lemma matches_map_exactly vs :
      Forall2 matches (map exactly vs) vs.
    Proof.
      rewrite <- Forall2_map_l. apply Forall2_same. apply Forall_forall. simpl. auto.
    Qed.

    Lemma matches_map_exactly_inv vs vs' :
      Forall2 matches (map exactly vs) vs' -> vs' = vs.
    Proof.
      revert vs'. induction vs as [|v vs IH]; intros [|y vs'] H; invert H; auto.
      cbn [matches] in *. f_equal; auto.
    Qed.

    #[global] Instance eqb : Eqb value_pattern :=
      fun p1 p2 =>
        match p1, p2 with
        | exactly v1, exactly v2 => eqb v1 v2
        | any, any => true
        | _, _ => false
        end.

    #[global] Instance eqb_ok : Eqb_ok eqb.
    Proof.
      intros [v1|] [v2|]; cbv [Eqb.eqb eqb]; try congruence.
      destr (value_eqb v1 v2); congruence.
    Qed.
End __.
End value_pattern. Abbreviation value_pattern := value_pattern.value_pattern.
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

    Context {rel_eqb : Eqb relt} {rel_eqb_ok : Eqb_ok rel_eqb}.
    Context {value_eqb : Eqb value} {value_eqb_ok : Eqb_ok value_eqb}.

    Definition matchesb (fp : fact_pattern) f :=
      eqb fp.(rel) f.(normal_fact.rel) && forallb2 value_pattern.matchesb fp.(args) f.(normal_fact.args).

    #[global] Instance matchesb_spec fp f :
      Reflects (matches fp f) (matchesb fp f).
    Proof.
      cbv [matches matchesb Eqb.eqb]. destr (rel_eqb fp.(rel) f.(normal_fact.rel)); simpl.
      - eapply Reflects_iff; [exact _|]. intuition congruence.
      - constructor. intuition congruence.
    Qed.
  End __.

  Section __.
    Context {relt : relT} {value : valueT}.
    Context {rel_eqb : Eqb relt} {rel_eqb_ok : Eqb_ok rel_eqb}.
    Context {value_pattern_eqb : Eqb value_pattern} {value_pattern_eqb_ok : Eqb_ok value_pattern_eqb}.

    #[global] Instance eqb : Eqb fact_pattern :=
      fun p1 p2 => eqb p1.(rel) p2.(rel) && eqb p1.(args) p2.(args).

    #[global] Instance eqb_ok : Eqb_ok eqb.
    Proof.
      intros [R1 args1] [R2 args2]. cbv [Eqb.eqb eqb]. simpl.
      destr (rel_eqb R1 R2); [|congruence]. destr (list_eqb args1 args2); congruence.
    Qed.
  End __.
End fact_pattern. Abbreviation fact_pattern := fact_pattern.fact_pattern.

Module meta_fact.
  Section __.
    Context `{params : datalog_params}.
    Definition canonicalb (pat : list value_pattern) (vals : fset (list value)) :=
      forallb (forallb2 value_pattern.matchesb pat) (map.keys vals).

    Definition canonical (pat : list value_pattern) (vals : fset (list value)) :=
      Forall (Forall2 value_pattern.matches pat) (map.keys vals).

    Record meta_fact :=
      { pattern : fact_pattern;
        set : fset (list value);
        _pf : canonicalb pattern.(fact_pattern.args) set = true }.
  End __.
  #[global] Ltac2 Set to_destruct as prev := fun _ => pattern_pred pat:(@meta_fact _ _ _ _) :: prev ().
  #[global] Ltac2 Set to_cbn as prev := fun _ => reference:(pattern) :: reference:(set) :: prev ().

  Section __.
    Context `{params : datalog_params}.

    Definition to_canonical_set pat (vals : list (list value)) :=
      map.of_list (map (fun args => (args, tt))
                     (filter (forallb2 value_pattern.matchesb pat) vals)).

    Lemma contains_to_canonical_set pat vals nf_args :
      fset.contains (to_canonical_set pat vals) nf_args <->
        Forall2 value_pattern.matches pat nf_args /\ In nf_args vals.
    Proof.
      cbv [fset.contains to_canonical_set].
      rewrite keys_of_list_same_set, map_map, in_map_iff. simpl.
      setoid_rewrite filter_In. setoid_rewrite Reflects_true_iff; [|typeclasses eauto].
      split; intros; fwd; eauto.
    Qed.

    Lemma canonical_of_list pat vals :
      canonical pat (to_canonical_set pat vals).
    Proof.
      apply Forall_forall. intros nf_args Hin.
      apply contains_to_canonical_set in Hin. fwd. assumption.
    Qed.

    Definition mk (pat : fact_pattern) (vals : list (list value)) : meta_fact.
    Proof.
      refine {| pattern := pat; set := to_canonical_set pat.(fact_pattern.args) vals |}.
      abstract (rewrite Reflects_true_iff by typeclasses eauto;
                apply canonical_of_list).
    Defined.

    Lemma eq_ext mf1 mf2 :
      mf1.(pattern) = mf2.(pattern) ->
      mf1.(set) = mf2.(set) ->
      mf1 = mf2.
    Proof.
      destruct mf1, mf2. simpl. intros. subst. f_equal.
      apply Eqdep_dec.UIP_dec, Bool.bool_dec.
    Qed.

    Definition matches mf nf :=
      fact_pattern.matches mf.(pattern) nf /\ fset.contains mf.(set) nf.(normal_fact.args).

    Lemma matches_mk pat vals nf :
      matches (mk pat vals) nf <->
      fact_pattern.matches pat nf /\ In nf.(normal_fact.args) vals.
    Proof.
      cbv [matches fact_pattern.matches]. simpl.
      rewrite contains_to_canonical_set. tauto.
    Qed.

    Lemma contains_mk pat vals args :
      fset.contains (mk pat vals).(set) args <->
        Forall2 value_pattern.matches pat.(fact_pattern.args) args /\ In args vals.
    Proof. apply contains_to_canonical_set. Qed.

    Definition rel mf := mf.(pattern).(fact_pattern.rel).

    Definition normal_facts (mf : meta_fact) : list normal_fact :=
      map
        (fun args => {| normal_fact.rel := rel mf;
                    normal_fact.args := args |})
        (map.keys mf.(set)).

    Definition consistent_with (mf : meta_fact) (S : normal_fact -> Prop) :=
      forall nf,
        fact_pattern.matches mf.(meta_fact.pattern) nf ->
        fset.contains mf.(meta_fact.set) nf.(normal_fact.args) <-> S nf.

    Lemma consistent_with_ext mf S1 S2 :
      consistent_with mf S1 ->
      (forall nf, nf.(normal_fact.rel) = rel mf -> S1 nf <-> S2 nf) ->
      consistent_with mf S2.
    Proof.
      cbv [consistent_with]. intros H HS nf Hm. rewrite H by assumption. apply HS.
      destruct Hm as (Hrel & _). cbv [rel]. congruence.
    Qed.

    Definition agree (mf1 mf2 : meta_fact) :=
      forall nf,
        fact_pattern.matches mf1.(pattern) nf ->
        fact_pattern.matches mf2.(pattern) nf ->
        (fset.contains mf1.(set) nf.(normal_fact.args) <-> fset.contains mf2.(set) nf.(normal_fact.args)).

    Lemma agree_sym mf1 mf2 :
      agree mf1 mf2 ->
      agree mf2 mf1.
    Proof. cbv [agree]. intros H nf H1 H2. symmetry. auto. Qed.

    Lemma contains_matches (mf : meta_fact) x :
      fset.contains mf.(set) x ->
      Forall2 value_pattern.matches mf.(pattern).(fact_pattern.args) x.
    Proof.
      destruct mf as [? ? Hpf]. cbv [fset.contains]. simpl. intros Hin.
      rewrite Reflects_true_iff in Hpf by typeclasses eauto.
      rewrite Forall_forall in Hpf. auto.
    Qed.

    Lemma mk_same_set pat vals vals' :
      same_set vals vals' ->
      mk pat vals = mk pat vals'.
    Proof.
      intros Hsame. apply eq_ext; [reflexivity|]. apply fset.ext. intros args.
      rewrite !contains_mk, Hsame. reflexivity.
    Qed.

    Lemma mk_keys_perm pat vals :
      NoDup vals ->
      Forall (Forall2 value_pattern.matches pat.(fact_pattern.args)) vals ->
      Permutation (map.keys (mk pat vals).(set)) vals.
    Proof.
      intros Hnd Hm. rewrite Forall_forall in Hm.
      apply NoDup_Permutation; [apply map.keys_NoDup | assumption |]. intros args.
      pose proof (contains_mk pat vals args) as H. cbv [fset.contains] in H. rewrite H. intuition auto.
    Qed.

    Lemma mk_keys mf :
      mk mf.(pattern) (map.keys mf.(set)) = mf.
    Proof.
      apply eq_ext; [reflexivity|]. apply fset.ext. intros args.
      rewrite contains_mk. cbv [fset.contains]. intuition auto using contains_matches.
    Qed.

    Lemma in_normal_facts mf nf :
      In nf (normal_facts mf) <-> matches mf nf.
    Proof.
      cbv [normal_facts matches fact_pattern.matches fset.contains rel].
      rewrite in_map_iff. split.
      - intros (args & <- & Hin). simpl. ssplit; [reflexivity | | exact Hin].
        apply (contains_matches mf args Hin).
      - intros ((Hrel & Hargs) & Hin). exists nf.(normal_fact.args).
        destruct nf. simpl in *. subst. auto.
    Qed.

    Lemma eq_of_agree mf1 mf2 :
      mf1.(pattern) = mf2.(pattern) ->
      agree mf1 mf2 ->
      mf1 = mf2.
    Proof.
      intros Hpat Hagree. apply eq_ext; [assumption|]. apply fset.ext. intros x.
      destr (forallb2 value_pattern.matchesb mf1.(pattern).(fact_pattern.args) x).
      - simp. eapply (Hagree {| normal_fact.rel := _ |}); cbv [fact_pattern.matches]; simpl in *; eauto.
      - split; intros Hc; apply contains_matches in Hc; try contradiction.
        rewrite <- Hpat in Hc. contradiction.
    Qed.
  End __.
  #[global] Ltac2 Set to_cbn as prev := fun _ => reference:(mk) :: prev ().
End meta_fact. Abbreviation meta_fact := meta_fact.meta_fact.
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
End clause. Abbreviation clause := clause.clause.
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

    Definition expr_of p :=
      match p with
      | exactly e => Some e
      | any => None
      end.

    Context {expr_eqb : Eqb expr} {expr_eqb_ok : Eqb_ok expr_eqb}.

    #[global] Instance eqb : Eqb expr_pattern :=
      fun p1 p2 =>
        match p1, p2 with
        | exactly e1, exactly e2 => eqb e1 e2
        | any, any => true
        | _, _ => false
        end.

    #[global] Instance eqb_ok : Eqb_ok eqb.
    Proof.
      intros [e1|] [e2|]; cbv [Eqb.eqb eqb]; try congruence.
      destr (expr_eqb e1 e2); congruence.
    Qed.
  End __.
End expr_pattern. Abbreviation expr_pattern := expr_pattern.expr_pattern.

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

  Section __.
    Context {relt : relT} {exprvar : exprvarT} {fn : fnT}.
    Context {rel_eqb : Eqb relt} {rel_eqb_ok : Eqb_ok rel_eqb}.
    Context {expr_pattern_eqb : Eqb expr_pattern} {expr_pattern_eqb_ok : Eqb_ok expr_pattern_eqb}.

    #[global] Instance eqb : Eqb clause_pattern :=
      fun c1 c2 => eqb c1.(rel) c2.(rel) && eqb c1.(args) c2.(args).

    #[global] Instance eqb_ok : Eqb_ok eqb.
    Proof.
      intros [R1 args1] [R2 args2]. cbv [Eqb.eqb eqb]. simpl.
      destr (rel_eqb R1 R2); [|congruence]. destr (list_eqb args1 args2); congruence.
    Qed.
  End __.
End clause_pattern. Abbreviation clause_pattern := clause_pattern.clause_pattern.

Module fact.
  Section __.
    Context `{params : datalog_params}.
    Variant fact :=
      | normal (_ : normal_fact)
      | meta (_ : meta_fact).

    Definition rel f :=
      match f with
      | meta mf => meta_fact.rel mf
      | normal nf => normal_fact.rel nf
      end.

    (*if we know hyp and the normal_facts that hyp includes, then do we know f?*)
    Definition implied_by_mf (f : fact) (hyp : meta_fact) :=
      match f with
      | normal nf => meta_fact.matches hyp nf
      | meta mf => mf = hyp
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

    Lemma implied_by_mfs_pats mfs f :
      implied_by_mfs mfs f ->
      covered_by_pats (map meta_fact.pattern mfs) f.
    Proof.
      cbv [implied_by_mfs covered_by_pats implied_by_mf covered_by]. destruct f; intros H.
      - rewrite Exists_map. eapply Exists_impl; [|eassumption].
        cbv [meta_fact.matches]. simpl. intros. fwd. assumption.
      - rewrite Exists_map. eapply Exists_impl; [|eassumption].
        simpl. intros x Hx. rewrite Hx. reflexivity.
    Qed.

    Definition is_meta f :=
      match f with
      | meta _ => True
      | normal _ => False
      end.

    Definition normal_facts (f : fact) : list normal_fact :=
      match f with
      | normal nf => [nf]
      | meta _ => []
      end.

    Lemma in_normal_facts nf f :
      In nf (normal_facts f) <-> f = normal nf.
    Proof. destruct f; simpl; intuition congruence. Qed.

    Lemma in_flat_map_normal_facts nf fs :
      In nf (flat_map normal_facts fs) <-> In (normal nf) fs.
    Proof.
      rewrite in_flat_map. setoid_rewrite in_normal_facts.
      split; [intros (? & ? & ->) | intros]; eauto.
    Qed.

    Definition meta_facts (f : fact) : list meta_fact :=
      match f with
      | normal _ => []
      | meta mf => [mf]
      end.

    Lemma in_meta_facts mf f :
      In mf (meta_facts f) <-> f = meta mf.
    Proof. destruct f; simpl; intuition congruence. Qed.

    Lemma in_flat_map_meta_facts mf fs :
      In mf (flat_map meta_facts fs) <-> In (meta mf) fs.
    Proof.
      rewrite in_flat_map. setoid_rewrite in_meta_facts.
      split; [intros (? & ? & ->) | intros]; eauto.
    Qed.

    Definition normal_subset (S : fact -> Prop) :=
      fun nf => S (normal nf).

    Definition set_doesnt_lie (S : fact -> Prop) :=
      forall mf, S (meta mf) -> meta_fact.consistent_with mf (normal_subset S).

    Lemma set_doesnt_lie_agree (S : fact -> Prop) mf1 mf2 :
      set_doesnt_lie S ->
      S (meta mf1) ->
      S (meta mf2) ->
      meta_fact.agree mf1 mf2.
    Proof.
      cbv [set_doesnt_lie meta_fact.consistent_with meta_fact.agree].
      intros H H1 H2 nf Hm1 Hm2.
      rewrite (H _ H1) by assumption. rewrite (H _ H2) by assumption. reflexivity.
    Qed.

  End __.
End fact. Abbreviation fact := fact.fact.

Module result.
  Section __.
    Context `{params : datalog_params}.
    Record result :=
      { normal : list value -> Prop;
        done : list value_pattern -> Prop; }.

    (*ignores the relation of r*)
    Definition contains (r : result) (f : fact) :=
      match f with
      | fact.meta mf =>
          r.(done) mf.(meta_fact.pattern).(fact_pattern.args) /\
            meta_fact.consistent_with mf (fun nf => r.(normal) nf.(normal_fact.args))
      | fact.normal nf =>
          r.(normal) nf.(normal_fact.args)
      end.

    Definition of_facts R (fs : fact -> Prop) :=
      {| normal := fun nf_args => fs (fact.normal {| normal_fact.rel := R; normal_fact.args := nf_args |});
        done := fun mf_args =>
          exists mf, fs (fact.meta mf) /\
                mf.(meta_fact.pattern) = {| fact_pattern.rel := R; fact_pattern.args := mf_args |} |}.

    Lemma contains_of_facts R fs f :
      fact.set_doesnt_lie fs ->
      fact.rel f = R ->
      contains (of_facts R fs) f <-> fs f.
    Proof.
      intros Hlie Hrel. destruct f as [nf|mf]; simpl in Hrel; subst; simpl.
      - destruct nf. reflexivity.
      - split.
        + intros [(mf' & Hmf' & Hpat) Hcons]. replace mf with mf'; [exact Hmf'|].
          apply meta_fact.eq_of_agree.
          { rewrite Hpat. cbv [meta_fact.rel]. destruct (meta_fact.pattern mf). reflexivity. }
          intros [r a] Hm' Hm. rewrite (Hlie _ Hmf' _ Hm'), (Hcons _ Hm).
          cbv [fact_pattern.matches] in Hm. simpl in *. fwd. reflexivity.
        + intros Hmf. split.
          * exists mf. split; [exact Hmf|]. cbv [meta_fact.rel]. destruct (meta_fact.pattern mf).
            reflexivity.
          * intros [r a] Hm. rewrite (Hlie _ Hmf _ Hm). cbv [fact.normal_subset].
            cbv [fact_pattern.matches] in Hm. simpl in *. fwd. reflexivity.
    Qed.
  End __.
End result. Abbreviation result := result.result.

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
      | interp_agg vals concl_rel a hyp_rel (args : list value) :
        NoDup vals ->
        interp
          (agg concl_rel a hyp_rel)
          {| normal_fact.rel := concl_rel;
            normal_fact.args := interp_agg a vals :: args |}
          (fact.meta
             (meta_fact.mk
                {| fact_pattern.rel := hyp_rel;
                  fact_pattern.args := value_pattern.any :: value_pattern.any :: map value_pattern.exactly args |}
                (map (fun '(i, x) => i :: x :: args) vals))
             ::
             map (fun '(i, x_i) => fact.normal {| normal_fact.rel := hyp_rel; normal_fact.args := (i :: x_i :: args) |}) vals).

    (*if we know only mfs and the normal facts that mfs include, then can we derive f with exactly one rule application?*)
    Definition one_step_derives (p : list rule) (mfs : list meta_fact) (nf : normal_fact) :=
      exists hyps,
        Exists (fun r => interp r nf hyps) p /\
          Forall (fact.implied_by_mfs mfs) hyps.

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
End rule. Abbreviation rule := rule.rule.

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
      pattern_interp r mf.(meta_fact.pattern) (map meta_fact.pattern hyps) /\
        forall nf,
          fact_pattern.matches mf.(meta_fact.pattern) nf ->
          fset.contains mf.(meta_fact.set) nf.(normal_fact.args) <->
            rule.one_step_derives prog hyps nf.

    Definition concl_rels (r : meta_rule) :=
      map clause_pattern.rel r.(concls).

    Definition hyp_rels (r : meta_rule) :=
      map clause_pattern.rel r.(hyps).

    Definition concl_vars (r : meta_rule) :=
      flat_map clause_pattern.vars r.(concls).

    Definition hyp_vars (r : meta_rule) :=
      flat_map clause_pattern.vars r.(hyps).

    Definition all_vars (r : meta_rule) := concl_vars r ++ hyp_vars r.

    Definition hyp_args (r : meta_rule) :=
      flat_map clause_pattern.args r.(hyps).

    Definition is_bottomup (r : meta_rule) :=
      forall v, In v (all_vars r) -> In (expr_pattern.exactly (expr.var v)) (hyp_args r).

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
      cbv [interp]. intros H. fwd. subst.
      eapply pattern_interp_concl_relname_in. eassumption.
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
      intros [Hpat _].
      apply pattern_interp_hyp_relname_in in Hpat.
      rewrite Lists.List.Forall_map in Hpat. exact Hpat.
    Qed.

    Lemma interp_prog_ext p1 p2 r mf hyps :
      (forall mfs nf,
          In nf.(normal_fact.rel) (concl_rels r) ->
          rule.one_step_derives p1 mfs nf <-> rule.one_step_derives p2 mfs nf) ->
      interp p1 r mf hyps <-> interp p2 r mf hyps.
    Proof.
      cbv [interp]. intros H.
      assert (Hin : forall nf,
                 fact_pattern.matches mf.(meta_fact.pattern) nf ->
                 pattern_interp r mf.(meta_fact.pattern) (map meta_fact.pattern hyps) ->
                 In nf.(normal_fact.rel) (concl_rels r)).
      { intros nf Hmatch Hpat. rewrite <- (proj1 Hmatch).
        eauto using pattern_interp_concl_relname_in. }
      split; intros [Hpat Hset]; (split; [exact Hpat|]); intros nf Hmatch.
      - rewrite Hset by assumption. apply H. eauto.
      - rewrite Hset by assumption. symmetry. apply H. eauto.
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
End meta_rule. Abbreviation meta_rule := meta_rule.meta_rule.

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

    Lemma interp_step_strong p Q f hyps :
      interp_step p f hyps ->
      Forall (interp p Q) hyps ->
      interp p Q f.
    Proof. intros. eapply pftree.step; eassumption. Qed.

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
    #[local] Hint Resolve interp_step_hyp_relname_in : core.

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
    #[local] Hint Resolve interp_step_concl_relname_in : core.

    Definition all_rels (p : program) := concl_rels p ++ hyp_rels p.

    Ltac in_rel_list :=
      intros;
      cbv [all_rels concl_rels hyp_rels];
      rewrite ?in_app_iff, !in_flat_map;
      eauto 6.

    Lemma rule_concl_rel_in p r x :
      In r p.(rules) ->
      In x (rule.concl_rels r) ->
      In x (concl_rels p).
    Proof. in_rel_list. Qed.

    Lemma rule_hyp_rel_in p r x :
      In r p.(rules) ->
      In x (rule.hyp_rels r) ->
      In x (hyp_rels p).
    Proof. in_rel_list. Qed.

    Lemma meta_rule_concl_rel_in p mr x :
      In mr p.(meta_rules) ->
      In x (meta_rule.concl_rels mr) ->
      In x (concl_rels p).
    Proof. in_rel_list. Qed.

    Lemma meta_rule_hyp_rel_in p mr x :
      In mr p.(meta_rules) ->
      In x (meta_rule.hyp_rels mr) ->
      In x (hyp_rels p).
    Proof. in_rel_list. Qed.

    Lemma concl_rel_all p x :
      In x (concl_rels p) ->
      In x (all_rels p).
    Proof. cbv [all_rels]. intros. apply in_or_app. auto. Qed.

    Lemma hyp_rel_all p x :
      In x (hyp_rels p) ->
      In x (all_rels p).
    Proof. cbv [all_rels]. intros. apply in_or_app. auto. Qed.

    Lemma interp_invariant p Q f :
      interp p Q f <->
        interp p (fun f' => Q f' /\ (f' = f \/ In (fact.rel f') (hyp_rels p))) f.
    Proof.
      split; intros H.
      - apply pftree.invariant; eauto.
      - eapply pftree.weaken_hyp; [eassumption|]. simpl. intros. fwd. assumption.
    Qed.

    Lemma interp_invariant' p Q f :
      ~Q f ->
      interp p Q f <->
        interp p (fun f' => Q f' /\ In (fact.rel f') (hyp_rels p)) f.
    Proof.
      intros. rewrite interp_invariant. apply pftree.hyp_ext.
      intros. split; intros; fwd; eauto. (*TODO destruct_one_or*)
      invert H0p1; auto || (exfalso; auto).
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

    Lemma concl_rels_union p1 p2 :
      Permutation (concl_rels (union p1 p2)) (concl_rels p1 ++ concl_rels p2).
    Proof.
      cbv [concl_rels union]. simpl. rewrite !flat_map_app, <- !app_assoc.
      apply Permutation_app_head. apply Permutation_app_swap_app.
    Qed.

    Lemma hyp_rels_union p1 p2 :
      Permutation (hyp_rels (union p1 p2)) (hyp_rels p1 ++ hyp_rels p2).
    Proof.
      cbv [hyp_rels union]. simpl. rewrite !flat_map_app, <- !app_assoc.
      apply Permutation_app_head. apply Permutation_app_swap_app.
    Qed.

    Lemma all_rels_union p1 p2 :
      Permutation (all_rels (union p1 p2)) (all_rels p1 ++ all_rels p2).
    Proof.
      cbv [all_rels]. rewrite concl_rels_union, hyp_rels_union, <- !app_assoc.
      apply Permutation_app_head. apply Permutation_app_swap_app.
    Qed.

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

    Lemma good_input_set_ext p Q1 Q2 :
      good_input_set p Q1 ->
      (forall f, Q1 f <-> Q2 f) ->
      good_input_set p Q2.
    Proof.
      cbv [good_input_set fact.set_doesnt_lie meta_fact.consistent_with fact.normal_subset].
      intros [Hconcl Hlie] Hext. split.
      - intros f Hf. rewrite <- Hext in Hf. eauto.
      - intros mf Hmf nf Hmatch. rewrite <- Hext in *. eauto.
    Qed.

    Definition honest (p : program) :=
      forall Q, good_input_set p Q -> fact.set_doesnt_lie (interp p Q).

    Lemma one_step_derives_iff p Q mr mhyps pat nf :
      (forall f, Q f -> ~ In (fact.rel f) (concl_rels p)) ->
      meta_rules_valid p ->
      In mr p.(meta_rules) ->
      meta_rule.pattern_interp mr pat (map meta_fact.pattern mhyps) ->
      Forall (fun mhyp => meta_fact.consistent_with mhyp (fact.normal_subset (interp p Q))) mhyps ->
      (forall mhyp mf',
          In mhyp mhyps ->
          interp p Q (fact.meta mf') ->
          mhyp.(meta_fact.pattern) = mf'.(meta_fact.pattern) ->
          mhyp = mf') ->
      Forall (fun mhyp => interp p Q (fact.meta mhyp)) mhyps ->
      fact_pattern.matches pat nf ->
      rule.one_step_derives p.(rules) mhyps nf <-> interp p Q (fact.normal nf).
    Proof.
      intros Hinp Hvalid Hmr Hpat Hcons Hagree Hderiv Hmatch.
      rewrite Forall_forall in Hcons, Hderiv. cbv [meta_fact.consistent_with] in Hcons.
      split; intros H.
      - cbv [rule.one_step_derives] in H. fwd.
        eapply interp_step_strong.
        + constructor. apply Exists_exists. eauto.
        + apply Forall_forall. intros f Hf. rewrite Forall_forall in Hp1.
          specialize (Hp1 _ Hf). cbv [fact.implied_by_mfs] in Hp1.
          rewrite Exists_exists in Hp1. fwd. destruct f as [nf0 | m].
          * cbv [fact.implied_by_mf meta_fact.matches] in Hp1p1. fwd.
            exact (proj1 (Hcons _ Hp1p0 nf0 Hp1p1p0) Hp1p1p1).
          * cbv [fact.implied_by_mf] in Hp1p1. subst m. apply Hderiv. assumption.
      - invert H.
        + exfalso. apply meta_rule.pattern_interp_concl_relname_in in Hpat.
          cbv [fact_pattern.matches] in Hmatch. fwd. simp.
          eapply Hinp; [eassumption|]. simpl.
          cbv [concl_rels]. apply in_or_app. right. apply in_flat_map. eauto.
        + invert H0. rewrite Exists_exists in H2. fwd.
          specialize (Hvalid _ _ Hmr H2p0 _ _ _ _ Hpat H2p1 Hmatch).
          cbv [rule.one_step_derives]. eexists.
          split; [apply Exists_exists; eauto|].
          eapply Forall_impl; [eapply Forall_and; [exact Hvalid | exact H1]|].
          simpl. intros f Hf. fwd. apply in_map_iff in Hfp0p0. fwd.
          cbv [fact.implied_by_mfs]. apply Exists_exists. eexists.
          split; [eassumption|].
          cbv [fact.covered_by] in Hfp0p1. destruct f as [nf0 | m].
          * cbv [fact.implied_by_mf meta_fact.matches].
            split; [assumption|]. rewrite Hcons by eassumption. assumption.
          * cbv [fact.implied_by_mf]. symmetry. apply Hagree; auto.
    Qed.

    Lemma meta_rules_valid_step p Q mf mhyps :
      (forall f, Q f -> ~ In (fact.rel f) (concl_rels p)) ->
      meta_rules_valid p ->
      Exists (fun mr => meta_rule.interp p.(rules) mr mf mhyps) p.(meta_rules) ->
      Forall (fun mhyp => meta_fact.consistent_with mhyp (fact.normal_subset (interp p Q))) mhyps ->
      (forall mhyp mf',
          In mhyp mhyps ->
          interp p Q (fact.meta mf') ->
          mhyp.(meta_fact.pattern) = mf'.(meta_fact.pattern) ->
          mhyp = mf') ->
      Forall (fun mhyp => interp p Q (fact.meta mhyp)) mhyps ->
      meta_fact.consistent_with mf (fact.normal_subset (interp p Q)).
    Proof.
      intros Hinp Hvalid Hex Hcons Hagree Hderiv.
      rewrite Exists_exists in Hex. destruct Hex as [mr [Hmr [Hpat Hset]]].
      cbv [meta_fact.consistent_with fact.normal_subset]. intros nf Hmatch.
      rewrite Hset by assumption. eapply one_step_derives_iff; eassumption.
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
        apply meta_fact.eq_of_agree.
        + congruence.
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
          destruct H0p1 as [Hpat1 Hset1]. destruct H1p1 as [Hpat2 Hset2].
          rewrite Hset1, Hset2 by assumption.
          split; intros Hd.
          * eapply one_step_derives_mhyps in Hvalid.
            3: exact Hpat2. all: eassumption.
          * eapply one_step_derives_mhyps in Hvalid.
            3: exact Hpat1. all: try eassumption.
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
      intros. eapply (meta_facts_consistent' _ _ (fact.meta _) (fact.meta _)); eassumption.
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
        cbv [meta_fact.consistent_with] in H |- *. intros nf Hmatch.
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
          apply meta_fact.eq_of_agree; [assumption|].
          eapply meta_facts_consistent; try eassumption.
          apply H0. apply in_map. assumption.
        + rewrite Forall_forall. intros mhyp Hin.
          apply H0. apply in_map. assumption.
    Qed.

    Lemma use_honest p Q mf args :
      honest p ->
      good_input_set p Q ->
      interp p Q (fact.meta mf) ->
      Forall2 value_pattern.matches mf.(meta_fact.pattern).(fact_pattern.args) args ->
      fset.contains mf.(meta_fact.set) args <->
        interp p Q (fact.normal {| normal_fact.rel := meta_fact.rel mf;
                                  normal_fact.args := args |}).
    Proof.
      intros Hhonest Hgood H Hargs.
      apply (Hhonest Q Hgood mf H {| normal_fact.rel := meta_fact.rel mf;
                                    normal_fact.args := args |}).
      cbv [fact_pattern.matches]. auto.
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
End program. Abbreviation program := program.program.

#[export] Instance program_default `{relT} `{exprvarT} `{fnT} `{aggregatorT} : WithDefault program :=
  {| program.rules := []; program.meta_rules := [] |}.

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

Ltac invert_stuff :=
  match goal with
  | _ => progress cbn [value_pattern.matches fact.rel
                       clause.rel clause.args clause_pattern.rel clause_pattern.args
                       fact.implied_by_mfs fact.implied_by_mf] in *
  | _ => progress cbv [meta_fact.rel] in *
  | H : rule.one_step_derives _ _ _ |- _ => cbv [rule.one_step_derives] in H; fwd
  | H : meta_fact.matches _ _ |- _ => cbv [meta_fact.matches] in H; fwd
  | H : fact.implied_by_mfs _ _ |- _ => cbv [fact.implied_by_mfs] in H
  | H : rule.interp _ _ _ |- _ => invert1 H || invert0 H
  | H : clause.interp _ _ _ |- _ => cbv [clause.interp] in H; fwd
  | H : clause_pattern.interp _ _ _ |- _ => cbv [clause_pattern.interp] in H; fwd
  | H : meta_rule.pattern_interp _ _ _ |- _ => cbv [meta_rule.pattern_interp] in H; fwd
  | H : meta_rule.interp _ _ _ _ |- _ => cbv [meta_rule.interp] in H; fwd
  | H : expr.interp _ _ _ |- _ => invert1 H
  | H : expr_pattern.interp _ _ _ |- _ => invert1 H
  | H1: ?x = Some ?y, H2: ?x = Some ?z |- _ =>
      first [is_var y | is_var z]; assert (y = z) by congruence; clear H1; subst
  | _ => progress subst
  | _ => progress invert_list_stuff
  | _ => progress fwd
  | _ => progress simp
  | _ => congruence
  end.
