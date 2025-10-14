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

From Datalog Require Import Datalog Map Tactics Fp List.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List.

Import ListNotations.

Section __.
  Context {rel var fn aggregator T : Type}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map var T} {context_ok : map.ok context}.
  Context {var_eqb : var -> var -> bool} {var_eqb_spec :  forall x0 y0 : var, BoolSpec (x0 = y0) (x0 <> y0) (var_eqb x0 y0)}.

  Local Notation rule := (rule rel var fn aggregator).
  Local Notation fact := (fact rel var fn).
  Local Notation agg_expr := (agg_expr rel var fn aggregator).

  Implicit Type r : rule.
  Implicit Type ctx : context.
  Implicit Type aexpr : agg_expr.

  (*adding r to p definitely doesn't create any cycles*)
  Definition no_cycles r p :=
    Forall
      (fun concl => Forall
                   (fun r' => ~In concl.(fact_R) (map fact_R r'.(rule_hyps)) /\
                             match r'.(rule_agg) with
                             | None => True
                             | Some (_, aexpr) => ~In concl.(fact_R) (map fact_R aexpr.(agg_hyps))
                             end)
                   (r :: p))
      r.(rule_concls).
  
  (*not only is it a dag, but it's in topological order*)
  Inductive dag : list rule -> Prop :=
  | dag_nil : dag []
  | dag_cons r p :
    dag p ->
    no_cycles r p ->
    dag (r :: p).

  (*now i am wishing i had defined rule_impl in terms of a more primitive notion..*)
  Lemma good_rule_det' (r : rule) concl f1 f2 hyps agg_hyps :
    good_rule r ->
    r.(rule_concls) = [concl] ->
    rule_impl' r f1 hyps agg_hyps ->
    rule_impl' r f2 hyps agg_hyps ->
    f1 = f2.
  Proof.
    intros Hgood Hconcls H1 H2. invert H1. invert H2. cbv [good_rule] in Hgood. simpl in Hgood. fwd.
    assert (H': forall v, In (var_expr v) (flat_map fact_args r.(rule_hyps)) ->
                     agree_on ctx0 ctx v).
    { epose proof Forall2_and as H'. specialize H' with (1 := H3) (2 := H5).
      apply Forall2_forget_r in H'. rewrite Forall_forall in H'.
      intros v Hv. apply in_flat_map in Hv. fwd.
      specialize (H' _ ltac:(eassumption)). fwd. eauto using interp_fact_same_agree. }
    pose proof (fun v H => H' v (Hgoodp0 v H)) as H''. clear Hgoodp0 H'. clear H3 H5.
    rewrite Hconcls in H0, H4. invert_list_stuff. eapply interp_fact_det'; eauto.
    invert H; invert H1; try congruence.
    - apply Forall_forall. intros. symmetry. apply H''. cbv [appears_in_rule].
      left. rewrite Hconcls. simpl. rewrite app_nil_r. split; eauto.
      intros H'. fwd. congruence.
    - rewrite <- H0 in *. invert H. eapply interp_agg_expr_det' in H5; eauto.
      2: { intros. apply H''. cbv [appears_in_rule]. eauto 6. }
      subst. rewrite Forall_forall. intros v Hv. cbv [agree_on].
      do 2 rewrite map.get_put_dec. destr (var_eqb res v); auto. symmetry. apply H''.
      cbv [appears_in_rule]. left. rewrite Hconcls. split.
      { intros ?. fwd. congruence. }
      simpl. rewrite app_nil_r. assumption.
  Qed.

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
  
  Lemma rule_impl'_hyp_relname_in r x hyps agg_hyps' :
    rule_impl' r x hyps agg_hyps' ->
    Forall (fun hyp => In (fst hyp) (map fact_R (rule_hyps r))) hyps /\
      Forall (fun hyp => match r.(rule_agg) with
                      | Some (_, aexpr) => In (fst hyp) (map fact_R aexpr.(agg_hyps))
                      | None => False
                      end)
      (concat agg_hyps').
  Proof.
    intros H. invert H. split.
    - apply Forall2_forget_l in H2. eapply Forall_impl; [|eassumption].
      simpl. intros. fwd. invert Hp1. simpl. apply in_map. assumption.
    - invert H0; auto. eapply interp_agg_expr_hyp_relname_in. eassumption.
  Qed.

  Lemma rule_impl_hyp_relname_in r x hyps :
    rule_impl r x hyps ->
    Forall (fun hyp => In (fst hyp) (map fact_R (rule_hyps r)) \/
                      match r.(rule_agg) with
                      | Some (_, aexpr) => In (fst hyp) (map fact_R aexpr.(agg_hyps))
                      | None => False
                      end) hyps.
  Proof using .
    cbv [rule_impl]. intros. fwd. apply rule_impl'_hyp_relname_in in Hp1.
    fwd. apply Forall_app. split; eapply Forall_impl; eauto; simpl; eauto.
  Qed.
    
  Lemma no_cycles_spec r p f hyps :
    no_cycles r p ->
    Exists (fun r : rule => rule_impl r f hyps) (r :: p) ->
    Forall (fun hyp => ~In (fst hyp) (map fact_R (rule_concls r))) hyps.
  Proof.
    intros H1 H2. cbv [no_cycles] in H1. rewrite Forall_forall in *.
    intros x Hx H'. rewrite in_map_iff in H'. fwd. specialize (H1 _ H'p1).
    rewrite Exists_exists in H2. rewrite Forall_forall in H1. fwd.
    specialize (H1 _ H2p0). fwd.
    apply rule_impl_hyp_relname_in in H2p1. rewrite Forall_forall in H2p1.
    specialize (H2p1 _ Hx). destruct H2p1 as [H2p1|H2p1].
    - apply H1p0. rewrite in_map_iff in H2p1. fwd. rewrite H'p0. apply in_map_iff.
      eauto.
    - destruct (rule_agg x1) as [(?&?)|]; [|assumption]. rewrite <- H'p0 in H2p1. auto.
  Qed.           
  
  Lemma dag_terminates'' r p f :
    prog_impl_fact (r :: p) f ->
    ~In (fst f) (map fact_R r.(rule_concls)) ->
    no_cycles r p ->
    prog_impl_fact p f.
  Proof.
    intros H1 H2 H3. induction H1. invert H.
    { apply rule_impl_concl_relname_in in H5. exfalso. auto. }
    econstructor; [eassumption|]. epose proof no_cycles_spec as H5'.
    specialize (H5' _ _ _ _ ltac:(eauto) ltac:(eauto)). clear H5. clear H2 H0 x.
    rewrite Forall_forall in *. intros x Hx. apply H1; auto.
  Qed.
  
  Lemma dag_terminates' r p f :
    prog_impl_fact (r :: p) f ->
    no_cycles r p ->
    prog_impl_fact p f \/
      exists hyps',
        rule_impl r f hyps' /\
          Forall (prog_impl_fact p) hyps'.
  Proof.
    intros H1 H2. invert H1. pose proof no_cycles_spec as H'.
    specialize (H' _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    invert H.
    - right. eexists. split; [eassumption|]. rewrite Forall_forall in *.
      intros x Hx. specialize (H0 _ Hx). eapply dag_terminates'' in H0; eauto.
    - left. econstructor; eauto. rewrite Forall_forall in *. intros x Hx.
      eapply dag_terminates''; eauto. apply H0. assumption.
  Qed.

  Fixpoint choose_any_n {X : Type} n (fs : list X) :=
    match n with
    | S n' => flat_map (fun f => map (cons f) (choose_any_n n' fs)) fs
    | O => [[]]
    end.
  
  Lemma choose_n_spec {X : Type} n (hyps fs : list X) :
    length hyps = n ->
    incl hyps fs ->
    In hyps (choose_any_n n fs).
  Proof.
    revert hyps fs. induction n; intros hyps fs Hlen Hincl.
    - destruct hyps; [|discriminate Hlen]. simpl. auto.
    - destruct hyps; [discriminate Hlen|]. simpl in Hlen.
      apply incl_cons_inv in Hincl. fwd.
      specialize (IHn hyps _ ltac:(lia) ltac:(eassumption)).
      simpl. apply in_flat_map. eexists. split; [eassumption|].
      apply in_map. assumption.
  Qed.

  Definition eval_aexpr aexpr ctx agg_hyps's :=
    match option_coalesce (option_map get_set (subst_in_expr ctx aexpr.(agg_s))) with
    | None => None
    | Some s' =>
        
        let body's := zip (fun i' agg_hyps' =>
                             let bodyctx := map.of_list (context_of_hyps aexpr.(agg_hyps) agg_hyps') in
                             let bodyctx := map.putmany (map.put ctx aexpr.(agg_i) i') bodyctx in
                             subst_in_expr bodyctx aexpr.(agg_body)) s' agg_hyps's in
        match option_all body's with
        | None => None
        | Some body's =>
            Some (fold_right (interp_agg aexpr.(agg_agg)) (agg_id aexpr.(agg_agg)) body's)
        end
    end.

  Lemma eval_aexpr_complete ctx aexpr res agg_hyps's :
    good_agg_expr aexpr ->
    interp_agg_expr ctx aexpr res agg_hyps's ->
    eval_aexpr aexpr ctx agg_hyps's = Some res.
  Proof.
    intros Hgood H. invert H. cbv [eval_aexpr]. simpl.
    apply subst_in_expr_complete in H0. rewrite H0. simpl. rewrite H1.
    erewrite Forall2_option_all_some. 1: reflexivity.
    cbv [zip]. rewrite <- Forall2_map_l. eapply Forall3_combine12.
    apply Forall3_swap23. eapply Forall3_impl; [|eassumption]. simpl.
    clear H2. intros x y z Hxyz. fwd.
    apply subst_in_expr_complete. 
    eapply interp_expr_agree_on; eauto. cbv [good_agg_expr] in Hgood.
    simpl in Hgood. rewrite Forall_forall in Hgood. rewrite Forall_forall.
    intros v Hv. eassert (map.putmany _ _ = _) as ->. 2: apply agree_on_refl.
    apply putmany_extends_idk.
    - eapply interp_hyps_context_right_weak. eassumption.
    - cbv [map.extends]. intros k0 v0 Hkv.
      pose proof Hkv as Hkv'.
      erewrite map.get_of_list_zip in Hkv by eassumption.
      apply map.zipped_lookup_Some_in in Hkv. specialize (Hgood _ Hkv). clear Hkv.
      eapply bare_in_context_hyps in Hgood; eauto.
      apply interp_hyps_context_right in Hxyzp1.
      fwd. apply in_fst in Hgood. apply in_of_list_Some_strong in Hgood.
      fwd. rewrite Forall_forall in Hxyzp1. specialize (Hxyzp1 _ Hgoodp1).
      simpl in Hxyzp1. rewrite map.get_putmany_dec in Hxyzp1. rewrite Hkv' in Hxyzp1.
      invert Hxyzp1. assumption.
  Qed.
    
  Definition eval_rule r hyps' agg_hyps's :=
    let ctx := map.of_list (context_of_hyps r.(rule_hyps) hyps') in
    let ctx' :=
      match r.(rule_agg) with
      | None => Some ctx
      | Some (res, aexpr) =>
          match eval_aexpr aexpr ctx agg_hyps's with
          | None => None
          | Some res' => Some (map.put ctx res res')
          end
      end in
    match ctx' with
    | None => []
    | Some ctx' =>
        ListMisc.extract_Some (map (subst_in_fact ctx') r.(rule_concls))
    end.

  Lemma eval_rule_complete f r hyps' agg_hyps's :
    good_rule r ->
    rule_impl' r f hyps' agg_hyps's ->
    In f (eval_rule r hyps' agg_hyps's).
  Proof.
    intros Hgood Himpl. cbv [eval_rule]. cbv [good_rule] in Hgood.
    invert Himpl. rewrite Exists_exists in H0. fwd.
    invert H.
    - rewrite <- ListMisc.in_extract_Some. rewrite in_map_iff. eexists. split; eauto.
      apply subst_in_fact_complete. eapply interp_fact_agree_on; [eassumption|].
      apply Forall_forall. intros v H. apply interp_hyps_agree; auto.
      apply Hgoodp0. cbv [appears_in_rule]. left. rewrite in_flat_map.
      split; eauto. intros ?. fwd. congruence.
    - rewrite <- H0 in *. erewrite eval_aexpr_complete; try assumption; cycle 1.
      { eapply interp_agg_expr_agree_on; [eassumption|]. intros v Hv.
        specialize (Hgoodp0 v). specialize' Hgoodp0.
        { cbv [appears_in_rule]. right. right. eauto. }
        (*TODO factor out whatevre is happening in the next four lines*)
        eapply bare_in_context_hyps in Hgoodp0; eauto. fwd.
        apply in_fst in Hgoodp0. apply in_of_list_Some in Hgoodp0. fwd. cbv [agree_on].
        rewrite Hgoodp0. apply interp_hyps_context_right_weak in H1.
        apply H1 in Hgoodp0. rewrite Hgoodp0. reflexivity. }
      rewrite <- ListMisc.in_extract_Some. rewrite in_map_iff. eexists. split; eauto.
      apply subst_in_fact_complete. Check interp_fact_agree_on.
      eapply interp_fact_agree_on; [eassumption|]. apply Forall_forall.
      intros v Hv. cbv [agree_on]. do 2 rewrite map.get_put_dec.
      destr (var_eqb res v).
      { reflexivity. }
      apply interp_hyps_agree; auto.
      apply Hgoodp0. cbv [appears_in_rule]. left. rewrite in_flat_map.
      split; eauto. intros ?. fwd. congruence.
  Qed.

  Definition num_agg_hyps r :=
    match r.(rule_agg) with
    | None => O
    | Some (_, aexpr) => length aexpr.(agg_hyps)
    end.

  Lemma num_agg_hyps_spec' ctx res aexpr agg_hyps's :
    interp_agg_expr ctx aexpr res agg_hyps's ->
    Forall (fun agg_hyps' => length agg_hyps' = length aexpr.(agg_hyps)) agg_hyps's.
  Proof.
    invert 1. simpl. apply Forall3_ignore12 in H2. eapply Forall_impl; [|eassumption].
    clear. simpl. intros. fwd. apply Forall2_length in Hp1. auto.
  Qed.                    

  Lemma num_agg_hyps_spec r f hyps' agg_hyps's :
    rule_impl' r f hyps' agg_hyps's ->
    Forall (fun agg_hyps' => length agg_hyps' = num_agg_hyps r) agg_hyps's.
  Proof.
    intros H. invert H. cbv [num_agg_hyps]. invert H0; auto.
    eapply num_agg_hyps_spec'. eassumption.
  Qed.
  
  Definition step (r : rule) (facts : list (rel * list T)) : list (rel * list T) :=
    let hyps'_choices := choose_any_n (length r.(rule_hyps)) facts in
    flat_map
      (fun hyps' =>
         let agg_hyps'_choices := choose_any_n (num_agg_hyps r) facts in
         let agg_hyps's_choices := choose_any_n (agg_hyps'_len r hyps') agg_hyps'_choices in
         flat_map (eval_rule r hyps') agg_hyps's_choices)
      hyps'_choices.

  Lemma rule_impl'_hyps'_len r f hyps' agg_hyps' :
    rule_impl' r f hyps' agg_hyps' ->
    length hyps' = length r.(rule_hyps).
  Proof.
    intros H. invert H. apply Forall2_length in H2. auto.
  Qed.

  Lemma step_complete r hyps' facts f :
    good_rule r ->
    incl hyps' facts ->
    rule_impl r f hyps' ->
    In f (step r facts).
  Proof.
    intros H1 H2 H3. cbv [step]. apply in_flat_map.
    cbv [rule_impl] in H3. fwd.
    apply incl_app_inv in H2. fwd.
    apply incl_concat_l in H2p1.
    exists hyps'0. split.
    { apply choose_n_spec.
      - eapply rule_impl'_hyps'_len. eassumption.
      - assumption. }
    apply in_flat_map. exists agg_hyps's. split.
    { apply choose_n_spec.
      - eapply agg_hyps_determined; eassumption.
      - cbv [incl]. apply Forall_forall.
        eapply Forall_impl.
        2: { apply Forall_and; [eassumption|]. eapply num_agg_hyps_spec. eassumption. }
        simpl. intros. fwd. apply choose_n_spec; assumption. }
    apply eval_rule_complete; assumption.
  Qed.

  Definition step_everybody p fs := flat_map (fun r => step r fs) p.

  Definition eval n p := iter n (fun fs => step_everybody p fs ++ fs) nil.

  Definition eval_dag p := eval (length p) p.

  Lemma choose_any_n_mono {A : Type} n (xs ys : list A) :
    incl xs ys ->
    incl (choose_any_n n xs) (choose_any_n n ys).
  Proof.
    induction n; simpl; auto with incl.
  Qed.

  Hint Resolve choose_any_n_mono : core.

  Lemma step_mono r fs1 fs2 :
    incl fs1 fs2 ->
    incl (step r fs1) (step r fs2).
  Proof. cbv [step]. auto with incl. Qed.

  Hint Resolve step_mono : core.

  Lemma eval_mono n m p1 p2 :
    incl p1 p2 ->
    n <= m ->
    incl (eval n p1) (eval m p2).
  Proof.
    intros H. revert m. induction n; simpl; auto with incl. intros m Hm.
    destruct m as [|m]; [lia|]. specialize (IHn m ltac:(lia)).
    simpl. cbv [step_everybody]. auto with incl.
  Qed.

  Lemma incl_mono_fun {X : Type} (f g : list X -> list X) x n :
    (forall l1 l2, incl l1 l2 -> incl (f l1) (g l2)) ->
    incl (iter n f x) (iter n g x).
  Proof. intros. induction n; simpl; auto with incl. Qed.

  Lemma eval_dag_complete p :
    Forall good_rule p ->
    dag p ->
    forall f,
      prog_impl_fact p f ->
      In f (eval_dag p).
  Proof.
    intros Hgood H. induction H.
    - simpl. intros f Hf. invert Hf. invert_list_stuff.
    - invert Hgood. specialize (IHdag ltac:(assumption)). intros.
      cbv [eval_dag eval]. cbn [length iter]. (*does nothing.  why would you use nat_rect instead of fixpoint?*)
      rewrite iter_succ. 
      pose proof dag_terminates' as H'.
      specialize (H' _ _ _ ltac:(eassumption) ltac:(eassumption)).
      apply in_app_iff. destruct H' as [H'|H'].
      + right. apply IHdag in H'. eapply eval_mono in H'; eauto with incl.
      + left. fwd. unfold step_everybody at 1. cbn [flat_map]. apply in_app_iff. left.
        eapply step_complete; try eassumption. eapply incl_tran.
        { intros hyp' H'. apply IHdag. rewrite Forall_forall in H'p1. auto. }
        apply incl_mono_fun. cbv [step_everybody]. auto with incl.
  Qed.
End __.
