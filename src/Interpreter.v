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
From Stdlib Require Import Permutation.


From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics.

From Datalog Require Import Datalog Map Tactics Fp List.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List.

Import ListNotations.

Section __.
  Context {rel var fn aggregator T : Type}.
  Context `{sig : signature fn aggregator T} `{query_sig : query_signature rel}.
  Context {context : map.map var T} {context_ok : map.ok context}.
  Context {var_eqb : var -> var -> bool} {var_eqb_spec :  forall x0 y0 : var, BoolSpec (x0 = y0) (x0 <> y0) (var_eqb x0 y0)}.

  Local Notation expr := (expr var fn).
  Local Notation rule := (rule rel var fn aggregator).
  Local Notation fact := (fact rel var fn).
  Local Notation agg_expr := (agg_expr rel var fn aggregator).

  Implicit Type r : rule.
  Implicit Type ctx : context.
  Implicit Type aexpr : agg_expr.

  Definition not_appears_in_a_hyp R r :=
    ~In R (map fact_R r.(rule_hyps)) /\
      match r.(rule_agg) with
      | None => True
      | Some (_, aexpr) => ~In R (map fact_R aexpr.(agg_hyps))
      end.

  (*adding r to p definitely doesn't create any cycles*)
  Definition no_cycles r p :=
    Forall
      (fun concl => Forall (not_appears_in_a_hyp concl.(fact_R)) p)
      r.(rule_concls).
  
  (*not only is it a dag, but it's in topological order*)
  Inductive dag : list rule -> Prop :=
  | dag_nil : dag []
  | dag_cons r p :
    dag p ->
    no_cycles r (r :: p) ->
    dag (r :: p).

  Inductive dag' : list rule -> Prop :=
  | dag'_nil : dag' []
  | dag'_cons p1 p2 r :
    dag' (p1 ++ p2) ->
    no_cycles r (r :: p1 ++ p2) ->
    dag' (p1 ++ r :: p2).

  Hint Constructors dag dag' : core.

  Lemma no_cycles_app r p1 p2:
    no_cycles r p1 ->
    no_cycles r p2 ->
    no_cycles r (p1 ++ p2).
  Proof.
    intros H1 H2. cbv [no_cycles] in *. eapply Forall_impl.
    2: apply Forall_and; [exact H1|exact H2]. clear. simpl. intros. fwd.
    rewrite Forall_app. auto.
  Qed.

  Lemma no_cycles_incl r p1 p2 :
    no_cycles r p2 ->
    incl p1 p2 ->
    no_cycles r p1.
  Proof.
    intros H1 H2. cbv [no_cycles] in *. eapply Forall_impl; [|eassumption].
    simpl. intros f Hf. eauto using incl_Forall.
  Qed.
  
  Lemma dag'_dag p' :
    dag' p' ->
    exists p,
      incl p' p /\ incl p p' /\ dag p.
  Proof.
    intros H. induction H.
    - eauto with incl. 
    - fwd. exists (r :: p). ssplit.
      + apply incl_app; eauto 4 with incl.
      + apply incl_cons.
        -- apply in_app_iff. auto with incl.
        -- eapply incl_tran; [eassumption|]. eauto with incl.
      + constructor; auto. eauto using no_cycles_incl with incl.
  Qed.

  Lemma dag_dag' p :
    dag p ->
    dag' p.
  Proof.
    intros H. induction H; eauto. apply (dag'_cons nil); auto.
  Qed.

  Search Permutation repeat. (*wow that is exactly what i was looking for*)

  Lemma dag'_permutation p1 p2 :
    Permutation p1 p2 ->
    dag' p1 ->
    dag' p2.
  Proof.
    revert p2. remember (length p1) as n eqn:E. revert p1 E. induction n.
    - intros p1 E p2 H1 H2. apply Permutation_length in H1.
      destruct p2; simpl in *; try congruence. constructor.
    - intros p1 E p2 H1 H2. invert H2; try discriminate E.
      pose proof Permutation_in as H'. specialize H' with (1 := H1).
      specialize (H' r). specialize (H' ltac:(apply in_elt)).
      Search In (_ ++ _ :: _). apply in_split in H'. fwd. 
      apply Permutation_app_inv in H1. constructor.
      + eapply IHn; eauto. rewrite length_app in *. simpl in *. lia.
      + eapply no_cycles_incl; [eassumption|]. Search Permutation In.
        cbv [incl]. intros. eapply Permutation_in. 2: eassumption.
        Search Permutation. apply Permutation_sym. apply perm_skip. assumption.
  Qed.

  Lemma dag'_consn n r p :
    no_cycles r (r :: p) ->
    dag' p ->
    dag' (repeat r n ++ p).
  Proof.
    intros. induction n.
    - assumption.
    - simpl. apply (dag'_cons nil); simpl; try assumption.
      eapply no_cycles_incl; [eassumption|]. apply incl_cons; auto with incl.
      apply incl_app; auto with incl. cbv [incl]. intros r' Hr'. Search In repeat.
      apply repeat_spec in Hr'. subst. simpl. auto.
  Qed.

  Lemma dag'_incl p1 p2 :
    incl p1 p2 ->
    dag' p2 ->
    dag' p1.
  Proof.
    intros H1 H2. revert p1 H1. induction H2; intros p0 H0.
    - apply incl_l_nil in H0. subst. constructor.
    - Search Permutation repeat. eassert (incl _ (r :: p1 ++ p2)) as H'.
      { eapply incl_tran; [eassumption|]. apply incl_app; auto with incl. }
      clear H0. Search Permutation repeat. apply Permutation_incl_cons_inv_r in H'.
      fwd. eapply dag'_permutation; [apply Permutation_sym; eassumption|].
      apply dag'_consn.
      + eauto using no_cycles_incl with incl.
      + apply IHdag'. assumption.
  Qed.

  Lemma dag'_app p1 p2 :
    Forall (fun r => no_cycles r p2) p1 ->
    dag' p1 ->
    dag' p2 ->
    dag' (p1 ++ p2).
  Proof.
    intros H1 H2 H3. induction H2.
    - assumption.
    - rewrite <- app_assoc. simpl. apply Forall_app in H1. fwd.
      rewrite Forall_app in IHdag'. specialize (IHdag' ltac:(auto)).
      rewrite <- app_assoc in IHdag'. constructor; [assumption|].
      rewrite app_assoc. Search (_ :: _ ++ _). rewrite app_comm_cons. apply no_cycles_app; assumption.
  Qed.
  
  Definition diff_rels (p1 p2 : list rule) :=
    forall r1 r2 c1 c2,
      In r1 p1 ->
      In r2 p2 ->
      In c1 r1.(rule_concls) ->
      In c2 r2.(rule_concls) ->
      c1.(fact_R) <> c2.(fact_R).

  Lemma diff_rels_app_r p p1 p2 :
    diff_rels p p1 ->
    diff_rels p p2 ->
    diff_rels p (p1 ++ p2).
  Proof.
    cbv [diff_rels]. intros H H0 r1 r2 c1 c2 H1 H2 H3 H4. apply in_app_iff in H2.
    destruct H2; eauto.
  Qed.

  Lemma diff_rels_Forall_r p1 p2 :
    Forall (fun r2 =>
              forall r1 c1 c2,
                In r1 p1 ->
                In c1 r1.(rule_concls) ->
                In c2 r2.(rule_concls) ->
                c1.(fact_R) <> c2.(fact_R)) p2 ->
    diff_rels p1 p2.
  Proof.
    intros H. rewrite Forall_forall in H. cbv [diff_rels]. eauto.
  Qed.

  Lemma no_cycles_spec r p f hyps :
    no_cycles r p ->
    Exists (fun r : rule => rule_impl r f hyps) p ->
    Forall (fun hyp => ~In (fst hyp) (map fact_R (rule_concls r))) hyps.
  Proof.
    intros H1 H2. cbv [no_cycles] in H1. rewrite Forall_forall in *.
    intros x Hx H'. rewrite in_map_iff in H'. fwd. specialize (H1 _ H'p1).
    rewrite Exists_exists in H2. rewrite Forall_forall in H1. fwd.
    specialize (H1 _ H2p0). cbv [not_appears_in_a_hyp] in H1. fwd.
    apply rule_impl_hyp_relname_in in H2p1. rewrite Forall_forall in H2p1.
    specialize (H2p1 _ Hx). destruct H2p1 as [H2p1|H2p1].
    - apply H1p0. rewrite in_map_iff in H2p1. fwd. rewrite H'p0. apply in_map_iff.
      eauto.
    - destruct (rule_agg x1) as [(?&?)|]; [|assumption]. rewrite <- H'p0 in H2p1. auto.
  Qed.           
  
  Lemma dag_terminates'' r p f :
    prog_impl_fact (r :: p) f ->
    ~In (fst f) (map fact_R r.(rule_concls)) ->
    no_cycles r (r :: p) ->
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
    no_cycles r (r :: p) ->
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

  Fixpoint subst_in_expr ctx e : option T :=
    match e with
    | var_expr v => map.get ctx v
    | fun_expr f args => option_coalesce (option_map (interp_fun f) (option_all (map (subst_in_expr ctx) args)))
    end.

  Hint Constructors interp_expr : core.

  Lemma subst_in_expr_sound ctx e v :
    subst_in_expr ctx e = Some v ->
    interp_expr ctx e v.
  Proof.
    revert v. induction e; simpl; intros; eauto.
    apply option_coalesce_Some, option_map_Some in H0. fwd.
    apply option_all_Forall2 in H0p0. econstructor; eauto.
    rewrite <- Forall2_map_l in H0p0. eapply Forall2_impl_strong; [|eassumption].
    simpl. intros. rewrite Forall_forall in H. eauto.
  Qed.

  Lemma subst_in_expr_complete ctx e v :
    interp_expr ctx e v ->
    subst_in_expr ctx e = Some v.
  Proof.
    revert v. induction e; invert 1; simpl; eauto.
    erewrite Forall2_option_all.
    2: { rewrite <- Forall2_map_l. eapply Forall2_impl_strong; [|eassumption].
         rewrite Forall_forall in H. eauto. }
    simpl. rewrite H5. reflexivity.
  Qed.

  Definition subst_in_fact ctx (f : fact) :=
    option_map (fun args' => (f.(fact_R), args'))
      (option_all (map (subst_in_expr ctx) f.(fact_args))).

  Lemma subst_in_fact_sound ctx f f' :
    subst_in_fact ctx f = Some f' ->
    interp_fact ctx f f'.
  Proof.
    cbv [subst_in_fact]. intros H. apply option_map_Some in H.
    fwd. apply option_all_Forall2 in Hp0. constructor.
    rewrite <- Forall2_map_l in Hp0. eapply Forall2_impl; [|eassumption].
    simpl. auto using subst_in_expr_sound.
  Qed.

  Lemma subst_in_fact_complete ctx f f' :
    interp_fact ctx f f' ->
    subst_in_fact ctx f = Some f'.
  Proof.
    intros H. invert H. cbv [subst_in_fact].
    erewrite Forall2_option_all; [reflexivity|].
    rewrite <- Forall2_map_l. eapply Forall2_impl; [|eassumption].
    auto using subst_in_expr_complete.
  Qed.

  Lemma subst_in_expr_mono ctx ctx' e v :
    map.extends ctx' ctx ->
    subst_in_expr ctx e = Some v ->
    subst_in_expr ctx' e = Some v.
  Proof.
    intros H. revert v. induction e; simpl; intros; eauto. rewrite Forall_forall in H0.
    apply option_coalesce_Some, option_map_Some in H1. fwd.
    apply option_all_Forall2 in H1p0. erewrite Forall2_option_all.
    2: { rewrite <- Forall2_map_l in *. eapply Forall2_impl_strong; [|eassumption].
         simpl. eauto. }
    simpl. rewrite H1p1. reflexivity.
  Qed.
  
  Lemma subst_expr_with_vars ctx ctx' e :
    Forall (fun v => map.get ctx v <> None) (vars_of_expr e) ->
    map.extends ctx' ctx ->
    subst_in_expr ctx e = subst_in_expr ctx' e.
  Proof.
    induction e; simpl; intros; invert_list_stuff.
    - destruct (map.get _ _) eqn:E; try congruence. symmetry. auto.
    - rewrite Forall_flat_map in H0. f_equal. f_equal. f_equal. apply map_ext_in.
      rewrite Forall_forall in *. eauto.
  Qed.

  Definition context_of_args (args : list expr) (args' : list T) :=
    concat (zip (fun arg arg' =>
                   match arg with
                   | var_expr v => [(v, arg')]
                   | _ => []
                   end) args args').

  Definition context_of_fact (f : fact) (f' : rel * list T) :=
    context_of_args f.(fact_args) (snd f').
  
  Definition context_of_hyps (hyps : list fact) (hyps' : list (rel * list T)) :=
    concat (zip context_of_fact hyps hyps').

  Definition agg_hyps'_len r hyps' :=
    match r.(rule_agg) with
    | None => O
    | Some (_, aexpr) =>
        match option_coalesce (option_map get_set (subst_in_expr (map.of_list (context_of_hyps r.(rule_hyps) hyps')) aexpr.(agg_s))) with
        | Some s => length s
        | None => O
        end
    end.

  Lemma bare_in_context_args ctx x args args' :
    In (var_expr x) args ->
    Forall2 (interp_expr ctx) args args' ->
    exists v, In (x, v) (context_of_args args args').
  Proof.
    intros H1 H2. cbv [context_of_args]. apply Forall2_forget_r_strong in H2.
    rewrite Forall_forall in H2. specialize (H2 _ H1). fwd.
    exists y. cbv [zip]. rewrite in_concat. eexists. rewrite in_map_iff. split.
    { eexists. split; [|eassumption]. reflexivity. }
    simpl. auto.
  Qed.
  
  Lemma bare_in_context_fact ctx x f f' :
    In (var_expr x) f.(fact_args) ->
    interp_fact ctx f f' ->
    exists v, In (x, v) (context_of_fact f f').
  Proof.
    intros H1 H2. cbv [context_of_fact]. invert H2.
    eapply bare_in_context_args; eassumption.
  Qed.

  Lemma bare_in_context_hyps ctx x hyps hyps' :
    In (var_expr x) (flat_map fact_args hyps) ->
    Forall2 (interp_fact ctx) hyps hyps' ->
    exists v, In (x, v) (context_of_hyps hyps hyps').
  Proof.
    intros H1 H2. apply in_flat_map in H1. fwd. cbv [context_of_hyps].
    apply Forall2_forget_r_strong in H2. rewrite Forall_forall in H2.
    specialize (H2 _ H1p0). fwd. eapply bare_in_context_fact in H2p1; eauto. fwd.
    eexists. rewrite in_concat. cbv [zip]. eexists. rewrite in_map_iff. split.
    { eexists. split; [|eassumption]. reflexivity. }
    eassumption.
  Qed.

  Lemma interp_args_context_right ctx args args' :
    Forall2 (interp_expr ctx) args args' ->
    Forall (fun '(x, v) => map.get ctx x = Some v) (context_of_args args args').
  Proof.
    intros H. apply Forall2_combine in H. rewrite Forall_forall in *.
    intros [x v] Hx. cbv [context_of_fact] in Hx. apply in_concat in Hx. fwd.
    cbv [zip] in Hxp0. apply in_map_iff in Hxp0. fwd. apply H in Hxp0p1.
    do 2 (destruct_one_match_hyp; simpl in Hxp1; try contradiction).
    destruct Hxp1; try contradiction. invert H0. invert Hxp0p1. assumption.
  Qed.  
  
  Lemma interp_fact_context_right ctx f f' :
    interp_fact ctx f f' ->
    Forall (fun '(x, v) => map.get ctx x = Some v) (context_of_fact f f').
  Proof.
    intros H. invert H. apply interp_args_context_right. assumption.
  Qed.

  Lemma interp_hyps_context_right ctx hyps hyps' :
    Forall2 (interp_fact ctx) hyps hyps' ->
    Forall (fun '(x, v) => map.get ctx x = Some v) (context_of_hyps hyps hyps').
  Proof.
    intros H. apply Forall2_combine in H. rewrite Forall_forall in *.
    intros x Hx. cbv [context_of_hyps] in *. rewrite in_concat in Hx.
    fwd. cbv [zip] in Hxp0. rewrite in_map_iff in Hxp0. fwd. destruct x1 as [v v'].
    apply H in Hxp0p1. apply interp_fact_context_right in Hxp0p1.
    rewrite Forall_forall in Hxp0p1. apply Hxp0p1 in Hxp1. assumption.
  Qed.

  Lemma interp_hyps_context_right_weak ctx hyps hyps' :
    Forall2 (interp_fact ctx) hyps hyps' ->
    map.extends ctx (map.of_list (context_of_hyps hyps hyps')).
  Proof.
    intros H. apply interp_hyps_context_right in H. cbv [map.extends].
    intros. apply of_list_Some_in in H0. rewrite Forall_forall in H.
    apply H in H0. assumption.
  Qed.
  
  Lemma interp_hyps_agree ctx hyps hyps' v :
    Forall2 (interp_fact ctx) hyps hyps' ->
    In (var_expr v) (flat_map fact_args hyps) ->
    agree_on ctx (map.of_list (context_of_hyps hyps hyps')) v.
  Proof.
    intros H1 H2.
    pose proof bare_in_context_hyps as H'.
    specialize (H' _ _ _ _ ltac:(eassumption) ltac:(eassumption)). fwd.
    apply in_fst in H'. apply in_of_list_Some_strong in H'. fwd.
    eapply interp_hyps_context_right_weak in H1; eauto.
    specialize (H1 _ _ H'p0). cbv [agree_on]. rewrite H1, H'p0. reflexivity.
  Qed.

  Lemma agg_hyps_determined r f hyps :
    good_rule r ->
    forall agg_hyps's,
      rule_impl' r f hyps agg_hyps's ->
      length agg_hyps's = agg_hyps'_len r hyps.
  Proof.
    intros Hgood agg_hyps' H. invert H. cbv [agg_hyps'_len].
    invert H0; [reflexivity|]. invert H4. simpl. erewrite subst_in_expr_complete.
    2: { eapply interp_expr_agree_on; eauto. apply Forall_forall.
         cbv [good_rule] in Hgood.
         destruct Hgood as (Hgood&_). intros x Hx. specialize (Hgood x).
         specialize' Hgood.
         { cbv [appears_in_rule]. right. right. eexists. eexists. split; [solve[eauto] |].
           cbv [appears_in_agg_expr]. simpl. left. assumption. }
         eapply bare_in_context_hyps in Hgood; eauto. fwd.
         apply in_fst in Hgood. apply in_of_list_Some in Hgood. fwd. cbv [agree_on].
         rewrite Hgood. apply interp_hyps_context_right_weak in H2.
         apply H2 in Hgood. rewrite Hgood. reflexivity. }
   simpl. rewrite H3. apply Forall3_length in H5. fwd. lia.
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
    erewrite Forall2_option_all. 1: reflexivity.
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
      apply subst_in_fact_complete.
      eapply interp_fact_agree_on; [eassumption|]. apply Forall_forall.
      intros v Hv. cbv [agree_on]. do 2 rewrite map.get_put_dec.
      destr (var_eqb res v).
      { reflexivity. }
      apply interp_hyps_agree; auto.
      apply Hgoodp0. cbv [appears_in_rule]. left. rewrite in_flat_map.
      split; eauto. intros ?. fwd. congruence.
  Qed.

  Definition eval_rule_q r concl_ins hyps' agg_hyps's :=
    let ctx := map.putmany (map.of_list (context_of_args (flat_map fact_ins r.(rule_concls)) concl_ins)) (map.of_list (context_of_hyps r.(rule_hyps) hyps')) in
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

  Lemma eval_rule_q_complete R args r hyps' agg_hyps's :
    goodish_rule r ->
    rule_impl' r (R, args) hyps' agg_hyps's ->
    eval_rule_q r (firstn (ins R) args) hyps' agg_hyps's = [(R, args)].
  Proof.
    intros Hgood Himpl. cbv [eval_rule_q]. cbv [goodish_rule] in Hgood. fwd.
    invert Himpl. rewrite Hgoodp0 in *. invert_list_stuff. simpl. rewrite app_nil_r.
    invert H.
    - rewrite <- H4 in *. fwd. erewrite subst_in_fact_complete. 1: reflexivity.
      eapply interp_fact_agree_on; [eassumption|].
      apply Forall_forall. intros v H. cbv [agree_on]. invert H3.
      rewrite map.get_putmany_dec. destruct_one_match.
      + apply of_list_Some_in in E. apply interp_hyps_context_right in H1.
        rewrite Forall_forall in H1. apply H1 in E. assumption.
      + apply get_of_list_None_bw in E. specialize (Hgoodp3 v). specialize' Hgoodp3.
        { cbv [appears_in_rule]. left. rewrite <- H4.
          split; [intros ?; fwd; congruence|]. rewrite Hgoodp0. simpl. rewrite app_nil_r.
          assumption. }
        destruct Hgoodp3 as [H'|H'].
        -- eapply bare_in_context_hyps in H'; [|eassumption]. fwd.
           apply in_fst in H'. exfalso. auto.
        -- eapply Forall2_firstn in H5. pose proof H5 as H5'.
           apply interp_args_context_right in H5. rewrite Forall_forall in H5.
           cbv [fact_ins] in Hgoodp1. eapply bare_in_context_args in H5'.
           2: { rewrite Hgoodp1. apply in_map. eassumption. }
           fwd. apply in_fst in H5'. apply in_of_list_Some_strong in H5'.
           fwd. apply H5 in H5'p1. cbv [fact_ins]. rewrite H5'p0, H5'p1. reflexivity.
    - rewrite <- H0 in *. fwd. erewrite eval_aexpr_complete; try assumption.
      2: { eapply interp_agg_expr_agree_on; [eassumption|]. intros v Hv.
           specialize (Hgoodp3 v). specialize' Hgoodp3.
           { cbv [appears_in_rule]. right. right. eauto. }
           cbv [agree_on]. rewrite map.get_putmany_dec. destruct_one_match.
           + apply of_list_Some_in in E. apply interp_hyps_context_right in H1.
             rewrite Forall_forall in H1. apply H1 in E. assumption.
           + apply get_of_list_None_bw in E.
             destruct Hgoodp3 as [H'|H'].
             -- eapply bare_in_context_hyps in H'; [|eassumption]. fwd.
                apply in_fst in H'. exfalso. auto.
             -- invert H3. eapply Forall2_firstn in H5. pose proof H5 as H5'.
                apply interp_args_context_right in H5. rewrite Forall_forall in H5.
                cbv [fact_ins] in Hgoodp1. eapply bare_in_context_args in H5'.
                2: { rewrite Hgoodp1. apply in_map. eassumption. }
                fwd. apply in_fst in H5'. apply in_of_list_Some_strong in H5'.
                fwd. apply H5 in H5'p1. cbv [fact_ins]. rewrite H5'p0.
                rewrite map.get_put_diff in H5'p1; auto. intros ?. subst. eauto. }
      erewrite subst_in_fact_complete. 1: reflexivity.
      eapply interp_fact_agree_on; [eassumption|].
      apply Forall_forall. intros v H. cbv [agree_on]. invert H3.
      do 2 rewrite map.get_put_dec. destruct_one_match; try reflexivity.
      rewrite map.get_putmany_dec. destruct_one_match.
      + apply of_list_Some_in in E0. apply interp_hyps_context_right in H1.
        rewrite Forall_forall in H1. apply H1 in E0. assumption.
      + apply get_of_list_None_bw in E0. specialize (Hgoodp3 v). specialize' Hgoodp3.
        { cbv [appears_in_rule]. left. rewrite <- H0.
          split; [intros ?; fwd; congruence|]. rewrite Hgoodp0. simpl. rewrite app_nil_r.
          assumption. }
        destruct Hgoodp3 as [H'|H'].
        -- eapply bare_in_context_hyps in H'; [|eassumption]. fwd.
           apply in_fst in H'. exfalso. auto.
        -- eapply Forall2_firstn in H6. pose proof H6 as H6'.
           apply interp_args_context_right in H6. rewrite Forall_forall in H6.
           cbv [fact_ins] in Hgoodp1. eapply bare_in_context_args in H6'.
           2: { rewrite Hgoodp1. apply in_map. eassumption. }
           fwd. apply in_fst in H6'. apply in_of_list_Some_strong in H6'.
           fwd. apply H6 in H6'p1. cbv [fact_ins]. rewrite H6'p0.
           rewrite map.get_put_diff in H6'p1; auto.
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
