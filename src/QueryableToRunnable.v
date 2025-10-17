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

From Datalog Require Import Datalog Map Tactics Fp List Interpreter Dag.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List.

Import ListNotations.

Section relmap.
  Context {rel1 rel2 var fn aggregator T : Type}.
  Context `{sig : signature fn aggregator T}.
  Context (g : rel1 -> rel2).
  Context {context : map.map var T} {context_ok : map.ok context}.
  Context {var_eqb : var -> var -> bool} {var_eqb_spec :  forall x0 y0 : var, BoolSpec (x0 = y0) (x0 <> y0) (var_eqb x0 y0)}.

  Definition fact_relmap (f : fact rel1 var fn) :=
    {| fact_R := g f.(fact_R); fact_args := f.(fact_args) |}.

  Definition fact'_relmap (f' : rel1 * list T) :=
    let (R, args) := f' in (g R, args).

  Definition agg_expr_relmap (ae : agg_expr rel1 var fn aggregator) :=
    {| agg_agg := ae.(agg_agg); agg_i := ae.(agg_i); agg_vs := ae.(agg_vs);
                                     agg_s := ae.(agg_s);
                                     agg_body := ae.(agg_body);
                                     agg_hyps := map fact_relmap ae.(agg_hyps) |}.

  Lemma vars_of_fact_relmap f :
    vars_of_fact (fact_relmap f) = vars_of_fact f.
  Proof. reflexivity. Qed.

  Lemma good_agg_expr_relmap ae :
    good_agg_expr ae ->
    good_agg_expr (agg_expr_relmap ae).
  Proof.
    cbv [good_agg_expr]. intros H. eapply Forall_impl; [|eassumption]. simpl.
    intros. rewrite flat_map_map. simpl. apply H0.
  Qed.

  Lemma appears_in_agg_expr_with_bool v ae :
    appears_in_agg_expr v (agg_expr_relmap ae) ->
    appears_in_agg_expr v ae.
  Proof.
    destruct ae. cbv [agg_expr_relmap appears_in_agg_expr]. simpl.
    rewrite flat_map_map. erewrite flat_map_ext.
    2: { intros x. rewrite vars_of_fact_relmap. reflexivity. }
    auto.
  Qed.

  Lemma interp_fact_relmap ctx f f' :
    interp_fact ctx f f' ->
    interp_fact ctx (fact_relmap f) (fact'_relmap f').
  Proof. intros H. invert H. constructor. simpl. assumption. Qed.

  Hint Resolve interp_fact_relmap : core.
  Hint Constructors Forall3 : core.
  
  Lemma interp_agg_expr_relmap ctx (aexpr : agg_expr rel1 var fn aggregator) res' agg_hyps' :
    interp_agg_expr ctx aexpr res' agg_hyps' ->
    interp_agg_expr ctx (agg_expr_relmap aexpr) res' (map (map fact'_relmap) agg_hyps').
  Proof.
    intros H. invert H. cbv [agg_expr_relmap]. simpl.
    econstructor; eauto.
    erewrite <- Forall3_map3. eapply Forall3_impl; [|eassumption].
    simpl. intros. fwd. do 2 eexists. intuition eauto.
    rewrite <- Forall2_map_l. erewrite <- Forall2_map_r.
    eapply Forall2_impl; [|eassumption]. intros. apply interp_fact_relmap.
    eassumption.
  Qed.

  Lemma interp_facts_relmap hyps hyps' ctx :
    Forall2 (interp_fact ctx) hyps hyps' ->
    map fact_R hyps = map fst hyps' /\
      Forall2 (interp_fact ctx) (map fact_relmap hyps) (map fact'_relmap hyps').
  Proof. induction 1; simpl; fwd; intuition eauto. invert H. simpl. f_equal; auto. Qed.  
End relmap.

Section Transform.
  Context {rel var fn aggregator T : Type}.
  Context `{sig : signature fn aggregator T} `{query_sig : query_signature rel}.
  Context {context : map.map var T} {context_ok : map.ok context}.
  Context {var_eqb : var -> var -> bool} {var_eqb_spec :  forall x0 y0 : var, BoolSpec (x0 = y0) (x0 <> y0) (var_eqb x0 y0)}. 

  Local Notation rule' := (rule (rel*bool) var fn aggregator).
  Local Notation rule := (rule rel var fn aggregator).
  Local Notation fact' := (@fact (rel*bool) var fn).
  Local Notation fact := (@fact rel var fn).
  Local Notation agg_expr' := (agg_expr (rel * bool) var fn aggregator).
  Local Notation agg_expr := (agg_expr rel var fn aggregator).
  
  Notation plus_false := (fun x => (x, false)).
  Notation plus_true := (fun x => (x, true)).

  Definition agree (p : list rule) (r1 r2 : rule) :=
    forall R args1 args2 hyps1 hyps2,
      rule_impl r1 (R, args1) hyps1 ->
      rule_impl r2 (R, args2) hyps2 ->
      Forall (prog_impl_fact p) hyps1 ->
      Forall (prog_impl_fact p) hyps2 ->
      firstn (ins R) args1 = firstn (ins R) args2 ->
      args1 = args2.

  Lemma agree_weaken p1 p2 r1 r2 :
    agree p1 r1 r2 ->
    incl p2 p1 ->
    agree p2 r1 r2.
  Proof. cbv [agree]. eauto 6 using Forall_impl, prog_impl_fact_subset. Qed.    

  Definition pairs_satisfy {X : Type} (P : X -> X -> Prop) (l : list X) :=
    forall x1 x2, In x1 l -> In x2 l -> x1 = x2 \/ P x1 x2.

  Definition disjoint_pairs_satisfy : nat. Admitted.
  
  Lemma pairs_satisfy_weaken {X : Type} P1 P2 (l1 l2 : list X) :
    pairs_satisfy P1 l1 ->
    (forall x y, P1 x y -> P2 x y) ->
    incl l2 l1 ->
    pairs_satisfy P2 l2.
  Proof.
    cbv [pairs_satisfy]. intros H1 H2 H3 x y Hx Hy.
    specialize (H1 x y ltac:(eauto) ltac:(eauto)). destruct H1; auto.
  Qed.

  Definition functional (p : list rule) :=
    forall args1 args2 R,
      prog_impl_fact p (R, args1) ->
      prog_impl_fact p (R, args2) ->
      firstn (ins R) args1 = firstn (ins R) args2 ->
      args1 = args2.
  
  Hint Resolve pairs_satisfy_weaken agree_weaken : core.

  Lemma hyp_ins_det' (r : rule) R (args : list T) hyps ahyps :
    goodish_rule r ->
    rule_impl' r (R, args) hyps ahyps ->
    exists concl,
      r.(rule_concls) = [concl] /\
        let ctx := map.of_list (context_of_args (firstn (ins R) concl.(fact_args)) (firstn (ins R) args)) in
        Forall2 (fun f '(R, hyp_args) =>
                   f.(fact_R) = R /\ Forall2 (interp_expr ctx) (firstn (ins R) f.(fact_args)) (firstn (ins R) hyp_args))
          r.(rule_hyps) hyps.
  Proof.
    intros Hgood H. invert H. cbv [goodish_rule] in Hgood. fwd. eexists.
    split; [eassumption|]. simpl.
    rewrite Hgoodp0 in *. invert_list_stuff.
    eapply Forall2_impl_strong; [|eassumption].
    intros f (Ry&argsy) Hfy Hf Hy. invert Hfy. split; [reflexivity|].
    eapply Forall2_impl_strong. 2: apply Forall2_firstn; eassumption.
    intros x y Hx Hy0 Hxy. eapply interp_expr_agree_on; [eassumption|].
    rewrite Forall_forall. intros v Hv. assert (In v invars).
    { apply Hgoodp4. apply in_flat_map. eexists. split; eauto.
      apply in_flat_map. eauto. }
    invert H3. eapply Forall2_firstn in H6. pose proof H6 as H6'.
    eapply bare_in_context_args in H6.
    2: { cbv [fact_ins] in Hgoodp1. rewrite Hgoodp1. apply in_map. eassumption. }
    apply interp_args_context_right in H6'.
    fwd. cbv [agree_on]. apply in_fst in H6. apply in_of_list_Some_strong in H6.
    fwd. rewrite H6p0. rewrite Forall_forall in H6'. apply H6' in H6p1.
    move H0 at bottom. invert H0; [assumption|]. rewrite <- H1 in *.
    rewrite map.get_put_diff in H6p1; auto. intros ?. subst. eauto.
  Qed.

  Lemma hyp_ins_det (r : rule) R args1 args2 hyps1 hyps2 ahyps1 ahyps2 :
    goodish_rule r ->
    rule_impl' r (R, args1) hyps1 ahyps1 ->
    rule_impl' r (R, args2) hyps2 ahyps2 ->
    firstn (ins R) args1 = firstn (ins R) args2 ->
    Forall2 (fun '(R1, hyp1) '(R2, hyp2) =>
               R1 = R2 /\ firstn (ins R1) hyp1 = firstn (ins R2) hyp2)
      hyps1 hyps2.
  Proof.
    intros Hgood H1 H2 Hsame. eapply hyp_ins_det' in H1, H2; try assumption.
    fwd. rewrite H1p0 in *. invert H2p0. simpl in *.
    apply Forall2_flip in H1p1. eapply Forall2_Forall2_Forall3 in H2p1; [|exact H1p1].
    apply Forall3_ignore2 in H2p1. eapply Forall2_impl; [|eassumption].
    simpl. intros [Ra argsa] [Rb argsb] H. fwd. split; [reflexivity|].
    apply Forall2_flip in Hp1p1. eapply Forall2_Forall2_Forall3 in Hp3; [|exact Hp1p1].
    apply Forall3_ignore2 in Hp3. apply Forall2_eq_eq.
    eapply Forall2_impl; [|eassumption]. simpl. intros a b Hab. fwd.
    rewrite Hsame in *. eapply interp_expr_det; eassumption.
  Qed.

  Lemma ahyp_ins_det'1 (r : rule) R (args : list T) hyps ahypss :
    goodish_rule r ->
    rule_impl' r (R, args) hyps ahypss ->
    exists concl,
      r.(rule_concls) = [concl] /\
        match r.(rule_agg) with
        | None => ahypss = []
        | Some (_, aexpr) =>
            let ctx := map.of_list (context_of_args (firstn (ins R) concl.(fact_args)) (firstn (ins R) args)) in
            Forall (fun ahyps =>
                      Forall2 (fun f '(R, hyp_args) =>
                                 f.(fact_R) = R /\ Forall2 (interp_expr ctx) (firstn (ins R) f.(fact_args)) (firstn (ins R) hyp_args))
                        aexpr.(agg_hyps) ahyps) ahypss
        end.
  Proof.
    intros Hgood H. invert H. cbv [goodish_rule] in Hgood. fwd. eexists.
    split; [eassumption|]. simpl.
    rewrite Hgoodp0 in *. invert_list_stuff. invert H0. 1: reflexivity.
    rewrite <- H in *. invert H4. simpl in *. apply Forall3_ignore12 in H5.
    rewrite Forall_forall in *. intros ahyps Hahyps. specialize (H5 _ Hahyps).
    fwd. eapply Forall2_impl_strong; [|eassumption]. intros f [R' args'] Hff' Hf Hf'.
    invert Hff'. split; [reflexivity|]. eapply Forall2_impl_strong.
    2: apply Forall2_firstn; eassumption.
    intros e e' Hee' He He'. eapply interp_expr_agree_on; [eassumption|].
    rewrite Forall_forall. intros v Hv. move H3 at bottom. invert H3.
    eapply Forall2_firstn in H7. pose proof H7 as H7'.
    specialize (Hgoodp5p1 v). specialize' Hgoodp5p1.
    { apply in_flat_map. eexists. split; eauto. apply in_flat_map. eauto. }
    fwd. eapply bare_in_context_args in H7.
    2: { cbv [fact_ins] in Hgoodp1. rewrite Hgoodp1. apply in_map. eassumption. }
    fwd. apply interp_args_context_right in H7'. cbv [agree_on].
    apply in_fst in H7. apply in_of_list_Some_strong in H7. fwd.
    rewrite H7p0. clear H7p0. rewrite Forall_forall in H7'. apply H7' in H7p1.
    rewrite map.get_putmany_left.
    2: { erewrite map.get_of_list_zip by eassumption.
         apply zipped_lookup_notin_None. assumption. }
    rewrite map.get_put_diff by assumption.
    rewrite map.get_put_diff in H7p1.
    2: { intros H'. subst. eauto. }
    assumption.
  Qed.

  Lemma ahyp_ins_det'2 (r : rule) R (args : list T) hyps ahypss :
    goodish_rule r ->
    rule_impl' r (R, args) hyps ahypss ->
    exists concl,
      r.(rule_concls) = [concl] /\
        match r.(rule_agg) with
        | None => ahypss = []
        | Some (_, aexpr) =>
            let ctx := map.putmany (map.of_list (context_of_args (firstn (ins R) concl.(fact_args)) (firstn (ins R) args))) (map.of_list (context_of_hyps r.(rule_hyps) hyps)) in
            option_map (@length _)(*????*) (option_coalesce (option_map get_set (subst_in_expr ctx aexpr.(agg_s)))) = Some (length ahypss) 
        end.
  Proof.
    intros Hgood H. invert H. cbv [goodish_rule] in Hgood. fwd. eexists.
    split; [eassumption|]. simpl.
    rewrite Hgoodp0 in *. invert_list_stuff. invert H0. 1: reflexivity.
    rewrite <- H in *. invert H4. simpl in *. erewrite subst_in_expr_complete.
    { simpl. rewrite H1. simpl. apply Forall3_length in H5. fwd. f_equal. lia. }
    eapply interp_expr_agree_on; [eassumption|]. clear H5. rewrite Forall_forall. fwd.
    intros v Hv. cbv [agree_on]. invert H3.
    specialize (Hgoodp3 v). specialize' Hgoodp3.
    { cbv [appears_in_rule appears_in_agg_expr]. rewrite <- H. eauto 7. }
    move Hgoodp3 at bottom. rewrite map.get_putmany_dec. destruct_one_match.
    - apply of_list_Some_in in E. apply interp_hyps_context_right in H2.
      rewrite Forall_forall in H2. apply H2 in E. exact E.
    - apply get_of_list_None_bw in E. destruct Hgoodp3 as [H'|H'].
      { exfalso. apply E. clear E. eapply bare_in_context_hyps in H'.
        2: { eassumption. }
        fwd. eapply in_fst. eassumption. }
      clear H2. eapply Forall2_firstn in H6. pose proof H6 as H6'.
      eapply bare_in_context_args in H6.
      2: { cbv [fact_ins] in Hgoodp1. rewrite Hgoodp1. apply in_map. eassumption. }
      fwd. apply interp_args_context_right in H6'. rewrite Forall_forall in H6'.
      apply in_fst in H6. apply in_of_list_Some_strong in H6. fwd. rewrite H6p0.
      apply H6' in H6p1. rewrite map.get_put_diff in H6p1; auto. intros ?. subst. eauto.
  Qed.
  
  Lemma ahyp_ins_det (r : rule) R args1 args2 hyps ahypss1 ahypss2 :
    goodish_rule r ->
    rule_impl' r (R, args1) hyps ahypss1 ->
    rule_impl' r (R, args2) hyps ahypss2 ->
    firstn (ins R) args1 = firstn (ins R) args2 ->
    Forall2 (Forall2 (fun '(R1, hyp1) '(R2, hyp2) =>
                        R1 = R2 /\ firstn (ins R1) hyp1 = firstn (ins R2) hyp2))
      ahypss1 ahypss2.
  Proof.
    intros Hgood H1 H2 Hsame. pose proof H1 as H1'. pose proof H2 as H2'.
    apply ahyp_ins_det'1 in H1, H2; try assumption.
    apply ahyp_ins_det'2 in H1', H2'; try assumption.
    fwd. rewrite H1p0 in *. invert_list_stuff. destruct r.(rule_agg) as [(?&?)|]; simpl in *.
    2: subst; constructor. invert_list_stuff. rewrite Hsame in *.
    rewrite H2'p1p0p0 in *. invert_list_stuff. rewrite H2'p1p0p1 in *.
    invert_list_stuff. eapply Forall2_impl_strong.
    2: { apply Forall2_true. lia. }
    intros ahyps1 ahyps2 _ H1 H2. rewrite Forall_forall in *. apply H1p1 in H1.
    apply H2p1 in H2. apply Forall2_flip in H1.
    eapply Forall2_Forall2_Forall3 in H2; [|exact H1]. apply Forall3_ignore2 in H2.
    eapply Forall2_impl; [|eassumption]. simpl. intros [? ?] [? ?] H. fwd.
    split; [reflexivity|]. apply Forall2_eq_eq. apply Forall2_flip in Hp1p1.
    eapply Forall2_Forall2_Forall3 in Hp3; [|exact Hp1p1]. apply Forall3_ignore2 in Hp3.
    eapply Forall2_impl; [|eassumption]. simpl. intros. fwd.
    eapply interp_expr_det; eassumption.
  Qed.

  Lemma agree_functional p :
    dag (rel_graph p) ->
    Forall goodish_rule p ->
    pairs_satisfy (agree p) p ->
    functional p.
  Proof.
    intros H1 H2 H3. cbv [functional]. intros args1 args2 R. revert args1 args2.
    apply dag_wf in H1. specialize (H1 R). induction H1. clear H.
    intros args1 args2 Hargs1 Hargs2 Hins.
    invert Hargs1. invert Hargs2.
    pose proof H as Hrel1. pose proof H4 as Hrel2.
    apply rel_graph_spec in Hrel1, Hrel2. 
    cbv [pairs_satisfy] in H3. rewrite Exists_exists in *. fwd.
    match goal with
    | H1: _ , H2: _ |- _ => specialize (H3 _ _ H1 H2)
    end.
    destruct H3; [|solve[eauto]]. subst. cbv [rule_impl] in *. fwd.
    pose proof hyp_ins_det as H'. epose proof (H' _ _ args1 args2) as H'.
    rewrite Forall_forall in *.
    specialize (H' _ _ _ _ ltac:(eauto) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
    assert (hyps'0 = hyps').
    { apply Forall2_eq_eq. eapply Forall2_impl_strong; [|eassumption].
      simpl. intros [R1' args1'] [R2' args2'] H12 H1' H2'. fwd. f_equal.
      eapply H0; eauto.
      - move Hrel1 at bottom. eapply (Hrel1 (_, _)). apply in_app_iff. eauto.
      - eapply H1. apply in_app_iff. eauto.
      - eapply H5. apply in_app_iff. eauto. }
    subst. clear H'.
    pose proof ahyp_ins_det as H'. epose proof (H' _ _ args1 args2) as H'.
    specialize (H' _ _ _ ltac:(eauto) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
    assert (agg_hyps's0 = agg_hyps's).
    { apply Forall2_eq_eq. eapply Forall2_impl_strong; [|eassumption].
      simpl. intros xs ys Hxsys Hxs Hys. apply Forall2_eq_eq.
      eapply Forall2_impl_strong; [|eassumption]. simpl.
      intros [R1' args1'] [R2' args2'] H12 H1' H2'. fwd. f_equal.
      eapply H0; eauto.
      - move Hrel1 at bottom. eapply (Hrel1 (_, _)). apply in_app_iff. rewrite in_concat. eauto.
      - eapply H1. apply in_app_iff. rewrite in_concat. eauto.
      - eapply H5. apply in_app_iff. rewrite in_concat. eauto. }
    subst. clear H'.
    apply eval_rule_q_complete in Hp1p1, H4p1p1; auto.
    rewrite Hins in *. rewrite Hp1p1 in H4p1p1. invert_list_stuff.
    reflexivity.
  Qed.      

  (*if we get a message saying concls of r need to be computed, then send out messages
    saying premises of r need to be computed*)
  (*note: this is nonsensical if length r.(rule_concls) > 1*)
  Definition request_hyps (r : rule) : rule' :=
    {| rule_agg := None;
      rule_hyps := map (fact_relmap plus_false) (map with_only_ins r.(rule_concls));
      rule_concls := map (fact_relmap plus_false) (map with_only_ins (r.(rule_hyps) ++ rule_agg_hyps r))
    |}.

  (*add a hypothesis saying that the conclusion is something we need to compute*)
  (*note: this is fairly nonsensical (not semantically equivalent) if length r.(rule_concls) > 1*)
  Definition add_hyp (r : rule) : rule' :=
    {| rule_agg := option_map (fun '(x, y) => (x, agg_expr_relmap plus_true y)) r.(rule_agg);
      rule_hyps := map (fact_relmap plus_false) (map with_only_ins r.(rule_concls)) ++
                     map (fact_relmap plus_true) r.(rule_hyps);
      rule_concls := map (fact_relmap plus_true) r.(rule_concls) |}.

  (*semanticallly equivalent if each rule has concl length at most 1*)
  Definition make_good (p : list rule) : list rule' :=
    map request_hyps p ++ map add_hyp p.

  Lemma incl_fact_ins (f : fact) :
    incl (fact_ins f) (fact_args f).
  Proof. apply incl_firstn. Qed.

  Lemma appears_with_only_ins v (f : fact) :
    In v (vars_of_fact (with_only_ins f)) ->
    In v (vars_of_fact f).
  Proof.
    intros H. cbv [vars_of_fact] in *. simpl in *. cbv [fact_ins] in H.
    rewrite in_flat_map in *. fwd. eauto using In_firstn_to_In.
  Qed.

  Lemma barely_appears_with_only_ins v (f : fact) :
    In (var_expr v) (with_only_ins f).(fact_args) ->
    In (var_expr v) f.(fact_args).
  Proof.
    intros H. simpl in *. cbv [fact_ins] in H.
    apply In_firstn_to_In in H. assumption.
  Qed.

  Hint Resolve appears_with_only_ins barely_appears_with_only_ins vars_of_fact_relmap appears_in_agg_expr_with_bool good_agg_expr_relmap : core.

  Hint Resolve incl_fact_ins : core.

  Hint Extern 3 => progress simpl : core.
    
  Lemma appears_in_rule_request_hyps v r :
    goodish_rule r ->
    appears_in_rule v (request_hyps r) ->
    appears_in_rule v r.
  Proof.
    clear. intros Hgood H. cbv [goodish_rule] in Hgood. fwd.
    cbv [appears_in_rule] in *. simpl in *. rewrite Hgoodp0 in *.
    destruct H as [H| [H|H]]; fwd.
    - rewrite 2 flat_map_map in Hp1. erewrite flat_map_ext in Hp1.
      2: intros; apply vars_of_fact_relmap. rewrite flat_map_app, in_app_iff in Hp1.
      destruct Hp1 as [Hp1|Hp1].
      + right. left. cbv [vars_of_fact] in *. simpl in *.
        eapply incl_flat_map_strong; eauto; eauto with incl.
      + right. right. cbv [rule_agg_hyps] in Hp1.
        destruct (rule_agg r) as [(?&aexpr)|]; fwd. 2: simpl in Hp1; contradiction.
        do 2 eexists. split; [reflexivity|]. cbv [appears_in_agg_expr]. right. split.
        { rewrite flat_map_flat_map in Hgoodp5p1. apply Hgoodp5p1 in Hp1. fwd. simpl.
          intuition auto. }
        right. eapply incl_flat_map_strong; eauto; eauto with incl. simpl. cbv [incl].
        eauto using appears_with_only_ins.
    - left. split.
      2: { simpl in *. rewrite app_nil_r in *. rewrite vars_of_fact_relmap in H. eauto. }
      enough (In v invars).
      { intros H'. fwd. apply Hgoodp2. eauto. }
      clear -H Hgoodp1. simpl in H. rewrite app_nil_r in H.
      rewrite vars_of_fact_relmap in H. cbv [with_only_ins] in H.
      rewrite Hgoodp1 in H. cbv [vars_of_fact] in H. simpl in H.
      rewrite flat_map_map in H. simpl in H. rewrite <- map_is_flat_map, map_id in H.
      assumption.
    - congruence.
  Qed.      

  
  Lemma request_hyps_good r :
    goodish_rule r ->
    good_rule (request_hyps r).
  Proof.
    intros H. cbv [goodish_rule] in H. fwd. split; [|constructor].
    intros v Hv. simpl. rewrite Hp0. simpl. rewrite app_nil_r.
    rewrite Hp1. apply in_map. destruct Hv as [Hv| [Hv|Hv]]; fwd; simpl in *.
    - cbv [vars_of_fact] in Hvp1. do 2 rewrite flat_map_map in Hvp1.
      simpl in Hvp1. rewrite flat_map_app in Hvp1.
      rewrite in_app_iff in Hvp1. destruct Hvp1.
      { apply Hp4. rewrite flat_map_flat_map. assumption. }
      cbv [rule_agg_hyps] in H. destruct (rule_agg r) as [(?&?)|]; fwd.
      + rewrite flat_map_flat_map in Hp5p1. apply Hp5p1 in H. fwd. auto.
      + simpl in H. contradiction.
    - rewrite Hp0 in Hv. simpl in Hv. rewrite app_nil_r, vars_of_fact_relmap in Hv.
      cbv [with_only_ins] in Hv. rewrite Hp1 in Hv. cbv [vars_of_fact] in Hv.
      simpl in Hv. rewrite flat_map_map in Hv. simpl in Hv.
      rewrite <- map_is_flat_map, map_id in Hv. assumption.
    - congruence.
  Qed.

  Lemma appears_in_rule_add_hyp v r :
    goodish_rule r ->
    appears_in_rule v (add_hyp r) ->
    appears_in_rule v r.
  Proof.
    destruct r; cbv [appears_in_rule add_hyp]; simpl.
    intros Hgood. cbv [goodish_rule] in Hgood. simpl in Hgood. fwd.
    cbv [appears_in_rule] in *. simpl in *. intros [Hv| [Hv|Hv]]; fwd.
    - left. split; eauto. intros H'. apply Hvp0.
      fwd. simpl. eauto.
    - rewrite flat_map_map in Hv. rewrite vars_of_fact_relmap in Hv.
      erewrite flat_map_ext in Hv. 2: intros; apply vars_of_fact_relmap.
      apply in_app_iff in Hv. rewrite app_nil_r. destruct Hv as [Hv|Hv]; eauto.
      left. split; eauto. cbv [with_only_ins vars_of_fact] in Hv.
      rewrite Hgoodp1 in Hv. simpl in Hv. rewrite flat_map_map in Hv. simpl in Hv.
      rewrite <- map_is_flat_map, map_id in Hv. intros ?. fwd. eauto.
    - invert_list_stuff. eauto 7.
  Qed.
  
  Lemma add_hyp_good r :
    goodish_rule r ->
    good_rule (add_hyp r).
  Proof.
    intros HH. pose proof HH as (Hgood0&H). fwd. split.
    - intros v Hv. simpl. rewrite Hp0. simpl.
      apply appears_in_rule_add_hyp in Hv; [|assumption].
      apply Hp3 in Hv. rewrite flat_map_map. simpl. apply in_app_iff.
      destruct Hv as [Hv|Hv]; auto. left. rewrite Hp1. apply in_map; auto.
    - simpl. destruct (rule_agg r) as [(?&?)|]; simpl; fwd; auto.
  Qed.

  Hint Resolve interp_fact_relmap : core.

  Hint Extern 1 => unfold fact'_relmap; match goal with
                  | |- context[let '(_, _) := ?x in _] => destruct x
                  end : core.

  Hint Resolve interp_agg_expr_relmap : core.

  Lemma rule_impl_add_hyp R r args' hyps' :
    goodish_rule r ->
    rule_impl r (R, args') hyps' ->
    rule_impl (add_hyp r) ((R, true), args')
      (((R, false), firstn (ins R) args') :: map (fact'_relmap plus_true) hyps').
  Proof.
    intros Hgood H. cbv [goodish_rule] in Hgood. fwd.
    cbv [rule_impl] in *. fwd. eexists (_ :: _), _. split.
    { simpl. f_equal. rewrite map_app. rewrite concat_map. (*what a goofy name*)
      reflexivity. }
    cbv [add_hyp]. invert Hp1.
    (*TODO I don't completely understand why i have to do this*)
    eapply mk_rule_impl' with (ctx := ctx) (ctx' := ctx'); simpl.
    { invert H; simpl; constructor. auto. }
    { apply Exists_map. eapply Exists_impl; [|eassumption]. simpl. intros.
      eapply interp_fact_relmap in H2. Fail eassumption. Fail apply H2. exact H2. }
    rewrite Hgoodp0. simpl. constructor.
    2: { rewrite <- Forall2_map_l, <- Forall2_map_r. eauto using Forall2_impl. }
    cbv [with_only_ins]. rewrite Hgoodp1. rewrite Hgoodp0 in H0. invert_list_stuff.
    cbv [fact_relmap]. simpl. invert H3. constructor. simpl.
    cbv [fact_ins] in Hgoodp1. revert H4. eassert (fact_args concl = _) as ->.
    { erewrite <- (firstn_skipn _ (fact_args _)). rewrite Hgoodp1. reflexivity. }
    intros H3.  apply Forall2_app_inv_l in H3. fwd. eassert (firstn _ _ = _) as ->.
    2: { rewrite <- Forall2_map_l in *. eapply Forall2_impl_strong; [|eassumption].
         simpl. intros. invert H; [assumption|]. invert H0. constructor.
         rewrite map.get_put_diff in H5; auto. intros ?. subst. eauto. }
    apply Forall2_length in H3p0, H3p1.
    eassert (H': forall x y, x = y -> length x = length y) by (intros; subst; reflexivity).
    apply H' in Hgoodp1. rewrite length_firstn in *. rewrite length_map in *.
    rewrite length_skipn in *. rewrite <- Hgoodp1 in H3p0.
    assert (length l1' <= ins (fact_R concl)) by lia.
    assert (H'': length l1' = ins (fact_R concl) \/ length l2' = 0) by lia.
    destruct H'' as [H''|H''].
    - rewrite firstn_app_l by auto. reflexivity.
    - destruct l2'; [|discriminate H'']. rewrite app_nil_r.
      apply firstn_all2. lia.
  Qed.

  Definition f (wanted : _ * ((rel * bool) * list T) -> Prop)
    (S : (rel * list T -> Prop) * (rel * list T) -> Prop)
    (Px : ((rel * bool) * list T -> Prop) * ((rel * bool) * list T)) :=
    let '(P, x) := Px in
    let '((R, b), args) := x in
    if b then S (fun '(R, args) => P ((R, true), args), (R, args)) else
      wanted (P, ((R, false), args)).

  Definition g (S' : ((rel * bool) * list T -> Prop) * ((rel * bool) * list T) -> Prop)
    (Px : ((rel * list T) -> Prop) * (rel * list T)) :=
    let '(P, x) := Px in
    let '(R, args) := x in
    S' (fun '((R', b'), args') => match b' with
                               | true => P (R', args')
                               | false => (R', args') = (R, firstn (ins R) args) end, ((R, true), args)).

  Goal forall w S x, g (f w S) x <-> S x.
    intros w S [P [R args]]. split.
    - simpl. admit. (*very true*)
    - simpl. admit. (*very true*)
  Abort.

  Lemma invert_rule_impl_request_hyps R r b ins' hyps' :
    rule_impl (request_hyps r) (R, b, ins') hyps' -> b = false.
  Proof.
    cbv [rule_impl]. intros H. fwd. invert Hp1. apply Exists_exists in H0. fwd.
    cbv [request_hyps] in H0p0. simpl in H0p0. rewrite in_map_iff in H0p0. fwd.
    apply in_map_iff in H0p0p1. fwd. invert H0p1. reflexivity.
  Qed.

  Lemma rule_impl_request_hyps r R args R' args' hyps' :
    goodish_rule r (*very necessary, finally*)->
    rule_impl r (R, args) hyps' ->
    In (R', args') hyps' ->
    rule_impl (request_hyps r) (R', false, firstn (ins R') args')
      [(R, false, firstn (ins R) args)].
  Proof.
    intros Hgood H Hin. cbv [goodish_rule] in Hgood. fwd. cbv [request_hyps].
    rewrite Hgoodp0. simpl. unfold with_only_ins at 2. rewrite Hgoodp1. simpl.
    unfold fact_relmap at 2. simpl. cbv [rule_impl] in H. fwd.
    cbv [rule_impl]. eexists [_], nil. split; [reflexivity|]. invert Hp1.
    econstructor; simpl.
    - constructor.
    - do 2 rewrite Exists_map. apply Exists_app.
      rewrite in_app_iff in Hin. destruct Hin as [Hin|Hin].
      + left. apply Forall2_forget_l in H1. rewrite Forall_forall in H1.
        specialize (H1 _ ltac:(eassumption)). fwd. rewrite Exists_exists.
        eexists. split; [eassumption|]. invert H1p1. constructor.
        simpl. cbv [fact_ins]. apply Forall2_firstn. eassumption.
      + right. cbv [rule_agg_hyps]. invert H. 1: simpl in Hin; contradiction.
        rewrite <- H2 in *. fwd. invert H4. simpl in *.
        rewrite in_concat in Hin. fwd. apply Forall3_ignore12 in H5.
        rewrite Forall_forall in H5. specialize (H5 _ ltac:(eassumption)). fwd.
        apply Forall2_forget_l in H5p1. rewrite Forall_forall in H5p1.
        specialize (H5p1 _ ltac:(eassumption)). fwd. rewrite Exists_exists.
        eexists. split; [eassumption|].
        eapply interp_fact_relmap with (g := plus_false) in H5p1p1. simpl in H5p1p1.
        invert H5p1p1. constructor. simpl. cbv [fact_ins]. eapply Forall2_impl_strong.
        2: apply Forall2_firstn; eassumption. intros x2 y2 Hx2y2 Hx2 Hy2.
        simpl in H6. move Hgoodp5p1 at bottom.
        eapply interp_expr_agree_on; [eassumption|]. apply Forall_forall.
        intros v Hv. specialize (Hgoodp5p1 v). specialize' Hgoodp5p1.
        { apply in_flat_map. eexists. split; eauto. apply in_flat_map. eauto. }
        cbv [agree_on]. fwd. Fail solve [map_solver context_ok].
        erewrite map.get_putmany_left.
        { apply map.get_put_diff. assumption. }
        erewrite map.get_of_list_zip by eassumption. apply zipped_lookup_notin_None.
        assumption.
    - constructor; [|solve[constructor]]. rewrite Hgoodp0 in H0. invert_list_stuff.
      invert H3. constructor. simpl. eapply Forall2_impl_strong.
      2: { rewrite <- Hgoodp1. cbv [fact_ins]. apply Forall2_firstn. eassumption. }
      intros x y Hxy Hx Hy. apply in_map_iff in Hx. clear Hy. fwd. invert Hxy.
      constructor. invert H; [assumption|]. rewrite map.get_put_diff in H2; auto.
      intros ?. subst. apply Hgoodp2. eauto.
  Qed.

  Lemma agg_expr_relmap_id (ae : agg_expr) :
  agg_expr_relmap (fun x => x) ae = ae.
Proof.
  destruct ae. cbv [agg_expr_relmap]. simpl. erewrite map_ext with (g := fun x => x).
  2: { intros f. destruct f. reflexivity. }
  rewrite map_id. reflexivity.
Qed.

Lemma agg_expr_relmap_comp {rel1_ rel2_ rel3_ var_ fn_ aggregator_ : Type} (ae : @Datalog.agg_expr rel1_ var_ fn_ aggregator_) (g : rel1_ -> rel2_) (f : rel2_ -> rel3_) :
  agg_expr_relmap f (agg_expr_relmap g ae) = agg_expr_relmap (fun x => f (g x)) ae.
Proof.
  destruct ae. cbv [agg_expr_relmap]. simpl. rewrite map_map. reflexivity.
Qed.
  
  Lemma invert_rule_impl_add_hyp r R b args' hyps' :
    goodish_rule r ->
    rule_impl (add_hyp r) ((R, b), args') hyps' ->
    b = true /\
      exists hyps0',
        hyps' = ((R, false), firstn (ins R) args') :: hyps0' /\
          Forall (fun x => snd (fst x) = true) hyps0' /\
          rule_impl r (R, args') (map (fact'_relmap (fun '(R, _) => R)) hyps0').
  Proof.
    intros Hgood H. cbv [goodish_rule] in Hgood. fwd. cbv [rule_impl add_hyp] in H.
    fwd. invert Hp1; simpl in *. rewrite Hgoodp0 in *. simpl in *. invert_list_stuff.
    invert H2. split; [reflexivity|].
    cbv [with_only_ins] in H4. rewrite Hgoodp1 in H4. cbv [fact_relmap] in H3.
    simpl in H3. simpl in *. invert H4. simpl. simpl in H0.
      assert (args'0 = firstn (ins (fact_R concl)) args').
      { move H at bottom. move H3 at bottom. simpl in H3.
        cbv [fact_ins] in Hgoodp1. rewrite <- Hgoodp1 in H0.
        eapply Forall2_firstn in H3. eapply Forall2_unique_r. 1: exact H0.
        2: apply interp_expr_det. eapply Forall2_impl_strong; [|eassumption].
        intros. rewrite Hgoodp1 in H2. apply in_map_iff in H2. fwd.
        invert H1. constructor. invert H; [assumption|]. symmetry in H1.
        apply option_map_Some in H1. fwd. rewrite map.get_put_diff in H5; auto.
        intros H'. subst. apply Hgoodp2. eauto. }
      subst. eexists. split; [reflexivity|].
      apply interp_facts_relmap with (g := fst) in H6. fwd.
      rewrite map_map in H6p0. simpl in H6p0.
      eassert (H': forall x y, x = y -> map snd x = map snd y) by (intros; subst; reflexivity).
      apply H' in H6p0. clear H'. do 2 rewrite map_map in H6p0. simpl in H6p0.
      rewrite map_const in H6p0. eassert (H6p0': Forall _ _).
      { apply Forall_forall. intros x Hx. apply repeat_spec in Hx. exact Hx. }
      rewrite H6p0 in H6p0'. clear H6p0. apply Lists.List.Forall_map in H6p0'.
      invert H; simpl in *.
    - rewrite app_nil_r. symmetry in H4. apply option_map_None in H4. rewrite H4 in *.
      split; [assumption|]. cbv [rule_impl]. do 2 eexists.
      split; cycle 1.
      + eapply mk_rule_impl' with (ctx := ctx'); eauto.
        -- rewrite H4. constructor.
        -- rewrite Hgoodp0. constructor. constructor. assumption.
        -- rewrite map_map in H6p1. rewrite <- Forall2_map_l, <- Forall2_map_r in H6p1.
           erewrite <- Forall2_map_r. eapply Forall2_impl; [|eassumption]. simpl.
           intros. cbv [fact'_relmap fact_relmap] in H. simpl in H.
           instantiate (1 := fun _ => _). destruct a; simpl in *. exact H.
      + simpl. rewrite app_nil_r. cbv [fact'_relmap]. apply map_ext.
        intros [[? ?] ?]. reflexivity.
    - symmetry in H1. apply option_map_Some in H1. fwd. rewrite H1p0 in *.
      split.
      + apply Forall_app. split; [assumption|]. apply Forall_concat.
        invert H4. apply Forall3_ignore12 in H12. rewrite Forall_forall in *.
        intros x Hx. specialize (H12 _ Hx). simpl in *. fwd.
        apply Forall2_forget_l in H12p1. rewrite Forall_forall in *. intros z Hz.
        specialize (H12p1 _ Hz). fwd. apply in_map_iff in H12p1p0. fwd.
        invert H12p1p1. reflexivity.
      + cbv [rule_impl]. do 2 eexists. split.
        { rewrite map_app. rewrite concat_map. reflexivity. }
        eapply mk_rule_impl' with (ctx := ctx); eauto.
        -- rewrite H1p0. constructor. eapply interp_agg_expr_relmap with (g := fst) in H4.
           rewrite agg_expr_relmap_comp in H4. rewrite agg_expr_relmap_id in H4.
           apply H4.
        -- rewrite Hgoodp0. constructor. constructor. assumption.
        -- rewrite map_map in H6p1. rewrite <- Forall2_map_l, <- Forall2_map_r in H6p1.
           erewrite <- Forall2_map_r. eapply Forall2_impl; [|eassumption]. simpl.
           intros. cbv [fact'_relmap fact_relmap] in H. simpl in H.
           destruct b as [[? ?] ?]; simpl in *. destruct a0. exact H.
  Qed.      

  Lemma request_hyps_hyps_false r R b args hyps' :
    rule_impl (request_hyps r) (R, b, args) hyps' ->
    Forall (fun hyp' => snd (fst hyp') = false) hyps'.
  Proof.
    intros H. cbv [request_hyps rule_impl] in H. fwd. invert Hp1. simpl in *.
    apply Forall_forall.
    intros x Hx. invert H. rewrite app_nil_r in Hx. rewrite map_map in H1.
    apply Forall2_forget_l in H1. rewrite Forall_forall in H1.
    specialize (H1 _ ltac:(eassumption)). fwd.
    apply in_map_iff in H1p0. fwd. invert H1p1. reflexivity.
  Qed.

  Lemma f_fixpoint' r S w :
    goodish_rule r ->
    fp (F [request_hyps r]) w ->
    fp (F [r]) S ->
    fp (F [request_hyps r; add_hyp r]) (f w S).
  Proof.
    cbv [fp F]. intros Hgood Wfp H [P [[R b] args]] Hx. simpl.
    destruct Hx as [Hx| [Hx|Hx]]; auto.
    { destruct b; auto. }
    fwd. invert Hxp0.
    - simpl. pose proof H1 as H1'.
      apply invert_rule_impl_request_hyps in H1. subst. apply Wfp. right. right.
      exists hyps'. split.
      { constructor. assumption. }
      apply request_hyps_hyps_false in H1'. rewrite Forall_forall in Hxp1, H1'.
      rewrite Forall_forall. intros x Hx. specialize (Hxp1 _ Hx). specialize (H1' _ Hx).
      destruct x as [ [R' b'] args']. simpl in Hxp1, H1'. subst. assumption.
    - invert_list_stuff. eapply invert_rule_impl_add_hyp in H2; eauto. fwd. simpl.
      apply H. right. right. eexists. split; eauto. apply Forall_map. eapply Forall_impl.
      2: { eapply Forall_and. 1: apply Hxp1p1. apply H2p1p1. }
      simpl. intros [[R' b'] args']. simpl. intros. fwd. assumption.
  Qed.

  Lemma g_fixpoint' (*P*) r S :
    goodish_rule r ->
    S_sane S ->
    fp (F [request_hyps r; add_hyp r]) S ->
    fp (F [r]) (g S).
  Proof.
    cbv [fp F]. intros Hgood (Sgood1&Sgood2) H [P x] Hx. destruct Hx as [Hx| [Hx|Hx]]; auto.
    fwd. destruct x as [R args]. invert_list_stuff.
    pose proof rule_impl_add_hyp as H1'. specialize H1' with (1 := Hgood) (2 := H1).
    simpl. apply H. right. right. eexists. split.
    { apply Exists_cons_tl. constructor. eassumption. }
    constructor.
    { auto. }
    apply Forall_map. pose proof Hxp1 as H'. rewrite Forall_forall in H'.
    rewrite Forall_forall. intros [R' args'] Hx. specialize H' with (1 := Hx).
    simpl in H'. cbv [fact'_relmap]. eapply Sgood2; [eassumption|]. simpl.
    clear H'. intros y Hy. destruct y as [ [Ry By] argsy]. destruct By.
    { apply H; auto. }
    invert Hy. apply H. right. right. exists [(R, false, firstn (ins R) args)]. split.
    2: eauto. constructor. eapply rule_impl_request_hyps; eauto.
  Qed.

  Lemma f_sane w S :
    (forall x P, P x -> S (P, x)) ->
    (forall x P, P x -> w (P, x)) ->
    (forall x P, P x -> f w S (P, x)).
  Proof. intros H1 H2 [[R b] args] P. simpl. destruct b; eauto. Qed.

  Hint Resolve f_sane : core.
  Hint Unfold S_sane : core.

  Lemma f_fixpoint w p S :
    S_sane w ->
    S_sane S ->
    Forall goodish_rule p ->
    fp (F p) S ->
    fp (F (map request_hyps p)) w ->
    fp (F (make_good p)) (f w S).
  Proof.
    intros (Wgood1&Wgood2) (Sgood1&Sgood2) H1 H2 HP. pose proof f_fixpoint' as H'.
    rewrite Forall_forall in H1.
    assert (forall r, In r p -> fp (F [request_hyps r]) w).
    { intros r Hr. rewrite <- split_fixpoint in HP by auto. apply HP. apply in_map. assumption. }
    apply split_fixpoint; auto. cbv [make_good]. intros r Hr.
    apply in_app_iff in Hr. destruct Hr as [Hr|Hr]; apply in_map_iff in Hr; fwd.
    - apply split_fixpoint; auto. rewrite <- split_fixpoint in H2 by auto. 
      specialize (H' _ _ _ ltac:(eauto) ltac:(eauto) ltac:(eauto)).
      rewrite <- split_fixpoint in H' by auto. simpl in *. intros. apply H'. tauto.
    - apply split_fixpoint; auto. rewrite <- split_fixpoint in H2 by auto.
      specialize (H' _ _ _ ltac:(eauto) ltac:(eauto) ltac:(eauto)).
      rewrite <- split_fixpoint in H' by auto. simpl in *. intros. apply H'. tauto.
  Qed.

  Lemma g_sane S :
    (forall x P, P x -> S (P, x)) ->
    (forall x P, P x -> g S (P, x)).
  Proof. intros H [R args] P HP. simpl. auto. Qed.

  Hint Resolve g_sane : core.

  Lemma g_fixpoint p S :
    Forall goodish_rule p ->
    S_sane S ->
    fp (F (make_good p)) S ->
    fp (F p) (g S).
  Proof.
    intros H1 (Sgood1&Sgood2) H2. pose proof g_fixpoint' as H'. rewrite Forall_forall in H1.
    apply split_fixpoint; auto. cbv [make_good]. intros r Hr.
    apply H'; auto.
    apply split_fixpoint; auto.
    intros r' Hr'. rewrite <- split_fixpoint in H2 by auto.
    destruct Hr' as [Hr' | [Hr' | Hr'] ]; [| |exfalso; auto]; subst; apply H2; cbv [make_good]; apply in_app_iff; auto using in_map.
  Qed.

  Lemma g_mono S1 S2 :
    (forall x, S1 x -> S2 x) ->
    forall x, g S1 x -> g S2 x.
  Proof. cbv [g]. intros H [P [R args]] Hx. auto. Qed.
  
  Lemma gf_id w S :
    S_sane S ->
    equiv S (g (f w S)).
  Proof. (*note: here i just use weakening, which follows from Sgood1 and Sgood2, but Sgood1 and Sgood2 together are stronger than weakening*)
    intros (Sgood1&Sgood2). cbv [equiv g f]. intros [P [R args]].
    intuition eauto. (*because eauto doesn't know how to unfold <-> ?*)
  Qed.

  Hint Resolve fp_lfp F_mono S_sane_lfp : core.

  Lemma lfp_preimage p :
    Forall goodish_rule p ->
    equiv (g (lfp (F (make_good p)))) (lfp (F p)).
  Proof.
    intros Hgood. eapply lfp_preimage'.
    - exact g_mono.
    - apply f_fixpoint with (w := lfp (F (map request_hyps p))); eauto.
    - apply g_fixpoint; eauto.
    - apply gf_id; eauto.
  Qed.

  Lemma equiv_trans {U : Type} (A B C : U -> _) :
    equiv A B -> equiv B C -> equiv A C.
  Proof. cbv [equiv]. intros. rewrite H, <- H0. reflexivity. Qed.

  Lemma equiv_symm {U : Type} (A B : U -> _) :
    equiv A B -> equiv B A.
  Proof. cbv [equiv]. intros. rewrite H. reflexivity. Qed.

  Lemma g_ext A B : equiv A B -> equiv (g A) (g B).
  Proof. cbv [equiv g]. intros H [P [R args]]. apply H. Qed.
      
  Lemma phase_correct p :
    Forall goodish_rule p ->
    equiv (fun '(P, f) => prog_impl_implication p P f) (g (fun '(P, f) => prog_impl_implication (make_good p) P f)).
  Proof.
    intros. eapply equiv_trans.
    { apply prog_impl_fact_lfp. }
    eapply equiv_trans.
    { apply equiv_symm. apply lfp_preimage. assumption. }
    apply equiv_symm. apply g_ext. apply prog_impl_fact_lfp.
  Qed. 

  Lemma source_impl_target p Q R args :
    Forall goodish_rule p ->
    prog_impl_implication p Q (R, args) ->
    prog_impl_implication (make_good p)
      (fun '((R0, b0), args0) => if b0 then Q (R0, args0) else (R0, args0) = (R, firstn (ins R) args))
      ((R, true), args).
  Proof.
    intros H1 H2. pose proof phase_correct _ H1 as H3. cbv [equiv] in H3.
    rewrite (H3 (_, _)) in H2. clear H3. simpl in H2. assumption.
  Qed.

  Lemma target_impl_source p R args Q :
    Forall goodish_rule p ->
    prog_impl_implication (make_good p) Q ((R, true), args) ->
    prog_impl_implication p (fun '(R, args) => Q ((R, true), args)) (R, args).
  Proof.
    intros H1 H2. pose proof phase_correct _ H1 as H3. cbv [equiv] in H3.
    rewrite (H3 (_, _)). clear H3. simpl. remember (R, true, args) as x eqn:E.
    revert R args E. (*TODO factor following out into lemma*)induction H2; intros; subst.
    - apply partial_in. assumption.
    - eapply partial_step. 1: apply H. cbv [make_good] in H.
      apply Exists_app in H. destruct H as [H|H].
      { clear -H. exfalso. rewrite Exists_map in H. apply Exists_exists in H.
        fwd. cbv [rule_impl] in Hp1. fwd. invert Hp1p1.
        cbv [request_hyps] in H0. simpl in H0. rewrite Exists_map in H0.
        apply Exists_exists in H0.
        fwd. invert H0p1. }
      rewrite Forall_forall in H1. rewrite Exists_map in H. apply Exists_exists in H.
      fwd. rewrite Forall_forall in H0. apply invert_rule_impl_add_hyp in Hp1; auto.
      fwd. constructor.
      2: { rewrite Forall_forall in *. intros [[R' b'] args'] H.
           specialize (Hp1p1p1 _ ltac:(eassumption)). simpl in Hp1p1p1. subst.
           apply partial_pftree_trans. eapply partial_pftree_weaken.
           1: apply H2p1; eauto. intros [[Ry By] argsy]. intros Hy. destruct By.
           - apply partial_in. assumption.
           - clear H2p0. invert Hy. eapply partial_step.
             { cbv [make_good]. apply Exists_app. left. apply Exists_map.
               apply Exists_exists. exists x. split; [assumption|].
               eapply rule_impl_request_hyps; eauto.
               apply in_map_iff. eexists (_, _, _). simpl. eauto. }
             constructor; [|constructor]. apply partial_in. reflexivity. }
      apply partial_in. reflexivity.
  Qed.
End Transform.
