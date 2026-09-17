From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Permutation.
From Stdlib Require Import micromega.Lia.

From Datalog Require Import Map Tactics Fp List Pftree Datalog RelMap.
From GraphSearch Require Import Dag.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List Datatypes.Option Eqb.

Import ListNotations.

Section Blocks.
  Context {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context {semantics : datalog_semantics fn aggregator T}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.
  Context {value_eqb : Eqb T} {value_eqb_ok : Eqb_ok value_eqb}.
  Context {value_set : map.map (list T) unit} {value_set_ok : map.ok value_set}.
  Context {lvar : Type}.

  Inductive block_rel {var} :=
  | local (_ : lvar)
  | input (_ : var).
  Arguments block_rel : clear implicits.

  Definition block_program var := program (relt := block_rel var).

  Inductive blocks_prog {var} :=
  | LetIn (x : blocks_prog) (f : var -> blocks_prog)
  (* | SetGlobal (x : gvar) (v : blocks_prog) *)
  (* note: probably i should let an input have type var or be a global.
     but i am ignoring globals for now.
   *)
  | Block (ret : lvar) (p : block_program var).
  Arguments blocks_prog : clear implicits.

  Definition example {var} (ret : lvar) p1 p2 : blocks_prog var :=
    LetIn (Block ret p1) (fun val => Block ret (p2 val)).

  Fixpoint interp_blocks_prog (e : blocks_prog (fact_args -> Prop)) : fact_args -> Prop :=
    match e with
    | LetIn x f =>
        interp_blocks_prog (f (interp_blocks_prog x))
    | Block ret p =>
        fun args =>
          program.interp p
            (fun f => exists R, fact.rel f = input R /\ R (fact.args_of f))
            (fact.of_args (local ret) args)
    end.

  Definition wf_rel {var1 var2} (ctx : list (var1 * var2)) (R1 : block_rel var1) (R2 : block_rel var2) :=
    match R1, R2 with
    | local x1, local x2 => x1 = x2
    | input v1, input v2 => In (v1, v2) ctx
    | _, _ => False
    end.

  Inductive wf_blocks_prog {var1 var2} : list (var1 * var2) -> blocks_prog var1 -> blocks_prog var2 -> Prop :=
  | wf_LetIn ctx x1 x2 f1 f2 :
    wf_blocks_prog ctx x1 x2 ->
    (forall x1' x2', wf_blocks_prog ((x1', x2') :: ctx) (f1 x1') (f2 x2')) ->
    wf_blocks_prog ctx (LetIn x1 f1) (LetIn x2 f2)
  | wf_Block ctx ret p1 p2 :
    wf_program (wf_rel ctx) p1 p2 ->
    wf_blocks_prog ctx (Block ret p1) (Block ret p2).

  Definition vars_of_block_rel {var} (R : block_rel var) :=
    match R with
    | input R0 => [R0]
    | local _ => []
    end.

  Ltac aggress' :=
    match goal with
    | _ => progress intros
    | _ => contradiction
    | _ => congruence
    | _ => progress simpl in *
    | H: _ \/ _ |- _ => destruct H
    | |- _ <-> _ => split
    | |- _ /\ _ => split
    | |- _ \/ _ => left; solve[repeat aggress']
    | |- _ \/ _ => right; solve[repeat aggress']
    end.

  Ltac fin := solve [repeat aggress'].

  Lemma inv_vars_of_block_rel var (R : block_rel var) R0 :
    In R0 (vars_of_block_rel R) <-> R = input R0.
  Proof. destruct R; fin. Qed.

  Definition vars_of_block {var} (p : block_program var) := flat_map vars_of_block_rel (program.hyp_rels p).

  Lemma inv_vars_of_block var p (R : var) :
    In R (vars_of_block p) <-> (In (input R) (program.hyp_rels p)).
  Proof.
    cbv [vars_of_block]. rewrite in_flat_map.
    setoid_rewrite inv_vars_of_block_rel. split; intros; fwd; eauto.
  Qed.

  (*TODO try out (var -> Prop) instead of (list var) ??*)
  Inductive vars_in {var} : list var -> blocks_prog var -> Prop :=
  | vars_in_LetIn ctx x f :
    vars_in ctx x ->
    (forall x', vars_in (x' :: ctx) (f x')) ->
    vars_in ctx (LetIn x f)
  | vars_in_Block ctx ret p :
    incl (vars_of_block p) ctx ->
    vars_in ctx (Block ret p).


  Lemma vars_in_incl var (ctx1 ctx2 : list var) (p : blocks_prog var) :
    incl ctx1 ctx2 ->
    vars_in ctx1 p ->
    vars_in ctx2 p.
  Proof.
    intros Hincl Hvars. revert ctx2 Hincl.
    induction Hvars; intros; constructor; auto with incl.
    eapply incl_tran; eassumption.
  Qed.

  Inductive flat_rel : Type :=
  | lvar_rel (block : nat) (name : lvar).

  Definition flat_program := program (relt := flat_rel).

  Context {lvar_eqb : Eqb lvar} {lvar_eqb_ok : Eqb_ok lvar_eqb}.

  Definition flatten_rel (block : nat) (R : block_rel flat_rel) :=
    match R with
    | local x => lvar_rel block x
    | input x => x
    end.

  Fixpoint flatten (name : nat) (e : blocks_prog flat_rel) : nat * flat_rel * flat_program :=
    match e with
    | LetIn x f =>
        let '(name', Rx, p2) := flatten name x in
        let '(name'', Rfx, p1) := flatten name' (f Rx) in
        (name'', Rfx, program.union p1 p2)
    | Block ret p =>
        (S name, lvar_rel name ret, map_program (flatten_rel name) p)
    end.

  Definition in_range lo hi x :=
    match x with
    | lvar_rel block_id _ => lo <= block_id < hi
    end.

  Definition not_as_big_as hi x :=
    match x with
    | lvar_rel block_id _ => block_id < hi
    end.

  Lemma flatten_rel_inj name rs :
    (forall x, In (input x) rs -> in_range O name x) ->
    injective_on (flatten_rel name) rs.
  Proof.
    intros Hin R1 R2 H1 H2 Heq. destruct R1, R2; simpl in Heq; try congruence.
    - apply Hin in H2. rewrite <- Heq in H2. simpl in H2. lia.
    - apply Hin in H1. rewrite Heq in H1. simpl in H1. lia.
  Qed.

  Lemma in_range_weaken lo0 lo hi hi0 x :
    in_range lo hi x ->
    lo0 <= lo ->
    hi <= hi0 ->
    in_range lo0 hi0 x.
  Proof. destruct x; simpl; auto; lia. Qed.

  Lemma not_as_big_as_weaken hi hi0 x :
    not_as_big_as hi x ->
    hi <= hi0 ->
    not_as_big_as hi0 x.
  Proof. destruct x; simpl; auto; lia. Qed.

  Lemma in_nonoverlapping_ranges lo1 hi1 lo2 hi2 x :
    in_range lo1 hi1 x ->
    in_range lo2 hi2 x ->
    hi1 <= lo2 ->
    False.
  Proof. destruct x; simpl; auto. lia. Qed.

  Definition is_not_input {var} (R : block_rel var) :=
    match R with
    | local _ => True
    | input _ => False
    end.

  Fixpoint valid_blocks_prog {var} (e : blocks_prog var) : Prop :=
    match e with
    | LetIn x f =>
        valid_blocks_prog x /\ (forall v, valid_blocks_prog (f v))
    | Block ret p =>
        program.meta_rules_valid p /\
          Forall is_not_input (program.concl_rels p)
    end.
  Hint Constructors vars_in : core.

  Lemma block_good_input_set (p : block_program (fact_args -> Prop)) :
    Forall is_not_input (program.concl_rels p) ->
    Forall fact_args.honest (vars_of_block p) ->
    program.good_input_set p
      (fun f => exists R, fact.rel f = input R /\ R (fact.args_of f) /\ In R (vars_of_block p)).
  Proof.
    intros Hconcl Hhonest. split.
    - intros ? H. fwd. rewrite Hp0 in *. intros H'. rewrite Forall_forall in Hconcl.
      apply Hconcl in H'. simpl in *. assumption.
    - cbv [fact.set_doesnt_lie]. intros. fwd. simp. simpl in *.
      (*TODO simp should do this*)cbv [meta_fact.rel] in *.
      simpl in *. subst. apply inv_vars_of_block in Hp2. cbv [fact.normal_subset]. simpl.
      rewrite Forall_forall in Hhonest. setoid_rewrite inv_vars_of_block in Hhonest.
      especialize Hhonest; eauto. cbv [fact_args.honest] in Hhonest.
      especialize Hhonest; eauto. cbv [fact_args.consistent] in Hhonest.
      cbv [fact.set_consistent_with]. simpl. intros nf Hnf. simp.
      (*TODO simp should do this*)cbv [fact_pattern.matches] in Hnf. simpl in Hnf. fwd.
      cbv [fact.normal_subset]. simpl. setoid_rewrite inv_vars_of_block.
      rewrite Hhonest by eassumption. split; intros; fwd; eauto.
  Qed.

  Lemma interp_blocks_prog_honest ctx (e : blocks_prog (fact_args -> Prop)) :
    valid_blocks_prog e ->
    vars_in ctx e ->
    Forall fact_args.honest ctx ->
    fact_args.honest (interp_blocks_prog e).
  Proof.
    intros Hvalid. induction 1; intros Hctx; simpl.
    - simpl in Hvalid. fwd. eauto.
    - simpl in Hvalid. fwd. Check program.interp_invariant.
      eapply fact_args.honest_ext.
      2: { intros. rewrite program.interp_invariant' at 2.
           2: { intro. fwd. rewrite fact.rel_of_args in *. congruence. }
           instantiate (1 := fun _ => _). simpl. reflexivity. }
      apply fact.set_doesnt_lie_honest_args.
      apply program.valid_impl_honest; [eassumption|].
      eapply program.good_input_set_ext.
      { eapply block_good_input_set; try assumption.
        rewrite Forall_forall in *. auto. }
      simpl. intros. split; intros H'; fwd; eauto.
      + rewrite H'p0 in *. apply in_flat_map in H'p2. fwd.
        apply inv_vars_of_block_rel in H'p2p1. subst. eauto.
      + rewrite H'p0p0 in *. setoid_rewrite in_flat_map.
        eexists. ssplit; eauto. eexists. split; eauto. simpl. auto.
  Qed.

  Lemma wf_program_not_input {var1 var2} (ctx : list (var1 * var2)) p1 p2 :
    wf_program (wf_rel ctx) p1 p2 ->
    Forall is_not_input (program.concl_rels p1) ->
    Forall is_not_input (program.concl_rels p2).
  Proof.
    intros Hwf Hnoinp. rewrite Forall_forall in *. intros R HR.
    eapply Forall2_In_r in HR; [|apply (wf_program_concl_rels _ _ _ Hwf)].
    fwd. apply in_combine_l in HRp0. apply Hnoinp in HRp0.
    destruct x, R; cbn in *; auto.
  Qed.

  Lemma wf_program_vars_of_block {var1 var2} (ctx : list (var1 * var2)) p1 p2 :
    wf_program (wf_rel ctx) p1 p2 ->
    incl (vars_of_block p1) (map fst ctx).
  Proof.
    intros Hwf R HR. apply inv_vars_of_block in HR.
    eapply Forall2_In_l in HR; [|apply (wf_program_hyp_rels _ _ _ Hwf)].
    fwd. destruct y; try contradiction. eapply in_fst. eassumption.
  Qed.

  Lemma wf_program_vars_of_block_r {var1 var2} (ctx : list (var1 * var2)) p1 p2 :
    wf_program (wf_rel ctx) p1 p2 ->
    incl (vars_of_block p2) (map snd ctx).
  Proof.
    intros Hwf R HR. apply inv_vars_of_block in HR.
    eapply Forall2_In_r in HR; [|apply (wf_program_hyp_rels _ _ _ Hwf)].
    fwd. destruct x; try contradiction. eapply in_snd. eassumption.
  Qed.

  Lemma wf_program_input_in_ctx {var1 var2} (ctx : list (var1 * var2)) p1 p2 x :
    wf_program (wf_rel ctx) p1 p2 ->
    Forall is_not_input (program.concl_rels p1) ->
    In (input x) (program.all_rels p2) ->
    In x (map snd ctx).
  Proof.
    intros Hwf Hnoinp HR. cbv [program.all_rels] in HR. apply in_app_iff in HR.
    destruct HR as [HR|HR].
    - exfalso. pose proof (wf_program_not_input _ _ _ Hwf Hnoinp) as Hni.
      rewrite Forall_forall in Hni. apply Hni in HR. exact HR.
    - eapply wf_program_vars_of_block_r; [eassumption|]. apply inv_vars_of_block, HR.
  Qed.

  Lemma wf_blocks_prog_vars_in {var1 var2} (x : var2) (ctx : list (var1 * var2)) (p : blocks_prog var1) (p' : blocks_prog var2) :
    wf_blocks_prog ctx p p' ->
    vars_in (map fst ctx) p.
  Proof.
    induction 1; simpl in *; eauto using wf_program_vars_of_block.
  Qed.

  Hint Resolve in_fst in_snd : core.

  Lemma flat_good_input_set ctx name (p : block_program flat_rel) :
    Forall (in_range O name) (map snd ctx) ->
    NoDup (map snd ctx) ->
    Forall is_not_input (program.concl_rels p) ->
    Forall fact_args.honest (map fst ctx) ->
    program.good_input_set (map_program (flatten_rel name) p)
      (fun f => exists R, In (R, fact.rel f) ctx /\ R (fact.args_of f)).
  Proof.
    intros Hctx Hnd Hconcl Hhonest. rewrite Forall_forall in Hctx, Hconcl, Hhonest. split.
    - intros f Hf Hin. fwd. rewrite concl_rels_map_program in Hin. apply in_map_iff in Hin. fwd.
      apply Hconcl in Hinp1. destruct x; [|contradiction]. simpl in Hinp0.
      apply in_snd, Hctx in Hfp0. rewrite <- Hinp0 in Hfp0. simpl in Hfp0. lia.
    - cbv [fact.set_doesnt_lie]. intros mf Hmf. fwd.
      cbv [fact.set_consistent_with fact.normal_subset]. intros nf Hnf.
      specialize (Hhonest _ ltac:(eauto using in_fst)).
      cbv [fact_args.honest] in Hhonest. specialize (Hhonest _ Hmfp1).
      cbv [fact_args.consistent] in Hhonest.
      cbv [fact_pattern.matches] in Hnf. simpl in *. cbv [meta_fact.rel] in Hmfp0. fwd.
      rewrite (Hhonest _ ltac:(eassumption)). split.
      + intros HR. exists R. split; [congruence | assumption].
      + intros (R0 & HR0 & HR). replace R0 with R in HR; [assumption|].
        eapply NoDup_snd_In_inj; [eassumption | eassumption | congruence].
  Qed.

  Lemma flatten_correct' ctx name e e0 name' Rret p :
    wf_blocks_prog ctx e e0 ->
    valid_blocks_prog e ->
    valid_blocks_prog e0 ->
    flatten name e0 = (name', Rret, p) ->
    Forall (in_range O name) (map snd ctx) ->
    NoDup (map snd ctx) ->
    Forall fact_args.honest (map fst ctx) ->
    name <= name' /\
      in_range name name' Rret /\
      Forall (in_range name name') (program.concl_rels p) /\
      Forall (fun R => in_range name name' R \/ In R (map snd ctx))
        (program.all_rels p) /\
      forall args,
        interp_blocks_prog e args <->
          program.interp p (fun f => exists R, In (R, fact.rel f) ctx /\ R (fact.args_of f))
            (fact.of_args Rret args).
  Proof.
    intros Hwf Hvalid Hvalid0. revert name name' Rret p.
    induction Hwf;
      intros name name' Rret p0 Hflat Hctx1 Hctx2 Hctx3;
      simpl in Hflat;
      fwd;
      simpl.
    - simpl in Hvalid, Hvalid0. fwd.
      specialize (IHHwf ltac:(assumption) ltac:(assumption)). epose_dep IHHwf.
      specialize (IHHwf ltac:(eassumption) ltac:(eassumption) ltac:(assumption) ltac:(eassumption)).
      fwd.
      rename H0 into IH'. specialize (IH' (interp_blocks_prog x1)).
      epose_dep IH'. specialize (IH' ltac:(eauto)). specialize (IH' ltac:(eauto)).
      epose_dep IH'.
      specialize (IH' ltac:(eassumption)). specialize' IH'.
      { constructor.
        - eapply in_range_weaken; [eassumption| |]; lia.
        - eapply Forall_impl; [eassumption|].
          intros. eapply in_range_weaken; [eassumption| |]; lia. }
      specialize' IH'.
      { simpl. constructor; auto. rewrite Forall_forall in Hctx1.
        intros Hf. apply in_map_iff in Hf. destruct Hf as [(?, ?) Hf]. fwd.
        simpl in *. specialize (Hctx1 _ ltac:(eauto)).
        eauto using in_nonoverlapping_ranges. }
      specialize' IH'.
      { simpl. eauto using interp_blocks_prog_honest, wf_blocks_prog_vars_in. }
      fwd. ssplit.
      + lia.
      + eapply in_range_weaken; [eassumption| |]; lia.
      + eapply Permutation_Forall; [ symmetry; apply program.concl_rels_union | ].
        apply Forall_app.
        eauto 10 using Forall_impl, in_range_weaken.
      + eapply Permutation_Forall; [ symmetry; apply program.all_rels_union | ].
        apply Forall_app. split.
        -- eapply Forall_impl; [eassumption|]. simpl.
           intros R [HR| [HR|HR]]; subst; eauto using in_range_weaken.
        -- eapply Forall_impl; [eassumption|]. simpl.
           intros R [HR|HR]; eauto using in_range_weaken.
      + intros args.
        rewrite program.stratify_iff.
        2: { apply program.stratified_of_disjoint. intros x H1 H2.
             rewrite Forall_forall in *.
             apply IH'p2 in H1. apply IHHwfp3 in H2. destruct H2 as [H2|H2].
             - eapply in_nonoverlapping_ranges. 1: exact H2. 1: exact H1. lia.
             - apply in_map_iff in H2. destruct H2 as [[? ?] H2]. fwd.
               specialize (Hctx1 _ ltac:(eauto)). simpl in H1.
               eapply in_nonoverlapping_ranges. 1: exact Hctx1. 1: exact H1. lia. }
        rewrite IH'p4.
        apply program.interp_hyp_ext_strong.
        { split; intros Hargs; simpl; fwd; exfalso.
          - destruct Hargsp0 as [Hargsp0|Hargsp0]; fwd.
            + apply IHHwfp4 in Hargsp1. rewrite fact.of_args_args_of in Hargsp1.
              apply program.interp_rel_of in Hargsp1. destruct Hargsp1 as [Hargsp1|Hargsp1].
              -- fwd. rewrite fact.rel_of_args in Hargsp1p0.
                 rewrite Forall_forall in Hctx1. apply in_snd in Hargsp1p0.
                 apply Hctx1 in Hargsp1p0.
                 eauto using in_nonoverlapping_ranges.
              -- rewrite fact.rel_of_args in Hargsp1.
                 rewrite Forall_forall in IHHwfp2.
                 apply IHHwfp2 in Hargsp1.
                 eauto using in_nonoverlapping_ranges.
            + rewrite fact.rel_of_args in Hargsp0.
              rewrite Forall_forall in Hctx1. apply in_snd in Hargsp0.
              apply Hctx1 in Hargsp0.
              eauto using in_nonoverlapping_ranges.
          - apply program.interp_rel_of in Hargs. destruct Hargs as [Hargs|Hargs].
            + fwd. rewrite fact.rel_of_args in Hargsp0.
              rewrite Forall_forall in Hctx1. apply in_snd in Hargsp0.
              apply Hctx1 in Hargsp0.
              eauto using in_nonoverlapping_ranges.
            + rewrite fact.rel_of_args in Hargs.
              rewrite Forall_forall in IHHwfp2.
              apply IHHwfp2 in Hargs.
              eauto using in_nonoverlapping_ranges. }
        intros f' HRf'. split; intros Hf'; fwd.
        -- simpl in Hf'p0. destruct Hf'p0 as [Hf'p0|Hf'p0].
           ++ fwd. rewrite IHHwfp4 in Hf'p1 by eassumption.
              rewrite fact.of_args_args_of in Hf'p1. exact Hf'p1.
           ++ apply pftree.leaf. eauto.
        -- pose proof Hf' as Hf''.
           apply program.interp_rel_of in Hf'. destruct Hf' as [Hf'|Hf'].
           ++ fwd. simpl. eauto.
           ++ rewrite Forall_forall in IH'p3.
              apply program.hyp_rel_all in HRf'.
              apply IH'p3 in HRf'.
              rewrite Forall_forall in IHHwfp2. apply IHHwfp2 in Hf'.
              destruct HRf' as [HRf'|HRf'].
              { exfalso. eauto using in_nonoverlapping_ranges. }
              simpl in HRf'. destruct HRf' as [HRf'|HRf'].
              --- subst. simpl. eexists. split; eauto. apply IHHwfp4.
                  rewrite fact.of_args_args_of. assumption.
              --- apply in_map_iff in HRf'. destruct HRf' as [[? ?] HRf'].
                  simpl in HRf'. fwd.
                  rewrite Forall_forall in Hctx1.
                  apply in_snd in HRf'p1. apply Hctx1 in HRf'p1.
                  exfalso. eauto using in_nonoverlapping_ranges.
    - simpl in Hvalid, Hvalid0. destruct Hvalid as (Hmrv & Hnoinp).
      destruct Hvalid0 as (Hmrv2 & Hnoinp2).
      ssplit.
      + lia.
      + lia.
      + lia.
      + rewrite concl_rels_map_program. apply List.Forall_map.
        eapply Forall_impl; [eapply wf_program_not_input; eassumption|].
        intros R HR. destruct R; simpl in *; [lia | contradiction].
      + rewrite all_rels_map_program. apply List.Forall_map. apply Forall_forall.
        intros R HR. destruct R; simpl; [left; lia | right].
        eapply wf_program_input_in_ctx; eassumption.
      + intros args. symmetry. rewrite Forall_forall in Hctx1.
        apply (interp_wf_iff (fun x R => exists y, wf_rel ctx R y /\ flatten_rel name y = x)).
        -- apply wf_program_flip. eapply wf_program_comp; [eassumption | apply wf_program_map].
        -- apply Forall_forall. intros x _ R R' (y & Hy & <-) (y' & Hy' & Hx').
           destruct R as [l|P], y as [l0|z]; simpl in Hy; try contradiction;
             destruct R' as [l'|P'], y' as [l0'|z']; simpl in Hy'; try contradiction;
             simpl in Hx'.
           ++ congruence.
           ++ exfalso. subst. apply in_snd, Hctx1 in Hy'. simpl in Hy'. lia.
           ++ exfalso. subst. apply in_snd, Hctx1 in Hy. simpl in Hy. lia.
           ++ subst. f_equal. eapply NoDup_snd_In_inj; eassumption.
        -- rewrite concl_rels_map_program. apply List.Forall_map.
           eapply Forall_impl; [eapply wf_program_not_input; eassumption|].
           intros [l|P] HR; [|contradiction]. intros x' R (y & Hy & Hx) (y' & Hy' & <-).
           destruct R as [l'|P'], y as [l0|z]; simpl in Hy; try contradiction;
             destruct y' as [l0'|z']; simpl in Hy'; try contradiction; simpl in *.
           ++ congruence.
           ++ exfalso. subst. apply in_snd, Hctx1 in Hy. simpl in Hy. lia.
        -- eapply meta_rules_valid_wf; [apply wf_program_map | | | exact Hmrv2].
           ++ apply Forall_forall. auto using functional_at_map.
           ++ apply inj_on_map, flatten_rel_inj. intros x Hx.
              rewrite Forall_forall in Hnoinp2. apply Hnoinp2 in Hx. contradiction.
        -- apply flat_good_input_set; try assumption. apply Forall_forall. assumption.
        -- intros g1 g2 Hg. pose proof (wf_fact_rel _ _ _ Hg) as Hrel.
           destruct Hrel as (y & Hy & Hx). rewrite (wf_fact_args _ _ _ Hg), <- Hx.
           destruct (fact.rel g2) as [l|P], y as [l0|z]; simpl in Hy; try contradiction; simpl.
           ++ split; intros (R & HR & HR'); exfalso; [|discriminate].
              apply in_snd, Hctx1 in HR. simpl in HR. lia.
           ++ split; intros (R & HR & HR').
              ** exists P. split; [reflexivity|]. replace P with R; [assumption|].
                 eapply NoDup_snd_In_inj; eassumption.
              ** injection HR as <-. eauto.
        -- apply wf_fact_of_args. exists (local ret). split; reflexivity.
  Qed.
End Blocks.


Arguments blocks_prog {_ _ _ _} _.
Arguments block_rel : clear implicits.

Ltac interp_exprs :=
  repeat match goal with
    | |- program.interp _ _ (fact.normal {| normal_fact.rel := input _;
                                           normal_fact.args := _ |}) =>
        apply pftree.leaf
    | |- program.interp _ _ (fact.meta {| meta_fact.pattern :=
                                           {| fact_pattern.rel := input _;
                                             fact_pattern.args := _ |};
                                         meta_fact.set := _ |}) =>
        apply pftree.leaf
    | _ => progress Datalog.interp_exprs
    | _ => (doExists 0 + doExists 1); split; [reflexivity|]
    end.
