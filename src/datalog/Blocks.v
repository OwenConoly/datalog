From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Permutation.
From Stdlib Require Import micromega.Lia.

From Datalog Require Import Map Tactics Fp List Pftree Datalog RelMap Eqb.
From GraphSearch Require Import Dag.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List Datatypes.Option Eqb.

Import ListNotations.

(*relations that are local to a block, "l" is for "local"*)
Definition lrelT := Type. Existing Class lrelT.
Abbreviation lrel := (_ : lrelT).
#[global] Typeclasses Transparent lrelT.

Module block_rel.
  Section __.
    Context `{_lrel : lrelT} {var : Type}.

    Inductive block_rel : relT :=
    | local (_ : lrel)
    | input (_ : var).

    Definition vars (R : block_rel) :=
      match R with
      | input R0 => [R0]
      | local _ => []
      end.

    Definition is_not_input (R : block_rel) :=
      match R with
      | local _ => True
      | input _ => False
      end.

    Context {var_eqb : Eqb var} {var_eqb_ok : Eqb_ok var_eqb}.
    Context {lrel_eqb : Eqb lrel} {lrel_eqb_ok : Eqb_ok lrel_eqb}.

    #[global] Instance eqb : Eqb block_rel :=
      fun R1 R2 =>
        match R1, R2 with
        | local l1, local l2 => eqb l1 l2
        | input l1, input l2 => eqb l1 l2
        | _, _ => false
        end.

    #[global] Instance eqb_ok : Eqb_ok eqb.
    Proof.
      intros x y. cbv [Eqb.eqb eqb].
      destruct x, y; try congruence; Tactics.destruct_one_match; congruence.
    Qed.
  End __.
  Arguments block_rel {_lrel} var.

  Section __.
    Context `{_lrel : lrelT}.
    Definition wf {var1 var2} (ctx : list (var1 * var2)) (R1 : block_rel var1) (R2 : block_rel var2) :=
      match R1, R2 with
      | local x1, local x2 => x1 = x2
      | input v1, input v2 => In (v1, v2) ctx
      | _, _ => False
      end.
  End __.
End block_rel. Abbreviation block_rel := block_rel.block_rel.

Module blocks_prog.
  Section __.
    Context `{params : datalog_params}.
    (*apparently works, just makes "Print Instances" act weird
    https://github.com/rocq-prover/rocq/issues/7342*)
    Remove Hints _rel : typeclass_instances.
    Context `{_lrel : lrelT}.

    Definition block var := program (relt := block_rel var).

    Inductive blocks_prog {var} :=
    | LetIn (x : blocks_prog) (f : var -> blocks_prog)
    (* | SetGlobal (x : gvar) (v : blocks_prog) *)
    (* note: probably i should let an input have type var or be a global.
     but i am ignoring globals for now.
     *)
    | Block (ret : lrel) (p : block var).
    Arguments blocks_prog : clear implicits.

    Definition inp_holds f :=
      match fact.rel f with
      | block_rel.input r => result.contains r f
      | block_rel.local _ => False
      end.

    Fixpoint interp (e : blocks_prog result) : result :=
      match e with
      | LetIn x f =>
          interp (f (interp x))
      | Block ret p =>
          result.of_facts (block_rel.local ret) (program.interp p inp_holds)
      end.

    Inductive wf {var1 var2} : list (var1 * var2) -> blocks_prog var1 -> blocks_prog var2 -> Prop :=
    | wf_LetIn ctx x1 x2 f1 f2 :
      wf ctx x1 x2 ->
      (forall x1' x2', wf ((x1', x2') :: ctx) (f1 x1') (f2 x2')) ->
      wf ctx (LetIn x1 f1) (LetIn x2 f2)
    | wf_Block ctx ret p1 p2 :
      program.wf (block_rel.wf ctx) p1 p2 ->
      wf ctx (Block ret p1) (Block ret p2).
  End __.
  Arguments blocks_prog {_ _ _ _} _.
End blocks_prog. Abbreviation blocks_prog := blocks_prog.blocks_prog.

Section Blocks.
  Context `{params : datalog_params}.
  Remove Hints _rel : typeclass_instances.
  Context `{_lrel : lrelT}.

  Lemma inv_vars_of_block_rel var (R : block_rel var) R0 :
    In R0 (block_rel.vars R) <-> R = block_rel.input R0.
  Proof. destruct R; simpl in *; intuition congruence. Qed.

  Definition vars_of_block {var} (p : blocks_prog.block var) := flat_map block_rel.vars (program.hyp_rels p).

  Lemma inv_vars_of_block var p (R : var) :
    In R (vars_of_block p) <-> (In (block_rel.input R) (program.hyp_rels p)).
  Proof.
    cbv [vars_of_block]. rewrite in_flat_map.
    setoid_rewrite inv_vars_of_block_rel. split; intros; fwd; eauto.
  Qed.

  Inductive flat_rel : Type :=
  | lvar_rel (block : nat) (name : lrel).

  Definition flat_program := program (relt := flat_rel).

  Definition flatten_rel (block : nat) (R : block_rel flat_rel) :=
    match R with
    | block_rel.local x => lvar_rel block x
    | block_rel.input x => x
    end.

  Fixpoint flatten (name : nat) (e : blocks_prog flat_rel) : nat * flat_rel * flat_program :=
    match e with
    | blocks_prog.LetIn x f =>
        let '(name', Rx, p2) := flatten name x in
        let '(name'', Rfx, p1) := flatten name' (f Rx) in
        (name'', Rfx, program.union p1 p2)
    | blocks_prog.Block ret p =>
        (S name, lvar_rel name ret, program.map_rel (flatten_rel name) p)
    end.

  Definition in_range lo hi x :=
    match x with
    | lvar_rel block_id _ => lo <= block_id < hi
    end.

  Lemma flatten_rel_inj name rs :
    (forall x, In (block_rel.input x) rs -> in_range O name x) ->
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

  Lemma in_nonoverlapping_ranges lo1 hi1 lo2 hi2 x :
    in_range lo1 hi1 x ->
    in_range lo2 hi2 x ->
    hi1 <= lo2 ->
    False.
  Proof. destruct x; simpl; auto. lia. Qed.

  Fixpoint valid_blocks_prog {var} (e : blocks_prog var) : Prop :=
    match e with
    | blocks_prog.LetIn x f =>
        valid_blocks_prog x /\ (forall v, valid_blocks_prog (f v))
    | blocks_prog.Block ret p =>
        program.meta_rules_valid p /\
          Forall block_rel.is_not_input (program.concl_rels p)
    end.

  Lemma inp_holds_doesnt_lie :
    fact.set_doesnt_lie blocks_prog.inp_holds.
  Proof.
    cbv [fact.set_doesnt_lie blocks_prog.inp_holds].
    intros mf Hmf. destruct (fact.rel _) eqn:E; [contradiction|].
    cbv [result.contains] in Hmf. fwd. cbv [meta_fact.consistent_with] in *.
    intros nf Hnf. rewrite Hmfp1 by assumption. cbv [fact.normal_subset].
    cbv [fact_pattern.matches] in Hnf. fwd. simpl. rewrite <- Hnfp0.
    simpl in E. cbv [meta_fact.rel] in E. rewrite E. reflexivity.
  Qed.

  Lemma wf_program_not_input {var1 var2} (ctx : list (var1 * var2)) p1 p2 :
    program.wf (block_rel.wf ctx) p1 p2 ->
    Forall block_rel.is_not_input (program.concl_rels p1) ->
    Forall block_rel.is_not_input (program.concl_rels p2).
  Proof.
    intros Hwf Hnoinp. rewrite Forall_forall in *. intros R HR.
    eapply Forall2_In_r in HR; [|apply (wf_program_concl_rels _ _ _ Hwf)].
    fwd. apply in_combine_l in HRp0. apply Hnoinp in HRp0.
    destruct x, R; cbn in *; auto.
  Qed.

  Lemma wf_program_vars_of_block_r {var1 var2} (ctx : list (var1 * var2)) p1 p2 :
    program.wf (block_rel.wf ctx) p1 p2 ->
    incl (vars_of_block p2) (map snd ctx).
  Proof.
    intros Hwf R HR. apply inv_vars_of_block in HR.
    eapply Forall2_In_r in HR; [|apply (wf_program_hyp_rels _ _ _ Hwf)].
    fwd. destruct x; try contradiction. eapply in_snd. eassumption.
  Qed.

  Lemma wf_program_input_in_ctx {var1 var2} (ctx : list (var1 * var2)) p1 p2 x :
    program.wf (block_rel.wf ctx) p1 p2 ->
    Forall block_rel.is_not_input (program.concl_rels p1) ->
    In (block_rel.input x) (program.all_rels p2) ->
    In x (map snd ctx).
  Proof.
    intros Hwf Hnoinp HR. cbv [program.all_rels] in HR. apply in_app_iff in HR.
    destruct HR as [HR|HR].
    - exfalso. pose proof (wf_program_not_input _ _ _ Hwf Hnoinp) as Hni.
      rewrite Forall_forall in Hni. apply Hni in HR. exact HR.
    - eapply wf_program_vars_of_block_r; [eassumption|]. apply inv_vars_of_block, HR.
  Qed.

  Hint Resolve in_fst in_snd : core.

  Lemma block_good_input_set (p : blocks_prog.block result) :
    Forall block_rel.is_not_input (program.concl_rels p) ->
    program.good_input_set p blocks_prog.inp_holds.
  Proof.
    intros Hconcl. split; [|exact inp_holds_doesnt_lie].
    intros f Hf Hin. rewrite Forall_forall in Hconcl. apply Hconcl in Hin.
    cbv [blocks_prog.inp_holds] in Hf. destruct (fact.rel f); simpl in *; contradiction.
  Qed.

  Lemma flat_good_input_set (ctx : list (result * flat_rel)) name (p : blocks_prog.block flat_rel) :
    Forall (in_range O name) (map snd ctx) ->
    NoDup (map snd ctx) ->
    Forall block_rel.is_not_input (program.concl_rels p) ->
    program.good_input_set (program.map_rel (flatten_rel name) p)
      (fun f => exists r, In (r, fact.rel f) ctx /\ result.contains r f).
  Proof.
    intros Hctx Hnd Hconcl. rewrite Forall_forall in Hctx, Hconcl. split.
    - intros f Hf Hin. fwd. rewrite concl_rels_map_program in Hin. apply in_map_iff in Hin. fwd.
      apply Hconcl in Hinp1. destruct x; [|contradiction]. simpl in Hinp0.
      apply in_snd, Hctx in Hfp0. rewrite <- Hinp0 in Hfp0. simpl in Hfp0. lia.
    - cbv [fact.set_doesnt_lie]. intros mf Hmf. fwd.
      cbv [result.contains] in Hmfp1. fwd. cbv [meta_fact.consistent_with fact.normal_subset] in *.
      intros nf Hnf. rewrite Hmfp1p1 by assumption. simpl.
      cbv [fact_pattern.matches] in Hnf. simpl in *. cbv [meta_fact.rel] in Hmfp0. fwd. split.
      + intros HR. exists r. split; [congruence | assumption].
      + intros (r0 & Hr0 & HR). replace r0 with r in HR; [assumption|].
        eapply NoDup_snd_In_inj; [eassumption | eassumption | congruence].
  Qed.

  Lemma flatten_correct' (ctx : list (result * flat_rel)) name e e0 name' Rret p :
    blocks_prog.wf ctx e e0 ->
    valid_blocks_prog e ->
    valid_blocks_prog e0 ->
    flatten name e0 = (name', Rret, p) ->
    Forall (in_range O name) (map snd ctx) ->
    NoDup (map snd ctx) ->
    name <= name' /\
      in_range name name' Rret /\
      Forall (in_range name name') (program.concl_rels p) /\
      Forall (fun R => in_range name name' R \/ In R (map snd ctx))
        (program.all_rels p) /\
      forall f,
        fact.rel f = Rret ->
        result.contains (blocks_prog.interp e) f <->
          program.interp p (fun f => exists r, In (r, fact.rel f) ctx /\ result.contains r f) f.
  Proof.
    intros Hwf Hvalid Hvalid0. revert name name' Rret p.
    induction Hwf;
      intros name name' Rret p0 Hflat Hctx1 Hctx2;
      simpl in Hflat;
      fwd;
      simpl.
    - simpl in Hvalid, Hvalid0. fwd.
      specialize (IHHwf ltac:(assumption) ltac:(assumption)). epose_dep IHHwf.
      specialize (IHHwf ltac:(eassumption) ltac:(eassumption) ltac:(assumption)).
      fwd.
      rename H0 into IH'. specialize (IH' (blocks_prog.interp x1)).
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
      + intros g Hg.
        rewrite program.stratify_iff.
        2: { apply program.stratified_of_disjoint. intros x H1 H2.
             rewrite Forall_forall in *.
             apply IH'p2 in H1. apply IHHwfp3 in H2. destruct H2 as [H2|H2].
             - eapply in_nonoverlapping_ranges. 1: exact H2. 1: exact H1. lia.
             - apply in_map_iff in H2. destruct H2 as [[? ?] H2]. fwd.
               specialize (Hctx1 _ ltac:(eauto)). simpl in H1.
               eapply in_nonoverlapping_ranges. 1: exact Hctx1. 1: exact H1. lia. }
        rewrite (IH'p4 g Hg).
        apply program.interp_hyp_ext_strong.
        { split; intros Hargs; simpl; fwd; exfalso.
          - destruct Hargsp0 as [Hargsp0|Hargsp0]; fwd.
            + rewrite Hg in IHHwfp1. eapply in_nonoverlapping_ranges; [exact IHHwfp1 | exact IH'p1 | lia].
            + rewrite Forall_forall in Hctx1. apply in_snd, Hctx1 in Hargsp0. rewrite Hg in Hargsp0.
              eapply in_nonoverlapping_ranges; [exact Hargsp0 | exact IH'p1 | lia].
          - apply program.interp_rel_of in Hargs. destruct Hargs as [Hargs|Hargs].
            + fwd. rewrite Forall_forall in Hctx1. apply in_snd, Hctx1 in Hargsp0. rewrite Hg in Hargsp0.
              eapply in_nonoverlapping_ranges; [exact Hargsp0 | exact IH'p1 | lia].
            + rewrite Forall_forall in IHHwfp2. apply IHHwfp2 in Hargs. rewrite Hg in Hargs.
              eapply in_nonoverlapping_ranges; [exact Hargs | exact IH'p1 | lia]. }
        intros f' HRf'. split; intros Hf'; fwd.
        -- simpl in Hf'p0. destruct Hf'p0 as [Hf'p0|Hf'p0].
           ++ fwd. apply IHHwfp4 in Hf'p1; [exact Hf'p1 | reflexivity].
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
              --- subst. simpl. eexists. split; eauto. apply IHHwfp4; auto.
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
      + intros g Hg. rewrite Forall_forall in Hctx1.
        rewrite (wf_fact_contains (fun x R => exists y, block_rel.wf ctx R y /\ flatten_rel name y = x)
                   _ g (fact.map_rel (fun _ => block_rel.local ret) g)).
        2: { apply wf_fact_map_rel_r. exists (block_rel.local ret). split; [reflexivity | simpl; congruence]. }
        rewrite result.contains_of_facts.
        2: { apply program.valid_impl_honest; [assumption|]. apply block_good_input_set. assumption. }
        2: { apply fact.rel_map_rel. }
        symmetry.
        eapply interp_wf_iff.
        -- apply wf_program_flip. eapply wf_program_comp; [eassumption | apply wf_program_map].
        -- apply Forall_forall. intros x _ R R' (y & Hy & <-) (y' & Hy' & Hx').
           cbv [map_rel] in *. subst.
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
           cbv [map_rel] in *. subst.
           destruct R as [l'|P'], y as [l0|z]; simpl in Hy; try contradiction;
             destruct y' as [l0'|z']; simpl in Hy'; try contradiction; simpl in *.
           ++ congruence.
           ++ exfalso. subst. apply in_snd, Hctx1 in Hy. simpl in Hy. lia.
        -- eapply meta_rules_valid_wf; [apply wf_program_map | | | exact Hmrv2].
           ++ apply Forall_forall. auto using functional_at_map.
           ++ apply inj_on_map, flatten_rel_inj. intros x Hx.
              rewrite Forall_forall in Hnoinp2. apply Hnoinp2 in Hx. contradiction.
        -- apply flat_good_input_set; try assumption. apply Forall_forall. assumption.
        -- intros g1 g2 Hg12. cbv [blocks_prog.inp_holds].
           pose proof (wf_fact_rel _ _ _ Hg12) as (y & Hy & Hx). rewrite <- Hx.
           destruct (fact.rel g2) as [l|P], y as [l0|z]; simpl in Hy; try contradiction; simpl.
           ++ split; [intros (R & HR & HR') | intros []].
              apply in_snd, Hctx1 in HR. simpl in HR. lia.
           ++ split.
              ** intros (R & HR & HR'). replace P with R; [|eapply NoDup_snd_In_inj; eassumption].
                 apply (wf_fact_contains _ _ _ _ Hg12), HR'.
              ** intros HP. exists P. split; [exact Hy|]. apply (wf_fact_contains _ _ _ _ Hg12), HP.
        -- apply wf_fact_map_rel_r. eexists (block_rel.local _). split; [reflexivity | ].
           cbv [map_rel]. simpl. congruence.
  Qed.
End Blocks.

Ltac interp_exprs :=
  repeat match goal with
    | |- program.interp _ _ (fact.normal {| normal_fact.rel := block_rel.input _;
                                           normal_fact.args := _ |}) =>
        apply pftree.leaf
    | |- program.interp _ _ (fact.meta {| meta_fact.pattern :=
                                           {| fact_pattern.rel := block_rel.input _;
                                             fact_pattern.args := _ |};
                                         meta_fact.set := _ |}) =>
        apply pftree.leaf
    | _ => progress Datalog.interp_exprs
    | _ => (doExists 0 + doExists 1); split; [reflexivity|]
    end.
