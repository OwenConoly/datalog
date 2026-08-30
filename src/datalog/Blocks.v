From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.

From Datalog Require Import Map Tactics Fp List Datalog RelMap.
From GraphSearch Require Import Dag.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List Datatypes.Option Eqb.

Import ListNotations.

Section Blocks.
  Context {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.
  Context {lvar : Type}.

  Inductive block_rel :=
  | local (_ : lvar)
  | input (_ : lvar).

  Definition block_rule := rule (rel := block_rel).

  Inductive blocks_prog {var} :=
  | LetIn (x : blocks_prog) (f : var -> blocks_prog)
  (* | SetGlobal (x : gvar) (v : blocks_prog) *)
  (* why the inputs nonsense?  because---to give meta-rules correct semantics---
     we need to be able to distinguish between different relations that have the
     same denotation.  mapping them to different lvars achieves this.

     an alternative solution would be: instead of defining interp_blocks_prog with
     var := fact_args -> Prop, instead do var := nat, or maybe
     var := nat * (fact_args -> Prop).
     but i do not want to deal with that.

     we should have NoDup (map fst inputs).

     note: probably i should let an input have type var or be a global.
     but i am ignoring globals for now.
   *)
  | Block (ret : lvar) (inputs : list (lvar * var)) (p : list block_rule).
  Arguments blocks_prog : clear implicits.

  Context (lvar1 lvar2 : lvar).
  Context (p1 p2 : list block_rule).
  Print fact_args.
  Print fact.
  Definition example {var} : @blocks_prog var :=
    LetIn (Block lvar1 [] p1) (fun val =>
                                Block lvar1 [(lvar2, val)] p2).

  Fixpoint interp_blocks_prog (e : blocks_prog (fact_args -> Prop)) : fact_args -> Prop :=
    match e with
    | LetIn x f =>
        interp_blocks_prog (f (interp_blocks_prog x))
    | Block ret inputs p =>
        fun args =>
          prog_impl p
            (fun f => Exists (fun '(R, R') => input R = rel_of f /\ R' (args_of f)) inputs)
            (fact_of (local ret) args)
    end.

  Inductive wf_blocks_prog {var1 var2} : list (var1 * var2) -> blocks_prog var1 -> blocks_prog var2 -> Prop :=
  | wf_LetIn ctx x1 x2 f1 f2 :
    wf_blocks_prog ctx x1 x2 ->
    (forall x1' x2', wf_blocks_prog ((x1', x2') :: ctx) (f1 x1') (f2 x2')) ->
    wf_blocks_prog ctx (LetIn x1 f1) (LetIn x2 f2)
  | wf_Block ctx ret inps1 inps2 p :
    Forall2 (fun '(x1, R1) '(x2, R2) => x1 = x2 /\ In (R1, R2) ctx) inps1 inps2 ->
    wf_blocks_prog ctx (Block ret inps1 p) (Block ret inps2 p).

  (*TODO try out (var -> Prop) instead of (list var) ??*)
  Inductive vars_in {var} : list var -> blocks_prog var -> Prop :=
  | vars_in_LetIn ctx x f :
    vars_in ctx x ->
    (forall x', vars_in (x' :: ctx) (f x')) ->
    vars_in ctx (LetIn x f)
  | vars_in_Block ctx ret inps p :
    Forall (fun '(_, R) => In R ctx) inps ->
    vars_in ctx (Block ret inps p).

  Lemma vars_in_incl var (ctx1 ctx2 : list var) (p : blocks_prog var) :
    incl ctx1 ctx2 ->
    vars_in ctx1 p ->
    vars_in ctx2 p.
  Proof.
    intros Hincl Hvars. revert ctx2 Hincl.
    induction Hvars; intros; constructor; auto with incl.
    eapply Forall_impl; [|eassumption]. intros [? ?]. auto with incl.
  Qed.


  Inductive flat_rel : Type :=
  (* | input_rel (block : nat) (name : lvar) *)
  | false_rel
  | lvar_rel (block : nat) (name : lvar).

  Context {relmap : map.map lvar flat_rel} {relmap_ok : map.ok relmap}.
  Context {lvar_eqb : Eqb lvar} {lvar_eqb_ok : Eqb_ok lvar_eqb}.

  Definition flatten_rel (block : nat) (m : relmap) (R : block_rel) :=
    match R with
    | local x => lvar_rel block x
    | input x => match map.get m x with
                | Some R => R
                | None => false_rel
                end
    end.

  Fixpoint flatten (name : nat) (e : blocks_prog flat_rel) : nat * flat_rel * list rule :=
    match e with
    | LetIn x f =>
        let '(name', Rx, p2) := flatten name x in
        let '(name'', Rfx, p1) := flatten name' (f Rx) in
        (name'', Rfx, p1 ++ p2)
    | Block ret inputs p =>
        let p' := map (map_rule_rels (flatten_rel name (map.of_list inputs))) p in
        (S name, lvar_rel name ret, p')
    end.

  Definition in_range lo hi x :=
    match x with
    | lvar_rel block_id _ => lo <= block_id < hi
    | false_rel => False
    end.

  Definition not_as_big_as hi x :=
    match x with
    | lvar_rel block_id _ => block_id < hi
    | false_rel => False
    end.

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

  Definition is_not_input R :=
    match R with
    | local _ => True
    | input _ => False
    end.

  Fixpoint valid_blocks_prog {var} (e : blocks_prog var) : Prop :=
    match e with
    | LetIn x f =>
        valid_blocks_prog x /\ (forall v, valid_blocks_prog (f v))
    | Block ret inputs p =>
        meta_rules_valid p /\
          NoDup (map fst inputs) /\
          Forall is_not_input (flat_map concl_rels p)
    end.

  Lemma valid_blocks_prog_LetIn {var : Type} (x : blocks_prog var) (f : var -> blocks_prog var) :
    valid_blocks_prog (LetIn x f) = (valid_blocks_prog x /\ forall v, valid_blocks_prog (f v)).
  Proof. reflexivity. Qed.

  Hint Constructors vars_in : core.

  Lemma interp_blocks_prog_honest ctx (e : blocks_prog (fact_args -> Prop)) :
    valid_blocks_prog e ->
    vars_in ctx e ->
    Forall honest_args ctx ->
    honest_args (interp_blocks_prog e).
  Proof.
    intros Hvalid. induction 1; intros Hctx; simpl.
    - simpl in Hvalid. fwd. eauto.
    - simpl in Hvalid. fwd.
      simpl. apply doesnt_lie_honest_args.
      eapply valid_impl_honest; eauto.
      split.
      + intros f_target Hf_target.
        apply Exists_exists in Hf_target. fwd.
        rewrite <- Hf_targetp1p0. intros H'. rewrite Forall_forall in Hvalidp2.
        apply Hvalidp2 in H'. apply H'.
      + cbv [doesnt_lie consistent].
        intros mf_rel mf_args mf_set Hmf nf_args Hmatch.
        apply Exists_exists in Hmf. fwd. simpl in *. subst.
        rewrite Forall_forall in H.
        specialize (H _ ltac:(eassumption)). simpl in H.
        assert (honest_args P) as Hhonest_P.
        { rewrite Forall_forall in Hctx. apply Hctx. assumption. }
        cbv [honest_args args_consistent] in Hhonest_P.
        rewrite Hhonest_P by eassumption.
        split; intros H'.
        ** apply Exists_exists. eexists (_, _). simpl. eauto.
        ** apply Exists_exists in H'. destruct H' as [[R0 R0'] [Hin0 [Hrel0 Hargs0]]].
           simpl in Hrel0. fwd.
           assert (P = R0').
           { eapply NoDup_fst_In_inj; eassumption. }
           subst R0'. exact Hargs0.
  Qed.

  Lemma blocks_prog_impl_mf_ext (e : blocks_prog (fact_args -> Prop)) mf_args mf_set mf_set' :
    interp_blocks_prog e (meta_fact_args mf_args mf_set) ->
    (forall nf_args,
        Forall2 matches mf_args nf_args ->
        mf_set nf_args <-> mf_set' nf_args) ->
    interp_blocks_prog e (meta_fact_args mf_args mf_set').
  Proof.
    revert mf_args mf_set mf_set'.
    induction e; intros mf_args mf_set mf_set' Himpl Hext.
    - simpl in *. eauto.
    - simpl in *.
      eapply prog_impl_mf_ext'; [exact Himpl | exact Hext |].
      intro H_Q. apply Exists_exists in H_Q. fwd. discriminate.
  Qed.

  Lemma use_valid_blocks_prog ctx p mf_args mf_set :
    valid_blocks_prog p ->
    vars_in ctx p ->
    Forall honest_args ctx ->
    interp_blocks_prog p (meta_fact_args mf_args mf_set) ->
    interp_blocks_prog p (meta_fact_args mf_args (fun args => interp_blocks_prog p (normal_fact_args args))).
  Proof.
    intros.
    eapply blocks_prog_impl_mf_ext; [eassumption|].
    intros. eapply interp_blocks_prog_honest; [|try eassumption..]. assumption.
  Qed.

  Lemma wf_blocks_prog_vars_in {var1 var2} (x : var2) (ctx : list (var1 * var2)) (p : blocks_prog var1) (p' : blocks_prog var2) :
    wf_blocks_prog ctx p p' ->
    vars_in (map fst ctx) p.
  Proof.
    induction 1; simpl in *; eauto.
    constructor. eapply Forall_impl.
    2: { eapply Forall2_forget_r. eassumption. }
    simpl. intros [? ?] ?. fwd. eapply in_fst. eassumption.
  Qed.

  Hint Resolve in_fst in_snd : core.
  Lemma flatten_correct' ctx name e e0 name' Rret p :
    wf_blocks_prog ctx e e0 ->
    valid_blocks_prog e ->
    flatten name e0 = (name', Rret, p) ->
    Forall (in_range O name) (map snd ctx) ->
    NoDup (map snd ctx) ->
    Forall honest_args (map fst ctx) ->
    name <= name' /\
      in_range name name' Rret /\
      Forall (in_range name name') (flat_map concl_rels p) /\
      Forall (fun R => in_range name name' R \/ In R (map snd ctx) \/ R = false_rel) (flat_map all_rels p) /\
      forall args,
        interp_blocks_prog e args <->
          prog_impl p (fun f => exists R, In (R, rel_of f) ctx /\ R (args_of f))
            (fact_of Rret args).
  Proof.
    intros Hwf Hvalid. revert name name' Rret p.
    induction Hwf;
      intros name name' Rret p0 Hflat Hctx1 Hctx2 Hctx3;
      simpl in Hflat;
      fwd;
      simpl.
    - simpl in Hvalid. fwd.
      specialize (IHHwf ltac:(assumption)). epose_dep IHHwf.
      specialize (IHHwf ltac:(eassumption) ltac:(eassumption) ltac:(assumption) ltac:(eassumption)).
      fwd.
      rename H0 into IH'. specialize (IH' (interp_blocks_prog x1)).
      epose_dep IH'. specialize (IH' ltac:(eauto)). epose_dep IH'.
      specialize (IH' ltac:(eassumption)). specialize' IH'.
      { constructor.
        - eapply in_range_weaken; [eassumption| |]; lia.
        - eapply Forall_impl; [|eassumption].
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
      + rewrite flat_map_app. apply Forall_app.
        eauto 10 using Forall_impl, in_range_weaken.
      + rewrite flat_map_app. apply Forall_app. split.
        -- eapply Forall_impl; [|eassumption]. simpl.
           intros R [HR| [[HR|HR]|HR]]; subst; eauto using in_range_weaken.
        -- eapply Forall_impl; [|eassumption]. simpl.
           intros R [HR|HR]; eauto using in_range_weaken.
      + intros args.
        rewrite staged_program_iff.
        2: { intros x H1 H2. rewrite Forall_forall in *.
             apply IH'p2 in H1. apply IHHwfp3 in H2. destruct H2 as [H2|[H2|H2]].
             - eapply in_nonoverlapping_ranges. 1: exact H2. 1: exact H1. lia.
             - apply in_map_iff in H2. destruct H2 as [[? ?] H2]. fwd.
               specialize (Hctx1 _ ltac:(eauto)). simpl in H1.
               eapply in_nonoverlapping_ranges. 1: exact Hctx1. 1: exact H1. lia.
             - subst. cbv [in_range] in H1. contradiction. }
        rewrite IH'p4.
        apply prog_impl_hyp_ext_strong.
        { split; intros Hargs; simpl; fwd; exfalso.
          - destruct Hargsp0 as [Hargsp0|Hargsp0]; fwd.
            + apply IHHwfp4 in Hargsp1. rewrite fact_of_rel_of_args_of in Hargsp1.
              apply prog_impl_rel_of in Hargsp1. destruct Hargsp1 as [Hargsp1|Hargsp1].
              -- fwd. rewrite rel_of_fact_of in Hargsp1p0.
                 rewrite Forall_forall in Hctx1. apply in_snd in Hargsp1p0.
                 apply Hctx1 in Hargsp1p0.
                 eauto using in_nonoverlapping_ranges.
              -- rewrite rel_of_fact_of in Hargsp1.
                 rewrite Forall_forall in IHHwfp2.
                 apply IHHwfp2 in Hargsp1.
                 eauto using in_nonoverlapping_ranges.
            + rewrite rel_of_fact_of in Hargsp0.
              rewrite Forall_forall in Hctx1. apply in_snd in Hargsp0.
              apply Hctx1 in Hargsp0.
              eauto using in_nonoverlapping_ranges.
          - apply prog_impl_rel_of in Hargs. destruct Hargs as [Hargs|Hargs].
            + fwd. rewrite rel_of_fact_of in Hargsp0.
              rewrite Forall_forall in Hctx1. apply in_snd in Hargsp0.
              apply Hctx1 in Hargsp0.
              eauto using in_nonoverlapping_ranges.
            + rewrite rel_of_fact_of in Hargs.
              rewrite Forall_forall in IHHwfp2.
              apply IHHwfp2 in Hargs.
              eauto using in_nonoverlapping_ranges. }
        intros f' HRf'. split; intros Hf'; fwd.
        -- simpl in Hf'p0. destruct Hf'p0 as [Hf'p0|Hf'p0].
           ++ fwd. rewrite IHHwfp4 in Hf'p1 by eassumption.
              rewrite fact_of_rel_of_args_of in Hf'p1. exact Hf'p1.
           ++ apply prog_impl_leaf. eauto.
        -- pose proof Hf' as Hf''.
           apply prog_impl_rel_of in Hf'. destruct Hf' as [Hf'|Hf'].
           ++ fwd. simpl. eauto.
           ++ rewrite Forall_forall in IH'p3.
              eapply incl_flat_map_strong in HRf'.
              2: { apply incl_refl. }
              2: { intros. Search hyp_rels. apply hyp_rels_incl_all_rels. }
              apply IH'p3 in HRf'.
              rewrite Forall_forall in IHHwfp2. apply IHHwfp2 in Hf'.
              destruct HRf' as [HRf'|HRf'].
              { exfalso. eauto using in_nonoverlapping_ranges. }
              simpl in HRf'. destruct HRf' as [[HRf'|HRf']|HRf'].
              --- subst. simpl. eexists. split; eauto. apply IHHwfp4.
                  rewrite fact_of_rel_of_args_of. assumption.
              --- apply in_map_iff in HRf'. destruct HRf' as [[? ?] HRf'].
                  simpl in HRf'. fwd.
                  rewrite Forall_forall in Hctx1.
                  apply in_snd in HRf'p1. apply Hctx1 in HRf'p1.
                  exfalso. eauto using in_nonoverlapping_ranges.
              --- apply prog_impl_rel_of in Hf''. destruct Hf'' as [Hf''|Hf''].
                  { fwd. simpl. eauto. }
                  exfalso. rewrite HRf' in Hf''. apply IHHwfp2 in Hf''.
                  simpl in Hf''. contradiction.
    - simpl in Hvalid.
      eassert (inps_eq : map fst _ = map fst _).
      { apply Forall2_eq_eq. rewrite <- Forall2_map_l, <- Forall2_map_r.
        eapply Forall2_impl; [eassumption|]. intros (?, ?) (?, ?) ?. fwd. reflexivity. }
      ssplit.
      + lia.
      + lia.
      + simpl. lia.
      + apply Forall_flat_map. apply List.Forall_map. apply Forall_forall.
        intros r Hr. rewrite concl_rels_map_rule_rels. apply List.Forall_map.
        fwd. apply Forall_forall. intros R HR. destruct R.
        2: { exfalso. rewrite Forall_forall in Hvalidp2.
             eapply (Hvalidp2 (input _)). apply in_flat_map. eauto. }
        simpl. lia.
      + apply Forall_flat_map. apply List.Forall_map. apply Forall_forall.
        intros r Hr. rewrite all_rels_map_rule_rels. apply List.Forall_map.
        apply Forall_forall. intros R HR.
        destruct R; try solve [simpl; auto]. simpl.
        destruct (map.get _ _) eqn:E; simpl.
        -- apply of_list_Some_in in E.
           apply Forall2_forget_l in H. rewrite Forall_forall in H.
           apply H in E. destruct E as [[? ?] ?]. fwd. eauto.
        -- auto.
      + intros args. erewrite prog_impl_map_rule_rels_iff with (f := flatten_rel _ _).
        -- rewrite map_fact_fact_of. simpl. apply prog_impl_hyp_ext_strong.
           ++ split; intros H'; fwd.
              --- apply Exists_exists in H'p1. fwd.
                  apply Forall2_forget_r in H. rewrite Forall_forall in H.
                  specialize (H _ ltac:(eassumption)). fwd.
                  rewrite Forall_forall in Hctx1. apply in_snd in Hp1p1.
                  specialize (Hctx1 _ ltac:(eassumption)).
                  simpl in Hctx1.
                  assert (H_rel : rel_of (fact_of (lvar_rel name ret) args) = rel_of (map_fact (flatten_rel name (map.of_list inps2)) f)) by congruence.
                  rewrite rel_of_fact_of, rel_of_map_fact in H_rel.
                  rewrite <- H'p1p1p0 in H_rel.
                  cbv [flatten_rel] in H_rel.
                  erewrite map.get_of_list_In_NoDup in H_rel; try eassumption.
                  2: { rewrite <- inps_eq. assumption. }
                  rewrite <- H_rel in Hp1p1.
                  destruct f0; simpl in Hctx1; try contradiction.
                  fwd.
                  lia.
              --- rewrite rel_of_fact_of in H'p0. rewrite args_of_fact_of in H'p1.
                  rewrite Forall_forall in Hctx1. apply in_snd in H'p0.
                  specialize (Hctx1 _ ltac:(eassumption)). simpl in Hctx1. lia.
           ++ intros f'. split; intros H'; fwd.
              --- rewrite rel_of_map_fact, args_of_map_fact.
                  apply Exists_exists in H'p1. fwd. apply Forall2_forget_r in H.
                  rewrite Forall_forall in H. apply H in H'p1p0. fwd.
                  rewrite <- H'p1p1p0. simpl.
                  erewrite map.get_of_list_In_NoDup; try eassumption.
                  2: { rewrite <- inps_eq. assumption. }
                  eauto.
              --- rewrite Forall_forall in Hctx1.
                  specialize (Hctx1 _ ltac:(eauto)).
                  simpl in Hctx1.
                  rewrite <- (fact_of_rel_of_args_of f').
                  destruct (rel_of f'); simpl in Hctx1; try contradiction.
                  rewrite in_flat_map in *. fwd. rewrite in_map_iff in *. fwd.
                  rewrite hyp_rels_map_rule_rels in *. rewrite in_map_iff in *.
                  fwd.
                  eexists (fact_of _ _). rewrite map_fact_fact_of.
                  rewrite H0p1p0. split; [reflexivity|].
                  match goal with
                  | H: flatten_rel _ _ ?x = lvar_rel _ _ |- _ => destruct x; simpl in H
                  end.
                  { fwd. lia. }
                  destruct (map.get _ _) eqn:E; subst; try discriminate.
                  apply of_list_Some_in in E.
                  apply Forall2_forget_l in H. rewrite Forall_forall in H.
                  specialize (H _ ltac:(eassumption)). destruct H as [(?, ?) H].
                  fwd.
                  epose proof NoDup_snd_In_inj as H'.
                  specialize (H' _ _ _ _ ltac:(eassumption) Hp2 H'p0). subst.
                  rewrite rel_of_fact_of, args_of_fact_of.
                 apply Exists_exists. eexists (_, _). eauto.
        -- fwd. assumption.
        -- intros f Hf. apply Exists_exists in Hf. fwd. rewrite <- Hfp1p0.
           rewrite Forall_forall in Hvalidp2. intros H'. eapply (Hvalidp2 (input _)).
           eassumption.
        -- cbv [doesnt_lie]. intros mf_rel mf_args mf_set Hmf.
           apply Exists_exists in Hmf. fwd. simpl in *. subst.
           cbv [consistent]. intros nf_args Hnf_args.
           apply Forall2_forget_r in H. rewrite Forall_forall in H.
           specialize (H _ ltac:(eassumption)). fwd. rewrite Forall_forall in Hctx3.
           specialize (Hctx3 _ ltac:(eauto)).
           cbv [honest_args args_consistent] in Hctx3. rewrite Hctx3 by eassumption.
           simpl. split; intros Hnf_args'.
           ++ apply Exists_exists. eexists (_, _). eauto.
           ++ apply Exists_exists in Hnf_args'. fwd.
              eapply NoDup_fst_In_inj in Hnf_args'p0. 3: exact Hmfp0.
              2: assumption. subst. assumption.
        -- eenough _ as H'.
           { intros f1 f2 Hfs. epose proof (H' f1 f2 Hfs) as H1. split; [exact H1|].
             apply H'. symmetry. assumption. }

           intros f1 f2 Hequiv Hf1. apply Exists_exists in Hf1. fwd.
           cbv [fact_equiv] in Hequiv. do 2 rewrite map_fact_eq_fact_of in Hequiv.
           apply fact_of_inj in Hequiv. fwd. rewrite <- Hf1p1p0 in Hequivp0.
           pose proof H as H0.
           apply Forall2_forget_r in H. rewrite Forall_forall in H.
           specialize (H _ ltac:(eassumption)). fwd. simpl in Hequivp0.
           erewrite map.get_of_list_In_NoDup in Hequivp0; try eassumption.
           2: { rewrite <- inps_eq. assumption. }
           subst. clear Hp0. rewrite Forall_forall in Hctx1.
           specialize (Hctx1 _ ltac:(eauto)).
           destruct (rel_of f2); simpl in Hctx1, Hp1p1. 1: lia.
           destruct (map.get _ _) eqn:E.
           2: { simpl in Hctx1. contradiction. }
           apply of_list_Some_in in E.
           apply Forall2_forget_l in H0. rewrite Forall_forall in H0.
           apply H0 in E. destruct E as [[? ?] ?]. fwd. apply Exists_exists.
           eexists (_, _). split; [exact Hp0|]. split; [reflexivity|].
           eapply NoDup_snd_In_inj in Hp2. 3: exact Hp1p1. 2: assumption.
           subst. rewrite <- Hequivp1. assumption.
        -- fwd. apply Forall_forall. intros R HR. destruct R.
           2: { exfalso. rewrite Forall_forall in Hvalidp2.
                eapply (Hvalidp2 (input _)). eassumption. }
           cbv [injective_on]. simpl. intros R' HR'.
           destruct R'; simpl in HR'; fwd; auto. exfalso.
           apply of_list_Some_in in E. apply Forall2_forget_l in H.
           rewrite Forall_forall in H. apply H in E. destruct E as [[? ?] ?]. fwd.
           rewrite Forall_forall in Hctx1. specialize (Hctx1 _ ltac:(eauto)).
           simpl in Hctx1. lia.
        -- rewrite rel_of_fact_of.
           cbv [injective_on]. simpl. intros R' HR'.
           destruct R'; simpl in HR'; fwd; auto. exfalso.
           apply of_list_Some_in in E. apply Forall2_forget_l in H.
           rewrite Forall_forall in H. apply H in E. destruct E as [[? ?] ?]. fwd.
           rewrite Forall_forall in Hctx1. specialize (Hctx1 _ ltac:(eauto)).
           simpl in Hctx1. lia.
  Qed.
End Blocks.

Arguments blocks_prog {_ _ _ _} _.
Arguments block_rel : clear implicits.

Ltac interp_exprs :=
  repeat match goal with
    | |- prog_impl _ _ (normal_fact (input _) _) =>
        apply prog_impl_leaf
    | |- prog_impl _ _ (meta_fact (input _) _ _) =>
        apply prog_impl_leaf
    | _ => progress Datalog.interp_exprs
    | _ => (doExists 0 + doExists 1); split; [reflexivity|]
    end.
