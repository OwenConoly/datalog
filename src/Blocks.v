From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.

From Datalog Require Import Map Tactics Fp List Dag Datalog.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List Datatypes.Option.

Import ListNotations.

Definition paired {U1 U2} (P : U1 -> U2 -> Prop) x1 x2 :=
  (forall x2', P x1 x2' -> x2' = x2) /\ (forall x1', P x1' x2 -> x1' = x1).

Definition one_to_one {U1 U2} (P : U1 -> U2 -> Prop) R1 R2 x1 :=
  R1 x1 /\
    forall x2,
      P x1 x2 ->
      R2 x2 ->
      (forall x2', P x1 x2' -> R2 x2' -> x2' = x2) /\ (forall x1', P x1' x2 -> R1 x1' -> x1' = x1).

Definition fun_rel {U1 U2} (f : U1 -> U2) x y := f x = y.

Lemma Forall2_eq_map {A B} (f : B -> A) (l1 : list A) (l2 : list B) :
  Forall2 (fun_rel f) l2 l1 <-> l1 = map f l2.
Proof.
  split.
  - induction 1; simpl; congruence.
  - intros ->. induction l2; constructor; reflexivity || assumption.
Qed.

Section Blocks.
  Context {lvar gvar exprvar fn aggregator T : Type}.
  Context {sig : signature fn aggregator T}.
  Context {gmap : map.map gvar (fact_args T -> Prop)} {gmap_ok : map.ok gmap}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.

  Variant blocks_rel {var} :=
    | local (x : lvar)
    | global (x : gvar)
    | Var (x : var).
  Arguments blocks_rel : clear implicits.

  Definition block_rule var :=
    rule (blocks_rel var) exprvar fn aggregator.

  Inductive blocks_prog {var} :=
  | LetIn (x : blocks_prog) (f : var -> blocks_prog)
  (* | SetGlobal (x : gvar) (v : blocks_prog) *)
  | Block (ret : lvar) (p : list (block_rule var)).
  Arguments blocks_prog : clear implicits.

  Section well_formed.
    Context {var1 var2 : Type} {rel1 rel2 : Type}.
    Section with_ctx.
      Context (wf_rel : rel1 -> rel2 -> Prop).

      Inductive wf_clause : clause rel1 exprvar fn -> clause rel2 exprvar fn -> Prop :=
      | wf_clause_intro R1 R2 args :
        wf_rel R1 R2 ->
        wf_clause {| clause_rel := R1; clause_args := args |} {| clause_rel := R2; clause_args := args |}.

      Inductive wf_meta_clause : meta_clause rel1 exprvar fn -> meta_clause rel2 exprvar fn -> Prop :=
      | wf_meta_clause_intro R1 R2 args :
        wf_rel R1 R2 ->
        wf_meta_clause {| meta_clause_rel := R1; meta_clause_args := args |} {| meta_clause_rel := R2; meta_clause_args := args |}.

      Inductive wf_rule : rule rel1 exprvar fn aggregator -> rule rel2 exprvar fn aggregator -> Prop :=
      | wf_normal_rule concls1 concls2 hyps1 hyps2 :
        Forall2 wf_clause concls1 concls2 ->
        Forall2 wf_clause hyps1 hyps2 ->
        wf_rule (normal_rule concls1 hyps1) (normal_rule concls2 hyps2)
      | wf_meta_rule concls1 concls2 hyps1 hyps2 :
        Forall2 wf_meta_clause concls1 concls2 ->
        Forall2 wf_meta_clause hyps1 hyps2 ->
        wf_rule (meta_rule concls1 hyps1) (meta_rule concls2 hyps2)
      | wf_agg_rule R1 R2 R1' R2' a :
        wf_rel R1 R2 ->
        wf_rel R1' R2' ->
        wf_rule (agg_rule R1 a R1') (agg_rule R2 a R2').

      Definition wf_fact (f1 : fact rel1 T) (f2 : fact rel2 T) : Prop :=
        wf_rel (rel_of f1) (rel_of f2) /\ args_of f1 = args_of f2.
      Hint Unfold wf_fact : core.

      Ltac invs :=
        repeat match goal with
          | H: wf_fact (normal_fact _ _) ?f |- _ =>
              destruct H as [? ?];
              destruct f;
              simpl in *;
              [fwd|congruence];
              subst
          | H: wf_fact (meta_fact _ _ _) ?f |- _ =>
              destruct H as [? ?];
              destruct f;
              simpl in *;
              [congruence|fwd];
              subst
          end.

      Lemma interp_clause_wf s (c1 : clause rel1 _ _) (c2 : clause rel2 _ _) f1 :
        wf_clause c1 c2 ->
        interp_clause s c1 f1 ->
        exists f2,
          interp_clause (context := context) s c2 f2 /\
            wf_fact f1 f2.
      Proof.
        cbv [interp_clause]. invert 1. intros.
        fwd. simpl in *. eauto 7.
      Qed.

      Lemma Forall2_interp_clause_wf ctx0 cs1 cs2 fs1 :
        Forall2 wf_clause cs1 cs2 ->
        Forall2 (interp_clause ctx0) cs1 fs1 ->
        exists fs2,
          Forall2 (interp_clause ctx0) cs2 fs2 /\
            Forall2 wf_fact fs1 fs2.
      Proof.
        intros Hwf Hinterp. revert cs2 Hwf.
        induction Hinterp; intros cs2 Hwf; invert Hwf.
        - eauto.
        - edestruct @interp_clause_wf as [f2 [Hinterp2 Hwf_f]]; eauto.
          edestruct IHHinterp as [fs2 [Hinterp_fs2 Hwf_fs]]; eauto.
      Qed.

      Lemma wf_non_meta_rule_impl r1 r2 R1 args hyps1 :
        wf_rule r1 r2 ->
        non_meta_rule_impl r1 R1 args hyps1 ->
        exists R2 hyps2,
          non_meta_rule_impl r2 R2 args hyps2 /\
            wf_rel R1 R2 /\
            Forall2 wf_fact hyps1 hyps2.
      Proof.
        intros Hwf Himpl.
        destruct r1, r2; invert Himpl; invert Hwf; repeat invert_stuff.
        - rewrite Exists_exists in *. fwd. apply Forall2_forget_r in H3.
          rewrite Forall_forall in H3. specialize (H3 _ ltac:(eassumption)).
          fwd. eapply interp_clause_wf in H1p1; eauto. fwd. invs.
          edestruct @Forall2_interp_clause_wf as [hyps2 [Hinterp2 Hwf_hyps]]; eauto.
          do 2 eexists. ssplit.
          + econstructor.
            -- apply Exists_exists. eauto.
            -- eassumption.
          + assumption.
          + assumption.
        - do 2 eexists.
          ssplit; eauto.
          constructor; simpl; eauto.
          rewrite <- Forall2_map_l, <- Forall2_map_r.
          apply Forall2_same.
          apply Forall_forall.
          intros [? ?] _. eauto.
      Qed.

      Lemma interp_meta_clause_wf s c1 c2 f1 :
        wf_meta_clause c1 c2 ->
        interp_meta_clause s c1 f1 ->
        exists f2, interp_meta_clause s c2 f2 /\ wf_fact f1 f2.
      Proof.
        cbv [interp_meta_clause]. invert 1. simpl. intros. fwd.
        eexists. split; eauto. constructor; simpl; auto.
      Qed.

      Lemma Forall2_interp_meta_clause_wf ctx0 cs1 cs2 fs1 :
        Forall2 wf_meta_clause cs1 cs2 ->
        Forall2 (interp_meta_clause ctx0) cs1 fs1 ->
        exists fs2, Forall2 (interp_meta_clause ctx0) cs2 fs2 /\ Forall2 wf_fact fs1 fs2.
      Proof.
        intros Hwf Hinterp. revert cs2 Hwf.
        induction Hinterp; intros cs2 Hwf; invert Hwf.
        - eauto.
        - edestruct @interp_meta_clause_wf as [f2 [Hinterp2 Hwf_f]]; eauto.
          edestruct IHHinterp as [fs2 [Hinterp_fs2 Hwf_fs]]; eauto.
      Qed.

      Lemma wf_meta_cond_iff' fact_supported1 fact_supported2 p1 p2 (R1 : rel1) (R2 : rel2) args'' hyps1 hyps2 :
        Forall2 wf_rule p1 p2 ->
        wf_rel R1 R2 ->
        (forall R2', wf_rel R1 R2' -> In R2' (flat_map concl_rels p2) -> R2 = R2') ->
        Forall2 wf_fact hyps1 hyps2 ->
        (forall f1 f2,
            Forall2 wf_fact hyps1 hyps2 ->
            wf_fact f1 f2 ->
            fact_supported1 hyps1 f1 ->
            fact_supported2 hyps2 f2) ->
        one_step_derives0 fact_supported1 p1 hyps1 R1 args'' ->
        one_step_derives0 fact_supported2 p2 hyps2 R2 args''.
      Proof.
        intros H1 H2 HR2 H3 Hfs.
        cbv [one_step_derives0]. intros H. fwd.
        apply Forall2_forget_r in H1. rewrite Forall_forall in H1.
        apply H1 in Hp0. fwd.
        edestruct wf_non_meta_rule_impl as [R2' [hyps2'' [Himpl [Hrel Hhyps]]]]; eauto.
        apply HR2 in Hrel.
        2: { apply in_flat_map. eexists. split; [eassumption|].
             eapply non_meta_rule_impl_concl_relname_in.
             eassumption. }
        subst.
        do 2 eexists. split; [eassumption|]. split; [eassumption|].
        apply Forall2_forget_l in Hhyps.
        rewrite Forall_forall in Hhyps, Hp2. rewrite Forall_forall.
        intros f' Hf'. specialize (Hhyps _ Hf'). fwd. specialize (Hp2 _ Hhypsp0).
        eauto.
      Qed.
    End with_ctx.

    Section map.
      Context (f : rel1 -> rel2).
      Definition map_clause_rel (c : clause rel1 exprvar fn) :=
        {| clause_rel := f c.(clause_rel);
          clause_args := c.(clause_args) |}.

      Ltac t :=
        repeat match goal with
          | |- _ => progress (intros; simpl)
          | |- wf_clause _ ?x _ => is_var x; destruct x
          | |- wf_meta_clause _ ?x _ => is_var x; destruct x
          | |- wf_rule _ ?x _ => is_var x; destruct x
          | |- wf_fact _ ?x _ => is_var x; destruct x
          | H: wf_clause _ _ _ |- _ => invert H
          | H: wf_meta_clause _ _ _ |- _ => invert H
          | H: wf_rule _ _ _ |- _ => invert H
          | H: wf_fact _ ?x ?y |- _ => is_var x; cbv [wf_fact] in H; destruct x, y; simpl in H; fwd; try congruence
          | H: fun_rel _ _ _ |- _ => cbv [fun_rel] in H; subst
          | |- Forall2 _ _ (map _ _) => rewrite <- Forall2_map_r
          | |- Forall2 _ ?x ?x => apply Forall2_same; apply Forall_forall; intros
          | |- Forall2 _ _ _ => eapply Forall2_impl; [|eassumption]
          | |- _ = map _ _ => apply Forall2_eq_map
          | |- _ => constructor
          | |- _ => reflexivity
          | |- _ => f_equal; [solve[t]|solve[t]|..]
          end.

      Lemma map_clause_wf c :
        wf_clause (fun_rel f) c (map_clause_rel c).
      Proof. t. Qed.

      Lemma map_clause_wf_bw c c' :
        wf_clause (fun_rel f) c c' ->
        c' = map_clause_rel c.
      Proof. t. Qed.

      Definition map_meta_clause_rel (c : meta_clause rel1 exprvar fn) :=
        {| meta_clause_rel := f c.(meta_clause_rel);
          meta_clause_args := c.(meta_clause_args) |}.

      Lemma map_meta_clause_wf c :
        wf_meta_clause (fun_rel f) c (map_meta_clause_rel c).
      Proof. t. Qed.

      Lemma map_meta_clause_wf_bw c c' :
        wf_meta_clause (fun_rel f) c c' ->
        c' = map_meta_clause_rel c.
      Proof. t. Qed.

      Definition map_rule_rels (r : rule rel1 exprvar fn aggregator) :=
        match r with
        | normal_rule concls hyps =>
            normal_rule (map (map_clause_rel) concls) (map (map_clause_rel) hyps)
        | meta_rule concls hyps =>
            meta_rule (map (map_meta_clause_rel) concls) (map (map_meta_clause_rel) hyps)
        | agg_rule concl agg hyp =>
            agg_rule (f concl) agg (f hyp)
        end.

      Lemma map_rule_wf r :
        wf_rule (fun_rel f) r (map_rule_rels r).
      Proof. t. Qed.

      Lemma map_rule_wf_bw r r' :
        wf_rule (fun_rel f) r r' ->
        r' = map_rule_rels r.
      Proof. t. Qed.

      Definition map_fact (fct : fact rel1 T) : fact rel2 T :=
        match fct with
        | normal_fact R args => normal_fact (f R) args
        | meta_fact R mf_args mf_set => meta_fact (f R) mf_args mf_set
        end.

      Lemma map_fact_wf fct :
        wf_fact (fun_rel f) fct (map_fact fct).
      Proof. t. Qed.

      Lemma map_fact_wf_bw fct fct' :
        wf_fact (fun_rel f) fct fct' ->
        fct' = map_fact fct.
      Proof. t. Qed.

      Lemma fact_of_g_args_of fct :
        fact_of (f (rel_of fct)) (args_of fct) = map_fact fct.
      Proof. destruct fct; reflexivity. Qed.
    End map.
  End well_formed.
  Hint Constructors wf_clause wf_meta_clause wf_rule : core.
  Hint Unfold wf_fact : core.

  Section wf_symm.
    Context {var1 var2 : Type}
      (rel : Type -> Type)
      (wf_rel : forall {var1 var2}, rel var1 -> rel var2 -> Prop).
    Arguments wf_rel {_ _}.
  End wf_symm.


  Ltac invs :=
    repeat match goal with
      | H: wf_fact _ (normal_fact _ _) ?f |- _ =>
          destruct H as [? ?];
          destruct f;
          simpl in *;
          [fwd|congruence];
          subst
      | H: wf_fact _ (meta_fact _ _ _) ?f |- _ =>
          destruct H as [? ?];
          destruct f;
          simpl in *;
          [congruence|fwd];
          subst
      end.

  Section rel_again.
    Context rel1 rel2 (wf_rel : rel1 -> rel2 -> Prop).
    Lemma wf_clause_sym (c1 : clause rel1 _ _) (c2 : clause rel2 _ _) :
      wf_clause wf_rel c1 c2 ->
      wf_clause (fun r2 r1 => wf_rel r1 r2) c2 c1.
    Proof.
      invert 1; eauto.
    Qed.
    Hint Resolve wf_clause_sym : core.

    Lemma wf_meta_clause_sym c1 c2 :
      wf_meta_clause wf_rel c1 c2 ->
      wf_meta_clause (fun r2 r1 => wf_rel r1 r2) c2 c1.
    Proof.
      invert 1; eauto.
    Qed.
    Hint Resolve wf_meta_clause_sym : core.

    Lemma wf_fact_sym f1 f2 :
      wf_fact wf_rel f1 f2 ->
      wf_fact (fun R2 R1 => wf_rel R1 R2) f2 f1.
    Proof.
      intros [Hrel Hargs]. eauto.
    Qed.
    Hint Resolve wf_fact_sym : core.

    Lemma wf_fact_weaken_wf_rel wf_rel' f1 f2 :
      (forall R1 R2, wf_rel R1 R2 -> wf_rel' R1 R2) ->
      wf_fact wf_rel f1 f2 ->
      wf_fact wf_rel' f1 f2.
    Proof. invert 2; eauto. Qed.

    Lemma wf_rule_sym r1 r2 :
      wf_rule wf_rel r1 r2 ->
      wf_rule (fun R2 R1 => wf_rel R1 R2) r2 r1.
    Proof.
      invert 1; eauto 10 using Forall2_flip, Forall2_impl.
    Qed.
    Hint Resolve wf_rule_sym : core.
  End rel_again.

  Section rel_again.
    Context rel1 rel2 (wf_rel : rel1 -> rel2 -> Prop).

    Lemma wf_rule_impl fact_supported1 fact_supported2 p1 p2 r1 r2 f1 hyps1 :
      (forall hyps2 f1 f2,
          Forall2 (wf_fact wf_rel) hyps1 hyps2 ->
          wf_fact wf_rel f1 f2 ->
          fact_supported1 hyps1 f1 <-> fact_supported2 hyps2 f2) ->
      Forall2 (wf_rule wf_rel) p1 p2 ->
      wf_rule wf_rel r1 r2 ->
      one_to_one wf_rel (fun R1 => In R1 (flat_map concl_rels p1)) (fun R2 => In R2 (flat_map concl_rels p2)) (rel_of f1) ->
      rule_impl (one_step_derives0 fact_supported1 p1) r1 f1 hyps1 ->
      exists f2 hyps2,
        rule_impl (one_step_derives0 fact_supported2 p2) r2 f2 hyps2 /\
          wf_fact wf_rel f1 f2 /\
          Forall2 (wf_fact wf_rel) hyps1 hyps2.
    Proof.
      intros Hfs Hp Hwf Hoo. invert 1.
      - edestruct @wf_non_meta_rule_impl as [R2 [hyps2 [Himpl [Hrel Hhyps]]]]; eauto.
        eexists (normal_fact _ _), _. eauto 6.
      - invert Hwf. rewrite Exists_exists in *. fwd.
        apply Forall2_forget_r in H4.
        rewrite Forall_forall in H4. specialize (H4 _ ltac:(eassumption)).
        fwd. eapply interp_meta_clause_wf in H4p1; eauto. fwd. invs.
        edestruct @Forall2_interp_meta_clause_wf as [? [? ?]]; eauto.
        eexists (meta_fact _ _ _), _. ssplit; [|eauto|eauto].
        2: { constructor; simpl; eauto. Search wf_rel. }
        econstructor.
        + apply Exists_exists. eauto.
        + eassumption.
        + intros. rewrite H2 by eassumption. split.
          -- intros H'. eapply wf_meta_cond_iff'; try eassumption.
             ++ intros. apply Hoo in H5; auto. fwd. apply H5p0; auto.
             ++ apply Hfs.
          -- intros H'. eapply wf_meta_cond_iff'.
             ++ eauto using Forall2_flip, Forall2_impl, wf_rule_sym.
           ++ simpl. eauto.
           ++ simpl. intros R2' HR2'.
              apply Hoo in HR2'; auto.
           ++ eauto using Forall2_flip, Forall2_impl, wf_fact_sym.
           ++ intros ? ? ? Hf. eapply Hfs; try eassumption.
              eapply wf_fact_sym in Hf.
              eauto using wf_fact_sym.
           ++ assumption.
  Qed.
  End rel_again.

  Section well_formed.
    Context {var1 var2 : Type}.
    Inductive wf_blocks_rel (ctx : list (var1 * var2)) : blocks_rel var1 -> blocks_rel var2 -> Prop :=
    | wf_local_rel x :
      wf_blocks_rel _ (local x) (local x)
    | wf_global_rel x :
      wf_blocks_rel _ (global x) (global x)
    | wf_Var_rel x1 x2 :
      In (x1, x2) ctx ->
      wf_blocks_rel _ (Var x1) (Var x2).

    Definition wf_blocks_clause ctx := wf_clause (wf_blocks_rel ctx).
    Definition wf_blocks_meta_clause ctx := wf_meta_clause (wf_blocks_rel ctx).
    Definition wf_block_rule ctx := wf_rule (wf_blocks_rel ctx).
    Definition wf_block_fact ctx := wf_fact (wf_blocks_rel ctx).

    Inductive wf_blocks_prog : list (var1 * var2) -> blocks_prog var1 -> blocks_prog var2 -> Prop :=
    | wf_LetIn ctx x1 x2 f1 f2 :
      wf_blocks_prog ctx x1 x2 ->
      (forall x1' x2', wf_blocks_prog ((x1', x2') :: ctx) (f1 x1') (f2 x2')) ->
      wf_blocks_prog ctx (LetIn x1 f1) (LetIn x2 f2)
    | wf_Block ctx ret p1 p2 :
      Forall2 (wf_block_rule ctx) p1 p2 ->
      wf_blocks_prog ctx (Block ret p1) (Block ret p2).

    Lemma Forall2_wf_clause_Var_in_ctx (ctx : list (var1 * var2)) cs1 cs2 x :
      Forall2 (wf_blocks_clause ctx) cs1 cs2 ->
      In (Var x) (map clause_rel cs2) ->
      In x (map snd ctx).
    Proof.
      intros Hwf HIn.
      apply Forall2_forget_l in Hwf.
      rewrite Forall_forall in Hwf.
      apply in_map_iff in HIn. fwd.
      apply Hwf in HInp1. fwd. invert HInp1p1. simpl in *. subst.
      apply in_map_iff. invert H. eexists (_, _); split; [reflexivity |eassumption].
    Qed.

    Lemma Forall2_wf_meta_clause_Var_in_ctx (ctx : list (var1 * var2)) cs1 cs2 x :
      Forall2 (wf_blocks_meta_clause ctx) cs1 cs2 ->
      In (Var x) (map meta_clause_rel cs2) ->
      In x (map snd ctx).
    Proof.
      intros Hwf HIn.
      apply Forall2_forget_l in Hwf.
      rewrite Forall_forall in Hwf.
      apply in_map_iff in HIn. fwd.
      apply Hwf in HInp1. fwd. invert HInp1p1. simpl in *. subst.
      apply in_map_iff. invert H. eexists (_, _); split; [reflexivity |eassumption].
    Qed.

    Lemma wf_block_rule_Var_in_ctx ctx (r1 : block_rule var1) (r2 : block_rule var2) x :
      wf_block_rule ctx r1 r2 ->
      In (Var x) (all_rels r2) ->
      In x (map snd ctx).
    Proof.
      intros Hwf HIn. invert Hwf; simpl in HIn.
      - apply in_app_iff in HIn. destruct HIn as [HIn | HIn];
          eauto using Forall2_wf_clause_Var_in_ctx.
      - apply in_app_iff in HIn. destruct HIn as [HIn | HIn];
          eauto using Forall2_wf_meta_clause_Var_in_ctx.
      - destruct HIn as [-> | [-> | []]];
          match goal with
          | H : wf_blocks_rel _ _ (Var x) |- _ => invert H
          end;
          apply in_map_iff; eexists (_, _); (split; [reflexivity | eassumption]).
    Qed.
  End well_formed.

  Definition block_fact_supported globals meta_facts (f : fact (blocks_rel (fact_args T -> Prop)) T) : Prop :=
    match rel_of f with
    | local R => Exists (fun hyp => f = hyp \/ fact_matches f hyp) meta_facts
    | global R => exists R', map.get globals R = Some R' /\ R' (args_of f)
    | Var R => R (args_of f)
    end.

  Definition block_one_step_derives globals meta_facts :=
    one_step_derives0 (context := context) (block_fact_supported globals) meta_facts.

  (*bad name, confused me*)
  Definition block_rule_impl globals (p : list (block_rule _)) f hyps :=
    match rel_of f with
    | local R => Exists (fun r => rule_impl (block_one_step_derives globals p) r f hyps) p
    | global R => exists R', map.get globals R = Some R' /\ R' (args_of f)
    | Var R' => R' (args_of f)
    end.

  Definition block_prog_impl (globals : gmap) (p : list (block_rule _)) :=
    pftree (block_rule_impl globals p) (fun _ => False).

  Lemma block_prog_impl_step globals p f hyps :
    block_rule_impl globals p f hyps ->
    Forall (block_prog_impl globals p) hyps ->
    block_prog_impl globals p f.
  Proof. intros. eapply pftree_step; eassumption. Qed.

  Lemma inv_block_prog_impl globals p f :
    block_prog_impl globals p f ->
    exists hyps,
      block_rule_impl globals p f hyps /\
        Forall (block_prog_impl globals p) hyps.
  Proof. invert 1; contradiction || eauto. Qed.

  Fixpoint interp_blocks_prog (globals : gmap) (e : blocks_prog (fact_args T -> Prop)) : fact_args T -> Prop :=
    match e with
    | LetIn x f =>
        interp_blocks_prog globals (f (interp_blocks_prog globals x))
    | Block ret p => fun args => block_prog_impl globals p (fact_of (local ret) args)
    end.

  Definition very_honest_block_prog globals p :=
    forall R mf_args mf_set mhyps,
      block_rule_impl globals p (meta_fact R mf_args mf_set) mhyps ->
      forall args hyps,
        block_rule_impl globals p (normal_fact R args) hyps ->
        Forall (fun f =>
                  match f with
                  | normal_fact R' nf_args' =>
                      exists mf_args' mf_set',
                      In (meta_fact R' mf_args' mf_set') mhyps /\
                        Forall2 matches mf_args' nf_args'
                  | meta_fact _ _ _ => True
                  end) hyps.

  Definition honest_block_prog globals p :=
    forall mf_rel mf_args mf_set,
      block_prog_impl globals p (meta_fact mf_rel mf_args mf_set) ->
      consistent mf_rel mf_args mf_set (block_prog_impl globals p).

  Lemma very_honest_block_prog_honest_block_prog globals p :
    very_honest_block_prog globals p ->
    honest_block_prog globals p.
  Proof. Abort.

  Lemma block_prog_impl_mf_ext globals p mf_rel mf_args mf_set mf_set' :
    block_prog_impl globals p (meta_fact (local mf_rel) mf_args mf_set) ->
    (forall nf_args,
        Forall2 matches mf_args nf_args ->
        mf_set nf_args <-> mf_set' nf_args) ->
    block_prog_impl globals p (meta_fact (local mf_rel) mf_args mf_set').
  Proof.
    intros H1 H2. apply inv_block_prog_impl in H1.
    cbn [block_rule_impl rel_of] in H1. fwd.
    eapply block_prog_impl_step; [|eassumption].
    simpl. eapply Exists_impl; [|eassumption].
    simpl. eauto using rule_impl_mf_ext.
  Qed.

  Lemma use_honest_block_prog globals p mf_rel mf_args mf_set :
    honest_block_prog globals p ->
    block_prog_impl globals p (meta_fact (local mf_rel) mf_args mf_set) ->
    block_prog_impl globals p (meta_fact (local mf_rel) mf_args (fun args => block_prog_impl globals p (normal_fact (local mf_rel) args))).
  Proof.
    intros H1 H2. eapply block_prog_impl_mf_ext; [eassumption|].
    cbv [honest_block_prog] in H1. apply H1. apply H2.
  Qed.

  Fixpoint honest_blocks_prog globals e :=
    match e with
    | LetIn x f =>
        honest_blocks_prog globals x /\
          honest_blocks_prog globals (f (interp_blocks_prog globals x))
    | Block ret p =>
        honest_block_prog globals p
    end.

  Variant flat_rel :=
    | lvar_rel (block_id : nat) (lvar_name : lvar)
    | gvar_rel (gvar_name : gvar).

  Definition is_local_rel {var} (R : blocks_rel var) :=
    match R with
    | local _ => true
    | _ => false
    end.

  Definition is_local_clause {var} (c : clause (blocks_rel var) exprvar fn) :=
    is_local_rel c.(clause_rel).

  Definition is_local_meta_clause {var} (c : meta_clause (blocks_rel var) exprvar fn) :=
    is_local_rel c.(meta_clause_rel).

  Definition keep_local_concls {var} (r : block_rule var) : list (block_rule var) :=
    match r with
    | normal_rule concls hyps =>
        [normal_rule (filter is_local_clause concls) hyps]
    | meta_rule concls hyps =>
        [meta_rule (filter is_local_meta_clause concls) hyps]
    | agg_rule concl agg hyp =>
        if is_local_rel concl then [r] else []
    end.

  Definition flatten_rel (block_id : nat) (rel : blocks_rel flat_rel) :=
    match rel with
    | local x => lvar_rel block_id x
    | global x => gvar_rel x
    | Var x => x
    end.

  Fixpoint flatten (name : nat) (e : blocks_prog flat_rel) : nat * flat_rel * list (rule flat_rel exprvar fn aggregator) :=
    match e with
    | LetIn x f =>
        let '(name', Rx, p2) := flatten name x in
        let '(name'', Rfx, p1) := flatten name' (f Rx) in
        (name'', Rfx, p1 ++ p2)
    | Block ret p =>
        let p' := flat_map keep_local_concls p in
        let p'' := map (map_rule_rels (flatten_rel name)) p' in
        (S name, lvar_rel name ret, p'')
    end.

  Definition in_range lo hi x :=
    match x with
    | lvar_rel block_id _ => lo <= block_id < hi
    | gvar_rel _ => False
    end.

  Definition not_as_big_as hi x :=
    match x with
    | lvar_rel block_id _ => block_id < hi
    | gvar_rel _ => True
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


  Lemma in_keep_local_concls_Forall_local {var} (r r' : block_rule var) :
    In r' (keep_local_concls r) ->
    Forall (fun R => is_local_rel R = true) (concl_rels r').
  Proof.
    destruct r; simpl.
    - intros [<- | []]. apply Forall_map, Forall_filter. auto.
    - intros [<- | []]. apply Forall_map, Forall_filter. intros []; auto.
    - destruct (is_local_rel concl_rel) eqn:E.
      + intros [<- | []]. constructor; auto.
      + intros [].
  Qed.

  Lemma concl_rels_map_rule_rels {R1 R2} (f : R1 -> R2) (r : rule R1 exprvar fn aggregator) :
    concl_rels (map_rule_rels f r) = map f (concl_rels r).
  Proof.
    destruct r; simpl.
    - do 2 rewrite map_map. reflexivity.
    - do 2 rewrite map_map. reflexivity.
    - reflexivity.
  Qed.

  Lemma all_rels_map_rule_rels {R1 R2} (f : R1 -> R2) (r : rule R1 exprvar fn aggregator) :
    all_rels (map_rule_rels f r) = map f (all_rels r).
  Proof.
    destruct r; simpl.
    - rewrite map_app. do 4 rewrite map_map. reflexivity.
    - rewrite map_app. do 4 rewrite map_map. reflexivity.
    - reflexivity.
  Qed.

  Lemma incl_all_rels_keep_local_concls {var} (r r' : block_rule var) :
    In r' (keep_local_concls r) ->
    incl (all_rels r') (all_rels r).
  Proof.
    destruct r; simpl.
    - intros [<- | []] R. simpl. rewrite !in_app_iff. intros [HR | HR].
      + left. apply in_map_iff in HR. destruct HR as [c [<- Hc]].
        apply filter_In in Hc. destruct Hc as [Hc _].
        apply in_map_iff. eauto.
      + right. assumption.
    - intros [<- | []] R. simpl. rewrite !in_app_iff. intros [HR | HR].
      + left. apply in_map_iff in HR. destruct HR as [c [<- Hc]].
        apply filter_In in Hc. destruct Hc as [Hc _].
        apply in_map_iff. eauto.
      + right. assumption.
    - destruct (is_local_rel concl_rel) eqn:E.
      + intros [<- | []] R HR. exact HR.
      + intros [].
  Qed.

  Lemma in_nonoverlapping_ranges lo1 hi1 lo2 hi2 x :
    in_range lo1 hi1 x ->
    in_range lo2 hi2 x ->
    hi1 <= lo2 ->
    False.
  Proof. destruct x; simpl; auto. lia. Qed.

  Definition is_global x :=
    match x with
    | gvar_rel _ => True
    | lvar_rel _ _ => False
    end.

  Lemma in_range_not_global lo hi x :
    in_range lo hi x ->
    is_global x ->
    False.
  Proof. destruct x; auto. Qed.

  (*BEGIN BLOCK_PROG LEMMAS*)

  Lemma pftree_equiv {U} (P1 P2 : U -> list U -> Prop) Q (x:U) :
    (forall y l, P1 y l <-> P2 y l) ->
    pftree P1 Q x <-> pftree P2 Q x.
  Proof.
    intros H. split; intros Htree.
    - eapply pftree_weaken; [exact Htree | intros y l Hyl; apply H; exact Hyl].
    - eapply pftree_weaken; [exact Htree | intros y l Hyl; apply H; exact Hyl].
  Qed.

  Lemma interp_clause_local {var} ctx (c : clause (blocks_rel var) exprvar fn) R args :
    interp_clause ctx c (normal_fact (local R) args) ->
    is_local_clause c = true.
  Proof.
    cbv [interp_clause is_local_clause is_local_rel].
    intros [nf_args [H1 H2]]. invert H2. reflexivity.
  Qed.

  Lemma interp_meta_clause_local {var} ctx (c : meta_clause (blocks_rel var) exprvar fn) R args S :
    interp_meta_clause ctx c (meta_fact (local R) args S) ->
    is_local_meta_clause c = true.
  Proof.
    cbv [interp_meta_clause is_local_meta_clause is_local_rel].
    intros [mf_args [mf_set [H1 H2]]]. invert H2. reflexivity.
  Qed.

  Lemma non_meta_rule_impl_local_iff {var} (r : block_rule var) R args hyps :
    non_meta_rule_impl r (local R) args hyps <->
    Exists (fun r' => non_meta_rule_impl r' (local R) args hyps) (keep_local_concls r).
  Proof.
    destruct r; simpl.
    - split; intros H.
      + constructor. invert H. econstructor; eauto.
        rewrite Exists_exists in *. fwd.
        eexists. split; [|eassumption].
        apply filter_In. split; [eassumption|].
        eapply interp_clause_local; eauto.
      + repeat invert_stuff. econstructor; eauto.
        rewrite Exists_exists in *. fwd. rewrite filter_In in *.
        fwd. eauto.
    - split; intros; repeat invert_stuff.
    - destruct concl_rel eqn:E; subst; simpl; split; intros; repeat invert_stuff.
      + constructor. constructor. assumption.
      + constructor. assumption.
  Qed.

  Lemma meta_fact_rule_impl_local_iff {var} p (r : block_rule var) R args S hyps :
    rule_impl p r (meta_fact (local R) args S) hyps <->
    Exists (fun r' => rule_impl p r' (meta_fact (local R) args S) hyps) (keep_local_concls r).
  Proof.
    destruct r as [concls hyps_rule | concls hyps_rule | concl agg hyp]; simpl.
    - split; intros; repeat invert_stuff.
    - split; intros H.
      + constructor. invert H. econstructor; eauto.
        rewrite Exists_exists in *. fwd.
        eexists. split; [|eassumption].
        apply filter_In. split; [eassumption|].
        eapply interp_meta_clause_local; eauto.
      + repeat invert_stuff. econstructor; eauto.
        rewrite Exists_exists in *. fwd. rewrite filter_In in *.
        fwd. eauto.
    - destruct (is_local_rel concl) eqn:E; split; intros; repeat invert_stuff.
  Qed.

  Lemma meta_condition_equiv {var} fact_supported0 (p : list (block_rule var)) hyps R args :
    one_step_derives0 fact_supported0 p hyps (local R) args <->
      one_step_derives0 fact_supported0 (flat_map keep_local_concls p) hyps (local R) args.
  Proof.
    cbv [one_step_derives one_step_derives0]. split; intros H; fwd.
    - apply non_meta_rule_impl_local_iff in Hp1.
      rewrite Exists_exists in *. fwd.
      do 2 eexists. split; eauto. apply in_flat_map. eauto.
    - rewrite in_flat_map in *. fwd.
      do 2 eexists. split; eauto. split; eauto.
      apply non_meta_rule_impl_local_iff.
      apply Exists_exists. eauto.
  Qed.

  Lemma rule_impl_local_iff' {var} fact_supported0 (p : list (block_rule var)) (r : block_rule var) f hyps :
    forall R, rel_of f = local R ->
      rule_impl (one_step_derives0 fact_supported0 p) r f hyps <->
      Exists (fun r' => rule_impl (one_step_derives0 fact_supported0 (flat_map keep_local_concls p)) r' f hyps) (keep_local_concls r).
  Proof.
    intros R Heq. destruct f; simpl in *; subst.
    - split; intros H.
      + repeat invert_stuff. rewrite non_meta_rule_impl_local_iff in *.
        eapply Exists_impl; [|eassumption]. simpl. eauto.
      + constructor. apply non_meta_rule_impl_local_iff.
        eapply Exists_impl; [|eassumption]. simpl. intros.
        repeat invert_stuff.
    - split; intros H.
      + apply meta_fact_rule_impl_local_iff in H.
        eapply Exists_impl; [|eassumption]. simpl.
        invert 1. econstructor; eauto.
        intros. rewrite H8 by assumption. apply meta_condition_equiv.
      + apply meta_fact_rule_impl_local_iff.
        eapply Exists_impl; [|eassumption]. simpl.
        invert 1. econstructor; eauto.
        intros. rewrite H8 by assumption. symmetry. apply meta_condition_equiv.
  Qed.

  Lemma rule_impl_local_iff (p : list (block_rule _)) (r : block_rule _) f hyps :
    forall R, rel_of f = local R ->
         rule_impl (block_one_step_derives map.empty p) r f hyps <->
           Exists (fun r' => rule_impl (block_one_step_derives map.empty (flat_map keep_local_concls p)) r' f hyps) (keep_local_concls r).
  Proof. apply rule_impl_local_iff'. Qed.

  Section vars.
    Context {var1 var2 : Type}.

  Lemma fact_matches_wf_local_fw (ctx : list (var1 * var2)) f1 hyp1 f2 hyp2 x :
    wf_block_fact ctx f1 f2 ->
    wf_block_fact ctx hyp1 hyp2 ->
    rel_of f1 = local x ->
    fact_matches f1 hyp1 ->
    fact_matches f2 hyp2.
  Proof.
    intros [Hrel1 Hargs1] [Hrel2 Hargs2] Hloc Hmatch.
    cbv [fact_matches] in *. fwd.
    destruct f2, hyp2; simpl in *; try discriminate; repeat invert_stuff.
    subst.
    invert Hrel1. invert Hrel2.
    do 4 eexists. split; [eassumption | split; [eassumption | split; reflexivity]].
  Qed.

  Lemma wf_blocks_rel_sym (ctx : list (var1 * var2)) R1 R2 :
    wf_blocks_rel ctx R1 R2 ->
    wf_blocks_rel (map (fun '(a, b) => (b, a)) ctx) R2 R1.
  Proof.
    invert 1; constructor.
    apply in_map_iff. eexists (_, _). eauto.
  Qed.
  Hint Resolve wf_blocks_rel_sym : core.

  End vars.

  Print block_fact_supported. Search gvar.
  Definition block_fact_supported' {U} (globals : gmap) ctx meta_facts (f : fact (blocks_rel U) T) :=
    match rel_of f with
    | local _ =>
        Exists
          (fun hyp =>
             f = hyp \/ fact_matches f hyp)
          meta_facts
    | global R =>
        exists R', map.get globals R = Some R' /\ R' (args_of f)
    | Var x => exists R', In (R', x) ctx /\ R' (args_of f)
    end.


  Lemma NoDup_map_in_inj {A B} (f : A -> B) (l : list A) x1 x2 :
    NoDup (map f l) ->
    In x1 l ->
    In x2 l ->
    f x1 = f x2 ->
    x1 = x2.
  Proof.
    intros Hnodup H1 H2 Heq.
    apply in_split in H1. destruct H1 as [l1 [l2 ->]].
    rewrite map_app in Hnodup. simpl in Hnodup.
    apply NoDup_remove_2 in Hnodup.

    apply in_app_or in H2. destruct H2 as [H2 | [H2 | H2]].
    - exfalso. apply Hnodup. apply in_or_app. left.
      rewrite Heq. apply in_map. exact H2.
    - exact H2.
    - exfalso. apply Hnodup. apply in_or_app. right.
      rewrite Heq. apply in_map. exact H2.
  Qed.

  Lemma NoDup_fst_In_inj {A B} (l : list (A * B)) k v1 v2 :
    NoDup (map fst l) ->
    In (k, v1) l ->
    In (k, v2) l ->
    v1 = v2.
  Proof.
    intros Hnodup H1 H2.
    assert (Heq : (k, v1) = (k, v2)) by (eapply NoDup_map_in_inj; eauto).
    congruence.
  Qed.

  Lemma NoDup_snd_In_inj {A B} (l : list (A * B)) k v1 v2 :
    NoDup (map snd l) ->
    In (v1, k) l ->
    In (v2, k) l ->
    v1 = v2.
  Proof.
    intros Hnodup H1 H2.
    assert (Heq : (v1, k) = (v2, k)) by (eapply NoDup_map_in_inj; eauto).
    congruence.
  Qed.

  Lemma blah ctx hyps1 hyps2 f1 (f2 : fact (blocks_rel flat_rel) T) :
    NoDup (map snd ctx) ->
    Forall2 (wf_block_fact ctx) hyps1 hyps2 ->
    wf_block_fact ctx f1 f2 ->
    block_fact_supported map.empty hyps1 f1 <->
      block_fact_supported' map.empty ctx hyps2 f2.
  Proof.
    intros Hctx Hhyps Hf.
    cbv [block_fact_supported block_fact_supported'].
    destruct Hf as [Hf1 Hf2]. invert Hf1.
    - split; intros H'.
      + rewrite Exists_exists in *. fwd. apply Forall2_forget_r in Hhyps.
        rewrite Forall_forall in Hhyps. apply Hhyps in H'p0. fwd.
        eexists. split; [eassumption|].
        destruct H'p1 as [H'p1|H'p1].
        -- subst. left. cbv [wf_block_fact wf_fact] in H'p0p1.
           fwd. destruct f2, y, x0; simpl in *; subst; fwd; try congruence;
             match goal with
             | H: wf_blocks_rel _ (local _) _ |- _ => invert H
             end;
             reflexivity.
        -- right. eapply fact_matches_wf_local_fw; eauto. cbv [wf_fact]. split; eauto.
           rewrite <- H0, <- H. constructor.
      + rewrite Exists_exists in *. fwd. apply Forall2_forget_l in Hhyps.
        rewrite Forall_forall in Hhyps. apply Hhyps in H'p0. fwd.
        eexists. split; [eassumption|].
        destruct H'p1 as [H'p1|H'p1].
        -- subst. left. cbv [wf_block_fact wf_fact] in H'p0p1.
           fwd. destruct f1, x1, x0; simpl in *; subst; fwd; try congruence;
             match goal with
             | H: wf_blocks_rel _ _ (local _) |- _ => invert H
             end;
             reflexivity.
        -- right. eapply fact_matches_wf_local_fw; eauto.
           ++ cbv [wf_block_fact wf_fact]. split; eauto.
              apply wf_blocks_rel_sym. rewrite <- H0, <- H. constructor.
           ++ apply wf_fact_sym. eapply wf_fact_weaken_wf_rel; [|eassumption].
              intros. apply wf_blocks_rel_sym. eassumption.
    - rewrite Hf2. reflexivity.
    - rewrite Hf2. split; eauto.
      intros. fwd.
      assert (x1 = R') by (eapply NoDup_snd_In_inj; eauto).
      subst.
      exact H2p1.
  Qed.

  Lemma wf_blocks_rel_local_one_to_one {var1 var2} (ctx: list (var1 * var2)) x :
    one_to_one (wf_blocks_rel ctx) (local x).
  Proof.
    cbv [one_to_one paired]. intros y Hwf. invert Hwf.
    split; intros ? Hwf; invert Hwf; reflexivity.
  Qed.

  Lemma block_prog_impl_to_flat ctx p1 p2 name f1 f2 :
    NoDup (map snd ctx) ->
    Forall2 (wf_block_rule ctx) p1 p2 ->
    wf_block_fact ctx f1 f2 ->
    block_prog_impl map.empty p1 f1 ->
    prog_impl (map (map_rule_rels (flatten_rel name)) (flat_map keep_local_concls p2))
      (fun f' => exists R, In (R, rel_of f') ctx /\ R (args_of f'))
      (fact_of (flatten_rel name (rel_of f2)) (args_of f2)).
  Proof.
    intros Hctx Hp Hf H. revert f2 Hf.
    induction H; try contradiction.
    intros f2 Hf.
    move H at bottom. cbv [block_rule_impl] in H.
    destruct (rel_of x) eqn:E.
    - apply Exists_exists in H. fwd.
      pose proof Hp as Hp'.
      apply Forall2_forget_r in Hp. rewrite Forall_forall in Hp. apply Hp in Hp0.
      fwd. eapply wf_rule_impl in Hp1.
      3,4: eassumption.
      2: { Print block_fact_supported. Unshelve.
           2: { apply block_fact_supported'. 1: exact map.empty. exact ctx. }
           intros. apply blah; try assumption. }
      2: { rewrite E. apply wf_blocks_rel_local_one_to_one. }
      fwd.
      cbv [wf_fact] in Hp1p1. fwd. rewrite E in *. invert Hp1p1p0.
      rewrite rule_impl_local_iff' in Hp1p0 by eauto.
      apply Exists_exists in Hp1p0. fwd.
      eapply wf_rule_impl with (wf_rel := fun_rel (flatten_rel name)) (fact_supported2 := fact_supported) in Hp1p0p1.
      4: { apply map_rule_wf. }
      3: { instantiate (1 := map _ _). rewrite <- Forall2_map_r.
           apply Forall2_same. apply Forall_forall. intros ? _.
           apply map_rule_wf. }
      3: { (*suffices to say that flatten_rel is injective*) admit. }
      2: { admit. }
      fwd.
      eapply prog_impl_step.
      -- apply Exists_map. apply Exists_flat_map.
         apply Exists_exists. eexists. split; [eassumption|].
         apply Exists_exists. eexists. split; [eassumption|].
         eassert (fact_of _ _ = _) as ->; [|eassumption].
         cbv [wf_fact wf_block_fact fun_rel] in *. fwd.
         rewrite E in Hfp0. invert Hfp0. simpl in *. rewrite <- Hfp1.
         destruct f1, x, f0; simpl in *; f_equal; subst; try congruence || reflexivity.
      -- apply Forall2_forget_l in Hp1p0p1p2. apply Forall2_forget_l in Hp1p2.
         rewrite Forall_forall in *. intros f2' Hf2'. move H1 at bottom.
         specialize (Hp1p0p1p2 _ Hf2'). fwd. cbv [wf_fact fun_rel] in *. fwd.
         specialize (Hp1p2 _ ltac:(eassumption)). fwd.
         specialize (H1 _ ltac:(eassumption)).
         rewrite <- fact_of_rel_of_args_of.
         rewrite <- Hp1p0p1p2p1p1. rewrite <- Hp1p0p1p2p1p0. apply H1.
         cbv [wf_block_fact wf_fact]. auto.
    -

  Lemma block_prog_impl_to_flat globals p name f ctx :
    block_prog_impl globals p f ->
    prog_impl (map (map_rule_rels (flatten_rel name)) (flat_map keep_local_concls p))
      (fun f' => exists R, In (R, rel_of f') ctx /\ R (args_of f'))
      (fact_of (flatten_rel name (rel_of f)) (args_of f)).
  Proof.
    (* Handled via pftree_ind and Forall mapping *)
  Admitted.

  (*END BLOCK_PROG LEMMAS*)

  Lemma flatten_correct ctx name e e0 name' Rret p :
    wf_blocks_prog ctx e e0 ->
    flatten name e0 = (name', Rret, p) ->
    Forall (fun '(_, R) => in_range O name R) ctx ->
    name <= name' /\
      in_range name name' Rret /\
      Forall (in_range name name') (flat_map concl_rels p) /\
      Forall (fun R => in_range name name' R \/ In R (map snd ctx) \/ is_global R) (flat_map all_rels p) /\
      forall args,
        interp_blocks_prog map.empty e args <->
          prog_impl p (fun f => exists R, In (R, rel_of f) ctx /\ R (args_of f))
            (fact_of Rret args).
  Proof.
    intros Hwf. revert name name' Rret p.
    induction Hwf;
      intros name name' Rret p Hflat Hctx;
      simpl in Hflat;
      fwd;
      simpl.
    - epose_dep IHHwf.
      specialize (IHHwf ltac:(eassumption)). specialize' IHHwf.
      { eapply Forall_impl; [|eassumption].
        intros [? ?]. intros. assumption. }
      fwd.
      rename H0 into IH'. epose_dep IH'.
      specialize (IH' ltac:(eassumption)). specialize' IH'.
      { constructor.
        - eapply in_range_weaken; [eassumption| |]; lia.
        - eapply Forall_impl; [|eassumption].
          intros [? ?]. intros. eapply in_range_weaken; [eassumption| |]; lia. }
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
               apply Hctx in H2p1. simpl in H1.
               eapply in_nonoverlapping_ranges. 1: exact H2p1. 1: exact H1. lia.
             - eauto using in_range_not_global. }
        rewrite IH'p4.
        apply prog_impl_hyp_ext_strong.
        { split; intros Hargs; simpl; fwd; exfalso.
          - destruct Hargsp0 as [Hargsp0|Hargsp0]; fwd.
            + apply IHHwfp4 in Hargsp1. rewrite fact_of_rel_of_args_of in Hargsp1.
              apply prog_impl_rel_of in Hargsp1. destruct Hargsp1 as [Hargsp1|Hargsp1].
              -- fwd. rewrite rel_of_fact_of in Hargsp1p0.
                 rewrite Forall_forall in Hctx. apply Hctx in Hargsp1p0.
                 eauto using in_nonoverlapping_ranges.
              -- rewrite rel_of_fact_of in Hargsp1.
                 rewrite Forall_forall in IHHwfp2.
                 apply IHHwfp2 in Hargsp1.
                 eauto using in_nonoverlapping_ranges.
            + rewrite rel_of_fact_of in Hargsp0.
              rewrite Forall_forall in Hctx. apply Hctx in Hargsp0.
              eauto using in_nonoverlapping_ranges.
          - apply prog_impl_rel_of in Hargs. destruct Hargs as [Hargs|Hargs].
            + fwd. rewrite rel_of_fact_of in Hargsp0.
              rewrite Forall_forall in Hctx. apply Hctx in Hargsp0.
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
              { subst. simpl. eexists. split; eauto. apply IHHwfp4.
                rewrite fact_of_rel_of_args_of. assumption. }
              2: { exfalso. eauto using in_range_not_global. }
              apply in_map_iff in HRf'. destruct HRf' as [[? ?] HRf'].
              simpl in HRf'. fwd.
              rewrite Forall_forall in Hctx.
              apply Hctx in HRf'p1.
              exfalso. eauto using in_nonoverlapping_ranges.
    - ssplit.
      + lia.
      + lia.
      + simpl. lia.
      + apply Forall_flat_map. apply Forall_map. apply Forall_flat_map.
        apply Forall_forall. intros r _. apply Forall_forall. intros r' Hr'.
        rewrite concl_rels_map_rule_rels. apply Forall_map.
        apply in_keep_local_concls_Forall_local in Hr'.
        eapply Forall_impl; [|eassumption]. simpl. intros R.
        destruct R; simpl; try congruence. lia.
      + apply Forall_flat_map. apply Forall_map. apply Forall_flat_map.
        apply Forall_forall. intros r Hr. apply Forall_forall. intros r' Hr'.
        rewrite all_rels_map_rule_rels. apply Forall_map.
        apply Forall_forall. intros R HR.
        destruct R; simpl; auto.
        apply Forall2_forget_l in H.
        rewrite Forall_forall in H.
        specialize (H _ Hr). fwd.
        eapply wf_block_rule_Var_in_ctx in Hp1; [|].
        2: { eapply incl_all_rels_keep_local_concls; [eassumption|eassumption]. }
        rewrite Forall_forall in Hctx. auto.
      + intros args. rewrite <- block_prog_impl_keep_local_concls.
        647892
          ,6
           +   CTRN6 `a|
         98765432xdfgy          /
        split; intros Hargs.
        -- admit.
        -- admit.
           all: fail.
  Abort.

End Blocks.
Arguments blocks_prog : clear implicits.

Ltac invert_stuff :=
  first [Datalog.invert_stuff |
          match goal with
          | H: block_rule_impl _ _ _ _ |- _ => cbv [block_rule_impl] in H; simpl in H
          | H : block_prog_impl _ _ _ |- _ => apply inv_block_prog_impl in H; try (destruct H as [H|H]; [contradiction|])
          end].

Ltac interp_exprs :=
  repeat first [match goal with
                | |- block_prog_impl _ _ ?f =>
                    let x := constr:(rel_of f) in
                    let x := (eval simpl in x) in
                    match x with
                    | global _ => idtac
                    | Var _ => idtac
                    end;
                    apply block_prog_impl_step with (hyps := []); [|constructor]
                | |- block_rule_impl _ _ _ _ => cbv [block_rule_impl]; simpl
                end |
                 Datalog.interp_exprs ].
