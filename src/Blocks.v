From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.

From Datalog Require Import Map Tactics Fp List Dag Datalog.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List Datatypes.Option.

Import ListNotations.

Definition paired {U1 U2} (P : U1 -> U2 -> Prop) x1 x2 :=
  (forall x2', P x1 x2' -> x2' = x2) /\ (forall x1', P x1' x2 -> x1' = x1).

Definition one_to_one {U1 U2} (P : U1 -> U2 -> Prop) R1 R2 x1 :=
  forall x2,
    P x1 x2 ->
    R2 x2 ->
    (forall x2', P x1 x2' -> R2 x2' -> x2' = x2) /\ (forall x1', P x1' x2 -> R1 x1' -> x1' = x1).

Lemma one_to_one_smaller_sets U1 U2 (P : U1 -> U2 -> _) R1 R2 R1' R2' x1 :
  (forall x1', R1' x1' -> R1 x1') ->
  (forall x2', R2' x2' -> R2 x2') ->
  one_to_one P R1 R2 x1 ->
  one_to_one P R1' R2' x1.
Proof.
  cbv [one_to_one]. intros ? ? H **. edestruct H; eauto 6.
Qed.

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

  Inductive block_rel :=
  | local (_ : lvar)
  | input (_ : lvar).

  Definition block_rule := rule block_rel exprvar fn aggregator.

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

  Fixpoint interp_blocks_prog (globals : gmap) (e : blocks_prog (fact_args T -> Prop)) : fact_args T -> Prop :=
    match e with
    | LetIn x f =>
        interp_blocks_prog globals (f (interp_blocks_prog globals x))
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

  Section map.
    Context {rel1 rel2} (f : rel1 -> rel2) (Hf : forall x y, f x = f y -> x = y).

    Definition map_fact (fct : fact rel1 T) : fact rel2 T :=
      match fct with
      | normal_fact R args => normal_fact (f R) args
      | meta_fact R mf_args mf_set => meta_fact (f R) mf_args mf_set
      end.

    Definition map_clause_rel (c : clause rel1 exprvar fn) :=
      {| clause_rel := f c.(clause_rel);
        clause_args := c.(clause_args) |}.

    Lemma interp_clause_map_fw ctx c h :
      interp_clause ctx c h ->
      interp_clause ctx (map_clause_rel c) (map_fact h).
    Proof. intros. repeat invert_stuff. interp_exprs. Qed.

    Lemma interp_clause_map_bw ctx c h :
      interp_clause ctx (map_clause_rel c) (map_fact h) ->
      interp_clause ctx c h.
    Proof.
      intros.
      destruct h, c; simpl in *; repeat invert_stuff; simpl in *.
      apply_somewhere Hf. subst. interp_exprs.
    Qed.

    Lemma Forall2_interp_clause_map_fw ctx hyps1 hyps2 :
      Forall2 (interp_clause ctx) hyps1 hyps2 ->
      Forall2 (interp_clause ctx) (map map_clause_rel hyps1) (map map_fact hyps2).
    Proof.
      intros.
      rewrite <- Forall2_map_l, <- Forall2_map_r.
      eapply Forall2_impl; [|eassumption].
      eauto using interp_clause_map_fw.
    Qed.

    Lemma Forall2_interp_clause_map_bw ctx hyps1 hyps2 :
      Forall2 (interp_clause ctx) (map map_clause_rel hyps1) (map map_fact hyps2) ->
      Forall2 (interp_clause ctx) hyps1 hyps2.
    Proof.
      intros H. rewrite <- Forall2_map_l, <- Forall2_map_r in H.
      eapply Forall2_impl; [|eassumption].
      eauto using interp_clause_map_bw.
    Qed.

    Definition map_meta_clause_rel (c : meta_clause rel1 exprvar fn) :=
      {| meta_clause_rel := f c.(meta_clause_rel);
        meta_clause_args := c.(meta_clause_args) |}.

    Definition map_rule_rels (r : rule rel1 exprvar fn aggregator) :=
      match r with
      | normal_rule concls hyps =>
          normal_rule (map (map_clause_rel) concls) (map (map_clause_rel) hyps)
      | meta_rule concls hyps =>
          meta_rule (map (map_meta_clause_rel) concls) (map (map_meta_clause_rel) hyps)
      | agg_rule concl agg hyp =>
          agg_rule (f concl) agg (f hyp)
      end.

    Lemma non_meta_rule_impl_map_fw r R args hyps :
      non_meta_rule_impl r R args hyps ->
      non_meta_rule_impl (map_rule_rels r) (f R) args (map map_fact hyps).
    Proof.
      invert 1.
      - econstructor.
        + apply Exists_map. eapply Exists_impl; [|eassumption].
          simpl. intros c Hc. eapply interp_clause_map_fw in Hc. eassumption.
        + apply Forall2_interp_clause_map_fw. eassumption.
      - simpl. eassert (meta_fact _ _ _ :: _ = _) as ->.
        2: { econstructor. eassumption. }
        f_equal. rewrite map_map. apply map_ext. intros [? ?]. reflexivity.
    Qed.

    Lemma interp_meta_clause_map_fw ctx c f0 :
      interp_meta_clause ctx c f0 ->
      interp_meta_clause ctx (map_meta_clause_rel c) (map_fact f0).
    Proof.
      cbv [interp_meta_clause]. intros. fwd. unfold map_fact. eauto.
    Qed.

    Lemma Forall2_interp_meta_clause_map_fw ctx hyps1 hyps2 :
      Forall2 (interp_meta_clause ctx) hyps1 hyps2 ->
      Forall2 (interp_meta_clause ctx) (map map_meta_clause_rel hyps1) (map map_fact hyps2).
    Proof.
      intros. rewrite <- Forall2_map_l, <- Forall2_map_r.
      eapply Forall2_impl; [|eassumption].
      eauto using interp_meta_clause_map_fw.
    Qed.

  Lemma fact_matches_map_fw f1 f2 :
    fact_matches f1 f2 ->
    fact_matches (map_fact f1) (map_fact f2).
  Proof.
    intros. cbv [fact_matches] in *. fwd. unfold map_fact. eauto 10.
  Qed.

  Lemma fact_matches_map_bw f1 f2 :
    fact_matches (map_fact f1) (map_fact f2) ->
    fact_matches f1 f2.
  Proof.
    intros H. cbv [fact_matches] in H. fwd.
    destruct f1, f2; simpl in *; try discriminate.
    repeat invert_stuff.
    apply_somewhere Hf. subst.
    cbv [fact_matches]. eauto 10.
  Qed.

  Lemma interp_meta_clause_map_bw ctx c f0 :
    interp_meta_clause ctx (map_meta_clause_rel c) (map_fact f0) ->
    interp_meta_clause ctx c f0.
  Proof.
    intros H. cbv [interp_meta_clause] in *. fwd.
    destruct f0; simpl in *; try discriminate.
    repeat invert_stuff. apply_somewhere Hf. subst.
    eauto.
  Qed.

  Lemma Forall2_interp_meta_clause_map_bw ctx hyps1 hyps2 :
    Forall2 (interp_meta_clause ctx) (map map_meta_clause_rel hyps1) (map map_fact hyps2) ->
    Forall2 (interp_meta_clause ctx) hyps1 hyps2.
  Proof.
    intros H. rewrite <- Forall2_map_l, <- Forall2_map_r in H.
    eapply Forall2_impl; [|eassumption].
    eauto using interp_meta_clause_map_bw.
  Qed.

    Lemma map_fact_inj f1 f2 :
      map_fact f1 = map_fact f2 ->
      f1 = f2.
    Proof.
      intros Heq.
      destruct f1, f2; simpl in Heq; try discriminate;
        repeat invert_stuff; apply_somewhere Hf; subst; auto.
    Qed.

    Lemma non_meta_rule_impl_map_bw r R args hyps :
      non_meta_rule_impl (map_rule_rels r) (f R) args (map map_fact hyps) ->
      non_meta_rule_impl r R args hyps.
    Proof.
      intros H. destruct r; invert H.
      - econstructor.
        + rewrite Exists_map in *. eapply Exists_impl; [|eassumption].
          simpl. intros. eapply interp_clause_map_bw; eauto.
        + eapply Forall2_interp_clause_map_bw; eassumption.
      - apply_somewhere Hf. subst.
        destruct hyps as [|f0 hyps']; simpl in *; invert_list_stuff.
        destruct f0; simpl in *; repeat invert_stuff.
        apply_somewhere Hf. subst.
        eassert (meta_fact _ _ _ :: _ = _) as ->.
        2: { econstructor. eassumption. }
        f_equal. eapply map_inj. 2: rewrite <- H1.
        { intros. eapply map_fact_inj; eassumption. }
        rewrite map_map. apply map_ext. intros [? ?]. reflexivity.
    Qed.

    Lemma non_meta_rule_invert_map r R args hyps :
      non_meta_rule_impl (map_rule_rels r) (f R) args hyps ->
      exists hyps0,
        hyps = map map_fact hyps0.
    Proof.
      intros H. destruct r; invert H.
      - rewrite Exists_map in *. rewrite <- Forall2_map_l in *.
        epose proof Forall_exists_r_Forall2 as H'. edestruct H' as [hyps0 Hhyps0].
        2: { eexists. apply Forall2_eq_map. apply Forall2_flip. eassumption. }
        apply Forall2_forget_l in H6. eapply Forall_impl; [|eassumption].
        simpl. intros. fwd. repeat invert_stuff. simpl.
        eexists (normal_fact _ _). reflexivity.
      - apply_somewhere Hf. subst. eexists (meta_fact _ _ _ :: map (fun '(i, x_i) => normal_fact _ _) _).
        simpl. f_equal. rewrite map_map. apply map_ext. intros [? ?]. reflexivity.
    Qed.

    Lemma meta_cond_map_iff p R (args'' : list T) hyps :
      (exists r hyps'',
          In r p /\
            non_meta_rule_impl r R args'' hyps'' /\
            Forall (fun f' => Exists (fun hyp => f' = hyp \/ fact_matches f' hyp) hyps) hyps'')
      <->
        (exists r_map hyps''_map,
            In r_map (map map_rule_rels p) /\
              non_meta_rule_impl r_map (f R) args'' hyps''_map /\
              Forall (fun f' => Exists (fun hyp => f' = hyp \/ fact_matches f' hyp) (map map_fact hyps)) hyps''_map).
    Proof.
      split; intros H; fwd.
      - do 2 eexists.
        split; [apply in_map; eassumption | split].
        + apply non_meta_rule_impl_map_fw. eassumption.
        + rewrite Lists.List.Forall_map. eapply Forall_impl; [|eassumption].
          intros f' Hex. apply Exists_exists in Hex. fwd.
          apply Exists_exists. eexists. split; [apply in_map; eassumption |].
          destruct Hexp1 as [<- | Hmatch]; [left; reflexivity | right].
          apply fact_matches_map_fw. eassumption.
      - apply in_map_iff in Hp0. fwd.
        pose proof Hp1 as Hp1'.
        apply non_meta_rule_invert_map in Hp1. fwd.
        do 2 eexists. split; [eassumption | split].
        + eapply non_meta_rule_impl_map_bw; eassumption.
        + rewrite Lists.List.Forall_map in Hp2. eapply Forall_impl; [|eassumption].
          simpl. intros f0 Hf0. apply Exists_map in Hf0.
          eapply Exists_impl; [|eassumption].
          simpl. intros f' Hf'. destruct Hf' as [Hf' | Hf']; eauto using map_fact_inj, fact_matches_map_bw.
    Qed.

    Lemma rule_impl_map_rule_rels_fw p r f0 hyps :
      rule_impl (one_step_derives p) r f0 hyps ->
      rule_impl (one_step_derives (map map_rule_rels p))
        (map_rule_rels r)
        (map_fact f0)
        (map map_fact hyps).
    Proof.
      invert 1.
      - econstructor. apply non_meta_rule_impl_map_fw. eassumption.
      - simpl. econstructor.
        + rewrite Exists_map. eapply Exists_impl; [|eassumption].
          simpl. intros c Hc. eapply interp_meta_clause_map_fw in Hc. eassumption.
        + apply Forall2_interp_meta_clause_map_fw. eassumption.
        + intros args'' Hargs. rewrite H2 by assumption.
          apply meta_cond_map_iff.
    Qed.

    Lemma rule_impl_map_rule_rels_bw p r f0 hyps :
      rule_impl (one_step_derives (map map_rule_rels p))
        (map_rule_rels r)
        (map_fact f0)
        (map map_fact hyps) ->
      rule_impl (one_step_derives p) r f0 hyps.
    Proof.
      invert 1.
      - destruct f0; simpl in *; repeat invert_stuff. constructor.
        eapply non_meta_rule_impl_map_bw; eassumption.
      - destruct f0; simpl in *; repeat invert_stuff.
        destruct r; simpl in *; repeat invert_stuff.
        econstructor.
        + rewrite Exists_map in *. eapply Exists_impl; [|eassumption].
          simpl. intros c Hc. eapply interp_meta_clause_map_bw; eauto.
        + eapply Forall2_interp_meta_clause_map_bw; eauto.
        + intros args'' Hargs. rewrite H4 by assumption.
          symmetry. apply meta_cond_map_iff.
    Qed.

    Lemma concl_rels_map_rule_rels r :
      concl_rels (map_rule_rels r) = map f (concl_rels r).
    Proof.
      destruct r; simpl.
      - do 2 rewrite map_map. reflexivity.
      - do 2 rewrite map_map. reflexivity.
      - reflexivity.
    Qed.

    Lemma all_rels_map_rule_rels r :
      all_rels (map_rule_rels r) = map f (all_rels r).
    Proof.
      destruct r; simpl.
      - rewrite map_app. do 4 rewrite map_map. reflexivity.
      - rewrite map_app. do 4 rewrite map_map. reflexivity.
      - reflexivity.
    Qed.

    Lemma fact_of_g_args_of fct :
      fact_of (f (rel_of fct)) (args_of fct) = map_fact fct.
    Proof. destruct fct; reflexivity. Qed.
  End map.

  Inductive flat_rel : Type :=
  | input_rel (block : nat) (name : lvar)
  | local_rel (block : nat) (name : lvar).

  Definition flatten_rel (block : nat) (R : block_rel) :=
    match R with
    | local x => local_rel block x
    | input x => input_rel block x
    end.

  Fixpoint flatten (name : nat) (e : blocks_prog flat_rel) : nat * flat_rel * list (rule flat_rel exprvar fn aggregator) :=
    match e with
    | LetIn x f =>
        let '(name', Rx, p2) := flatten name x in
        let '(name'', Rfx, p1) := flatten name' (f Rx) in
        (name'', Rfx, p1 ++ p2)
    | Block ret inputs p =>
        let p' := map (map_rule_rels (flatten_rel name)) p in
        (S name, local_rel name ret, p')
    end.

  Definition very_honest_block_prog (p : list block_rule) :=
    forall R mf_args mf_set mhyps r,
      In r p ->
      rule_impl (one_step_derives p) r (meta_fact R mf_args mf_set) mhyps ->
      forall args hyps,
        rule_impl (one_step_derives p) r (normal_fact R args) hyps ->
        Forall (fun f =>
                  match f with
                  | normal_fact R' nf_args' =>
                      exists mf_args' mf_set',
                      In (meta_fact R' mf_args' mf_set') mhyps /\
                        Forall2 matches mf_args' nf_args'
                  | meta_fact _ _ _ => True
                  end) hyps.

  (*TODO this is wrong, there should be some restrcition on Q*)
  Definition honest_block_prog (p : list block_rule) :=
    forall Q mf_rel mf_args mf_set,
      prog_impl p Q (meta_fact mf_rel mf_args mf_set) ->
      consistent mf_rel mf_args mf_set (prog_impl p Q).

  Lemma very_honest_block_prog_honest_block_prog p :
    very_honest_block_prog p ->
    honest_block_prog p.
  Proof. Abort.

  Lemma use_honest_prog p Q mf_rel mf_args mf_set :
    honest_block_prog p ->
    prog_impl p Q (meta_fact mf_rel mf_args mf_set) ->
    prog_impl p Q (meta_fact mf_rel mf_args (fun args => prog_impl p Q (normal_fact mf_rel args))).
  Proof.
    intros H1 H2.
    (*   eapply prog_impl_mf_ext; [eassumption|]. *)
    (*   cbv [honest_block_prog] in H1. apply H1. apply H2. *)
    (* Qed. *)
  Abort.

  (* Fixpoint honest_blocks_prog globals e := *)
  (*   match e with *)
  (*   | LetIn x f => *)
  (*       honest_blocks_prog globals x /\ *)
  (*         honest_blocks_prog globals (f (interp_blocks_prog globals x)) *)
  (*   | Block ret p => *)
  (*       honest_block_prog globals p *)
  (*   end. *)

  (*BEGIN BLOCK_PROG LEMMAS*)

  (* Lemma block_prog_impl_to_flat ctx p1 p2 name f1 f2 : *)
  (*   NoDup (map snd ctx) -> *)
  (*   Forall2 (wf_block_rule ctx) p1 p2 -> *)
  (*   wf_block_fact ctx f1 f2 -> *)
  (*   block_prog_impl map.empty p1 f1 -> *)
  (*   prog_impl (map (map_rule_rels (flatten_rel name)) (flat_map keep_local_concls p2)) *)
  (*     (fun f' => exists R, In (R, rel_of f') ctx /\ R (args_of f')) *)
  (*     (fact_of (flatten_rel name (rel_of f2)) (args_of f2)). *)
  (* Proof. *)
  (*   intros Hctx Hp Hf H. revert f2 Hf. *)
  (*   induction H; try contradiction. *)
  (*   intros f2 Hf. *)
  (*   move H at bottom. cbv [block_rule_impl] in H. *)
  (*   destruct (rel_of x) eqn:E. *)
  (*   - apply Exists_exists in H. fwd. *)
  (*     pose proof Hp as Hp'. *)
  (*     apply Forall2_forget_r in Hp. rewrite Forall_forall in Hp. apply Hp in Hp0. *)
  (*     fwd. eapply wf_rule_impl in Hp1. *)
  (*     3,4: eassumption. *)
  (*     2: { Print block_fact_supported. Unshelve. *)
  (*          2: { apply block_fact_supported'. 1: exact map.empty. exact ctx. } *)
  (*          intros. apply blah; try assumption. } *)
  (*     2: { rewrite E. eapply one_to_one_smaller_sets. *)
  (*          3: apply wf_blocks_rel_local_one_to_one. *)
  (*          1,2: simpl; auto. } *)
  (*     fwd. *)
  (*     cbv [wf_fact] in Hp1p1. fwd. rewrite E in *. invert Hp1p1p0. *)
  (*     rewrite rule_impl_local_iff' in Hp1p0 by eauto. *)
  (*     apply Exists_exists in Hp1p0. fwd. *)
  (*     eapply wf_rule_impl with (wf_rel := fun_rel (flatten_rel name)) (fact_supported2 := fact_supported) in Hp1p0p1. *)
  (*     4: { apply map_rule_wf. } *)
  (*     3: { instantiate (1 := map _ _). rewrite <- Forall2_map_r. *)
  (*          apply Forall2_same. apply Forall_forall. intros ? _. *)
  (*          apply map_rule_wf. } *)
  (*     3: { rewrite <- H. *)
  (*          apply fun_rel_flatten_rel_local_one_to_one. *)
  (*          intros R [HR|HR]. *)
  (*          - apply in_flat_map in HR. destruct HR as [r'' [Hr'' H_R]]. *)
  (*            apply in_flat_map in Hr''. destruct Hr'' as [r_orig [H_orig H_keep]]. *)
  (*            eapply in_keep_local_concls_Forall_local in H_keep. *)
  (*            rewrite Forall_forall in H_keep. apply H_keep. exact H_R. *)
  (*          - eapply in_keep_local_concls_Forall_local in Hp1p0p0. *)
  (*            rewrite Forall_forall in Hp1p0p0. apply Hp1p0p0. exact HR. } *)
  (*     2: { intros hyps' f3 f4 Hhyps Hfs. destruct Hfs as [Hfs1 Hfs2]. *)
  (*          cbv [fun_rel] in Hfs1. cbv [block_fact_supported']. *)
  (*          cbv [fact_supported]. destruct (rel_of f3). *)
  (*          - admit. *)
  (*          - admit. *)
  (*          - split; intros H'. *)
  (*            + fwd. simpl in Hfs1. subst. *)
  (*            , f4; simpl in Hfs1, Hfs2; try discriminate Hfs2; fwd; subst. *)
  (*          - cbv [block_fact_supported' fact_supported]. simpl. *)
  (*          simpl in Hfs1. *)
  (*          invert Hfs1 *)
  (*          split; intros H'. *)
  (*          - cbv [block_fact_supported'] in H'. *)
  (*          Print fact_supported. Print block_fact_supported'. admit. } *)
  (*     fwd. *)
  (*     eapply prog_impl_step. *)
  (*     -- apply Exists_map. apply Exists_flat_map. *)
  (*        apply Exists_exists. eexists. split; [eassumption|]. *)
  (*        apply Exists_exists. eexists. split; [eassumption|]. *)
  (*        eassert (fact_of _ _ = _) as ->; [|eassumption]. *)
  (*        cbv [wf_fact wf_block_fact fun_rel] in *. fwd. *)
  (*        rewrite E in Hfp0. invert Hfp0. simpl in *. rewrite <- Hfp1. *)
  (*        destruct f1, x, f0; simpl in *; f_equal; subst; try congruence || reflexivity. *)
  (*     -- apply Forall2_forget_l in Hp1p0p1p2. apply Forall2_forget_l in Hp1p2. *)
  (*        rewrite Forall_forall in *. intros f2' Hf2'. move H1 at bottom. *)
  (*        specialize (Hp1p0p1p2 _ Hf2'). fwd. cbv [wf_fact fun_rel] in *. fwd. *)
  (*        specialize (Hp1p2 _ ltac:(eassumption)). fwd. *)
  (*        specialize (H1 _ ltac:(eassumption)). *)
  (*        rewrite <- fact_of_rel_of_args_of. *)
  (*        rewrite <- Hp1p0p1p2p1p1. rewrite <- Hp1p0p1p2p1p0. apply H1. *)
  (*        cbv [wf_block_fact wf_fact]. auto. *)
  (*   - *)

  (* Lemma block_prog_impl_to_flat globals p name f ctx : *)
  (*   block_prog_impl globals p f -> *)
  (*   prog_impl (map (map_rule_rels (flatten_rel name)) (flat_map keep_local_concls p)) *)
  (*     (fun f' => exists R, In (R, rel_of f') ctx /\ R (args_of f')) *)
  (*     (fact_of (flatten_rel name (rel_of f)) (args_of f)). *)
  (* Proof. *)
  (*   (* Handled via pftree_ind and Forall mapping *) *)
  (* Admitted. *)

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
