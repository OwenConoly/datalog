From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.

From Datalog Require Import Map Tactics Fp List Dag Datalog.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List Datatypes.Option.

Import ListNotations.

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
    Context {var1 var2 : Type}.

    Inductive wf_blocks_rel (ctx : list (var1 * var2)) : blocks_rel var1 -> blocks_rel var2 -> Prop :=
    | wf_local_rel x :
      wf_blocks_rel _ (local x) (local x)
    | wf_global_rel x :
      wf_blocks_rel _ (global x) (global x)
    | wf_Var_rel x1 x2 :
      In (x1, x2) ctx ->
      wf_blocks_rel _ (Var x1) (Var x2).

    Inductive wf_block_rule (ctx : list (var1 * var2)) : block_rule var1 -> block_rule var2 -> Prop :=
    | wf_normal_rule concls1 concls2 hyps1 hyps2 :
      Forall2 (wf_blocks_rel ctx) (map clause_rel concls1) (map clause_rel concls2) ->
      Forall2 (wf_blocks_rel ctx) (map clause_rel hyps1) (map clause_rel hyps2) ->
      wf_block_rule _ (normal_rule concls1 hyps1) (normal_rule concls2 hyps2)
    | wf_meta_rule concls1 concls2 hyps1 hyps2 :
      Forall2 (wf_blocks_rel ctx) (map meta_clause_rel concls1) (map meta_clause_rel concls2) ->
      Forall2 (wf_blocks_rel ctx) (map meta_clause_rel hyps1) (map meta_clause_rel hyps2) ->
      wf_block_rule _ (meta_rule concls1 hyps1) (meta_rule concls2 hyps2)
    | wf_agg_rule R1 R2 R1' R2' a :
      wf_blocks_rel ctx R1 R2 ->
      wf_blocks_rel ctx R1' R2' ->
      wf_block_rule _ (agg_rule R1 a R1') (agg_rule R2 a R2').

    Inductive wf_blocks_prog : list (var1 * var2) -> blocks_prog var1 -> blocks_prog var2 -> Prop :=
    | wf_LetIn ctx x1 x2 f1 f2 :
      wf_blocks_prog ctx x1 x2 ->
      (forall x1' x2', wf_blocks_prog ((x1', x2') :: ctx) (f1 x1') (f2 x2')) ->
      wf_blocks_prog ctx (LetIn x1 f1) (LetIn x2 f2)
    | wf_Block ctx ret p1 p2 :
      Forall2 (wf_block_rule ctx) p1 p2 ->
      wf_blocks_prog ctx (Block ret p1) (Block ret p2).
  End well_formed.


  (*bad name, confused me*)
  Definition block_rule_impl globals (p : list (block_rule _)) f hyps :=
    match rel_of f with
    | local R => Exists (fun r => rule_impl p r f hyps) p
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

  (*given A B, compute (A \cup B) \cap (A \cup B).
    (a rather uninteresting function to compute, but whatever)
   *)
  Axiom (dummy : exprvar) (ret : lvar).
  Example intersection_of_unions (A B : gvar) var : blocks_prog var :=
    LetIn
      (Block ret [normal_rule
                    [{| clause_rel := local ret; clause_args := [var_expr dummy] |}]
                    [{| clause_rel := global A; clause_args := [var_expr dummy] |}];
                  normal_rule
                    [{| clause_rel := local ret; clause_args := [var_expr dummy] |}]
                    [{| clause_rel := global B; clause_args := [var_expr dummy] |}]])
      (fun union =>
         Block ret [normal_rule
                      [{| clause_rel := local ret; clause_args := [var_expr dummy] |}]
                      [{| clause_rel := Var union; clause_args := [var_expr dummy] |};
                       {| clause_rel := Var union; clause_args := [var_expr dummy] |}]]).

  Goal forall A B A' B' x,
      A <> B ->
      let iou := interp_blocks_prog (map.put (map.put map.empty A A') B B') (intersection_of_unions A B _) in
      iou (normal_fact_args [x]) <-> A' (normal_fact_args [x]) \/ B' (normal_fact_args [x]).
  Proof. Abort.

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

  Definition map_clause_rel {R1 R2} (f : R1 -> R2) (c : clause R1 exprvar fn) :=
    {| clause_rel := f c.(clause_rel);
       clause_args := c.(clause_args) |}.

  Definition map_meta_clause_rel {R1 R2} (f : R1 -> R2) (c : meta_clause R1 exprvar fn) :=
    {| meta_clause_rel := f c.(meta_clause_rel);
       meta_clause_args := c.(meta_clause_args) |}.

  Definition map_rule_rels {R1 R2} (f : R1 -> R2) (r : rule R1 exprvar fn aggregator) :=
    match r with
    | normal_rule concls hyps =>
        normal_rule (map (map_clause_rel f) concls) (map (map_clause_rel f) hyps)
    | meta_rule concls hyps =>
        meta_rule (map (map_meta_clause_rel f) concls) (map (map_meta_clause_rel f) hyps)
    | agg_rule concl agg hyp =>
        agg_rule (f concl) agg (f hyp)
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

  Search (Datalog.fact _ _ -> Datalog.fact_args _).
  Print rule.
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

  (* Lemma in_concl_rels_keep_local_concls {var} (r : block_rule var) R : *)
  (*   In R (flat_map concl_rels (keep_local_concls r)) -> *)
  (*   In R (concl_rels r) /\ is_local_rel R = true. *)
  (* Proof. *)
  (*   destruct r; simpl; try rewrite app_nil_r; intros H. *)
  (*   - apply in_map_iff in H. fwd. apply filter_In in Hp1. fwd. auto using in_map. *)
  (*   - apply in_map_iff in H. fwd. apply filter_In in Hp1. fwd. auto using in_map. *)
  (*   - destruct (is_local_rel concl_rel) eqn:E; simpl in H; intuition congruence. *)
  (* Qed. *)

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

  Lemma Forall2_wf_blocks_rel_Var_in_ctx {var1 var2} (ctx : list (var1 * var2)) R1s R2s x :
    Forall2 (wf_blocks_rel ctx) R1s R2s ->
    In (Var x) R2s ->
    In x (map snd ctx).
  Proof.
    intros Hwf HIn.
    apply Forall2_forget_l in Hwf.
    rewrite Forall_forall in Hwf.
    apply Hwf in HIn. fwd. invert HInp1.
    apply in_map_iff. eexists (_, _); split; [reflexivity | eassumption].
  Qed.

  Lemma wf_block_rule_Var_in_ctx {var1 var2} ctx (r1 : block_rule var1) (r2 : block_rule var2) x :
    wf_block_rule ctx r1 r2 ->
    In (Var x) (all_rels r2) ->
    In x (map snd ctx).
  Proof.
    intros Hwf HIn. invert Hwf; simpl in HIn.
    - apply in_app_iff in HIn. destruct HIn as [HIn | HIn];
        eauto using Forall2_wf_blocks_rel_Var_in_ctx.
    - apply in_app_iff in HIn. destruct HIn as [HIn | HIn];
        eauto using Forall2_wf_blocks_rel_Var_in_ctx.
    - destruct HIn as [-> | [-> | []]];
        match goal with
        | H : wf_blocks_rel _ _ (Var x) |- _ => invert H
        end;
        apply in_map_iff; eexists (_, _); (split; [reflexivity | eassumption]).
  Qed.

  Lemma flatten_rels_good var1 ctx (e : blocks_prog var1) e0 name name' Rret p :
    wf_blocks_prog ctx e e0 ->
    flatten name e0 = (name', Rret, p) ->
    Forall (fun '(_, R) => not_as_big_as name R) ctx ->
    name <= name' /\
      not_as_big_as name' Rret /\
      Forall (in_range name name') (flat_map concl_rels p) /\
      Forall (not_as_big_as name') (flat_map all_rels p).
  Proof.
    intros Hwf.
    revert name name' Rret p.
    induction Hwf;
      intros name name' Rret p0 Hflat Hctx;
      simpl in Hflat;
      fwd.
    - epose_dep IHHwf.
      specialize (IHHwf ltac:(eassumption)). specialize' IHHwf.
      { eapply Forall_impl; [|eassumption].
        intros [? ?]. intros. eapply not_as_big_as_weaken; [eassumption|]. lia. }
      fwd.
      rename H0 into IH'. epose_dep IH'.
      specialize (IH' ltac:(eassumption)). specialize' IH'.
      { constructor; [eassumption|]. eapply Forall_impl; [|eassumption].
        intros [? ?]. intros. eapply not_as_big_as_weaken; [eassumption|]. lia. }
      fwd. ssplit.
      + lia.
      + assumption.
      + rewrite flat_map_app. apply Forall_app.
        eauto 10 using Forall_impl, in_range_weaken.
      + rewrite flat_map_app. apply Forall_app.
        eauto 10 using Forall_impl, not_as_big_as_weaken.
    - ssplit.
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
        rewrite Forall_forall in Hctx.
        apply in_map_iff in Hp1. destruct Hp1 as [[? ?] Hp1]. fwd.
        apply Hctx in Hp1p1. eapply not_as_big_as_weaken; [eassumption|]. lia.
        Unshelve. auto.

  Abort.

  Lemma flatten_correct ctx name e e0 name' Rret p :
    Forall (fun '(_, R) => not_as_big_as name' R) ctx ->
    wf_blocks_prog ctx e e0 ->
    flatten name e0 = (name', Rret, p) ->
    forall args,
      interp_blocks_prog map.empty e args <->
        prog_impl p (fun f => exists R, In (R, rel_of f) ctx /\ R (args_of f))
          (fact_of Rret args).
  Proof.
    intros Hctx Hwf. revert name name' Rret p.
    induction Hwf;
      intros name name' Rret p Hflat args;
      simpl in Hflat;
      fwd;
      repeat match goal with
        | IH: forall _ _ _ _, _ -> _ |- _ => specialize (IH _ _ _ _ ltac:(eassumption))
        end;
      fwd;
      simpl.
    - rewrite staged_program_iff.
      2: { admit. }
      rewrite H0 by eassumption.
      apply prog_impl_hyp_ext. intros f'. split; intros Hf'; fwd.
      + simpl in Hf'p0. destruct Hf'p0 as [Hf'p0|Hf'p0].
        -- fwd. rewrite IHHwf in Hf'p1 by eassumption.
           rewrite fact_of_rel_of_args_of in Hf'p1. exact Hf'p1.
        -- apply prog_impl_leaf. eauto.
      + rewrite <- fact_of_rel_of_args_of in Hf'. rewrite <- IHHwf in Hf'. eassumption.
           simpl in Hf'p1.
      Search prog_impl.
      admit.
    - simpl.
      split; intros Hargs.
      + eapply IHHwf.
      split; intros Hargs.
      +
    forall args,
      e' args <->
    True.

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
