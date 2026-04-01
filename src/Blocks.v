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
    | Block ret p => (S name, lvar_rel name ret, map (map_rule_rels (flatten_rel name)) p)
    end.
  Search (Datalog.fact _ _ -> Datalog.fact_args _).
  Lemma flatten_correct ctx name e e0 name' Rret p :
    wf_blocks_prog ctx e e0 ->
    flatten name e0 = (name', Rret, p) ->
    forall args,
      interp_blocks_prog map.empty e args <->
        prog_impl p (fun f => exists R, In (R, rel_of f) ctx /\ R (args_of f))
          (fact_of Rret args).
  Proof.
    intros Hwf. revert name name' Rret p.
    induction Hwf;
      intros name name' Rret p Hflat args;
      simpl in Hflat;
      fwd;
      simpl.
    - rewrite staged_program_iff.
      2: { admit. }
      rewrite H0 by eassumption.
      apply prog_impl_hyp_ext. intros f'. split; intros Hf'; fwd.
      + simpl in Hf'p0. destruct Hf'p0 as [Hf'p0|Hf'p0].
        -- fwd. rewrite IHHwf in Hf'p1 by eassumption.
           rewrite fact_of_rel_of_args_of in Hf'p1. exact Hf'p1.
        --
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
