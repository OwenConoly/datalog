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
        let '(name', Rx, p1) := flatten name x in
        let '(name'', Rfx, p2) := flatten name' (f Rx) in
        (name'', Rfx, p1 ++ p2)
    | Block ret p => (S name, lvar_rel name ret, map (map_rule_rels (flatten_rel name)) p)
    end.

  (* Lemma flatten_correct name e : *)
  (*   True. *)

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
