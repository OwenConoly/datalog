From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From coqutil Require Import Map.Interface Map.Properties Map.Solver Datatypes.List Tactics Tactics.fwd Eqb.
From Datalog Require Import Eqb.
From Datalog Require Import List Pftree Datalog (* FancyNotations *) Tactics Blocks Interpreter.
Import ListNotations.

Section __.
Variant bop := sum | prod.
Variant type := val | set.
Definition obj := nat.
Context {context : map.map nat obj} {context_ok : map.ok context}.
Variant agg_fn :=
  | fn_lit (o : obj)
  | fn_bop (o : bop).
#[local] Instance agg_exprvar : exprvarT := nat.
#[local] Instance agg_fnT : fnT := agg_fn.
#[local] Instance agg_aggregatorT : aggregatorT := bop.
#[local] Instance obj_valueT : valueT := obj.

Definition fn_inj f :=
  match f with
  | fn_lit _ => true
  | fn_bop _ => false
  end.

#[global] Instance bop_eqb : Eqb bop :=
  fun o1 o2 =>
    match o1, o2 with
    | sum, sum => true
    | prod, prod => true
    | _, _ => false
    end.

#[global] Instance bop_eqb_ok : Eqb_ok bop_eqb.
Proof. intros x y. cbv [eqb bop_eqb]. destruct x, y; congruence. Qed.

#[global] Instance fn_eqb : Eqb fn :=
  fun f1 f2 =>
    match f1, f2 with
    | fn_lit l1, fn_lit l2 => l1 =? l2
    | fn_bop o1, fn_bop o2 => eqb o1 o2
    | _, _ => false
    end.

#[global] Instance fn_eqb_ok : Eqb_ok fn_eqb.
Proof.
  intros x y. cbv [eqb fn_eqb]. destruct x, y; try congruence.
  - destruct (Nat.eqb_spec o o0); subst; congruence.
  - pose proof (eqb_spec o o0) as Ho. cbv [eqb] in Ho.
    destruct (bop_eqb o o0); subst; congruence.
Qed.

Definition bop_id o :=
  match o with
  | sum => O
  | prod => 1
  end.

(*to make nontrivial use of some meta-rule features, should have prod and proj or something, maybe subset-satisfying-prop*)
Inductive Sexpr {var} : type -> Type :=
| Var : forall t, var t -> Sexpr t
| bop_over_vals : bop -> Sexpr val -> Sexpr val -> Sexpr val
| empty : Sexpr set
| singleton : Sexpr val -> Sexpr set
(* | union : Sexpr set -> Sexpr set -> Sexpr set *)
| intersection : Sexpr set -> Sexpr set -> Sexpr set
| let_in t1 t2 : Sexpr t1 -> (var t1 -> Sexpr t2) -> Sexpr t2
| bop_over_set : bop -> Sexpr set -> Sexpr val.
Arguments Sexpr : clear implicits.

Record ctx_elt2 {var1 var2 : type -> Type} :=
  { ctx_elt_t : type; ctx_elt_p1 : var1 ctx_elt_t; ctx_elt_p2 : var2 ctx_elt_t }.
Arguments ctx_elt2 : clear implicits.

Inductive wf_Sexpr {var1 var2} : list (ctx_elt2 var1 var2) -> forall t, Sexpr var1 t -> Sexpr var2 t -> Prop :=
| wf_Var ctx t x1 x2 :
  In {| ctx_elt_p1 := x1; ctx_elt_p2 := x2 |} ctx ->
  wf_Sexpr ctx _ (Var t x1) (Var t x2)
| wf_bop_over_vals ctx o x1 x2 y1 y2 :
  wf_Sexpr ctx _ x1 x2 ->
  wf_Sexpr ctx _ y1 y2 ->
  wf_Sexpr ctx _ (bop_over_vals o x1 y1) (bop_over_vals o x2 y2)
| wf_empty ctx :
  wf_Sexpr ctx _ empty empty
| wf_singleton ctx x1 x2 :
  wf_Sexpr ctx _ x1 x2 ->
  wf_Sexpr ctx _ (singleton x1) (singleton x2)
| wf_intersection ctx x1 x2 y1 y2 :
  wf_Sexpr ctx _ x1 x2 ->
  wf_Sexpr ctx _ y1 y2 ->
  wf_Sexpr ctx _ (intersection x1 y1) (intersection x2 y2)
| wf_let_in ctx t1 t2 x1 x2 y1 y2 :
  wf_Sexpr ctx _ x1 x2 ->
  (forall x1' x2', wf_Sexpr ({| ctx_elt_p1 := x1'; ctx_elt_p2 := x2' |} :: ctx) _ (y1 x1') (y2 x2')) ->
  wf_Sexpr ctx _ (let_in t1 t2 x1 y1) (let_in _ _ x2 y2)
| wf_bop_over_set ctx o x1 x2 :
  wf_Sexpr ctx _ x1 x2 ->
  wf_Sexpr ctx _ (bop_over_set o x1) (bop_over_set o x2).

Definition SExpr t := forall var, Sexpr var t.
Definition Wf_Sexpr {t} (e : SExpr t) :=
  forall var1 var2, wf_Sexpr [] t (e var1) (e var2).

Definition lit x : expr := expr.app (fn_lit x) [].

Definition interp_bop o x y :=
  match o with
  | sum => x + y
  | prod => x * y
  end.

Definition interp_fn (f : fn) (args : list obj) : option obj :=
  match f with
  | fn_lit x =>
      match args with
      | [] => Some x
      | _ => None
      end
  | fn_bop o =>
      match args with
      | [x; y] => Some (interp_bop o x y)
      | _ => None
      end
  end.

(*might become less trivial later idk*)
Definition extract_nat (x : obj) :=
  Some x.

#[local] Instance Sig : datalog_semantics agg_fn bop obj :=
  { interp_fun := interp_fn;
    get_nat := fun _ => O;
    agg_bop := interp_bop;
    agg_id := bop_id }.

#[local] Instance agg_params : datalog_params (_rel := block_rel nat) := {}.

Lemma fn_inj_correct f :
  fn_inj f = true ->
  partial_injective (interp_fun f).
Proof.
  destruct f; simpl; try congruence.
  intros _. intros x y v Hx Hy.
  destruct x, y; simpl in *; try discriminate; auto.
Qed.

#[global] Instance block_rel_eqb {A} {aeqb : Eqb A} : Eqb (block_rel A) :=
  fun R1 R2 =>
    match R1, R2 with
    | local l1, local l2 => aeqb l1 l2
    | input l1, input l2 => aeqb l1 l2
    | _, _ => false
    end.

#[global] Instance block_rel_eqb_ok {A} {aeqb : Eqb A} {aeqb_ok : Eqb_ok aeqb}
  : Eqb_ok block_rel_eqb.
Proof.
  intros x y. cbv [eqb block_rel_eqb].
  destruct x, y; try congruence;
    (pose proof (eqb_spec a a0) as Ha; cbv [eqb] in Ha;
     destruct (aeqb a a0); subst; congruence).
Qed.

Fixpoint compile_Sexpr {t} {var} (e : Sexpr (fun _ => var) t) : blocks_prog var :=
  match e with
  | Var t x =>
      Block O [(O, x)]
        {| program.rules :=
             [rule.impl
                [{| clause.rel := local O; clause.args := [expr.var O] |}]
                [{| clause.rel := input O; clause.args := [expr.var O] |}]];
          program.meta_rules :=
            [{| meta_rule.concls :=
                 [{| clause_pattern.rel := local O;
                    clause_pattern.args := [expr_pattern.any] |}];
               meta_rule.hyps :=
                 [{| clause_pattern.rel := input O;
                    clause_pattern.args := [expr_pattern.any] |}] |}] |}
  | bop_over_vals o x y =>
      LetIn (compile_Sexpr x)
        (fun x' =>
           LetIn (compile_Sexpr y)
             (fun y' =>
                Block O [(O, x'); (1, y')]
                  {| program.rules :=
                       [rule.impl
                          [{| clause.rel := local O;
                             clause.args := [expr.app (fn_bop o) [expr.var O; expr.var (S O)]] |}]
                          [{| clause.rel := input 0; clause.args := [expr.var O] |};
                           {| clause.rel := input 1; clause.args := [expr.var (S O)] |}]];
                    program.meta_rules :=
                      [{| meta_rule.concls :=
                           [{| clause_pattern.rel := local O;
                              clause_pattern.args := [expr_pattern.any] |}];
                         meta_rule.hyps :=
                           [{| clause_pattern.rel := input 0;
                              clause_pattern.args := [expr_pattern.any] |};
                            {| clause_pattern.rel := input 1;
                              clause_pattern.args := [expr_pattern.any] |}] |}] |}))
  | empty =>
      Block O []
        {| program.rules := [];
          program.meta_rules :=
            [{| meta_rule.concls :=
                 [{| clause_pattern.rel := local O;
                    clause_pattern.args := [expr_pattern.any] |}];
               meta_rule.hyps := [] |}] |}
  | singleton x => (*we happen to represent sets in the same format as elements*)
      compile_Sexpr x
  | intersection x y =>
      LetIn (compile_Sexpr x)
        (fun x' =>
           LetIn (compile_Sexpr y)
             (fun y' =>
                Block O [(0, x'); (1, y')]
                  {| program.rules :=
                       [rule.impl
                          [{| clause.rel := local O; clause.args := [expr.var O] |}]
                          [{| clause.rel := input 0; clause.args := [expr.var O] |};
                           {| clause.rel := input 1; clause.args := [expr.var O] |}]];
                    program.meta_rules :=
                      [{| meta_rule.concls :=
                           [{| clause_pattern.rel := local O;
                              clause_pattern.args := [expr_pattern.any] |}];
                         meta_rule.hyps :=
                           [{| clause_pattern.rel := input 0;
                              clause_pattern.args := [expr_pattern.any] |};
                            {| clause_pattern.rel := input 1;
                              clause_pattern.args := [expr_pattern.any] |}] |}] |}))
  | let_in t1 t2 x f =>
      LetIn (compile_Sexpr x)
        (fun x' => compile_Sexpr (f x'))
  | bop_over_set o x =>
      LetIn (compile_Sexpr x)
        (fun x' =>
           Block O [(0, x')]
             {| program.rules :=
                  [rule.agg (local O) o (local (S O));
                   rule.impl
                     [{| clause.rel := local (S O); clause.args := [expr.var O; expr.var O] |}]
                     [{| clause.rel := input 0; clause.args := [expr.var O] |}]];
               program.meta_rules :=
                 [{| meta_rule.concls :=
                      [{| clause_pattern.rel := local O;
                         clause_pattern.args := [expr_pattern.any] |}];
                    meta_rule.hyps :=
                      [{| clause_pattern.rel := local (S O);
                         clause_pattern.args := [expr_pattern.any; expr_pattern.any] |}] |};
                  {| meta_rule.concls :=
                      [{| clause_pattern.rel := local (S O);
                         clause_pattern.args := [expr_pattern.any; expr_pattern.any] |}];
                     meta_rule.hyps :=
                       [{| clause_pattern.rel := input 0;
                          clause_pattern.args := [expr_pattern.any] |}] |}] |})
  end.

Definition sum_expr {var} (S : var set) :=
  bop_over_set sum (Var _ S).

Definition interp_type t : Type :=
  match t with
  | val => nat
  | set => nat -> Prop
  end.

Inductive interp_Sexpr : forall {t}, Sexpr interp_type t -> interp_type t -> Prop :=
| interp_Var t x :
  interp_Sexpr (Var t x) x
| interp_bop_over_vals o x y x' y' :
  interp_Sexpr x x' ->
  interp_Sexpr y y' ->
  interp_Sexpr (bop_over_vals o x y) (interp_bop o x' y')
| interp_empty :
  interp_Sexpr empty (fun _ => False)
| interp_singleton x x' :
  interp_Sexpr x x' ->
  interp_Sexpr (singleton x) (eq x')
(* | interp_union s1 s2 s1' s2' : *)
(*   interp_Sexpr s1 s1' -> *)
(*   interp_Sexpr s2 s2' -> *)
(*   interp_Sexpr (union s1 s2) (fun x => s1' x \/ s2' x) *)
| interp_intersection s1 s2 s1' s2' :
  interp_Sexpr s1 s1' ->
  interp_Sexpr s2 s2' ->
  interp_Sexpr (intersection s1 s2) (fun x => s1' x /\ s2' x)
| interp_let_in t1 t2 x y x' y' :
  interp_Sexpr x x' ->
  interp_Sexpr (y x') y' ->
  interp_Sexpr (let_in t1 t2 x y) y'
| interp_bop_over_set o (x : Sexpr _ set) x' l :
  interp_Sexpr x x' ->
  is_list_set x' l ->
  interp_Sexpr (bop_over_set o x) (fold_right (interp_bop o) (bop_id o) l).

Inductive Sexpr_with_args {var} : type -> Type :=
| with_args_nil t : Sexpr var t -> Sexpr_with_args t
| with_args_cons t : var t -> Sexpr_with_args t.
Arguments Sexpr_with_args : clear implicits.

Definition set_of {t} (e' : interp_type t) :=
  match t return interp_type t -> interp_type val -> Prop with
  | set => fun e' => e'
  | val => fun e' => eq e'
  end e'.

Definition agrees {t} (e : fact.args -> Prop) (e' : interp_type t) :=
  (forall x, set_of e' x <-> e (fact.normal_args [x])) /\
    (exists S, e (fact.meta_args [value_pattern.any] S)).

(*a fresh name, so that the recursive occurrences below really refer to this
  tactic rather than to the imported [Datalog.invert_stuff]*)
Ltac agg_invert_stuff :=
  match goal with
  | _ => match goal with _ => Datalog.invert_stuff end
  | H: _ \/ _ |- _ => destruct H as [H|H]
  | H: In _ (_ :: _) |- _ => destruct H
  | H: program.interp_step _ _ _ |- _ => invert H
  | H: Forall _ (map _ _) |- _ => progress cbn [map] in H
  | H: Exists _ _ |- _ => invert1_Exists ltac:(repeat agg_invert_stuff) H
  | H: pftree _ _ (fact.normal _) |- _ =>
      (apply pftree.invert in H; destruct H; [solve[repeat agg_invert_stuff]|]) ||
      (apply pftree.invert in H; destruct H; [|solve[repeat agg_invert_stuff]])
  end.

Ltac invert_stuff := agg_invert_stuff.

Lemma check_is_not_input var (vs : list (@block_rel var)):
  forallb (fun v => match v with | input _ => false | local _ => true end) vs = true ->
  Forall is_not_input vs.
Proof.
  intros H. fwd. eapply Forall_impl; [eassumption|]. simpl.
  intros R. destruct R; simpl; congruence || auto.
Qed.

Lemma compile_Sexpr_valid var t (e : Sexpr (fun _ => var) t) :
  valid_blocks_prog (compile_Sexpr e).
Proof.
  induction e; simpl;
    repeat match goal with
      | _ => progress (intros; ssplit; auto)
      | |- program.meta_rules_valid _ =>
          eapply check_meta_rules_valid_sound with (fn_inj := fn_inj);
          [apply fn_inj_correct|];
          reflexivity
      | |- NoDup _ =>
          eapply @nodupb_sound; [typeclasses eauto|];
          reflexivity
      | |- Forall is_not_input _ =>
          apply check_is_not_input; reflexivity
      end.
Qed.

Ltac destr_vbp :=
  repeat match goal with
    | H: valid_blocks_prog _ |- _ =>
        progress (cbn [compile_Sexpr] in H;
                  repeat rewrite valid_blocks_prog_LetIn in H;
                  fwd)
    | H: forall _, valid_blocks_prog _ |- _ =>
        specialize (H (fun _ => False))
    | H: forall _, valid_blocks_prog _ /\ _ |- _ =>
        specialize (H (fun _ => False))
    end.

Hint Resolve vars_in_incl : core.
Hint Constructors vars_in : core.
Lemma compile_Sexpr_vars_in var1 var2 t (dummy : forall t, var1 t) e (ctx : list (@ctx_elt2 var1 (fun _ => var2))) e0 :
  wf_Sexpr ctx t e e0 ->
  vars_in (map (@ctx_elt_p2 _ (fun _ => _)) ctx) (compile_Sexpr e0).
Proof.
  induction 1;
    repeat match goal with
      | _ => progress (intros; simpl in * )
      | |- vars_in _ _ => constructor
      | |- In _ (map _ _) => apply in_map_iff
      | |- Forall _ (_ :: _) => constructor
      | |- Forall _ [] => constructor
      | _ => solve[eauto]
      | |- vars_in (_ :: _) _ => eapply vars_in_incl; [|solve[eauto]]; auto with incl
      end.
  eexists. split; [|eassumption]. reflexivity.
Qed.

Definition dummy (t : type) : interp_type t :=
  match t with
  | val => O
  | set => fun _ => False
  end.
Hint Resolve dummy : core.

Ltac interp_exprs := Blocks.interp_exprs.
Hint Unfold Option.option_relation : core.
Lemma compile_Sexpr_correct ctx t e e0 e' :
  wf_Sexpr ctx t e e0 ->
  Forall (fun elt => agrees elt.(ctx_elt_p2) elt.(ctx_elt_p1)) ctx ->
  Forall fact.honest_args (map (@ctx_elt_p2 _ (fun _ => _)) ctx) ->
  valid_blocks_prog (compile_Sexpr e0) ->
  interp_Sexpr e e' ->
  agrees (interp_blocks_prog (compile_Sexpr e0)) e'.
Proof.
  intros Hwf Hctx Hhonest Hvalid. revert e'. induction Hwf; intros e' He'.
  - dep_invert He'. rewrite Forall_forall in Hctx.
    specialize (Hctx _ H). clear H. simpl in Hctx.
    cbv [agrees] in Hctx. fwd.
    cbv [agrees]. simpl. split.
    + intros x. rewrite Hctxp0. clear Hctxp0. split.
      -- intros Hx. eapply pftree.step with
           (l := map fact.normal [{| normal_fact.rel := input O;
                                    normal_fact.args := [x] |}]).
         ++ constructor. apply Exists_cons_hd.
            eapply rule.interp_impl with (ctx := map.put map.empty 0 _); interp_exprs.
         ++ interp_exprs.
      -- intros Hx. repeat invert_stuff. assumption.
    + eexists. eapply pftree.step with
        (l := map fact.meta [{| meta_fact.pattern :=
                                 {| fact_pattern.rel := input O;
                                   fact_pattern.args := [value_pattern.any] |};
                               meta_fact.set := S |}]).
      -- constructor. simpl. apply Exists_cons_hd.
         eapply meta_rule.interp_canonical with (ctx := map.empty); interp_exprs.
      -- interp_exprs.
  - dep_invert He'.
    destr_vbp.
    specialize (IHHwf1 ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) _ ltac:(eassumption)).
    specialize (IHHwf2 ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) _ ltac:(eassumption)).
    cbv [agrees] in IHHwf1, IHHwf2. fwd.
    simpl. split.
    + intros x. simpl. split.
      -- intros. subst. eapply pftree.step with
           (l := map fact.normal
                   [{| normal_fact.rel := input 0; normal_fact.args := [x'] |};
                    {| normal_fact.rel := input 1; normal_fact.args := [y'] |}]).
         ++ constructor. apply Exists_cons_hd.
            eapply rule.interp_impl with (ctx := map.put (map.put map.empty 0 _) 1 _); interp_exprs.
         ++ interp_exprs.
            --- apply IHHwf1p0. reflexivity.
            --- apply IHHwf2p0. reflexivity.
      -- intros H. repeat invert_stuff. simpl in *. repeat invert_stuff.
         match goal with
         | H: _ |- _ => apply IHHwf1p0 in H
         end.
         match goal with
         | H: _ |- _ => apply IHHwf2p0 in H
         end.
         cbv [set_of] in *. subst. reflexivity.
    + eexists. eapply pftree.step with
        (l := map fact.meta
                [{| meta_fact.pattern :=
                     {| fact_pattern.rel := input 0;
                       fact_pattern.args := [value_pattern.any] |};
                   meta_fact.set := _ |};
                 {| meta_fact.pattern :=
                     {| fact_pattern.rel := input 1;
                       fact_pattern.args := [value_pattern.any] |};
                   meta_fact.set := _ |}]).
      -- constructor. simpl. apply Exists_cons_hd.
         eapply meta_rule.interp_canonical with (ctx := map.empty); interp_exprs.
      -- interp_exprs.
  - dep_invert He'. simpl. split.
    + intros x. split.
      -- contradiction.
      -- intros H. repeat invert_stuff.
    + eexists. eapply pftree.step with (l := map fact.meta []).
      -- constructor. simpl. apply Exists_cons_hd.
         eapply meta_rule.interp_canonical with (ctx := map.empty); interp_exprs.
      -- interp_exprs.
  - dep_invert He'.
    specialize (IHHwf ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) _ ltac:(eassumption)).
    cbv [agrees] in IHHwf. fwd. split.
    + intros x. rewrite <- IHHwfp0. split; auto.
    + eauto.
  - dep_invert He'.
    destr_vbp.
    specialize (IHHwf1 ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) _ ltac:(eassumption)).
    specialize (IHHwf2 ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) _ ltac:(eassumption)).
    cbv [agrees] in IHHwf1, IHHwf2. cbv [agrees]. fwd. simpl. split.
    + intros x. rewrite IHHwf1p0, IHHwf2p0. clear IHHwf1p0 IHHwf2p0. split.
      -- intros [? ?]. eapply pftree.step with
           (l := map fact.normal
                   [{| normal_fact.rel := input 0; normal_fact.args := [x] |};
                    {| normal_fact.rel := input 1; normal_fact.args := [x] |}]).
         ++ constructor. apply Exists_cons_hd.
            eapply rule.interp_impl with (ctx := map.put map.empty 0 _); interp_exprs.
         ++ interp_exprs.
      -- intros H. repeat invert_stuff. simpl in *. repeat invert_stuff. auto.
    + eexists. eapply pftree.step with
        (l := map fact.meta
                [{| meta_fact.pattern :=
                     {| fact_pattern.rel := input 0;
                       fact_pattern.args := [value_pattern.any] |};
                   meta_fact.set := _ |};
                 {| meta_fact.pattern :=
                     {| fact_pattern.rel := input 1;
                       fact_pattern.args := [value_pattern.any] |};
                   meta_fact.set := _ |}]).
      -- constructor. simpl. apply Exists_cons_hd.
         eapply meta_rule.interp_canonical with (ctx := map.empty); interp_exprs.
      -- interp_exprs.
  - rename H0 into IHHwf'.
    dep_invert He'.
    simpl in Hvalid. fwd.
    specialize (IHHwf ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) _ ltac:(eassumption)).
    simpl in IHHwf'.
    epose_dep IHHwf'.
    specialize (IHHwf' ltac:(eauto)). specialize' IHHwf'.
    { constructor; auto. eapply interp_blocks_prog_honest; eauto.
      eapply compile_Sexpr_vars_in; eauto. }
    specialize (IHHwf' ltac:(eauto) ltac:(eauto) ltac:(eauto)).
    clear Hctx. cbv [agrees] in *. fwd. split.
    + intros x. rewrite IHHwf'p0. clear IHHwf'p0.
      simpl. reflexivity.
    + simpl. eauto.
  - dep_invert He'.
    destr_vbp.
    rename H2 into Hset.
    specialize (IHHwf ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) _ ltac:(eassumption)).
    cbv [agrees]. simpl. cbv [agrees] in IHHwf. fwd. split.
    + intros x. split.
      -- intros. subst. eapply pftree.step.
         ++ constructor. apply Exists_cons_hd.
            eassert (fold_right _ _ _ = _) as ->.
            2: { eapply rule.interp_agg. eapply is_list_set_ext.
                 - apply is_list_set_map with (f := fun x => (x, x)).
                   2: eassumption.
                   cbv [Finite.Injective]. invert 1. reflexivity.
                 - simpl. intros [? ?]. instantiate (1 := fun x =>
                                                            match x with
                                                            | [_; _] => _
                                                            | _ => _
                                                            end).
                   simpl. reflexivity. }
            simpl. cbv [interp_agg]. rewrite map_map. simpl.
            rewrite map_id. reflexivity.
         ++ constructor.
            --- eapply pftree.step with
                  (l := map fact.meta
                          [{| meta_fact.pattern :=
                               {| fact_pattern.rel := input 0;
                                 fact_pattern.args := [value_pattern.any] |};
                             meta_fact.set :=
                               fun args => interp_blocks_prog (compile_Sexpr x2)
                                             (fact.normal_args args) |}]).
                +++ constructor. simpl. doExists 1.
                    eapply meta_rule.interp_intro with (ctx := map.empty)
                      (pat := {| fact_pattern.rel := local 1;
                                fact_pattern.args := [value_pattern.any; value_pattern.any] |}).
                    { interp_exprs. }
                    { interp_exprs. }
                    split; [reflexivity|].
                    simpl. intros. repeat invert_stuff. split.
                    ---- intros H. fwd. cbv [rule.one_step_derives].
                         exists (map fact.normal [{| normal_fact.rel := input 0;
                                               normal_fact.args := [x] |}]). split.
                         { doExists 1.
                           eapply rule.interp_impl with (ctx := map.put map.empty 0 _); interp_exprs. }
                         constructor; [|constructor]. apply Exists_cons_hd.
                         cbv [fact.implied_by_mf meta_fact.matches]. simpl. split.
                         { split; [reflexivity|]. repeat constructor. }
                         apply IHHwfp0. assumption.
                    ---- intros H. repeat invert_stuff.
                         eexists. split; [reflexivity|]. apply IHHwfp0. assumption.
                +++ constructor; [|constructor]. apply pftree.leaf.
                    simpl. apply Exists_cons_hd. split; [reflexivity|].
                    eapply use_valid_blocks_prog.
                    ++++ eauto.
                    ++++ eapply compile_Sexpr_vars_in. 2: eassumption. 1: eauto.
                    ++++ eauto.
                    ++++ eassumption.
            --- rewrite map_map. apply List.Forall_map.
                cbv [is_list_set] in Hset. fwd. apply Forall_forall.
                intros x Hx. apply Hsetp0 in Hx. apply IHHwfp0 in Hx.
                eapply pftree.step with
                  (l := map fact.normal [{| normal_fact.rel := input 0;
                                           normal_fact.args := [x] |}]).
                +++ constructor. doExists 1.
                    eapply rule.interp_impl with (ctx := map.put map.empty 0 _); interp_exprs.
                +++ interp_exprs.
      -- intros H.
         repeat lazymatch goal with
                | H: pftree _ _ (fact.meta _) |- _ => fail
                | _ => invert_stuff
                end.
         lazymatch goal with
         | H: pftree _ _ (fact.meta _) |- _ => rename H into Hmf
         end.
         simpl in Hvalidp1. fwd.
         apply program.valid_impl_honest in Hvalidp1p0.
         eapply Hvalidp1p0 in Hmf.
         2: { apply block_good_input_set.
              - constructor; [intros []|constructor].
              - eassumption.
              - constructor; [|constructor]. simpl.
                eapply interp_blocks_prog_honest; eauto.
                eapply compile_Sexpr_vars_in; eauto. }
         move Hmf at bottom.
         assert (Heq: forall x y, (x = y /\ x' x) <-> S0 [x; y]).
         { intros x y. cbv [fact.set_consistent_with] in Hmf.
           specialize (Hmf {| normal_fact.rel := local 1;
                             normal_fact.args := [x; y] |}).
           simpl in Hmf.
           specialize (Hmf ltac:(split; [reflexivity|]; repeat constructor)).
           rewrite Hmf.
           cbv [fact.normal_subset]. rewrite IHHwfp0. split.
           - intros H'. fwd. eapply pftree.step with
               (l := map fact.normal [{| normal_fact.rel := input 0;
                                        normal_fact.args := [y] |}]).
             + constructor. doExists 1.
               eapply rule.interp_impl with (ctx := map.put map.empty 0 _); interp_exprs.
             + interp_exprs.
           - intros H'. repeat invert_stuff. auto. }
         match goal with
         | H: is_list_set (fun _ => _) _ |- _ => rename H into Hset'
         end.
         move Hset at bottom. move Hset' at bottom.
         cbv [interp_agg]. simpl.
         apply fold_right_change_order.
         { (*all bops are commutative, for a certain interpretation of the word*)
           intros. destruct o; simpl; lia. }
         eapply is_list_set_perm. 1: eassumption.
         cbv [is_list_set] in Hset, Hset'. fwd. split.
         { intros x. split; intros Hx.
           - rewrite in_map_iff. eexists (_, _). rewrite <- Hset'p0. rewrite <- Heq.
             simpl. eauto.
           - apply in_map_iff in Hx. fwd. apply Hset'p0 in Hxp1. destruct x0.
             apply Heq in Hxp1. fwd. assumption. }
         apply Finite.Injective_map_NoDup_in; [|assumption].
         intros (?, ?) (?, ?). simpl. intros H1' H2' ?. subst.
         apply Hset'p0 in H1', H2'. apply Heq in H1', H2'. fwd. reflexivity.
    + eexists. eapply pftree.step with
        (l := map fact.meta
                [{| meta_fact.pattern :=
                     {| fact_pattern.rel := local 1;
                       fact_pattern.args := [value_pattern.any; value_pattern.any] |};
                   meta_fact.set := _ |}]).
      -- constructor. simpl. apply Exists_cons_hd.
         eapply meta_rule.interp_canonical with (ctx := map.empty); interp_exprs.
      -- constructor; [|constructor].
         eapply pftree.step with
           (l := map fact.meta
                   [{| meta_fact.pattern :=
                        {| fact_pattern.rel := input 0;
                          fact_pattern.args := [value_pattern.any] |};
                      meta_fact.set := _ |}]).
         ++ constructor. simpl. doExists 1.
            eapply meta_rule.interp_canonical with (ctx := map.empty); interp_exprs.
         ++ interp_exprs.
            Unshelve.
            all: exact True.
Qed.

Lemma compile_SExpr_correct t (e : SExpr t) e' :
  Wf_Sexpr e ->
  interp_Sexpr (e _) e' ->
  agrees (interp_blocks_prog (compile_Sexpr (e _))) e'.
Proof.
  intros Hwf Hinterp.
  eapply compile_Sexpr_correct with (ctx := []).
  - apply Hwf.
  - constructor.
  - constructor.
  - apply compile_Sexpr_valid.
  - exact Hinterp.
Qed.
End __.
