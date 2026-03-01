From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From coqutil Require Import Map.Interface Map.Properties Map.Solver Datatypes.List Tactics Tactics.fwd.
From Datalog Require Import List Datalog (* FancyNotations *) Tactics.
Import ListNotations.

Section __.
Variant bop := sum | prod.
Variant type := val | set.
Let rel : Type := nat.
Variant obj0 :=
  | natobj' (_ : nat).
Variant obj :=
  | primitive (_ : obj0)
  (* | setobj (_ : nat -> Prop) *)
  (* | listsetobj (_ : list nat -> Prop) *)
  | setobj (_ : nat -> Prop)
  | factset (_ : rel * list obj0 -> Prop)
  | blank
  | iter.
Context {context : map.map nat obj} {context_ok : map.ok context}.
Definition natobj x := primitive (natobj' x).
Let fact : Type := fact rel obj.
Variant fn :=
  | fn_lit (o : obj)
  | fn_bop (o : bop)
  | fn_fun (f : list (rel * list obj0 -> Prop) -> rel * list obj0 -> Prop).
Let rule := rule rel nat fn bop.
Let expr := expr nat fn.

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

Section well_formed.
  Context {var1 var2 : type -> Type}.
  Record ctx_elt2 :=
    { ctx_elt_t : type; ctx_elt_p1 : var1 ctx_elt_t; ctx_elt_p2 : var2 ctx_elt_t }.

  Inductive wf_Sexpr : list ctx_elt2 -> forall t, Sexpr var1 t -> Sexpr var2 t -> Prop :=
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
End well_formed.

Definition lit x : expr := fun_expr (fn_lit x) [].

Definition union : list expr -> expr :=
  fun_expr (fn_fun (fun args x => Exists (fun P => P x) args)).

Print signature.

Definition interp_bop o x y :=
  match o with
  | sum => x + y
  | prod => x * y
  end.
Print fn. Print option_all.
Definition interp_fn (f : fn) (args : list obj) : option obj :=
  match f with
  | fn_lit x => Some x
  | fn_bop o =>
      match args with
      | [primitive (natobj' x); primitive (natobj' y)] => Some (natobj (interp_bop o x y))
      | _ => None
      end
  | fn_fun g =>
      match option_all (map (fun x =>
                               match x with
                               | factset f => Some f
                               | _ => None
                               end) args)
      with
      | Some args' => Some (factset (g args'))
      | None => None
      end
  end.
Print signature. Print obj.
Definition get_set (s : obj) :=
  match s with
  | primitive _ => None
  | setobj P => Some (fun x =>
                       match x with
                       | primitive (natobj' x0) => P x0
                       | _ => False
                       end)
  | factset fs => None
  | blank => None
  | iter => None
  end.

Check fold_right.
Definition extract_nat (x : obj) :=
  match x with
  | primitive (natobj' x0) => Some x0
  | _ => None
  end.

Definition interp_agg o (i_xis : list (obj * obj)) :=
  match option_all (map extract_nat (map snd i_xis)) with
  | Some xis => natobj (fold_right (interp_bop o) (bop_id o) xis)
  | None => natobj O
  end.

Instance Sig : signature fn bop obj :=
  { interp_fun := interp_fn ;
    get_set := get_set;
    iter := iter;
    interp_agg := interp_agg }.

Definition closure (p : list rule) : list expr -> expr :=
  fun_expr (fn_fun (fun args x => prog_impl_implication (sig := Sig) p
                                 (fun y => exists y',
                                      Exists (fun P => P y') args /\
                                        y = {| fact_R := (fst y', normal);
                                              fact_args := map primitive (snd y') |})
                                 {| fact_R := (fst x, normal); fact_args := map primitive (snd x) |})).

Definition bare_rule : Type := (rel * list expr) * list (rel * list expr).

Definition is_blank (e : expr) :=
  match e with
  | fun_expr (fn_lit blank) [] => true
  | _ => false
  end.

(* Definition meta_rule_of (p : list rule) (r : bare_rule) := *)
(*   let (concl, hyps) := r in *)

Fixpoint compile_Sexpr (name : nat) (out : rel) {t} (e : Sexpr (fun _ => nat) t) : nat * list rule * (list rule -> list rule) :=
  match e with
  | Var t x => (name,
                [normal_rule
                   [{| clause_R := (out, normal); clause_args := [var_expr O] |}]
                   [{| clause_R := (x, normal); clause_args := [var_expr O] |}]],
                fun p =>
                  [normal_rule
                     [{| clause_R := (out, meta); clause_args := [var_expr O; lit blank] |}]
                     [{| clause_R := (x, meta); clause_args := [var_expr O; lit blank] |}]
              ])
  | bop_over_vals o x y =>
      let x' := name in
      let '(name1, p1, p1') := compile_Sexpr (S name) x' x in
      let y' := name1 in
      let '(name2, p2, p2') := compile_Sexpr (S name1) y' y in
      (name2,
        normal_rule
          [{| clause_R := (out, normal); clause_args := [fun_expr (fn_bop o) [var_expr O; var_expr (S O)]] |}]
          [{| clause_R := (x', normal); clause_args := [var_expr O] |};
           {| clause_R := (y', normal); clause_args := [var_expr (S O)] |}]
          :: p1 ++ p2,
        fun p =>
          normal_rule
            [{| clause_R := (out, meta); clause_args := [closure p [var_expr O; var_expr (S O)]; lit blank]|}]
            [{| clause_R := (x', meta); clause_args := [var_expr O; lit blank]|};
             {| clause_R := (y', meta); clause_args := [var_expr (S O); lit blank]|}]
            :: p1' p ++ p2' p)
  | empty => (name, [],
              fun p =>[normal_rule
                      [{| clause_R := (out, meta); clause_args := [fun_expr (fn_lit (factset (fun _ => False))) []; fun_expr (fn_lit blank) []] |}]
                      []])
  | singleton x => (*we happen to represent sets in the same format as elements*)
      compile_Sexpr name out x
  | intersection x y =>
      let x' := name in
      let '(name1, p1, p1') := compile_Sexpr (S name) x' x in
      let y' := name1 in
      let '(name2, p2, p2') := compile_Sexpr (S name1) y' y in
      (name2,
        normal_rule
          [{| clause_R := (out, normal); clause_args := [var_expr O] |}]
          [{| clause_R := (x', normal); clause_args := [var_expr O] |};
           {| clause_R := (y', normal); clause_args := [var_expr O] |}]
          :: p1 ++ p2,
        fun p =>
          normal_rule
            [{| clause_R := (out, meta); clause_args := [closure p [var_expr O; var_expr (S O)]] |}]
            [{| clause_R := (x', meta); clause_args := [var_expr O; lit blank] |};
             {| clause_R := (y', meta); clause_args := [var_expr O; lit blank] |}]
            :: p1' p ++ p2' p)
  | let_in t1 t2 x y =>
      let x' := name in
      let '(name1, p1, p1') := compile_Sexpr (S name) x' x in
      let '(name2, p2, p2') := compile_Sexpr (S name1) out (y x') in
      (name2, p1 ++ p2, fun p => p1' p ++ p2' p)
  | bop_over_set o x =>
      let x' := name in
      let '(name1, p1, p1') := compile_Sexpr (S name) x' x in
      (name1, agg_rule out o x' :: p1, p1')
  end.

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

Definition agrees Q (p : list rule) t name (e' : interp_type t) :=
  match t return interp_type t -> _ with
  | set => fun e' =>
            (forall x,
                prog_impl_implication p Q
                                      {| fact_R := (name, normal);
                                        fact_args := [natobj x] |} <->
                  e' x)
  | _ => fun e' =>
          forall x,
            prog_impl_implication p Q {| fact_R := (name, normal);
                                        fact_args := [natobj x] |} <->
              e' = x
  end e'.

Ltac dep_invert H :=
  invert H;
  repeat match goal with
    | H: existT _ _ _ = existT _ _ _ |- _ => apply Eqdep.EqdepTheory.inj_pair2 in H
    end;
  subst.

Lemma cons_is_app {T} (x : T) l :
  x :: l = [x] ++ l.
Proof. reflexivity. Qed.

Lemma cons_two_is_app {T} (x y : T) l :
  x :: y :: l = [x; y] ++ l.
Proof. reflexivity. Qed.

Lemma disjoint_lists_alt {T} (l1 l2 : list T) :
  Forall (fun x => Forall (fun y => y <> x) l2) l1 ->
  disjoint_lists l1 l2.
Proof.
  cbv [disjoint_lists]. induction 1; simpl.
  - auto.
  - intros ? [?|?]; subst; eauto.
    rewrite Forall_forall in *. unfold not in *. eauto.
Qed.

Lemma compile_Sexpr_correct Q datalog_ctx ctx t e e_nat e' name out name' p p' :
  wf_Sexpr ctx t e e_nat ->
  Forall (fun elt => agrees Q datalog_ctx _ elt.(ctx_elt_p2) elt.(ctx_elt_p1)) ctx ->
  ~In out (map (fun x => @ctx_elt_p2 _ (fun _ => nat) x) ctx) ->
  Forall (fun R => R <> out) (flat_map hyp_rels datalog_ctx) ->
  interp_Sexpr e e' ->
  compile_Sexpr name out e_nat = (name', p, p') ->
  agrees Q (p ++ p' p ++ datalog_ctx) t out e'.
Proof.
  intros Hwf. revert datalog_ctx.
  induction Hwf; intros datalog_ctx Hctx Hout1 Hout2 He' Hcomp.
  - dep_invert He'. simpl in Hcomp. invert Hcomp. destruct t; simpl.
    + intros x. split.
      -- intros Himpl. rewrite cons_two_is_app in Himpl. apply staged_program in Himpl.
         2: { simpl. apply disjoint_lists_alt; auto. }
         apply loopless_program in Himpl.
         2: { simpl. apply disjoint_lists_alt. enough (x2 <> out) by auto.
              intro. subst. apply Hout1. apply in_map_iff. eexists.
              split; [|eassumption]. reflexivity. }
         destruct Himpl as [Himpl|Himpl].
         ++ admit.
         ++ fwd. apply Exists_cons in Himplp1. destruct Himplp1 as [Himpl|Himpl].
            --- rewrite Forall_forall in Hctx.
                specialize (Hctx _ ltac:(eassumption)). simpl in Hctx. apply Hctx.
                invert_stuff. eassert (_ = y) as ->.
                { destruct y. simpl in *. f_equal; auto; congruence. }
                assumption.
            --- invert_stuff.
      -- intros. subst. eapply prog_impl_step.
         ++ apply Exists_cons_hd. Check map.put.
            apply normal_rule_impl with (ctx := map.put map.empty 0 (natobj x)).
            --- apply Exists_cons_hd. cbv [interp_clause]. simpl. split; auto.
                constructor; [|constructor]. constructor.
                (*map_solver context_ok. (*anomaly*) *)
                rewrite map.get_put_same. reflexivity.
            --- constructor; [|constructor]. cbv [interp_clause]. simpl.
                instantiate (1 := {| fact_R := _; fact_args := _ |}).
                simpl. split; eauto. constructor; [|constructor].
                constructor. apply map.get_put_same.
         ++ constructor; [|constructor]. rewrite Forall_forall in Hctx.
            specialize (Hctx _ ltac:(eassumption)). simpl in Hctx.
            eapply prog_impl_implication_subset; [|apply Hctx; reflexivity].
            intros. simpl. auto.
    + intros x. split.
      --
