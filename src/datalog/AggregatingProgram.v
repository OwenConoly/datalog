From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From coqutil Require Import Map.Interface Map.Properties Map.Solver Datatypes.List Tactics Tactics.fwd.
From Datalog Require Import List Datalog (* FancyNotations *) Tactics Blocks.
Import ListNotations.

Section __.
Variant bop := sum | prod.
Variant type := val | set.
Notation rel := nat (only parsing).
Definition obj := nat.
Context {context : map.map nat obj} {context_ok : map.ok context}.
Context {gmap : map.map rel (fact_args obj -> Prop)} {gmap_ok : map.ok gmap}.
Notation fact := (fact rel obj).
Variant fn :=
  | fn_lit (o : obj)
  | fn_bop (o : bop).
Notation rule := (rule rel nat fn bop).
Notation expr := (expr nat fn). Print blocks_prog.
Notation blocks_prog var := (@blocks_prog nat nat fn bop var).

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

Definition interp_bop o x y :=
  match o with
  | sum => x + y
  | prod => x * y
  end.

Definition interp_fn (f : fn) (args : list obj) : option obj :=
  match f with
  | fn_lit x => Some x
  | fn_bop o =>
      match args with
      | [x; y] => Some (interp_bop o x y)
      | _ => None
      end
  end.

(*might become less trivial later idk*)
Definition extract_nat (x : obj) :=
  Some x.

Definition interp_agg o (i_xis : list (obj * obj)) :=
  match option_all (map extract_nat (map snd i_xis)) with
  | Some xis => fold_right (interp_bop o) (bop_id o) xis
  | None => O
  end.

Instance Sig : signature fn bop obj :=
  { interp_fun := interp_fn ;
    interp_agg := interp_agg }.

Definition bare_rule : Type := (rel * list expr) * list (rel * list expr).

Definition is_blank (e : expr) :=
  match e with
  | fun_expr (fn_lit blank) [] => true
  | _ => false
  end.
Print meta_rule. Print meta_clause. Print blocks_prog. Print LetIn.
Fixpoint compile_Sexpr {t} {var} (e : Sexpr (fun _ => var) t) : blocks_prog var :=
  match e with
  | Var t x =>
      Block O [(O, x)]
        [normal_rule
           [{| clause_rel := local O; clause_args := [var_expr O] |}]
           [{| clause_rel := input O; clause_args := [var_expr O] |}];
         meta_rule
           [{| meta_clause_rel := local O; meta_clause_args := [None] |}]
           [{| meta_clause_rel := input O; meta_clause_args := [None] |}]]
  | bop_over_vals o x y =>
      LetIn (compile_Sexpr x)
        (fun x' =>
           LetIn (compile_Sexpr y)
             (fun y' =>
                Block O [(O, x'); (1, y')]
                  [normal_rule
                     [{| clause_rel := local O; clause_args := [fun_expr (fn_bop o) [var_expr O; var_expr (S O)]] |}]
                     [{| clause_rel := input 0; clause_args := [var_expr O] |};
                      {| clause_rel := input 1; clause_args := [var_expr (S O)] |}];
                   meta_rule
                     [{| meta_clause_rel := local O; meta_clause_args := [None] |}]
                     [{| meta_clause_rel := input 0; meta_clause_args := [None] |};
                      {| meta_clause_rel := input 1; meta_clause_args := [None] |}]]))
  | empty => Block O [] [meta_rule
                          [{| meta_clause_rel := local O; meta_clause_args := [None] |}]
                          []]
  | singleton x => (*we happen to represent sets in the same format as elements*)
      compile_Sexpr x
  | intersection x y =>
      LetIn (compile_Sexpr x)
        (fun x' =>
           LetIn (compile_Sexpr y)
             (fun y' =>
                Block O [(0, x'); (1, y')]
                  [normal_rule
                     [{| clause_rel := local O; clause_args := [var_expr O] |}]
                     [{| clause_rel := input 0; clause_args := [var_expr O] |};
                      {| clause_rel := input 1; clause_args := [var_expr O] |}];
                   meta_rule
                     [{| meta_clause_rel := local O; meta_clause_args := [None] |}]
                     [{| meta_clause_rel := input 0; meta_clause_args := [None] |};
                      {| meta_clause_rel := input 1; meta_clause_args := [None] |}]]))
  | let_in t1 t2 x f =>
      LetIn (compile_Sexpr x)
        (fun x' => compile_Sexpr (f x'))
  | bop_over_set o x =>
      LetIn (compile_Sexpr x)
        (fun x' =>
           Block O [(0, x')]
             [agg_rule (local O) o (local (S O));
              meta_rule
                [{| meta_clause_rel := local O; meta_clause_args := [None] |}]
                [{| meta_clause_rel := local (S O); meta_clause_args := [None; None] |}];
              normal_rule
                [{| clause_rel := local (S O); clause_args := [var_expr O; var_expr O] |}]
                [{| clause_rel := input 0; clause_args := [var_expr O] |}];
              meta_rule
                [{| meta_clause_rel := local (S O); meta_clause_args := [None; None] |}]
                [{| meta_clause_rel := input 0; meta_clause_args := [None] |}]])
  end.

Definition sum_expr {var} (S : var set) :=
  bop_over_set sum (Var _ S).
Print compile_Sexpr.
Compute (compile_Sexpr (sum_expr 0)).

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

(* Definition well_typed (f : fact) := *)
(*   match snd f.(fact_R) with *)
(*   | normal => exists x, f.(fact_args) = [primitive x] *)
(*   | meta => exists S0, f.(fact_args) = [factset S0; blank] *)
(*   end. *)

(* Definition good_inputs is_input (Q : fact -> Prop) := *)
(*   forall f, Q f -> is_input (fst f.(fact_R)) /\ well_typed f. *)

(* Definition well_typed_prog (p : list rule) := *)
(*   forall Q, *)
(*     (forall f, Q f -> well_typed f) -> *)
(*     (forall f, prog_impl_implication p Q f -> well_typed f). *)

(* Definition is_normal (r : rule) := *)
(*   match r with *)
(*   | normal_rule _ _ => True *)
(*   | agg_rule _ _ _ => False *)
(*   end. *)

(* Definition syntactically_depends_only_on (p : list rule) R Rs := *)
(*   Forall (fun r => In (R, normal) (concl_rels r) -> incl (hyp_rels r) (map (fun x => (x, normal)) Rs)) p. *)

(* Definition mrs_very_sound p := forall R, mrs_very_sound_for p R. *)

Ltac plda :=
  repeat lazymatch goal with
    | |- Forall _ _ => first [constructor | eapply Forall_impl; [|eassumption]; cbv beta | apply Forall_forall; intros ]
    | |- _ <> _ => intro
    | |- _ => intros; fwd; congruence
    end.

Definition set_of {t} (e' : interp_type t) :=
  match t return interp_type t -> interp_type val -> Prop with
  | set => fun e' => e'
  | val => fun e' => eq e'
  end e'.

Definition agrees {t} (e : fact_args _ -> Prop) (e' : interp_type t) :=
  (forall x, set_of e' x <-> e (normal_fact_args [x])) /\
    (exists S, e (meta_fact_args [None] S)).

Ltac invert0_Exists H :=
  repeat first [invert0 H |
                 apply Exists_cons in H; destruct H as [H|H]; [solve[repeat invert_stuff] | invert0_Exists H] ].

Ltac invert1_Exists H :=
  repeat first [invert0 H |
                 apply Exists_cons in H; destruct H as [H|H]; [solve[repeat invert_stuff] | invert1_Exists H] |
                 apply Exists_cons in H; destruct H as [H|H]; [|invert0_Exists H] ].

Ltac invert_stuff :=
  first [invert_stuff |
          match goal with
          | H: Exists _ _ |- _ => invert1_Exists H
          end].

Ltac interp_exprs := interp_exprs.

Hint Unfold Option.option_relation : core.
Lemma compile_Sexpr_correct ctx t e e0 e' :
  wf_Sexpr ctx t e e0 ->
  Forall (fun elt => agrees elt.(ctx_elt_p2) elt.(ctx_elt_p1)) ctx ->
  honest_blocks_prog map.empty (compile_Sexpr e0) ->
  interp_Sexpr e e' ->
  agrees (interp_blocks_prog map.empty (compile_Sexpr e0)) e'.
Proof.
  intros Hwf Hctx Hnl. revert e'. induction Hwf; intros e' He'.
  - dep_invert He'. rewrite Forall_forall in Hctx.
    specialize (Hctx _ H). clear H. simpl in Hctx.
    cbv [agrees] in Hctx. fwd. cbv [agrees]. simpl. split.
    + intros. rewrite Hctxp0. clear Hctxp0. split.
      -- intros. eapply block_prog_impl_step.
         ++ simpl. apply Exists_cons_hd. constructor.
            eapply normal_rule_impl with (ctx := map.put map.empty 0 _); interp_exprs.
         ++ interp_exprs.
      -- intros. repeat invert_stuff. assumption.
    (*meta fact*)
    + eexists. eapply block_prog_impl_step.
      -- simpl. apply Exists_cons_tl. apply Exists_cons_hd.
         eapply meta_rule_impl with (ctx := map.empty) (S := fun _ => _); interp_exprs.
      -- interp_exprs.
  - dep_invert He'.
    cbn [honest_blocks_prog compile_Sexpr] in Hnl. fwd.
    specialize (IHHwf1 ltac:(eassumption) ltac:(eassumption) _ ltac:(eassumption)).
    specialize (IHHwf2 ltac:(eassumption) ltac:(eassumption) _ ltac:(eassumption)).
    cbv [agrees] in IHHwf1, IHHwf2. fwd.
    simpl. split.
    + intros x. simpl. split.
      -- intros. subst. eapply block_prog_impl_step.
         ++ simpl. apply Exists_cons_hd. constructor.
            eapply normal_rule_impl with (ctx := map.put (map.put map.empty 0 _) 1 _); interp_exprs.
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
    + eexists. eapply block_prog_impl_step.
      -- simpl. apply Exists_cons_tl. apply Exists_cons_hd.
         eapply meta_rule_impl with (ctx := map.empty) (S := fun _ => _); interp_exprs.
      -- interp_exprs.
  - dep_invert He'. simpl. split.
    + intros x. split.
      -- contradiction.
      -- intros H. repeat invert_stuff.
    + eexists. eapply block_prog_impl_step.
      -- simpl. apply Exists_cons_hd.
         eapply meta_rule_impl with (ctx := map.empty) (S := fun _ => _); interp_exprs.
      -- interp_exprs.
  - dep_invert He'.
    specialize (IHHwf ltac:(eassumption) ltac:(eassumption) _ ltac:(eassumption)).
    cbv [agrees] in IHHwf. fwd. split.
    + intros x. rewrite <- IHHwfp0. split; auto.
    + eauto.
  - dep_invert He'.
    cbn [honest_blocks_prog compile_Sexpr] in Hnl. fwd.
    specialize (IHHwf1 ltac:(eassumption) ltac:(eassumption) _ ltac:(eassumption)).
    specialize (IHHwf2 ltac:(eassumption) ltac:(eassumption) _ ltac:(eassumption)).
    cbv [agrees] in IHHwf1, IHHwf2. cbv [agrees]. fwd. simpl. split.
    + intros x. rewrite IHHwf1p0, IHHwf2p0. clear IHHwf1p0 IHHwf2p0. split.
      -- intros [? ?]. eapply block_prog_impl_step.
         ++ simpl. apply Exists_cons_hd. constructor.
            eapply normal_rule_impl with (ctx := map.put map.empty 0 _); interp_exprs.
         ++ interp_exprs.
      -- intros H. repeat invert_stuff. auto.
    + eexists. eapply block_prog_impl_step.
      -- simpl. apply Exists_cons_tl. apply Exists_cons_hd.
         eapply meta_rule_impl with (ctx := map.empty) (S := fun _ => _); interp_exprs.
      -- interp_exprs.
  - rename H0 into IHHwf'.
    dep_invert He'.
    cbn [honest_blocks_prog compile_Sexpr] in Hnl. fwd.
    specialize (IHHwf ltac:(eassumption) ltac:(eassumption) _ ltac:(eassumption)).
    specialize (IHHwf' _ _ ltac:(eauto) ltac:(eauto) _ ltac:(eauto)).
    clear Hctx. cbv [agrees] in *. fwd. split.
    + intros x. rewrite IHHwf'p0. clear IHHwf'p0.
      simpl. reflexivity.
    + simpl. eauto.
  - dep_invert He'.
    cbn [honest_blocks_prog compile_Sexpr] in Hnl. fwd.
    rename H2 into Hset.
    specialize (IHHwf ltac:(eassumption) ltac:(eassumption) _ ltac:(eassumption)).
    cbv [agrees]. simpl. cbv [agrees] in IHHwf. fwd. split.
    + intros x. split.
      -- intros. subst. eapply block_prog_impl_step.
         ++ simpl. eapply Exists_cons_hd. constructor.
            eassert (fold_right _ _ _ = _) as ->.
            2: { constructor. eapply is_list_set_ext.
                 - apply is_list_set_map with (f := fun x => (x, x)).
                   2: eassumption.
                   cbv [FinFun.Injective]. invert 1. reflexivity.
                 - simpl. intros [? ?]. instantiate (1 := fun x =>
                                                            match x with
                                                            | [_; _] => _
                                                            | _ => _
                                                            end).
                   simpl. reflexivity. }
         simpl. cbv [interp_agg]. do 2 rewrite map_map. simpl.
         cbv [extract_nat]. rewrite option_all_map_Some. reflexivity.
         ++ constructor.
         --- eapply block_prog_impl_mf_ext.
            +++ eapply use_honest_block_prog; [assumption|].
                eapply block_prog_impl_step.
                ---- simpl. do 3 apply Exists_cons_tl. apply Exists_cons_hd.
                    eapply meta_rule_impl with (ctx := map.empty) (S := fun _ => _); interp_exprs.
                ---- interp_exprs.
            +++ simpl. intros. repeat invert_stuff. split.
                ---- intros H. repeat invert_stuff.
                    eexists. split; [reflexivity|]. apply IHHwfp0. assumption.
                ---- intros H. fwd.
                    eapply block_prog_impl_step.
                    ++++ simpl. do 2 apply Exists_cons_tl. apply Exists_cons_hd.
                         constructor.
                         eapply normal_rule_impl with (ctx := map.put map.empty 0 _); interp_exprs.
                    ++++ interp_exprs. apply IHHwfp0. assumption.
         --- rewrite map_map. apply Forall_map.
            cbv [is_list_set] in Hset. fwd. apply Forall_forall.
            intros x Hx. apply Hsetp0 in Hx. apply IHHwfp0 in Hx.
            eapply block_prog_impl_step.
            +++ simpl. do 2 apply Exists_cons_tl. apply Exists_cons_hd.
                constructor.
                eapply normal_rule_impl with (ctx := map.put map.empty 0 _); interp_exprs.
            +++ interp_exprs.
      -- intros H. Print honest_block_prog.
         repeat lazymatch goal with
                | H: block_prog_impl _ _ (meta_fact _ _ _) |- _ => fail
                | _ => invert_stuff
                end.
         lazymatch goal with
         | H: block_prog_impl _ _ (meta_fact _ _ _) |- _ => rename H into Hmf
         end.
         apply Hnlp1 in Hmf. move Hmf at bottom.
         assert (Heq: forall x y, (x = y /\ x' x) <-> S0 [x; y]).
         { intros x y. cbv [consistent] in Hmf. rewrite Hmf; [|interp_exprs].
           rewrite IHHwfp0. split.
           - intros H. fwd. eapply block_prog_impl_step.
             + simpl. do 2 apply Exists_cons_tl. apply Exists_cons_hd. constructor.
               eapply normal_rule_impl with (ctx := map.put map.empty 0 _); interp_exprs.
             + interp_exprs.
           - intros H. repeat invert_stuff. auto. }
         match goal with
         | H: is_list_set (fun _ => _) _ |- _ => rename H into Hset'
         end.
         move Hset at bottom. move Hset' at bottom.
         cbv [interp_agg]. cbv [extract_nat]. rewrite option_all_map_Some.
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
         apply FinFun.Injective_map_NoDup_in; [|assumption].
         intros (?, ?) (?, ?). simpl. intros H1' H2' ?. subst.
         apply Hset'p0 in H1', H2'. apply Heq in H1', H2'. fwd. reflexivity.
    + eexists. eapply block_prog_impl_step.
      -- simpl. apply Exists_cons_tl. apply Exists_cons_hd.
         eapply meta_rule_impl with (ctx := map.empty) (S := fun _ => _); interp_exprs.
      -- interp_exprs. eapply block_prog_impl_step.
         ++ simpl. do 3 apply Exists_cons_tl. apply Exists_cons_hd.
            eapply meta_rule_impl with (ctx := map.empty) (S := fun _ => _); interp_exprs.
         ++ interp_exprs.
            Unshelve.
            all: exact True.
Qed.
