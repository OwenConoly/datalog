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
Notation rel := nat.
Variant obj0 :=
  | natobj' (_ : nat).
Variant obj :=
  | primitive (_ : obj0)
  (* | setobj (_ : nat -> Prop) *)
  (* | listsetobj (_ : list nat -> Prop) *)
  | setobj (_ : nat -> Prop)
  | factset (_ : list obj0 -> Prop)
  | blank
  | iter.
Context {context : map.map nat obj} {context_ok : map.ok context}.
Definition natobj x := primitive (natobj' x).
Notation fact := (fact rel obj).
Variant fn :=
  | fn_lit (o : obj)
  | fn_bop (o : bop)
  | fn_fun (f : list (list obj0 -> Prop) -> list obj0 -> Prop).
Notation rule := (rule rel nat fn bop).
Notation expr := (expr nat fn).

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

(*TODO i'll want to use this one eventually*)
Definition closure' (p : list rule) R (Rs : list rel) : list expr -> expr :=
  fun_expr (fn_fun (fun args x => prog_impl_implication (sig := Sig) p
                                 (fun y => exists R' y',
                                      Exists (fun '(R0, P) => R0 = R' /\ P y') (combine Rs args) /\
                                        y = {| fact_R := (R', normal);
                                              fact_args := map primitive y' |})
                                 {| fact_R := (R, normal); fact_args := map primitive x |})).

Definition closure (p : list rule) R Rs : list expr -> expr :=
  fun_expr (fn_fun (fun args x => prog_impl_implication (sig := Sig) p
                                 (fun y => exists R' x0,
                                      Exists (fun '(R0, P) => R0 = R' /\ P [x0]) (combine Rs args) /\
                                        y = {| fact_R := (R', normal);
                                              fact_args := [primitive x0] |})
                                 {| fact_R := (R, normal); fact_args := map primitive x |})).

Definition bare_rule : Type := (rel * list expr) * list (rel * list expr).

Definition is_blank (e : expr) :=
  match e with
  | fun_expr (fn_lit blank) [] => true
  | _ => false
  end.

(* Definition meta_rule_of (p : list rule) (r : bare_rule) := *)
(*   let (concl, hyps) := r in *)

Definition closure_rule (p : list rule) R (Rs : list rel) : rule :=
  normal_rule
    [{| clause_R := (R, meta); clause_args := [closure p R Rs (map var_expr (seq O (length Rs))); lit blank] |}]
    (map (fun '(R', i) => {| clause_R := (R', meta); clause_args := [var_expr i; lit blank] |}) (combine Rs (seq O (length Rs)))).

Fixpoint compile_Sexpr (name : nat) (out : rel) {t} (e : Sexpr (fun _ => nat) t) : nat * list rule * (list rule -> list rule) :=
  match e with
  | Var t x => (name,
                [normal_rule
                   [{| clause_R := (out, normal); clause_args := [var_expr O] |}]
                   [{| clause_R := (x, normal); clause_args := [var_expr O] |}]],
                fun p =>
                  [closure_rule p out [x]])
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
            [{| clause_R := (out, meta); clause_args := [closure p out [x'; y'] [var_expr O; var_expr (S O)]; lit blank]|}]
            [{| clause_R := (x', meta); clause_args := [var_expr O; lit blank]|};
             {| clause_R := (y', meta); clause_args := [var_expr (S O); lit blank]|}]
            :: p1' p ++ p2' p)
  | empty => (name, [],
              fun p => [normal_rule
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
        fun p => closure_rule p out [x'; y'] :: p1' p ++ p2' p)
  | let_in t1 t2 x y =>
      let x' := name in
      let '(name1, p1, p1') := compile_Sexpr (S name) x' x in
      let '(name2, p2, p2') := compile_Sexpr (S name1) out (y x') in
      (name2, p1 ++ p2, fun p => p1' p ++ p2' p)
  | bop_over_set o x =>
      let x' := name in
      let x'' := S name in
      let '(name1, p1, p1') := compile_Sexpr (S x'') x' x in
      (name1, agg_rule out o x''
                :: normal_rule
                [{| clause_R := (x'', meta);
                   clause_args := [var_expr O; lit iter] |}]
                [{| clause_R := (x', meta);
                   clause_args := [var_expr O; lit blank] |}]
                :: normal_rule
                [{| clause_R := (x'', normal);
                   clause_args := [var_expr O; var_expr O] |}]
                [{| clause_R := (x', normal);
                   clause_args := [var_expr O] |}]
                :: p1, p1')
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
                  e' x) /\
              exists x,
                prog_impl_implication p Q
                                      {| fact_R := (name, meta);
                                        fact_args := [factset x; blank] |}
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

Lemma option_all_map_Some {T} (l : list T) :
  option_all (map Some l) = Some l.
Proof.
  induction l; simpl; auto. rewrite IHl. reflexivity.
Qed.

Lemma idk (p : list rule) Q f :
  ~In f.(fact_R) (flat_map concl_rels p) ->
  prog_impl_implication p Q f ->
  Q f.
Proof.
  intros Hp H. invert H; auto. apply Exists_exists in H0. fwd.
  apply rule_impl_concl_relname_in in H0p1. rewrite in_flat_map in Hp.
  exfalso. eauto.
Qed.

(*TODO there's got to be a less hacky way to do this*)
Lemma decomp_fact (ctx : context) y blah1 blah2 :
  interp_clause ctx y ({| fact_R := blah1; fact_args := blah2 |} : fact) ->
  interp_clause ctx y {| fact_R := blah1; fact_args := blah2 |}.
Proof. auto. Qed.

Ltac interp_exprs :=
  repeat rewrite map_app; simpl;
  repeat match goal with
    | _ => progress simpl
    | |- Forall2 _ (_ ++ _) _ => apply Forall2_app
    | |- Forall2 _ (_ :: _) _ => constructor
    | |- Forall2 _ nil _ => constructor
    | |- Forall2 _ (map var_expr (map inl _)) _ =>
        do 2 rewrite <- Forall2_map_l; try apply Forall2_firstn; solve [interp_exprs]
    | |- Forall2 _ _ _ =>
        (eapply Forall2_impl; [|eassumption]; simpl; intros) ||
          (* (eapply Forall2_impl; *)
          (*  [|apply idx_map_works || *)
          (*      (match goal with *)
          (*       | H: _ = length ?x |- context[seq _ (length ?x)] => rewrite <- H *)
          (*       | H: length ?x = _ |- context[seq _ (length ?x)] => rewrite H *)
          (*       end; *)
    (*       apply idx_map_works)]; simpl; intros) *)
                                                             idtac
    | |- interp_expr _ _ _ => econstructor
    (* | |- interp_expr _ (fun_expr _ _) _ => econstructor *)
    (* | |- interp_expr _ (var_expr _) _ => constructor *)
    (* | |- interp_expr _ (lower_idx _) _ => *)
    (*     eapply interp_expr_subst_more; [|eapply eval_Zexpr_to_substn; eassumption || (apply eval_Zexpr_Z_eval_Zexpr; eassumption)] *)
    (* | |- interp_expr _ (lower_guard _) _ => *)
    (*     eapply interp_expr_subst_more; [|eapply eval_Bexpr_to_substn; eassumption] *)
    | |- interp_expr _ _ _ =>
        eapply interp_expr_subst_more; [|eassumption]
    | |- interp_clause _ _ _ =>
        eapply interp_clause_subst_more; [|eassumption]
    (* | |- map.extends _ _ => extends_solver *)
    (* | |- map.get ?ctx' _ = _ => try subst ctx'; solve_map_get *)
    (* | |- map.get ?ctx' _ = _ => let H := fresh "H" in eenough (map.extends _ _) as H; [apply H; eassumption|]; solve[extends_solver] *)
    | |- interp_clause _ _ ?x =>
        try (is_evar x; eapply decomp_fact); split
    | |- _ /\ _ => split; [solve [interp_exprs] |]
    | |- Exists _ [_] => apply Exists_cons_hd
    (* | |- Forall2 _ (map lower_idx _) _ => eapply Forall2_impl; [|apply eval_Zexprlist_to_substn; eassumption]; intros *)
    | |- _ => reflexivity
    end.

Definition consistent (Q : fact -> Prop) :=
  forall R S0,
    Q {| fact_R := (R, meta); fact_args := [factset S0; blank] |} ->
    forall x,
      Q {| fact_R := (R, normal); fact_args := [primitive x] |} <->
        S0 [x].

Definition well_typed (f : fact) :=
  match snd f.(fact_R) with
  | normal => exists x, f.(fact_args) = [primitive x]
  | meta => exists S0, f.(fact_args) = [factset S0; blank]
  end.

Definition good_inputs is_input (Q : fact -> Prop) :=
  forall f, Q f -> is_input (fst f.(fact_R)) /\ well_typed f.

Definition well_typed_prog (p : list rule) :=
  forall Q,
    (forall f, Q f -> well_typed f) ->
    (forall f, prog_impl_implication p Q f -> well_typed f).

Definition mrs_very_sound_for (p : list rule) R :=
  forall Q S0,
    consistent Q ->
    prog_impl_implication p Q {| fact_R := (R, meta); fact_args := [factset S0; blank] |} ->
    forall x,
      prog_impl_implication p Q {| fact_R := (R, normal); fact_args := [primitive x] |} <->
        Q {| fact_R := (R, normal); fact_args := [primitive x] |} \/ S0 [x].

(*should allow depending on meta facts.?*)
(*i want to say that R depends only on Rs.  this only makes sense when R is not an input*)
Definition depends_only_on (p : list rule) R Rs :=
  forall Q x,
    consistent Q ->
    prog_impl_implication p Q {| fact_R := (R, normal); fact_args := [primitive x] |} ->
    Q {| fact_R := (R, normal); fact_args := [primitive x] |} \/
      prog_impl_implication p (fun f =>
                                 exists x R',
                                   In R' Rs /\
                                     f = {| fact_R := (R', normal); fact_args := [primitive x] |} /\
                                     prog_impl_implication p Q f) {| fact_R := (R, normal); fact_args := [primitive x] |}.

Definition is_normal (r : rule) :=
  match r with
  | normal_rule _ _ => True
  | agg_rule _ _ _ => False
  end.

Definition syntactically_depends_only_on (p : list rule) R Rs :=
  Forall (fun r => In (R, normal) (concl_rels r) -> incl (hyp_rels r) (map (fun x => (x, normal)) Rs)) p.

Lemma depends_only_on_mrs_very_sound_for p R Rs :
  ~In (R, meta) (flat_map hyp_rels p) ->
  ~In R Rs ->
  depends_only_on p R Rs ->
  mrs_very_sound_for p R ->
  Forall (mrs_very_sound_for p) Rs ->
  mrs_very_sound_for (closure_rule p R Rs :: p) R.
Proof.
  intros HR1 HR2 HRs Hp1 Hp2. intros Q S0 HQ1 HS0 x.
  assert (Hstaged : disjoint_lists [(R, meta)] (flat_map hyp_rels p)).
  { simpl. apply disjoint_lists_alt. constructor; [|constructor].
    apply Forall_forall. intros x0 Hx0 ?. subst. auto. }
  assert (Hloopless : disjoint_lists
                        (flat_map concl_rels [closure_rule p R Rs])
                        (flat_map hyp_rels [closure_rule p R Rs])).
  { simpl. rewrite map_map. apply disjoint_lists_alt.
    constructor; [|constructor]. rewrite app_nil_r.
    apply Forall_map. apply Forall_forall. intros (R', ?). intros HR'.
    apply in_combine_l in HR'. simpl. intro. fwd. auto. }
  rewrite cons_is_app in HS0.
  apply staged_program in HS0; [|assumption].
  apply loopless_program in HS0; [|assumption].
  rewrite (cons_is_app _ p).
  rewrite staged_program_iff; [|assumption].
  rewrite loopless_program_iff; [|assumption].
  destruct HS0 as [HS0|HS0].
  { apply Hp1 in HS0; [|assumption]. epose_dep HS0. rewrite HS0. split; auto.
    intros [[?|?]|?]; auto. fwd. invert_stuff. }
  fwd. invert_stuff. clear Hstaged Hloopless.
  simpl in *. invert_stuff. destruct (option_all _) eqn:E; [|discriminate]. fwd.
  split; intros Hx.
  - destruct Hx as [Hx|Hx].
    2: { clear -Hx. fwd. invert_stuff. }
    cbv [depends_only_on] in HRs. specialize (HRs _ _ HQ1 Hx).
    destruct HRs as [HRs|HRs]; auto.
    apply option_all_Forall2 in E. apply Forall2_forget_r in H5.
    rewrite Lists.List.Forall_map in H5. apply Forall_combine_Forall2 in H5.
    2: { rewrite length_seq. reflexivity. }
    apply Forall2_map_l in H3.
    eapply Forall2_Forall2_Forall3 in H3; [|exact H5]. clear H5.
    apply Forall3_ignore2 in H3. apply Forall2_map_l in E.
    eapply Forall2_Forall2_Forall3 in E; [|exact H3]. clear H3.
    apply Forall3_ignore2 in E.
    apply Forall2_forget_r_strong in E. rewrite Forall_forall in E.
    right. eapply prog_impl_implication_weaken_hyp; [exact HRs|].
    simpl. intros f Hf. fwd.
    specialize (E _ ltac:(eassumption)). fwd. invert_stuff. simpl in *. fwd.
    destruct y2. simpl in *. subst. rewrite H0 in *. fwd.
    rewrite Forall_forall in HS0p0. specialize (HS0p0  _ ltac:(eassumption)).
    eexists _, _. split.
    2: { simpl. reflexivity. }
    apply Exists_exists. eexists. split; [eassumption|]. simpl.
    move Hp2 at bottom. rewrite Forall_forall in Hp2.
    specialize (Hp2 _ ltac:(eassumption)). apply Hp2 in HS0p0.
    2: assumption.
    split; [reflexivity|].
    apply HS0p0. assumption.
  - destruct HS0 as [HS0|HS0].
    { apply Hp1 in HS0; try assumption. eapply prog_impl_implication_subset.
      2: { apply HS0. assumption. }
      simpl. auto. }
    fwd. invert_stuff. clear Hstaged Hloopless.
    simpl in *. invert_stuff. destruct (option_all _) eqn:E; [|discriminate]. fwd.
    simpl in Hx. apply prog_impl_implication_subset with (p1 := p).
    { simpl. auto. }
    eapply prog_impl_trans.
    eapply prog_impl_implication_weaken_hyp; [eassumption|].
    simpl. intros f Hf. fwd.
    apply option_all_Forall2 in E. apply Forall2_forget_r in H5.
    rewrite Lists.List.Forall_map in H5. apply Forall_combine_Forall2 in H5.
    2: { rewrite length_seq. reflexivity. }
    apply Forall2_map_l in H3.
    eapply Forall2_Forall2_Forall3 in H3; [|exact H5]. clear H5.
    apply Forall3_ignore2 in H3. apply Forall2_map_l in E.
    eapply Forall2_Forall2_Forall3 in E; [|exact H3]. clear H3.
    apply Forall3_ignore2 in E. apply Forall2_combine in E.
    apply Exists_exists in Hfp0. fwd. rewrite Forall_forall in E.
    specialize (E _ ltac:(eassumption)). fwd. invert_stuff. simpl in *. fwd.
    rewrite H0 in *. fwd. destruct y1. simpl in *. subst.
    rewrite Forall_forall in HS0p0. specialize (HS0p0 _ ltac:(eassumption)).
    rewrite Forall_forall in Hp2. apply Hp2 in HS0p0; try assumption.
    2: { apply in_combine_l in Hfp0p0. assumption. }
    apply HS0p0. assumption.
Qed.

Definition mrs_very_sound p := forall R, mrs_very_sound_for p R.

Ltac plda :=
  repeat lazymatch goal with
    | |- Forall _ _ => first [constructor | eapply Forall_impl; [|eassumption]; cbv beta | apply Forall_forall; intros ]
    | |- _ <> _ => intro
    | |- _ => intros; fwd; congruence
    end.

Lemma depends_only_on_mrs_very_sound p R Rs :
  ~In (R, meta) (flat_map hyp_rels p) ->
  ~In R Rs ->
  depends_only_on p R Rs ->
  mrs_very_sound p ->
  mrs_very_sound (closure_rule p R Rs :: p).
Proof.
  intros HR1 HR2 Hdep Hsound. cbv [mrs_very_sound]. intros R0. destr (Nat.eqb R R0).
  - apply depends_only_on_mrs_very_sound_for; auto. apply Forall_forall. auto.
  - cbv [mrs_very_sound_for]. intros Q S0 HQ1 HS0 x.
    rewrite cons_is_app in HS0. apply staged_program in HS0.
    2: { simpl. apply disjoint_lists_alt. plda. }
    apply invert_prog_impl in HS0. destruct HS0 as [HS0|HS0].
    2: { fwd. invert_stuff. simpl in *. fwd. congruence. }
    rewrite cons_is_app. rewrite staged_program_iff.
    2: { simpl. apply disjoint_lists_alt. plda. }
    apply Hsound in HS0; auto. rewrite <- HS0. split.
    + intros H'. apply invert_prog_impl in H'. destruct H' as [H'|H']; auto.
      fwd. invert_stuff.
    + intros. apply partial_in. assumption.
Qed.

Lemma syntactically_depends_only_on_correct p R Rs :
  well_typed_prog p ->
  syntactically_depends_only_on p R Rs ->
  depends_only_on p R Rs.
Proof.
  cbv [syntactically_depends_only_on depends_only_on]. intros Hp H Q x HQ1 H'.
  apply invert_prog_impl in H'. destruct H' as [H'|H'].
  { exfalso. apply HQ2 in H'. simpl in H'. fwd. auto. }
  fwd. eapply prog_impl_step.
  { eassumption. }
  apply Exists_exists in H'p0. fwd. rewrite Forall_forall in H.
  specialize (H _ ltac:(eassumption)). Search rule_impl concl_rels.
  specialize' H.
  { apply rule_impl_concl_relname_in in H'p0p1. simpl in H'p0p1. assumption. }
  apply rule_impl_hyp_relname_in in H'p0p1. rewrite Forall_forall in H'p0p1, H'p1.
  apply Forall_forall. intros f Hf. specialize (H'p0p1 _ Hf). specialize (H'p1 _ Hf).
  apply partial_in. destruct f as [[? ?] ?]. simpl in *.
  apply H in H'p0p1. apply in_map_iff in H'p0p1. fwd.
  pose proof H'p1 as H'p1'.
  apply Hp in H'p1'.
  2: { cbv [good_inputs] in HQ2. intros f' Hf'. apply HQ2 in Hf'. fwd. assumption. }
  cbv [well_typed] in H'p1'. simpl in H'p1'. fwd.
  do 2 eexists.
  split; [eassumption|].
  split; [reflexivity|].
  assumption.
Qed.

Lemma mrs_very_sound_staged is_input p1 p2 :
  disjoint_lists (flat_map concl_rels p1) (flat_map hyp_rels p2) ->
  mrs_very_sound is_input p1 ->
  mrs_very_sound is_input p2 ->
  mrs_very_sound is_input (p1 ++ p2).
Proof.
  intros Hdisj H1 H2. cbv [mrs_very_sound mrs_very_sound_for].
  intros R Q S0 HQ1 HQ2 HS0 x. apply staged_program in HS0; [|assumption].
  rewrite staged_program_iff; [|assumption].
  Print mrs_very_sound_for.


Lemma compile_Sexpr_correct is_input datalog_ctx ctx t e e_nat e' name out name' p p' :
  wf_Sexpr ctx t e e_nat ->
  Forall (fun elt => agrees (fun _ => False) datalog_ctx _ elt.(ctx_elt_p2) elt.(ctx_elt_p1)) ctx ->
  Forall (fun name0 => name0 <> out /\ name0 < name) (map (fun x => @ctx_elt_p2 _ (fun _ => nat) x) ctx) ->
  Forall (fun '(name0, _) => name0 <> out /\ name0 < name) (flat_map hyp_rels datalog_ctx) ->
  Forall (fun '(name0, _) => name0 <> out /\ name0 < name) (flat_map concl_rels datalog_ctx) ->
  interp_Sexpr e e' ->
  compile_Sexpr name out e_nat = (name', p, p') ->
  name <= name' /\
    agrees (fun _ => False) (p ++ p' p ++ datalog_ctx) t out e' /\
    mrs_very_sound is_input (p ++ p' p ++ datalog_ctx).
Proof.
  intros Hwf. revert datalog_ctx name out name' p p'.
  induction Hwf; intros datalog_ctx name out name' p p' Hctx Hnames Hout1 Hout2 He' Hcomp.
  - dep_invert He'. simpl in Hcomp. invert Hcomp. split; [lia|]. split.
    * destruct t; simpl.
    + intros x. split.
      -- intros Himpl. rewrite cons_two_is_app in Himpl. apply staged_program in Himpl.
         2: { simpl. apply disjoint_lists_alt. plda. }
         apply loopless_program in Himpl.
         2: { simpl. apply disjoint_lists_alt. enough (x2 <> out) by plda.
              intro. subst. rewrite Forall_forall in Hnames. epose_dep Hnames.
              specialize' Hnames.
              { apply in_map_iff. eexists.
                split; [|eassumption]. reflexivity. }
              simpl in Hnames. fwd. congruence. }
         destruct Himpl as [Himpl|Himpl].
         ++ apply idk in Himpl; [contradiction|]. simpl.
            rewrite Forall_forall in Hout2. intros H'. apply Hout2 in H'.
            fwd. congruence.
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
            --- apply Exists_cons_hd. interp_exprs. apply map.get_put_same.
            --- interp_exprs. apply map.get_put_same.
         ++ constructor; [|constructor]. rewrite Forall_forall in Hctx.
            specialize (Hctx _ ltac:(eassumption)). simpl in Hctx.
            eapply prog_impl_implication_subset; [|apply Hctx; reflexivity].
            intros. simpl. auto.
    + split.
      -- intros x. split.
         ++ intros Himpl. rewrite cons_two_is_app in Himpl. apply staged_program in Himpl.
            2: { simpl. apply disjoint_lists_alt. plda. }
            apply loopless_program in Himpl.
            2: { simpl. apply disjoint_lists_alt. enough (x2 <> out) by plda.
                 intro. subst. rewrite Forall_forall in Hnames. epose_dep Hnames.
                 specialize' Hnames.
                 { apply in_map_iff. eexists.
                   split; [|eassumption]. reflexivity. }
                 simpl in Hnames. fwd. congruence. }
            destruct Himpl as [Himpl|Himpl].
            --- apply idk in Himpl; [contradiction|]. simpl.
                rewrite Forall_forall in Hout2. intros H'. apply Hout2 in H'.
                fwd. congruence.
            --- fwd. apply Exists_cons in Himplp1. destruct Himplp1 as [Himpl|Himpl].
                +++ rewrite Forall_forall in Hctx.
                    specialize (Hctx _ ltac:(eassumption)). simpl in Hctx. fwd.
                    apply Hctxp0. invert_stuff. eassert (_ = y) as ->.
                    { destruct y. simpl in *. f_equal; auto; congruence. }
                    assumption.
                +++ invert_stuff.
         ++ intros. subst. eapply prog_impl_step.
            --- apply Exists_cons_hd.
                apply normal_rule_impl with (ctx := map.put map.empty 0 (natobj x)).
                +++ apply Exists_cons_hd. interp_exprs. apply map.get_put_same.
                +++ interp_exprs. apply map.get_put_same.
            --- constructor; [|constructor]. rewrite Forall_forall in Hctx.
                specialize (Hctx _ ltac:(eassumption)). simpl in Hctx. fwd.
                eapply prog_impl_implication_subset; [|apply Hctxp0; assumption].
                intros. simpl. auto.
      -- rewrite Forall_forall in Hctx. specialize (Hctx _ ltac:(eassumption)).
         simpl in Hctx. fwd. eexists. eapply prog_impl_step.
         ++ apply Exists_cons_tl. apply Exists_cons_hd.
            eapply normal_rule_impl with (ctx := map.put map.empty 0 (factset _)).
            --- apply Exists_cons_hd. interp_exprs.
                { apply map.get_put_same. }
                simpl. reflexivity.
            --- interp_exprs. apply map.get_put_same.
         ++ constructor; [|constructor].
            eapply prog_impl_implication_subset; [|eassumption].
            simpl. auto.
      * Check staged_program.

          intros R. destr (Nat.eqb R out).
        { eapply mrs_ cbv [mrs_very_sound_for]. intros Q HQ1 HQ2 S0 HS0 x.
          simpl. rewrite cons_two_is_app. rewrite staged_program_iff.
          2: { simpl. apply disjoint_lists_alt. enough (x2 <> out) by plda.
               intro. subst. rewrite Forall_forall in Hnames. epose_dep Hnames.
               specialize' Hnames.
               { apply in_map_iff. eexists.
                 split; [|eassumption]. reflexivity. }
               simpl in Hnames. fwd. congruence. }

          2: { split.
            intros S0.
         match goal with
         | |- ?P1 <-> _ => eassert (P1 <-> _)
         end.
         { rewrite cons_two_is_app. apply staged_program_iff. simpl. admit. }
         rewrite H0. clear H0.
         match goal with
         | |- ?P1 <-> _ => eassert (P1 <-> _)
         end.
         { apply loopless_program_iff. simpl. admit. }
         rewrite H0. clear H0.
         match goal with
         | |- ?P1 <-> _ => eassert (P1 <-> _)
         end.
         {
         split.
           { intros H'. rewrite staged_program_iff in H'. rewrite @staged_program_iff. Check staged_program.
        intros S0.
         match goal with
         | |- context[closure ?x] => remember x as p eqn:Ep
         end.
         split; intros Himpl.
         ++ rewrite cons_two_is_app in Himpl. apply staged_program in Himpl.
            2: { simpl. apply disjoint_lists_alt.
                 constructor.
                 { eapply Forall_impl; [|eassumption]. simpl. intros. fwd. auto. }
                 constructor.
                 { eapply Forall_impl; [|eassumption]. simpl. intros. fwd. auto. }
                 constructor. }
            apply loopless_program in Himpl.
            2: { simpl. apply disjoint_lists_alt. enough (x2 <> out) by auto.
                 intro. subst. rewrite Forall_forall in Hnames. epose_dep Hnames.
                 specialize' Hnames.
                 { apply in_map_iff. eexists.
                   split; [|eassumption]. reflexivity. }
                 simpl in Hnames. fwd. congruence. }
            destruct Himpl as [Himpl|Himpl].
            --- apply idk in Himpl; [contradiction|]. simpl.
                rewrite Forall_forall in Hout2. intros H'. apply Hout2 in H'.
                fwd. congruence.
            --- fwd. apply Exists_cons in Himplp1. destruct Himplp1 as [Himpl|Himpl].
                { invert_stuff. }
                invert_stuff.
                rewrite Forall_forall in Hctx.
                specialize (Hctx _ ltac:(eassumption)). simpl in Hctx. fwd.
                intros. (*specialize (Hctxp1 S0). move Hctxp1 at bottom.*)
                destruct y; simpl in *; fwd. split; intros Himpl.
                +++ rewrite cons_two_is_app in Himpl. apply staged_program in Himpl.
                    2: { simpl. apply disjoint_lists_alt.
                         constructor.
                         { eapply Forall_impl; [|eassumption]. simpl. intros. fwd. auto. }
                         constructor.
                         { eapply Forall_impl; [|eassumption]. simpl. intros. fwd. auto. }
                         constructor. }
                    apply loopless_program in Himpl.
                    2: { simpl. apply disjoint_lists_alt. enough (x2 <> out) by auto.
                         intro. subst. rewrite Forall_forall in Hnames. epose_dep Hnames.
                         specialize' Hnames.
                         { apply in_map_iff. eexists.
                           split; [|eassumption]. reflexivity. }
                         simpl in Hnames. fwd. congruence. }
                    destruct Himpl as [Himpl|Himpl].
                    { apply idk in Himpl; [contradiction|]. simpl.
                      intros H'. rewrite Forall_forall in Hout2. apply Hout2 in H'.
                      fwd. congruence. }
                    fwd. apply Exists_cons in Himplp1. destruct Himplp1 as [Himpl|Himpl].
                    2: { invert_stuff. }
                    invert_stuff. rewrite H2 in H8. fwd.
                    destruct y. simpl in *. subst. rewrite H1 in H3. fwd.
                    move H4 at bottom. eapply prog_impl_step.
                    { apply Exists_cons_hd.
                      eapply normal_rule_impl with (ctx := map.put map.empty 0 (natobj _)).
                      - apply Exists_cons_hd. interp_exprs. apply map.get_put_same.
                      - interp_exprs. apply map.get_put_same. }
                    constructor; [|constructor].
                    apply partial_in. eexists (_, [_]). split; [|reflexivity].
                    apply Exists_cons_hd. move Hctxp1 at bottom.
                    eapply Hctxp1 in H4. apply H4. assumption.
                +++ apply loopless_program in Himpl.
                    2: { simpl. apply disjoint_lists_alt. enough (x2 <> out) by auto.
                         intro. subst. rewrite Forall_forall in Hnames. epose_dep Hnames.
                         specialize' Hnames.
                         { apply in_map_iff. eexists.
                           split; [|eassumption]. reflexivity. }
                         simpl in Hnames. fwd. congruence. }
                    (* eapply prog_impl_step. *)
                    (* { apply Exists_cons_hd. *)
                    (*   eapply normal_rule_impl with (ctx := map.put map.empty 0 (natobj _)). *)
                    (*   - apply Exists_cons_hd. interp_exprs. apply map.get_put_same. *)
                    (*   - interp_exprs. apply map.get_put_same. } *)
                    (* constructor; [|constructor]. *)
                    destruct Himpl as [Himpl|Himpl].
                    { fwd. simpl in *. destruct y'. simpl in *. subst. invert_stuff.
                      destruct l; simpl in *; invert_stuff.
                      destruct l; simpl in *; invert_stuff. rewrite H1 in H3. fwd.
                      eapply Hctxp1 in H4. eapply prog_impl_implication_subset.
                      2: { apply H4. assumption.

                        apply H4 in H5.
                  invert Himpl.
                    apply staged_program in H'.
                rewrite H1 in H5. fwd. subst.
                eapply Hctxp1 in H4. (*seems true *) rewrite <- H4.
                apply Hctxp1.
                invert_stuff. eassert (_ = y) as ->.
                { destruct y. simpl in *. f_equal; auto; congruence. }
                assumption.
         ++ subst. eapply prog_impl_step.
            --- apply Exists_cons_tl. apply Exists_cons_hd.
                eapply normal_rule_impl with (ctx := map.put map.empty 0 (setobj _)).
                +++ apply Exists_cons_hd. interp_exprs. apply map.get_put_same.
                +++ interp_exprs. apply map.get_put_same.
            --- constructor; [|constructor]. rewrite Forall_forall in Hctx.
                specialize (Hctx _ ltac:(eassumption)). simpl in Hctx.
                fwd.
                eapply prog_impl_implication_subset.
                2: { simpl in *. specialize (Hctxp1 x x). apply Hctxp1. reflexivity. }
                intros. simpl. auto.
  - dep_invert He'. simpl in Hcomp. fwd.
    epose_dep IHHwf1. specialize IHHwf1 with (6 := E).
    specialize (IHHwf1 ltac:(eassumption)).
    specialize' IHHwf1.
    { eapply Forall_impl; [|eassumption]. simpl. intros. fwd. lia. }
    specialize' IHHwf1.
    { eapply Forall_impl; [|eassumption]. simpl. intros. fwd. lia. }
    specialize' IHHwf1.
    { eapply Forall_impl; [|eassumption]. simpl. intros. fwd. lia. }
    specialize' IHHwf1.
    { eassumption. }
    epose_dep IHHwf2. specialize IHHwf2 with (6 := E0).
    specialize (IHHwf2 ltac:(eassumption)).
    specialize' IHHwf2.
    { eapply Forall_impl; [|eassumption]. simpl. intros. fwd. lia. }
    specialize' IHHwf2.
    { eapply Forall_impl; [|eassumption]. simpl. intros. fwd. lia. }
    specialize' IHHwf2.
    { eapply Forall_impl; [|eassumption]. simpl. intros. fwd. lia. }
    specialize' IHHwf2.
    { eassumption. }
    fwd.
    split; [lia|]. admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - dep_invert He'. simpl in Hcomp. fwd.
    specialize IHHwf with (6 := E).
    epose_dep IHHwf.
    specialize' IHHwf.
    { eassumption. }
    specialize' IHHwf.
    { eapply Forall_impl; [|eassumption]. simpl. lia. }
    specialize' IHHwf.
    { eapply Forall_impl; [|eassumption]. simpl. lia. }
    specialize' IHHwf.
    { eapply Forall_impl; [|eassumption]. simpl. lia. }
    specialize (IHHwf ltac:(eassumption)). fwd.
    split; [lia|].
    intros p0. specialize (IHHwfp1 p0).
    cbv [agrees].
    simpl. intros x. split; intros Hx.
    + admit.
    + eapply prog_impl_step.
      -- apply Exists_cons_hd. eassert ([natobj _] = _) as ->. 2: econstructor.
         ++ simpl. cbv [interp_agg].
            instantiate (2 := map (fun x => (natobj x, natobj x)) l).
            do 2 rewrite map_map. simpl. rewrite option_all_map_Some.
            instantiate (1 := []).
            subst. reflexivity.
         ++ instantiate (2 := setobj _). simpl. reflexivity.
         ++ rewrite map_map. simpl. eapply is_list_set_ext.
            { apply is_list_set_map; [|eassumption].
              cbv [FinFun.Injective]. invert 1. reflexivity. }
            intros x0. simpl.
            destruct x0; split; intros Hx0;
              try contradiction; try (fwd; discriminate Hx0p0).
            --- fwd. cbv [natobj] in *. invert Hx0p0. exact Hx0p1.
            --- destruct o0. cbv [natobj]. eauto.
      -- simpl in IHHwfp1. constructor.
         ++ eapply prog_impl_step.
            --- apply Exists_cons_tl. apply Exists_cons_hd.
                eapply normal_rule_impl with (ctx := map.put map.empty 0 (setobj _)).
                +++ apply Exists_cons_hd. interp_exprs. apply map.get_put_same.
                +++ interp_exprs. apply map.get_put_same.
            --- constructor; [|constructor]. eapply prog_impl_implication_subset.
                2: { fwd. specialize (IHHwfp1p1 x' x'). apply IHHwfp1p1. reflexivity. }
                simpl. auto.
         ++ apply Forall_map. apply Forall_map.
            rename H2 into Hl. move Hl at bottom. destruct Hl as [Hlp0 Hlp1].
            apply Forall_forall. intros x0 Hx0. apply Hlp0 in Hx0.
            fwd. apply IHHwfp1p0 in Hx0.
            eapply prog_impl_step.
            --- apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd.
                eapply normal_rule_impl with (ctx := map.put map.empty 0 (natobj _)).
                +++ apply Exists_cons_hd. interp_exprs. 1,2: apply map.get_put_same.
                +++ interp_exprs. apply map.get_put_same.
            --- constructor; [|constructor].
                eapply prog_impl_implication_subset; [|eassumption].
                simpl. auto.
            Search
