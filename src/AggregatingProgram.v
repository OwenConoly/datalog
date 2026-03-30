From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From coqutil Require Import Map.Interface Map.Properties Map.Solver Datatypes.List Tactics Tactics.fwd.
From Datalog Require Import List Datalog (* FancyNotations *) Tactics.
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
Notation expr := (expr nat fn).
Notation blocks_prog var := (@blocks_prog nat nat nat fn bop var).

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
Print meta_rule. Print meta_clause. Print Datalog.blocks_prog. Print LetIn.
Fixpoint compile_Sexpr {t} {var} (e : Sexpr (fun _ => var) t) : blocks_prog var :=
  match e with
  | Var t x =>
      Block O
        [normal_rule
           [{| clause_rel := local O; clause_args := [var_expr O] |}]
           [{| clause_rel := Datalog.Var x; clause_args := [var_expr O] |}];
         meta_rule
           [{| meta_clause_rel := local O; meta_clause_args := [None] |}]
           [{| meta_clause_rel := Datalog.Var x; meta_clause_args := [None] |}]]
  | bop_over_vals o x y =>
      LetIn (compile_Sexpr x)
        (fun x' =>
           LetIn (compile_Sexpr y)
             (fun y' =>
                Block O
                  [normal_rule
                     [{| clause_rel := local O; clause_args := [fun_expr (fn_bop o) [var_expr O; var_expr (S O)]] |}]
                     [{| clause_rel := Datalog.Var x'; clause_args := [var_expr O] |};
                      {| clause_rel := Datalog.Var y'; clause_args := [var_expr (S O)] |}];
                   meta_rule
                     [{| meta_clause_rel := local O; meta_clause_args := [None] |}]
                     [{| meta_clause_rel := Datalog.Var x'; meta_clause_args := [None] |};
                      {| meta_clause_rel := Datalog.Var y'; meta_clause_args := [None] |}]]))
  | empty => Block O [meta_rule
                       [{| meta_clause_rel := local O; meta_clause_args := [None] |}]
                       []]
  | singleton x => (*we happen to represent sets in the same format as elements*)
      compile_Sexpr x
  | intersection x y =>
      LetIn (compile_Sexpr x)
        (fun x' =>
           LetIn (compile_Sexpr y)
             (fun y' =>
                Block O
                  [normal_rule
                     [{| clause_rel := local O; clause_args := [var_expr O] |}]
                     [{| clause_rel := Datalog.Var x'; clause_args := [var_expr O] |};
                      {| clause_rel := Datalog.Var y'; clause_args := [var_expr O] |}];
                   meta_rule
                     [{| meta_clause_rel := local O; meta_clause_args := [None] |}]
                     [{| meta_clause_rel := Datalog.Var x'; meta_clause_args := [None] |};
                      {| meta_clause_rel := Datalog.Var y'; meta_clause_args := [None] |}]]))
  | let_in t1 t2 x f =>
      LetIn (compile_Sexpr x)
        (fun x' => compile_Sexpr (f x'))
  | bop_over_set o x =>
      LetIn (compile_Sexpr x)
        (fun x' =>
           Block O
             [agg_rule (local O) o (local (S O));
              meta_rule
                [{| meta_clause_rel := local O; meta_clause_args := [None] |}]
                [{| meta_clause_rel := local (S O); meta_clause_args := [None; None] |}];
              normal_rule
                [{| clause_rel := local (S O); clause_args := [var_expr O; var_expr O] |}]
                [{| clause_rel := Datalog.Var x'; clause_args := [var_expr O] |}];
              meta_rule
                [{| meta_clause_rel := local (S O); meta_clause_args := [None; None] |}]
                [{| meta_clause_rel := Datalog.Var x'; meta_clause_args := [None] |}]])
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

(* Lemma idk (p : list rule) Q f : *)
(*   ~In f.(fact_R) (flat_map concl_rels p) -> *)
(*   prog_impl_implication p Q f -> *)
(*   Q f. *)
(* Proof. *)
(*   intros Hp H. invert H; auto. apply Exists_exists in H0. fwd. *)
(*   apply rule_impl_concl_relname_in in H0p1. rewrite in_flat_map in Hp. *)
(*   exfalso. eauto. *)
(* Qed. *)

(* Definition consistent (Q : fact -> Prop) := *)
(*   forall R S0, *)
(*     Q {| fact_R := (R, meta); fact_args := [factset S0; blank] |} -> *)
(*     forall x, *)
(*       Q {| fact_R := (R, normal); fact_args := [primitive x] |} <-> *)
(*         S0 [x]. *)

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

(* Definition mrs_very_sound_for (p : list rule) R := *)
(*   forall Q S0, *)
(*     consistent Q -> *)
(*     prog_impl_implication p Q {| fact_R := (R, meta); fact_args := [factset S0; blank] |} -> *)
(*     forall x, *)
(*       prog_impl_implication p Q {| fact_R := (R, normal); fact_args := [primitive x] |} <-> *)
(*         Q {| fact_R := (R, normal); fact_args := [primitive x] |} \/ S0 [x]. *)

(*should allow depending on meta facts.?*)
(*i want to say that R depends only on Rs.  this only makes sense when R is not an input*)
(* Definition depends_only_on (p : list rule) R Rs := *)
(*   forall Q x, *)
(*     consistent Q -> *)
(*     prog_impl_implication p Q {| fact_R := (R, normal); fact_args := [primitive x] |} -> *)
(*     Q {| fact_R := (R, normal); fact_args := [primitive x] |} \/ *)
(*       prog_impl_implication p (fun f => *)
(*                                  exists x R', *)
(*                                    In R' Rs /\ *)
(*                                      f = {| fact_R := (R', normal); fact_args := [primitive x] |} /\ *)
(*                                      prog_impl_implication p Q f) {| fact_R := (R, normal); fact_args := [primitive x] |}. *)

(* Definition is_normal (r : rule) := *)
(*   match r with *)
(*   | normal_rule _ _ => True *)
(*   | agg_rule _ _ _ => False *)
(*   end. *)

(* Definition syntactically_depends_only_on (p : list rule) R Rs := *)
(*   Forall (fun r => In (R, normal) (concl_rels r) -> incl (hyp_rels r) (map (fun x => (x, normal)) Rs)) p. *)

(* Lemma depends_only_on_mrs_very_sound_for p R Rs : *)
(*   ~In (R, meta) (flat_map hyp_rels p) -> *)
(*   ~In R Rs -> *)
(*   depends_only_on p R Rs -> *)
(*   mrs_very_sound_for p R -> *)
(*   Forall (mrs_very_sound_for p) Rs -> *)
(*   mrs_very_sound_for (closure_rule p R Rs :: p) R. *)
(* Proof. *)
(*   intros HR1 HR2 HRs Hp1 Hp2. intros Q S0 HQ1 HS0 x. *)
(*   assert (Hstaged : disjoint_lists [(R, meta)] (flat_map hyp_rels p)). *)
(*   { simpl. apply disjoint_lists_alt. constructor; [|constructor]. *)
(*     apply Forall_forall. intros x0 Hx0 ?. subst. auto. } *)
(*   assert (Hloopless : disjoint_lists *)
(*                         (flat_map concl_rels [closure_rule p R Rs]) *)
(*                         (flat_map hyp_rels [closure_rule p R Rs])). *)
(*   { simpl. rewrite map_map. apply disjoint_lists_alt. *)
(*     constructor; [|constructor]. rewrite app_nil_r. *)
(*     apply Forall_map. apply Forall_forall. intros (R', ?). intros HR'. *)
(*     apply in_combine_l in HR'. simpl. intro. fwd. auto. } *)
(*   rewrite cons_is_app in HS0. *)
(*   apply staged_program in HS0; [|assumption]. *)
(*   apply loopless_program in HS0; [|assumption]. *)
(*   rewrite (cons_is_app _ p). *)
(*   rewrite staged_program_iff; [|assumption]. *)
(*   rewrite loopless_program_iff; [|assumption]. *)
(*   destruct HS0 as [HS0|HS0]. *)
(*   { apply Hp1 in HS0; [|assumption]. epose_dep HS0. rewrite HS0. split; auto. *)
(*     intros [[?|?]|?]; auto. fwd. invert_stuff. } *)
(*   fwd. invert_stuff. clear Hstaged Hloopless. *)
(*   simpl in *. invert_stuff. destruct (option_all _) eqn:E; [|discriminate]. fwd. *)
(*   split; intros Hx. *)
(*   - destruct Hx as [Hx|Hx]. *)
(*     2: { clear -Hx. fwd. invert_stuff. } *)
(*     cbv [depends_only_on] in HRs. specialize (HRs _ _ HQ1 Hx). *)
(*     destruct HRs as [HRs|HRs]; auto. *)
(*     apply option_all_Forall2 in E. apply Forall2_forget_r in H5. *)
(*     rewrite Lists.List.Forall_map in H5. apply Forall_combine_Forall2 in H5. *)
(*     2: { rewrite length_seq. reflexivity. } *)
(*     apply Forall2_map_l in H3. *)
(*     eapply Forall2_Forall2_Forall3 in H3; [|exact H5]. clear H5. *)
(*     apply Forall3_ignore2 in H3. apply Forall2_map_l in E. *)
(*     eapply Forall2_Forall2_Forall3 in E; [|exact H3]. clear H3. *)
(*     apply Forall3_ignore2 in E. *)
(*     apply Forall2_forget_r_strong in E. rewrite Forall_forall in E. *)
(*     right. eapply prog_impl_implication_weaken_hyp; [exact HRs|]. *)
(*     simpl. intros f Hf. fwd. *)
(*     specialize (E _ ltac:(eassumption)). fwd. invert_stuff. simpl in *. fwd. *)
(*     destruct y2. simpl in *. subst. rewrite H0 in *. fwd. *)
(*     rewrite Forall_forall in HS0p0. specialize (HS0p0  _ ltac:(eassumption)). *)
(*     eexists _, _. split. *)
(*     2: { simpl. reflexivity. } *)
(*     apply Exists_exists. eexists. split; [eassumption|]. simpl. *)
(*     move Hp2 at bottom. rewrite Forall_forall in Hp2. *)
(*     specialize (Hp2 _ ltac:(eassumption)). apply Hp2 in HS0p0. *)
(*     2: assumption. *)
(*     split; [reflexivity|]. *)
(*     apply HS0p0. assumption. *)
(*   - destruct HS0 as [HS0|HS0]. *)
(*     { apply Hp1 in HS0; try assumption. eapply prog_impl_implication_subset. *)
(*       2: { apply HS0. assumption. } *)
(*       simpl. auto. } *)
(*     fwd. invert_stuff. clear Hstaged Hloopless. *)
(*     simpl in *. invert_stuff. destruct (option_all _) eqn:E; [|discriminate]. fwd. *)
(*     simpl in Hx. apply prog_impl_implication_subset with (p1 := p). *)
(*     { simpl. auto. } *)
(*     eapply prog_impl_trans. *)
(*     eapply prog_impl_implication_weaken_hyp; [eassumption|]. *)
(*     simpl. intros f Hf. fwd. *)
(*     apply option_all_Forall2 in E. apply Forall2_forget_r in H5. *)
(*     rewrite Lists.List.Forall_map in H5. apply Forall_combine_Forall2 in H5. *)
(*     2: { rewrite length_seq. reflexivity. } *)
(*     apply Forall2_map_l in H3. *)
(*     eapply Forall2_Forall2_Forall3 in H3; [|exact H5]. clear H5. *)
(*     apply Forall3_ignore2 in H3. apply Forall2_map_l in E. *)
(*     eapply Forall2_Forall2_Forall3 in E; [|exact H3]. clear H3. *)
(*     apply Forall3_ignore2 in E. apply Forall2_combine in E. *)
(*     apply Exists_exists in Hfp0. fwd. rewrite Forall_forall in E. *)
(*     specialize (E _ ltac:(eassumption)). fwd. invert_stuff. simpl in *. fwd. *)
(*     rewrite H0 in *. fwd. destruct y1. simpl in *. subst. *)
(*     rewrite Forall_forall in HS0p0. specialize (HS0p0 _ ltac:(eassumption)). *)
(*     rewrite Forall_forall in Hp2. apply Hp2 in HS0p0; try assumption. *)
(*     2: { apply in_combine_l in Hfp0p0. assumption. } *)
(*     apply HS0p0. assumption. *)
(* Qed. *)

(* Definition mrs_very_sound p := forall R, mrs_very_sound_for p R. *)

Ltac plda :=
  repeat lazymatch goal with
    | |- Forall _ _ => first [constructor | eapply Forall_impl; [|eassumption]; cbv beta | apply Forall_forall; intros ]
    | |- _ <> _ => intro
    | |- _ => intros; fwd; congruence
    end.

(* Lemma depends_only_on_mrs_very_sound p R Rs : *)
(*   ~In (R, meta) (flat_map hyp_rels p) -> *)
(*   ~In R Rs -> *)
(*   depends_only_on p R Rs -> *)
(*   mrs_very_sound p -> *)
(*   mrs_very_sound (closure_rule p R Rs :: p). *)
(* Proof. *)
(*   intros HR1 HR2 Hdep Hsound. cbv [mrs_very_sound]. intros R0. destr (Nat.eqb R R0). *)
(*   - apply depends_only_on_mrs_very_sound_for; auto. apply Forall_forall. auto. *)
(*   - cbv [mrs_very_sound_for]. intros Q S0 HQ1 HS0 x. *)
(*     rewrite cons_is_app in HS0. apply staged_program in HS0. *)
(*     2: { simpl. apply disjoint_lists_alt. plda. } *)
(*     apply invert_prog_impl in HS0. destruct HS0 as [HS0|HS0]. *)
(*     2: { fwd. invert_stuff. simpl in *. fwd. congruence. } *)
(*     rewrite cons_is_app. rewrite staged_program_iff. *)
(*     2: { simpl. apply disjoint_lists_alt. plda. } *)
(*     apply Hsound in HS0; auto. rewrite <- HS0. split. *)
(*     + intros H'. apply invert_prog_impl in H'. destruct H' as [H'|H']; auto. *)
(*       fwd. invert_stuff. *)
(*     + intros. apply partial_in. assumption. *)
(* Qed. *)

(* Lemma syntactically_depends_only_on_correct p R Rs : *)
(*   well_typed_prog p -> *)
(*   syntactically_depends_only_on p R Rs -> *)
(*   depends_only_on p R Rs. *)
(* Proof. *)
(*   cbv [syntactically_depends_only_on depends_only_on]. intros Hp H Q x HQ1 H'. *)
(*   apply invert_prog_impl in H'. destruct H' as [H'|H']. *)
(*   { exfalso. apply HQ2 in H'. simpl in H'. fwd. auto. } *)
(*   fwd. eapply prog_impl_step. *)
(*   { eassumption. } *)
(*   apply Exists_exists in H'p0. fwd. rewrite Forall_forall in H. *)
(*   specialize (H _ ltac:(eassumption)). Search rule_impl concl_rels. *)
(*   specialize' H. *)
(*   { apply rule_impl_concl_relname_in in H'p0p1. simpl in H'p0p1. assumption. } *)
(*   apply rule_impl_hyp_relname_in in H'p0p1. rewrite Forall_forall in H'p0p1, H'p1. *)
(*   apply Forall_forall. intros f Hf. specialize (H'p0p1 _ Hf). specialize (H'p1 _ Hf). *)
(*   apply partial_in. destruct f as [[? ?] ?]. simpl in *. *)
(*   apply H in H'p0p1. apply in_map_iff in H'p0p1. fwd. *)
(*   pose proof H'p1 as H'p1'. *)
(*   apply Hp in H'p1'. *)
(*   2: { cbv [good_inputs] in HQ2. intros f' Hf'. apply HQ2 in Hf'. fwd. assumption. } *)
(*   cbv [well_typed] in H'p1'. simpl in H'p1'. fwd. *)
(*   do 2 eexists. *)
(*   split; [eassumption|]. *)
(*   split; [reflexivity|]. *)
(*   assumption. *)
(* Qed. *)

(* Lemma mrs_very_sound_staged is_input p1 p2 : *)
(*   disjoint_lists (flat_map concl_rels p1) (flat_map hyp_rels p2) -> *)
(*   mrs_very_sound is_input p1 -> *)
(*   mrs_very_sound is_input p2 -> *)
(*   mrs_very_sound is_input (p1 ++ p2). *)
(* Proof. *)
(*   intros Hdisj H1 H2. cbv [mrs_very_sound mrs_very_sound_for]. *)
(*   intros R Q S0 HQ1 HQ2 HS0 x. apply staged_program in HS0; [|assumption]. *)
(*   rewrite staged_program_iff; [|assumption]. *)
(*   Print mrs_very_sound_for. *)

Definition set_of {t} (e' : interp_type t) :=
  match t return interp_type t -> interp_type val -> Prop with
  | set => fun e' => e'
  | val => fun e' => eq e'
  end e'.

Definition agrees {t} (e : fact_args _ -> Prop) (e' : interp_type t) :=
  forall x,
    set_of e' x <-> e (normal_fact_args [x]).

Ltac invert_stuff0 :=
  match goal with
  | _ => progress cbn [matches rel_of fact_of args_of clause_rel clause_args meta_clause_rel meta_clause_args] in *
  | H : rule_impl _ _ _ _ |- _ => invert1 H || invert0 H
  | H : block_prog_impl _ _ _ |- _ => apply inv_block_prog_impl in H; try (destruct H as [H|H]; [contradiction|])
  | H : non_meta_rule_impl _ _ _ _ |- _ => progress (invert1 H) || invert0 H
  | H : interp_clause _ _ _ |- _ => cbv [interp_clause] in H; fwd
  | H : interp_meta_clause _ _ _ |- _ => cbv [interp_meta_clause] in H; fwd
  | H : interp_expr _ _ _ |- _ => invert1 H
  | H : In _ [_] |- _ => destruct H; [|contradiction]
  | H1: ?x = Some ?y, H2: ?x = Some ?z |- _ => first [is_var y | is_var z]; assert (y = z) by congruence; clear H1; subst
  | _ => progress subst
  | _ => progress invert_list_stuff
  | _ => progress fwd
  | _ => congruence
  end.

Ltac invert0_Exists H :=
  repeat first [invert0 H |
                 apply Exists_cons in H; destruct H as [H|H]; [solve[repeat invert_stuff] | invert0_Exists H] ].

Ltac invert1_Exists H :=
  repeat first [invert0 H |
                 apply Exists_cons in H; destruct H as [H|H]; [solve[repeat invert_stuff] | invert1_Exists H] |
                 apply Exists_cons in H; destruct H as [H|H]; [|invert0_Exists H] ].

Ltac invert_stuff :=
  first [invert_stuff0 |
          match goal with
          | H: Exists _ _ |- _ => invert1_Exists H
          end].

Ltac interp_exprs :=
  repeat rewrite map_app; simpl;
  repeat match goal with
    | _ => progress simpl

    | |- Forall2 _ (_ ++ _) _ => apply Forall2_app
    | |- Forall2 _ (_ :: _) _ => constructor
    | |- Forall2 _ nil _ => constructor
    | |- Forall2 _ _ _ =>
        (eapply Forall2_impl; [|eassumption]; simpl; intros) ||
          idtac

    | |- Forall _ (_ :: _) => constructor; [interp_exprs|]
    | |- Forall _ [] => constructor

    | |- block_prog_impl _ _ ?f =>
        let x := constr:(rel_of f) in
        let x := (eval simpl in x) in
        match x with
        | global _ => idtac
        | Datalog.Var _ => idtac
        end;
        apply block_prog_impl_step with (hyps := []); [|constructor]
    | |- interp_expr _ _ _ => econstructor
    | |- interp_expr _ _ _ =>
        eapply interp_expr_subst_more; [|eassumption]
    | |- interp_clause _ _ _ =>
        eapply interp_clause_subst_more; [|eassumption]
    | |- interp_clause _ _ _ =>
        cbv [interp_clause]; eexists; split; [|reflexivity]; simpl
    | |- interp_meta_clause _ _ _ =>
        cbv [interp_meta_clause]; do 2 eexists; split; [|reflexivity]; simpl
    | |- _ /\ _ => split; [solve [interp_exprs] |]
    | |- Exists _ [_] => apply Exists_cons_hd

    | |- _ => rewrite map.get_put_diff by congruence
    | |- _ => rewrite map.get_put_same by reflexivity

    | |- _ => reflexivity
    | |- _ => eassumption (*hsould this just be assumption?*)
    end.

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
    simpl. intros x.  cbv [agrees] in Hctx. rewrite Hctx. clear Hctx.
    split.
    + intros. subst. eapply block_prog_impl_step.
      -- simpl. apply Exists_cons_hd. constructor.
         eapply normal_rule_impl with (ctx := map.put map.empty 0 _); interp_exprs.
      -- interp_exprs.
    + intros. repeat invert_stuff. assumption.
  - dep_invert He'.
    cbn [honest_blocks_prog compile_Sexpr] in Hnl. fwd.
    specialize (IHHwf1 ltac:(eassumption) ltac:(eassumption) _ ltac:(eassumption)).
    specialize (IHHwf2 ltac:(eassumption) ltac:(eassumption) _ ltac:(eassumption)).
    simpl in IHHwf1, IHHwf2.
    simpl. intros x. simpl. split.
    + intros. subst. eapply block_prog_impl_step.
      -- simpl. apply Exists_cons_hd. constructor.
         eapply normal_rule_impl with (ctx := map.put (map.put map.empty 0 _) 1 _); interp_exprs.
      -- interp_exprs.
         ++ apply IHHwf1. reflexivity.
         ++ apply IHHwf2. reflexivity.
    + intros H. repeat invert_stuff. simpl in *. repeat invert_stuff.
        match goal with
        | H: _ |- _ => apply IHHwf1 in H
        end.
        match goal with
        | H: _ |- _ => apply IHHwf2 in H
        end.
        cbv [set_of] in *. subst. reflexivity.
  - dep_invert He'. simpl. intros x. split.
    + contradiction.
    + intros H. repeat invert_stuff.
  - dep_invert He'.
    specialize (IHHwf ltac:(eassumption) ltac:(eassumption) _ ltac:(eassumption)).
    cbv [agrees] in IHHwf. cbv [agrees]. intros x. rewrite <- IHHwf. split; auto.
  - dep_invert He'.
    cbn [honest_blocks_prog compile_Sexpr] in Hnl. fwd.
    specialize (IHHwf1 ltac:(eassumption) ltac:(eassumption) _ ltac:(eassumption)).
    specialize (IHHwf2 ltac:(eassumption) ltac:(eassumption) _ ltac:(eassumption)).
    cbv [agrees] in IHHwf1, IHHwf2. cbv [agrees]. simpl.
    intros x. rewrite IHHwf1, IHHwf2. clear IHHwf1 IHHwf2. split.
    + intros [? ?]. eapply block_prog_impl_step.
      -- simpl. apply Exists_cons_hd. constructor.
         eapply normal_rule_impl with (ctx := map.put map.empty 0 _); interp_exprs.
      -- interp_exprs.
    + intros H. repeat invert_stuff. auto.
  - rename H0 into IHHwf'.
    dep_invert He'.
    cbn [honest_blocks_prog compile_Sexpr] in Hnl. fwd.
    specialize (IHHwf ltac:(eassumption) ltac:(eassumption) _ ltac:(eassumption)).
    specialize (IHHwf' _ _ ltac:(eauto) ltac:(eauto) _ ltac:(eauto)).
    clear Hctx. cbv [agrees] in *.
    intros x. rewrite IHHwf'. clear IHHwf'.
    simpl. reflexivity.
  - dep_invert He'.
    cbn [honest_blocks_prog compile_Sexpr] in Hnl. fwd.
    rename H2 into Hset.
    specialize (IHHwf ltac:(eassumption) ltac:(eassumption) _ ltac:(eassumption)).
    cbv [agrees]. simpl. cbv [agrees] in IHHwf. simpl in IHHwf. intros x. split.
    + intros. subst. eapply block_prog_impl_step.
      -- simpl. eapply Exists_cons_hd. constructor.
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
      -- constructor.
         ++ eapply block_prog_impl_mf_ext.
            --- eapply use_honest_block_prog; [assumption|].
                eapply block_prog_impl_step.
                +++ simpl. do 3 apply Exists_cons_tl. apply Exists_cons_hd.
                    eapply meta_rule_impl with (ctx := map.empty) (S := fun _ => _); interp_exprs.
                +++ interp_exprs. admit. (*this is where we need IH about meta fact*)
            --- simpl. intros. repeat invert_stuff. split.
                +++ intros H. repeat invert_stuff.
                    eexists. split; [reflexivity|]. apply IHHwf. assumption.
                +++ intros H. fwd.
                    eapply block_prog_impl_step.
                    ---- simpl. do 2 apply Exists_cons_tl. apply Exists_cons_hd.
                         constructor.
                         eapply normal_rule_impl with (ctx := map.put map.empty 0 _); interp_exprs.
                    ---- interp_exprs. apply IHHwf. assumption.
         ++ rewrite map_map. apply Forall_map.
            cbv [is_list_set] in Hset. fwd. apply Forall_forall.
            intros x Hx. apply Hsetp0 in Hx. apply IHHwf in Hx.
            eapply block_prog_impl_step.
            --- simpl. do 2 apply Exists_cons_tl. apply Exists_cons_hd.
                constructor.
                eapply normal_rule_impl with (ctx := map.put map.empty 0 _); interp_exprs.
            --- interp_exprs.
    + intros H. Print honest_block_prog.
      repeat lazymatch goal with
             | H: block_prog_impl _ _ (meta_fact _ _ _) |- _ => fail
             | _ => invert_stuff
             end.
      lazymatch goal with
      | H: block_prog_impl _ _ (meta_fact _ _ _) |- _ => rename H into Hmf
      end.
      apply Hnlp1 in Hmf. move Hmf at bottom.
      assert (Heq: forall x y, (x = y /\ x' x) <-> S [x; y]).
      { intros x y. cbv [consistent] in Hmf. rewrite Hmf; [|interp_exprs].
        rewrite IHHwf. split.
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
      Unshelve.
      all: exact True || exact (fun _ => True).
