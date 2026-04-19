From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.

From Datalog Require Import Map Tactics Fp List Dag Datalog.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List Datatypes.Option.

Import ListNotations.

Lemma map_eq_Forall2 {A B C} (f : A -> C) (g : B -> C) (l1 : list A) (l2 : list B) :
    map f l1 = map g l2 ->
    Forall2 (fun x y => f x = g y) l1 l2.
  Proof.
    revert l2. induction l1 as [|x l1' IH]; destruct l2 as [|y l2']; simpl; intro H; try discriminate.
    - constructor.
    - injection H as Heq Htail. constructor.
      + exact Heq.
      + apply IH. exact Htail.
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

  From coqutil Require Import Datatypes.HList. Print tuple.
  Fixpoint tuple T n : Type :=
    match n with
    | S n' => T * tuple T n'
    | O => unit
    end.
  (*alternatively, could define arrows T n T'...*)

  Inductive blocks_prog {var} : nat -> Type :=
  | Mutual {n} (rules : tuple var n -> blocks_prog n)
    : blocks_prog n
  | LetIn {n m} (x : blocks_prog n) (f : tuple var n -> blocks_prog m)
    : blocks_prog m
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
  | Block {n} (rets : tuple lvar n) (inputs : list (lvar * var)) (p : list block_rule)
    : blocks_prog n
  | Tuple {n} (_ : tuple var n)
    : blocks_prog n
  .
  Arguments blocks_prog : clear implicits.

  Inductive wide_pftree {U : Type} (P : U -> (U -> Prop) -> Prop) : U -> Prop :=
  | wide_pftree_step x l :
    P x l ->
    (forall y, l y -> wide_pftree _ y) ->
    wide_pftree _ x.

  Fixpoint tuple_map {A B : Type} (f : A -> B) {n : nat} : tuple A n -> tuple B n :=
    match n return tuple A n -> tuple B n with
    | O => fun _ => tt
    | S n' => fun '(x, xs) => (f x, tuple_map f xs)
    end.

  Fixpoint tuple_of_list {A : Type} (l : list A) : tuple A (length l) :=
    match l return tuple A (length l) with
    | [] => tt
    | x :: xs => (x, tuple_of_list xs)
    end.

  Fixpoint tuple_nth_error {A : Type} {n : nat} (i : nat) : tuple A n -> option A :=
    match n return tuple A n -> option A with
    | O => fun _ => None
    | S n' => fun '(x, xs) =>
               match i with
               | O => Some x
               | S i' => tuple_nth_error i' xs
               end
    end.

  Fixpoint tuple_seq start len : tuple nat len :=
    match len return tuple nat len with
    | O => tt
    | S len' => (start, tuple_seq (S start) len')
    end.

  Definition rel_of_tuple {U : Type} {n : nat} (t : tuple (U -> Prop) n) : nat * U -> Prop :=
    fun '(idx, u) => exists P, tuple_nth_error idx t = Some P /\ P u.

  Definition tuple_of_rel {U : Type} {n : nat} (R : nat * U -> Prop) : tuple (U -> Prop) n :=
    tuple_map (fun idx args => R (idx, args)) (tuple_seq O n).

  (*computes the least fixed point, for appropriate definitions of "least" and,
    "fixed point" of the step function.*)
  Definition tuple_lfp {U n} (step : tuple (U -> Prop) n -> tuple (U -> Prop) n) : nat * U -> Prop :=
    wide_pftree (fun f hyps =>
                   exists us, rel_of_tuple (step us) f /\ hyps = rel_of_tuple us).

  Fixpoint interp_blocks_prog (globals : gmap) {n} (e : blocks_prog (fact_args T -> Prop) n) : tuple (fact_args T -> Prop) n :=
    match e with
    | @Mutual _ n rules =>
        tuple_of_rel (tuple_lfp (fun fs => interp_blocks_prog globals (rules fs)))
    | LetIn x f =>
        interp_blocks_prog globals (f (interp_blocks_prog globals x))
    | Block rets inputs p =>
        tuple_map (fun ret args =>
                     prog_impl p
                       (fun f => Exists (fun '(R, R') => input R = rel_of f /\ R' (args_of f)) inputs)
                       (fact_of (local ret) args))
          rets
    | Tuple args => args
    end.
End Blocks.

From Stdlib Require Import String.
Open Scope string_scope.
Variant fn :=
  | add
  | lit (_ : nat).
Definition string_blocks_prog var := blocks_prog (lvar := string) (exprvar := string) (fn := fn) (aggregator := False) (var := var).
Definition string_block_rule := block_rule (lvar := string) (exprvar := string) (fn := fn) (aggregator := False).

Definition zero_prog : list string_block_rule :=
  [normal_rule
     [{| clause_rel := local "ret";
        clause_args := [fun_expr (lit O) []]|}]
     []].

Notation "[| |]" := (ntuple_nil _).
Notation "[| x |]" := (ntuple_cons _ O x (ntuple_nil _)).
Notation "[| x ; .. ; y |]" := (ntuple_cons _ _ x .. (ntuple_cons _ _ y (ntuple_nil _)) ..).

Fixpoint arrows (T : Type) (n : nat) (R : Type) : Type :=
  match n with
  | O => R
  | S n' => T -> arrows T n' R
  end.

Fixpoint tuple_uncurry {T R : Type} (n : nat) (f : arrows T n R) (t : tuple' T n) : R :=
  match t in tuple' _ m return arrows T m R -> R with
  | ntuple_nil _ => fun (v : R) => v
  | ntuple_cons _ m' x xs => fun (fn : T -> arrows T m' R) => tuple_uncurry m' (fn x) xs
  end f.

Definition lit_ x : expr string fn := fun_expr (lit x) [].
Notation "'tfun' [ n ] x .. y => body" :=
  (@tuple_uncurry _ _ n (fun x => .. (fun y => body) ..))
    (at level 200, x binder, y binder, right associativity).
Notation "'let^' [ n ] x .. y ':=' e1 'in' e2" :=
  (LetIn e1 (@tuple_uncurry _ _ n (fun x => .. (fun y => e2) ..)))
    (at level 200, x binder, y binder, right associativity).

(*
  The following is a manual compilation of the program
{ x = init();
  do while x != 0:
     x = f(x);
  return g(x); }

where init,f,g are pure functions.

CFG:

       +-----------------+
       |     block 1     |
       |   x = init()    |
       +-------+---------+
               |
               v
     +-->+-----+-----+
     |   |  block 2  |
     |   |  x = f(x) |
     |   +-----+-----+
     |         |
     |         v
     |   +-----+-----+
     ^   |   x!=0?   |
     |   +--+--+-----+
     |      |  |
     |  yes |  | no
     +------+  |
               v
       +-------+---------+
       |     block 3     |
       |   return g(x)   |
       +-----------------+

 *)


(*the compilation of the pure function init() in the source program*)
(*spec: Rinit(init(), t + 1) :- active(t)*)
Definition Rinit {var} (active : var) : string_blocks_prog var 1.
Admitted.

(*the compilation of the pure function f(x) in the source program*)
(*spec: Rf(f(x), t + 1) :- active(t), Rx(x, t) *)
Definition Rf {var} (active : var) (Rx : var) : string_blocks_prog var 1.
Admitted.

(*the compilation of the pure function g(x) in the source program*)
(*spec: Rg(g(x), t + 1) :- active(t), Rx(x, t) *)
Definition Rg {var} (active : var) (Rx : var) : string_blocks_prog var 1.
Admitted.

(*spec: incr(t + 1) :- active(t)*)
Definition incr {var} (active : var) : string_blocks_prog var 1 :=
  Block [|"ret"|] [("input", active)]
    [normal_rule
       [{| clause_rel := local "ret"; clause_args := [fun_expr add [var_expr "t"; lit_ 1]]|}]
       [{| clause_rel := input "input"; clause_args := [var_expr "t"]|}]].

(*spec: cond_false_incr(t + 1) :- active(t), Rcond(0, t)*)
Definition cond_false_incr {var} (active Rcond : var) : string_blocks_prog var 1 :=
  Block [|"ret"|] [("active", active); ("Rcond", Rcond)]
    [normal_rule
       [{| clause_rel := local "ret"; clause_args := [fun_expr add [var_expr "t"; lit_ 1]]|}]
       [{| clause_rel := input "active"; clause_args := [var_expr "t"] |};
        {| clause_rel := input "Rcond"; clause_args := [lit_ 0; var_expr "t"] |}]].

(*spec: cond_true_incr(t + 1) :- active(t), Rcond(x, t), x <> 0*)
Definition cond_true_incr {var} (active Rcond : var) : string_blocks_prog var 1.
(*i can't actually write this one yet, because i have no way of checking that something is nonzero.
  but it should be analogous to cond_false_incr*)
Admitted.

Definition union {var} (R1 R2 : var) : string_blocks_prog var 1 :=
  Block [|"ret"|] [("R1", R1); ("R2", R2)]
    [normal_rule
       [{| clause_rel := local "ret"; clause_args := [var_expr "x"] |}]
       [{| clause_rel := input "R1"; clause_args := [var_expr "x"] |}];
     normal_rule
       [{| clause_rel := local "ret"; clause_args := [var_expr "x"] |}]
       [{| clause_rel := input "R2"; clause_args := [var_expr "x"] |}]].

(*the compilation of the basic block x = init().
  when done, jump to block2*)
(*spec: we have Rx1(init(), t + 1) :- active1(t), and active2(t + 1) :- active1(t)
 *)
Definition cfg_block1 {var} (active1 : var) : string_blocks_prog var 2 :=
  let^[1] Rx_1 := Rinit active1 in
  let^[1] active2_1 := incr active1 in
  Tuple [| Rx_1; active2_1 |].

(*the compilation of the basic block {do while (x <> 0) {x = f(x)}}
  when condition is true, jump to self (block2).
  when condition is false, jump to block3.*)
Definition cfg_block2 {var} (active2 : var) (Rx : var) : string_blocks_prog var 3 :=
  let^[1] Rx_2 := Rf active2 Rx in
  let^[1] active2_2 := cond_true_incr active2 Rx in
  let^[1] active3_2 := cond_false_incr active2 Rx in
  Tuple [| Rx_2; active2_2; active3_2 |].

(*the compilation of the basic block { return g(x) }*)
Definition cfg_block3 {var} (active3 : var) (Rx : var) : string_blocks_prog var 1 :=
  let^[1] ret := Rg active3 Rx in
  Tuple [| ret |].

(*The compilation of the whole cfg.*)
Definition cfg' {var} (active1 : var) : string_blocks_prog var 4 :=
  Mutual [| "ret"; "Rx"; "active2"; "active3" |]
    (tfun[4] ret Rx active2 active3 =>
       let^[2] Rx_1 active2_1 := cfg_block1 active1 in
       let^[3] Rx_2 active2_2 active3_2 := cfg_block2 active2 Rx in
       let^[1] ret' := cfg_block3 active3 Rx in
       let^[1] Rx' := union Rx_1 Rx_2 in
       let^[1] active2' := union active2_1 active2_2 in
       let active3' := active3_2 in
       Tuple [| ret'; Rx'; active2'; active3' |]).

(*Extract the only relation that we care about.*)
Definition cfg {var} (active1 : var) : string_blocks_prog var 1 :=
  let^[4] ret _ _ _ := cfg' active1 in
  Tuple [| ret |].

Definition isEven n := exists m, n = m * 2.

Definition interp_fun f xs :=
  match f, xs with
  | add, [a; b] => Some (a + b)
  | lit x, [] => Some x
  | _, _ => None
  end.
Instance Sig : signature fn False nat :=
  { interp_fun := interp_fun ;
    interp_agg := fun _ _ => O }.

Lemma mut_example_correct n gvar gmap strmap :
  interp_blocks_prog (context := strmap) (gvar := gvar) (gmap := gmap) map.empty
    mut_example (normal_fact_args [n]) <-> isEven n.
Proof.
  cbv [mut_example]. split; intros H.
  - simpl in H. invert H.
    destruct l as [|R1 l]; [contradiction|].
    destruct l as [|R2 l]; [contradiction|].
    simpl in *.


    simpl in *. invert l. simpl in H0.



  Inductive wf_blocks_prog {var1 var2} : list (var1 * var2) -> blocks_prog var1 -> blocks_prog var2 -> Prop :=
  | wf_LetIn ctx x1 x2 f1 f2 :
    wf_blocks_prog ctx x1 x2 ->
    (forall x1' x2', wf_blocks_prog ((x1', x2') :: ctx) (f1 x1') (f2 x2')) ->
    wf_blocks_prog ctx (LetIn x1 f1) (LetIn x2 f2)
  | wf_Block ctx ret inps1 inps2 p :
    Forall2 (fun '(x1, R1) '(x2, R2) => x1 = x2 /\ In (R1, R2) ctx) inps1 inps2 ->
    wf_blocks_prog ctx (Block ret inps1 p) (Block ret inps2 p).

  Section map.
    Context {rel1 rel2} (f : rel1 -> rel2).

    Definition injective_on (x : rel1) : Prop :=
      forall y, f x = f y -> x = y.

    Definition rel_equiv R1 R2 := f R1 = f R2.

    Definition map_fact (fct : fact rel1 T) : fact rel2 T :=
      match fct with
      | normal_fact R args => normal_fact (f R) args
      | meta_fact R mf_args mf_set => meta_fact (f R) mf_args mf_set
      end.

    Definition fact_equiv f1 f2 := map_fact f1 = map_fact f2.

    Definition map_clause_rel (c : clause rel1 exprvar fn) :=
      {| clause_rel := f c.(clause_rel);
        clause_args := c.(clause_args) |}.

    Lemma interp_clause_map_fw ctx c h :
      interp_clause ctx c h ->
      interp_clause ctx (map_clause_rel c) (map_fact h).
    Proof. intros. repeat invert_stuff. interp_exprs. Qed.

    Hint Unfold interp_clause rel_equiv fact_equiv : core.
    Lemma interp_clause_map_bw ctx c h :
      interp_clause ctx (map_clause_rel c) (map_fact h) ->
      exists h', fact_equiv h h' /\ interp_clause ctx c h'.
    Proof.
      intros H. cbv [interp_clause] in H. fwd.
      destruct h; simpl in *; repeat invert_stuff.
      eexists (normal_fact (clause_rel c) _). split.
      - cbv [fact_equiv]. simpl. f_equal. assumption.
      - eauto.
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
      exists hyps2',
        Forall2 fact_equiv hyps2 hyps2' /\
        Forall2 (interp_clause ctx) hyps1 hyps2'.
    Proof.
      intros H. rewrite <- Forall2_map_l, <- Forall2_map_r in H.
      induction H.
      - eexists []. split; constructor.
      - apply interp_clause_map_bw in H. destruct H as [h' [Heq Hinterp]].
        destruct IHForall2 as [hyps2' [HForall_eq HForall_interp]].
        eexists (h' :: hyps2'). split; constructor; eauto.
    Qed.

    Lemma Forall2_interp_clause_map_bw' ctx hyps1 hyps2 :
      Forall2 (interp_clause ctx) (map map_clause_rel hyps1) (map map_fact hyps2) ->
      Forall2 (fun c h => exists h', fact_equiv h h' /\ interp_clause ctx c h') hyps1 hyps2.
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
      exists f1' f2',
        fact_equiv f1 f1' /\
        fact_equiv f2 f2' /\
        fact_matches f1' f2'.
    Proof.
      intros H. cbv [fact_matches] in H. fwd.
      destruct f1, f2; simpl in *; repeat invert_stuff.
      exists (normal_fact nf_rel nf_args), (meta_fact nf_rel mf_args mf_set).
      split; [|split].
      - cbv [fact_equiv]. simpl. f_equal.
      - cbv [fact_equiv]. simpl. f_equal. congruence.
      - cbv [fact_matches]. eauto 10.
    Qed.

    Hint Unfold interp_meta_clause : core.
    Lemma interp_meta_clause_map_bw ctx c h :
      interp_meta_clause ctx (map_meta_clause_rel c) (map_fact h) ->
      exists h', fact_equiv h h' /\ interp_meta_clause ctx c h'.
    Proof.
      intros H. cbv [interp_meta_clause] in H. fwd.
      destruct h; simpl in *; repeat invert_stuff.
      eexists (meta_fact (meta_clause_rel c) _ _). split.
      - cbv [fact_equiv]. simpl. f_equal. assumption.
      - eauto.
    Qed.

    Lemma Forall2_interp_meta_clause_map_bw' ctx hyps1 hyps2 :
      Forall2 (interp_meta_clause ctx) (map map_meta_clause_rel hyps1) (map map_fact hyps2) ->
      Forall2 (fun c h => exists h', fact_equiv h h' /\ interp_meta_clause ctx c h') hyps1 hyps2.
    Proof.
      intros H. rewrite <- Forall2_map_l, <- Forall2_map_r in H.
      eapply Forall2_impl; [|eassumption].
      eauto using interp_meta_clause_map_bw.
    Qed.

        Lemma rel_of_map_fact fct :
      rel_of (map_fact fct) = f (rel_of fct).
    Proof.
      destruct fct; reflexivity.
    Qed.

    Lemma args_of_map_fact fct :
      args_of (map_fact fct) = args_of fct.
    Proof.
      destruct fct; reflexivity.
    Qed.

    Lemma non_meta_rule_impl_map_bw r R args hyps :
      non_meta_rule_impl (map_rule_rels r) (f R) args (map map_fact hyps) ->
      exists R0 hyps0,
        rel_equiv R R0 /\
        Forall2 fact_equiv hyps hyps0 /\
          non_meta_rule_impl r R0 args hyps0.
    Proof.
      intros H. destruct r; invert H.
      - rewrite Exists_map in H2.
        apply Forall2_interp_clause_map_bw in H6.
        apply Exists_exists in H2. fwd.
        apply interp_clause_map_bw with (h := normal_fact _ _) in H2p1.
        fwd. cbv [fact_equiv] in H2p1p0. simpl in H2p1p0.
        destruct h'; simpl in H2p1p0; congruence || fwd.
        eexists nf_rel, _. ssplit; eauto.
        econstructor.
        + apply Exists_exists. eexists. split; [exact H2p0 |].
          eassumption.
        + eassumption.
      - destruct hyps as [|hyp hyps]; simpl in *; discriminate || fwd.
        destruct hyp; simpl in *; discriminate || fwd.
        do 2 eexists. split; [symmetry; eassumption|].
        split.
        2: { econstructor. eassumption. }
        constructor.
        { cbv [fact_equiv]. simpl. f_equal. auto. }
        rewrite <- Forall2_map_r.
        eapply Forall2_impl.
        2: { eapply map_eq_Forall2. symmetry. eassumption. }
        simpl. intros f' (?, ?) Hf'. destruct f'; simpl in Hf'; discriminate || fwd.
        cbv [fact_equiv]. simpl. f_equal. auto.
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
      - eexists (meta_fact _ _ _ ::
                 map (fun '(x, y) => normal_fact hyp_rel (x :: y :: _)) _).
        simpl. f_equal. rewrite map_map.
        apply map_ext. intros [? ?]. reflexivity.
    Qed.

    Lemma extensionally_equal_map_fw f1 f2 :
      extensionally_equal f1 f2 ->
      extensionally_equal (map_fact f1) (map_fact f2).
    Proof.
      intros H. destruct f1, f2; cbv [extensionally_equal] in *; try contradiction; fwd.
      - split; [f_equal; auto | auto].
      - split; [f_equal; auto | split; auto].
    Qed.

    Lemma extensionally_equal_map_bw f1 f2 :
      extensionally_equal (map_fact f1) (map_fact f2) ->
      exists f1' f2',
        fact_equiv f1 f1' /\
        fact_equiv f2 f2' /\
        extensionally_equal f1' f2'.
    Proof.
      intros H. destruct f1 as [R1 args1 | R1 mf_args1 mf_set1],
                         f2 as [R2 args2 | R2 mf_args2 mf_set2];
      cbv [extensionally_equal] in H; try contradiction; fwd.
      - exists (normal_fact R1 args1), (normal_fact R1 args2).
        simpl in *. fwd.
        split; [|split].
        + cbv [fact_equiv]. reflexivity.
        + cbv [fact_equiv]. simpl in *. f_equal. congruence.
        + cbv [extensionally_equal]. auto.
      - exists (meta_fact R1 mf_args1 mf_set1), (meta_fact R1 mf_args2 mf_set2).
        simpl in *. fwd.
        split; [|split].
        + cbv [fact_equiv]. reflexivity.
        + cbv [fact_equiv]. simpl. f_equal. congruence.
        + cbv [extensionally_equal]. eauto.
    Qed.

    Definition meta_facts_consistent_with_map (meta_facts : list (fact rel1 T)) :=
      forall R1 args1 S1 R2 args2 S2,
        In (meta_fact R1 args1 S1) meta_facts ->
        In (meta_fact R2 args2 S2) meta_facts ->
        f R1 = f R2 ->
        forall nf_args,
          Forall2 matches args1 nf_args ->
          Forall2 matches args2 nf_args ->
          S1 nf_args <-> S2 nf_args.

    Lemma meta_cond_map_iff mr mf_args mf_set p R (args : list T) meta_hyps :
      meta_rules_valid p ->
      In mr p ->
      rule_impl (one_step_derives p) mr (meta_fact R mf_args mf_set) meta_hyps ->
      Forall2 matches mf_args args ->
      meta_facts_consistent_with_map meta_hyps ->
      injective_on R ->
      one_step_derives p meta_hyps R args <->
        one_step_derives (map map_rule_rels p) (map map_fact meta_hyps) (f R) args.
    Proof.
      intros Hvalid HIn Hmr Hmf_args Hmfs_consistent Hinj.
      cbv [one_step_derives one_step_derives0].
      pose proof Hmr as Hmh.
      apply meta_hyps_are_meta_facts in Hmh.
      apply Hvalid in Hmr; [|assumption].
      clear Hvalid HIn.
      split; intros H; fwd.
      - do 2 eexists.
        split; [apply in_map; eassumption | split].
        + apply non_meta_rule_impl_map_fw. eassumption.
        + rewrite Lists.List.Forall_map. eapply Forall_impl; [|eassumption].
          intros f' Hex. apply Exists_exists in Hex. fwd.
          apply Exists_exists. eexists. split; [apply in_map; eassumption |].
          destruct Hexp1 as [Hext | Hmatch].
          * left. apply extensionally_equal_map_fw. eassumption.
          * right. apply fact_matches_map_fw. eassumption.
      - apply in_map_iff in Hp0. fwd.
        pose proof Hp1 as Hp1'.
        apply non_meta_rule_invert_map in Hp1. fwd.
        eapply non_meta_rule_impl_map_bw in Hp1'. fwd.
        apply Hinj in Hp1'p0. subst.
        specialize (Hmr _ _ _ ltac:(eassumption) ltac:(eauto) ltac:(eassumption)).
        do 2 eexists. split; [eassumption | split].
        + eassumption.
        + clear Hp1'p2.
          rewrite Lists.List.Forall_map in Hp2.
          apply Forall2_forget_l in Hp1'p1. apply Forall_forall.
          intros f' Hf'. rewrite Forall_forall in Hp1'p1.
          specialize (Hp1'p1 _ Hf'). fwd.
          rewrite Forall_forall in Hp2.
          specialize (Hp2 _ ltac:(eassumption)). apply Exists_map in Hp2.
          apply Exists_exists in Hp2. fwd.
          rewrite Forall_forall in Hmr. specialize (Hmr _ Hf').
          rewrite Forall_forall in Hmh. specialize (Hmh _ ltac:(eassumption)).
          destruct Hp2p1 as [Hext | Hmatch].
          * apply extensionally_equal_map_bw in Hext. fwd.
            destruct f'.
            { (*gross*)
              exfalso.
              destruct x0, x1, f1', f2';
                cbv [is_meta] in Hmh; try contradiction;
                cbv [fact_equiv map_fact] in Hp1'p1p1; try discriminate Hp1'p1p1;
                cbv [fact_equiv map_fact] in Hextp0; try discriminate Hextp0;
                cbv [fact_equiv map_fact] in Hextp1; try discriminate Hextp1;
                cbv [extensionally_equal] in Hextp2; try contradiction. }
            fwd.
            apply Exists_exists. eexists. split; [exact Hmr|].
            left. simpl. ssplit; auto.
            intros args' Hargs'.
                        cbv [fact_equiv map_fact] in Hp1'p1p1, Hextp0, Hextp1.
            destruct x0 as [| R_x0 args_x0 S_x0]; try discriminate.
            destruct f1' as [| R_f1 args_f1 S_f1]; try discriminate.
            destruct f2' as [| R_f2 args_f2 S_f2]; try contradiction.
            destruct x1 as [| R_x1 args_x1 S_x1]; try discriminate.
            simpl in Hextp2. fwd.
            rewrite Hextp2p2 by assumption.
            eapply Hmfs_consistent; try eassumption.
            congruence.
          * apply fact_matches_map_bw in Hmatch. fwd.
            destruct f'.
            2: { exfalso.
                 cbv [fact_matches] in Hmatchp2. fwd.
                 cbv [fact_equiv map_fact] in Hmatchp0, Hp1'p1p1.
                 destruct x0; congruence. }
            fwd. apply Exists_exists. eexists. split; [exact Hmrp0|].
            right. cbv [fact_matches]. do 4 eexists. ssplit; try reflexivity.
            1: assumption.
            cbv [fact_matches] in Hmatchp2.
            destruct Hmatchp2 as [R_f [nf_args_f [mf_args_f [mf_set_f [H_match_args [H_set_eval [H_f1' H_f2']]]]]]].
            subst f1' f2'.

            cbv [fact_equiv map_fact] in Hp1'p1p1, Hmatchp0, Hmatchp1.
            destruct x0 as [R_x0 args_x0 | ]; try discriminate.
            destruct x1 as [ | R_x1 mf_args_x1 S_x1]; try contradiction.

            inversion Hp1'p1p1; subst.
            inversion Hmatchp0; subst.
            inversion Hmatchp1; subst.

            eapply (proj1 (Hmfs_consistent _ _ _ _ _ _ Hp2p0 Hmrp0 ltac:(congruence) _ H_match_args Hmrp1)).
            exact H_set_eval.
    Qed.

    Lemma rule_impl_map_rule_rels_fw p r f0 hyps :
      meta_rules_valid p ->
      In r p ->
      injective_on (rel_of f0) ->
      meta_facts_consistent_with_map hyps ->
      rule_impl (one_step_derives p) r f0 hyps ->
      rule_impl (one_step_derives (map map_rule_rels p))
        (map_rule_rels r)
        (map_fact f0)
        (map map_fact hyps).
    Proof.
      intros Hvalid Hr Hinj Hcon Himpl. pose proof Himpl as Himpl0. invert Himpl.
      - econstructor. apply non_meta_rule_impl_map_fw. eassumption.
      - simpl. econstructor.
        + rewrite Exists_map. eapply Exists_impl; [|eassumption].
          simpl. intros c Hc. eapply interp_meta_clause_map_fw in Hc. eassumption.
        + apply Forall2_interp_meta_clause_map_fw. eassumption.
        + intros args'' Hargs. rewrite H1 by assumption.
          eapply meta_cond_map_iff; eassumption.
    Qed.

    Lemma Forall2_interp_meta_clause_map_bw ctx hyps1 hyps2 :
      Forall2 (interp_meta_clause ctx) (map map_meta_clause_rel hyps1) (map map_fact hyps2) ->
      exists hyps2',
        Forall2 fact_equiv hyps2 hyps2' /\
        Forall2 (interp_meta_clause ctx) hyps1 hyps2'.
    Proof.
      intros H. rewrite <- Forall2_map_l, <- Forall2_map_r in H.
      induction H.
      - eexists []. split; constructor.
      - apply interp_meta_clause_map_bw in H. destruct H as [h' [Heq Hinterp]].
        destruct IHForall2 as [hyps2' [HForall_eq HForall_interp]].
        eexists (h' :: hyps2'). split; constructor; eauto.
    Qed.

    Lemma meta_facts_consistent_with_map_equiv hyps hyps' :
      meta_facts_consistent_with_map hyps ->
      Forall2 fact_equiv hyps hyps' ->
      meta_facts_consistent_with_map hyps'.
    Proof.
      intros Hcon Heq.
      cbv [meta_facts_consistent_with_map].
      intros R1 args1 S1 R2 args2 S2 Hin1 Hin2 Hf_eq nf_args Hmatch1 Hmatch2.

      apply Forall2_forget_l in Heq. rewrite Forall_forall in Heq.
      apply Heq in Hin1, Hin2. fwd.

      cbv [fact_equiv map_fact] in Hin1p1, Hin2p1.
      destruct x as [| R1' args1' S1']; try discriminate.
      destruct x0 as [| R2' args2' S2']; try discriminate.
      fwd. eauto using eq_trans.
    Qed.

    Lemma rule_impl_map_rule_rels_bw p r f0 hyps :
      meta_rules_valid p ->
      In r p ->
      injective_on (rel_of f0) ->
      meta_facts_consistent_with_map hyps ->
      rule_impl (one_step_derives (map map_rule_rels p))
        (map_rule_rels r)
        (map_fact f0)
        (map map_fact hyps) ->
      exists f0' hyps',
        fact_equiv f0 f0' /\
        Forall2 fact_equiv hyps hyps' /\
        rule_impl (one_step_derives p) r f0' hyps'.
    Proof.
      intros Hvalid Hr Hinj Hcon Himpl. invert Himpl.
      - destruct f0; simpl in *; repeat invert_stuff.
        eassert (H':_) by (eapply non_meta_rule_impl_map_bw; eassumption).
        fwd. apply Hinj in H'p0. subst. eauto 7.
      - destruct f0; simpl in *; repeat invert_stuff.
        destruct r; simpl in *; repeat invert_stuff.
        apply Forall2_interp_meta_clause_map_bw in H2. fwd.
        rewrite Exists_map in H1. apply Exists_exists in H1. fwd.
        apply interp_meta_clause_map_bw with (h := meta_fact _ _ _) in H1p1. fwd.
        do 2 eexists. split; [eassumption|]. split; [eassumption|].
        cbv [fact_equiv] in H1p1p0. simpl in H1p1p0.
        destruct h'; simpl in H1p1p0; try discriminate. fwd.
        econstructor.
        + apply Exists_exists. eauto.
        + assumption.
        + intros. rewrite H3 by assumption. symmetry.
          apply Hinj in H1. subst.
          replace (map map_fact hyps) with (map map_fact hyps2').
          2: { apply Forall2_eq_map. rewrite <- Forall2_map_r.
               eapply Forall2_impl; [|eassumption].
               auto. }
          eapply meta_cond_map_iff; try eassumption.
          2: { eauto using meta_facts_consistent_with_map_equiv. }
          econstructor.
          -- apply Exists_exists. eexists. split; [eassumption|].
             cbv [interp_meta_clause]. cbv [interp_meta_clause] in H1p1p1.
             fwd. eauto.
          -- assumption.
          -- intros. reflexivity.
    Qed.

    Lemma rule_impl_map_rule_rels_f_target blah r f_target hyps :
      rule_impl blah (map_rule_rels r) f_target hyps ->
      exists f0, f_target = map_fact f0 /\ In (rel_of f0) (concl_rels r).
    Proof.
      invert 1.
      - destruct r; simpl in H0; invert H0.
        + rewrite Exists_map in H2. apply Exists_exists in H2. fwd.
          cbv [interp_clause] in H2p1. fwd.
          eexists (normal_fact _ _). simpl. auto using in_map.
        + eexists (normal_fact _ _). simpl. auto using in_map.
      - destruct r; simpl in H0; invert H0.
        rewrite Exists_map in H1. apply Exists_exists in H1. fwd.
        cbv [interp_meta_clause] in H1p1. fwd.
        eexists (meta_fact _ _ _). simpl. auto using in_map.
    Qed.

    Lemma prog_impl_fact_equiv (p : list (rule rel1 exprvar fn aggregator)) Q f1 f2 :
      Forall injective_on (flat_map concl_rels p) ->
      (forall f1' f2', fact_equiv f1' f2' -> Q f1' <-> Q f2') ->
      fact_equiv f1 f2 ->
      prog_impl p Q f1 <-> prog_impl p Q f2.
    Proof.
      intros Hinj HQ Heq. split; intros Hprog.
      - pose proof Hprog as Hprog_copy. apply prog_impl_rel_of in Hprog_copy.
        destruct Hprog_copy as [HQ1 | Hconcl].
        + apply prog_impl_leaf. apply (proj1 (HQ _ _ Heq)). exact HQ1.
        + rewrite Forall_forall in Hinj. apply Hinj in Hconcl. cbv [injective_on] in Hconcl.
          destruct f1 as [R1 args1 | R1 mf_args1 S1], f2 as [R2 args2 | R2 mf_args2 S2];
            cbv [fact_equiv map_fact] in Heq; try discriminate;
            inversion Heq;
            assert (f R1 = f R2) by congruence;
            apply Hconcl in H; subst; exact Hprog.
      - pose proof Hprog as Hprog_copy. apply prog_impl_rel_of in Hprog_copy.
        destruct Hprog_copy as [HQ2 | Hconcl].
        + apply prog_impl_leaf. apply (proj2 (HQ _ _ Heq)). exact HQ2.
        + rewrite Forall_forall in Hinj. apply Hinj in Hconcl. cbv [injective_on] in Hconcl.
          destruct f1 as [R1 args1 | R1 mf_args1 S1], f2 as [R2 args2 | R2 mf_args2 S2];
            cbv [fact_equiv map_fact] in Heq; try discriminate;
            inversion Heq;
            assert (f R2 = f R1) by congruence;
            apply Hconcl in H; subst; exact Hprog.
    Qed.

    Lemma prog_impl_map_rule_rels_fw p Q f0 :
      meta_rules_valid p ->
      (forall f, Q f -> ~ In (rel_of f) (flat_map concl_rels p)) ->
      doesnt_lie Q ->
      (forall f1 f2, fact_equiv f1 f2 -> Q f1 <-> Q f2) ->
      Forall injective_on (flat_map concl_rels p) ->
      prog_impl p Q f0 ->
      prog_impl (map map_rule_rels p) (fun f' => exists f, f' = map_fact f /\ Q f) (map_fact f0).
    Proof.
      intros Hvalid Hinp Hlie HQ Hinj Hprog.
      induction Hprog.
      - apply prog_impl_leaf. eexists; eauto.
      - apply Exists_exists in H. destruct H as [r [Hr_in Hr_impl]].
        eapply prog_impl_step.
        + apply Exists_map. apply Exists_exists. exists r. split; [exact Hr_in|].
          eapply rule_impl_map_rule_rels_fw; try eassumption.
          * rewrite Forall_forall in Hinj. apply Hinj. apply in_flat_map.
            eexists. split; [eassumption|].
            eapply rule_impl_concl_relname_in. eassumption.
          * intros R1 args1 S1 R2 args2 S2 Hin1 Hin2 Heq nf_args Hmatch1 Hmatch2.
            rewrite Forall_forall in H0.
            eapply meta_facts_consistent.
            -- eassumption.
            -- intros R' args1' args2' S1' S2' HQ1 HQ2 nf_args' Hmatch1' Hmatch2'.
               cbv [doesnt_lie consistent] in Hlie.
               rewrite (Hlie _ _ _ HQ1 _ Hmatch1'), (Hlie _ _ _ HQ2 _ Hmatch2').
               reflexivity.
            -- Fail assumption. (*why*) eassumption.
            -- apply H0. exact Hin1.
            -- rewrite prog_impl_fact_equiv; try eassumption.
               ++ apply H0. exact Hin2.
               ++ cbv [fact_equiv]. simpl. f_equal. congruence.
            -- eassumption.
            -- eassumption.
        + rewrite Lists.List.Forall_map. eapply Forall_impl; [|eassumption].
          simpl. auto.
    Qed.

    Hint Resolve prog_impl_leaf : core.
    Lemma prog_impl_map_rule_rels_bw' p Q f_target :
      meta_rules_valid p ->
      (forall f, Q f -> ~ In (rel_of f) (flat_map concl_rels p)) ->
      doesnt_lie Q ->
      (forall f1 f2, fact_equiv f1 f2 -> Q f1 <-> Q f2) ->
      Forall injective_on (flat_map concl_rels p) ->
      prog_impl (map map_rule_rels p) (fun f' => exists f, f' = map_fact f /\ Q f) f_target ->
      exists f0, f_target = map_fact f0 /\ prog_impl p Q f0.
    Proof.
      intros Hvalid Hinp Hlie HQ Hinj Hprog.
      induction Hprog.
      - fwd. eauto.
      - apply Exists_map in H. apply Exists_exists in H. fwd.
        pose proof Hp1 as H'. apply rule_impl_map_rule_rels_f_target in H'.
        fwd.
        apply Forall_exists_r_Forall2 in H1. fwd.
        pose proof H1 as H1'.
        apply Forall2_flip in H1'. eapply Forall2_impl in H1'.
        1: eapply Forall2_eq_map in H1'.
        2: { cbv [fun_rel]. intros. fwd. eauto. }
        subst.
        eassert (H':_).
        { eapply rule_impl_map_rule_rels_bw; try eassumption.
          - rewrite Forall_forall in Hinj. apply Hinj. apply in_flat_map.
            eexists. split; [eassumption|]. assumption.
          - intros R1 args1 S1 R2 args2 S2 Hin1 Hin2 Heq nf_args Hmatch1 Hmatch2.
            rewrite Forall_forall in H0. Check meta_facts_consistent.
            eapply meta_facts_consistent.
            -- eassumption.
            -- intros R' args1' args2' S1' S2' HQ1 HQ2 nf_args' Hmatch1' Hmatch2'.
               cbv [doesnt_lie consistent] in Hlie.
               rewrite (Hlie _ _ _ HQ1 _ Hmatch1'), (Hlie _ _ _ HQ2 _ Hmatch2').
               reflexivity.
            -- Fail assumption. (*why*) eassumption.
            -- apply Forall2_forget_l in H1. rewrite Forall_forall in H1.
               apply H1 in Hin1. fwd. eassumption.
            -- rewrite prog_impl_fact_equiv; try eassumption.
               ++ apply Forall2_forget_l in H1. rewrite Forall_forall in H1.
                  apply H1 in Hin2. fwd. eassumption.
               ++ cbv [fact_equiv]. simpl. f_equal. congruence.
            -- eassumption.
            -- eassumption. }
        fwd.
        eexists. split; [eassumption|].
        eapply prog_impl_step.
        { apply Exists_exists. eauto. }
        apply Forall2_forget_l in H'p2, H1. rewrite Forall_forall in H1, H'p2.
        apply Forall_forall. intros f' Hf'. apply H'p2 in Hf'. fwd.
        apply H1 in Hf'p0. fwd.
        rewrite <- prog_impl_fact_equiv; eassumption.
    Qed.

    Lemma map_fact_inj f0 f0' :
      injective_on (rel_of f0) ->
      map_fact f0 = map_fact f0' ->
      f0 = f0'.
    Proof.
      intros Hinj Heq.
      destruct f0 as [R1 args1 | R1 mf_args1 S1],
               f0' as [R2 args2 | R2 mf_args2 S2];
        cbv [map_fact rel_of] in *; try discriminate.
      - (* Case: normal_fact *)
        inversion Heq; subst.
        assert (R1 = R2) by (apply Hinj; congruence).
        subst. reflexivity.
      - (* Case: meta_fact *)
        inversion Heq; subst.
        assert (R1 = R2) by (apply Hinj; congruence).
        subst. reflexivity.
    Qed.

    Lemma prog_impl_map_rule_rels_iff p Q f0 :
      meta_rules_valid p ->
      (forall f, Q f -> ~ In (rel_of f) (flat_map concl_rels p)) ->
      doesnt_lie Q ->
      (forall f1 f2, fact_equiv f1 f2 -> Q f1 <-> Q f2) ->
      Forall injective_on (flat_map concl_rels p) ->
      injective_on (rel_of f0) ->
      prog_impl p Q f0 <->
      prog_impl (map map_rule_rels p) (fun f' => exists f, f' = map_fact f /\ Q f) (map_fact f0).
    Proof.
      intros. split; intros H'.
      - apply prog_impl_map_rule_rels_fw; assumption.
      - eapply prog_impl_map_rule_rels_bw' in H'; try assumption.
        destruct H' as [f0' [Heq Hprog]].
        eapply map_fact_inj in Heq; try assumption. subst. assumption.
    Qed.

    Lemma concl_rels_map_rule_rels r :
      concl_rels (map_rule_rels r) = map f (concl_rels r).
    Proof.
      destruct r; simpl.
      - do 2 rewrite map_map. reflexivity.
      - do 2 rewrite map_map. reflexivity.
      - reflexivity.
    Qed.

    Lemma hyp_rels_map_rule_rels r :
      hyp_rels (map_rule_rels r) = map f (hyp_rels r).
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

    Lemma map_fact_fact_of R args :
      map_fact (fact_of R args) = fact_of (f R) args.
    Proof.
      destruct args; reflexivity.
    Qed.

    Lemma map_fact_eq_fact_of f0 :
      map_fact f0 = fact_of (f (rel_of f0)) (args_of f0).
    Proof.
      destruct f0; reflexivity.
    Qed.
  End map.

  Inductive flat_rel : Type :=
  (* | input_rel (block : nat) (name : lvar) *)
  | false_rel
  | lvar_rel (block : nat) (name : lvar).

  Context {relmap : map.map lvar flat_rel} {relmap_ok : map.ok relmap}.
  Context {lvar_eqb : lvar -> lvar -> _} {lvar_eqb_spec : EqDecider lvar_eqb}.

  Definition flatten_rel (block : nat) (m : relmap) (R : block_rel) :=
    match R with
    | local x => lvar_rel block x
    | input x => match map.get m x with
                | Some R => R
                | None => false_rel
                end
    end.

  Fixpoint flatten (name : nat) (e : blocks_prog flat_rel) : nat * flat_rel * list (rule flat_rel exprvar fn aggregator) :=
    match e with
    | LetIn x f =>
        let '(name', Rx, p2) := flatten name x in
        let '(name'', Rfx, p1) := flatten name' (f Rx) in
        (name'', Rfx, p1 ++ p2)
    | Block ret inputs p =>
        let p' := map (map_rule_rels (flatten_rel name (map.of_list inputs))) p in
        (S name, lvar_rel name ret, p')
    end.

  (* Lemma use_honest_prog p Q mf_rel mf_args mf_set : *)
  (*   honest_block_prog p -> *)
  (*   prog_impl p Q (meta_fact mf_rel mf_args mf_set) -> *)
  (*   prog_impl p Q (meta_fact mf_rel mf_args (fun args => prog_impl p Q (normal_fact mf_rel args))). *)
  (* Proof. *)
  (*   intros H1 H2. *)
  (*   (*   eapply prog_impl_mf_ext; [eassumption|]. *) *)
  (*   (*   cbv [honest_block_prog] in H1. apply H1. apply H2. *) *)
  (*   (* Qed. *) *)
  (* Abort. *)

  Definition in_range lo hi x :=
    match x with
    | lvar_rel block_id _ => lo <= block_id < hi
    | false_rel => False
    end.

  Definition not_as_big_as hi x :=
    match x with
    | lvar_rel block_id _ => block_id < hi
    | false_rel => False
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

  Lemma in_nonoverlapping_ranges lo1 hi1 lo2 hi2 x :
    in_range lo1 hi1 x ->
    in_range lo2 hi2 x ->
    hi1 <= lo2 ->
    False.
  Proof. destruct x; simpl; auto. lia. Qed.

  Definition is_input R :=
    match R with
    | local _ => false
    | input _ => true
    end.

  Definition no_input_concls_in_block (p : list block_rule) :=
    forallb (fun R => negb (is_input R)) (flat_map concl_rels p).

  Fixpoint valid_blocks_prog {var} (e : blocks_prog var) : Prop :=
    match e with
    | LetIn x f =>
        valid_blocks_prog x /\ (forall v, valid_blocks_prog (f v))
    | Block ret inputs p =>
        meta_rules_valid p /\
          NoDup (map fst inputs) /\
          (forall l, ~ In (input l) (flat_map concl_rels p))
    end.

  Lemma interp_blocks_prog_honest {var2} (x : var2) ctx (e : blocks_prog (fact_args T -> Prop)) (e0 : blocks_prog var2) :
    wf_blocks_prog ctx e e0 ->
    valid_blocks_prog e ->
    Forall honest_args (map fst ctx) ->
    honest_args (interp_blocks_prog map.empty e).
  Proof.
    intros Hwf.
    induction Hwf as [ctx x1 x2 f1 f2 Hwf1 IH1 Hwf2 IH2 | ctx ret inps1 inps2 p Hfor];
      intros Hvalid Hctx.
    - (* Case: wf_LetIn *)
      simpl in Hvalid. destruct Hvalid as [Hvalid_x Hvalid_f].
      simpl.
      eapply IH2.
      + apply Hvalid_f.
      + simpl. constructor; [|exact Hctx].
        apply IH1; assumption.

    - (* Case: wf_Block *)
      simpl in Hvalid. destruct Hvalid as [Hvalid_p [Hnodup Hno_input]].
      simpl. apply doesnt_lie_honest_args.
      eapply valid_impl_honest.
      + exact Hvalid_p.

      + (* Prove Q doesn't overlap with concl_rels *)
        intros f_target Hf_target.
        apply Exists_exists in Hf_target. destruct Hf_target as [[R R'] [Hin [Hrel Hargs]]].
        rewrite <- Hrel. apply Hno_input.

      + (* Prove doesnt_lie using the context! *)
        cbv [doesnt_lie consistent].
        intros mf_rel mf_args mf_set Hmf nf_args Hmatch.
        apply Exists_exists in Hmf. destruct Hmf as [[R R'] [Hin [Hrel Hargs]]].
        simpl in Hrel. subst.

        (* 1. Extract the context binding from wf_Block's Forall2 *)
        apply Forall2_forget_r in Hfor. rewrite Forall_forall in Hfor.
        specialize (Hfor _ Hin). fwd.

        (* 2. Extract honest_args R' from the Hctx hypothesis *)
        assert (honest_args R') as Hhonest_R'.
        { rewrite Forall_forall in Hctx. apply Hctx.
          apply in_map_iff. eexists (_, _). simpl. eauto. }

        (* 3. Feed it into our evaluation! *)
        cbv [honest_args args_consistent] in Hhonest_R'.
        rewrite Hhonest_R' by eassumption.

        split; intros H'.
        * (* Forward *)
          apply Exists_exists. eexists (_, _). simpl. eauto.
        * (* Backward *)
          apply Exists_exists in H'. destruct H' as [[R0 R0'] [Hin0 [Hrel0 Hargs0]]].
          simpl in Hrel0. fwd.
          (* Enforce functional determinism using NoDup on the inputs list *)
          assert (R' = R0').
          { eapply NoDup_fst_In_inj; eassumption. }

          subst R0'. exact Hargs0.
          Unshelve. assumption.
  Qed.

  Hint Resolve in_fst in_snd : core.
  Lemma flatten_correct' ctx name e e0 name' Rret p :
    wf_blocks_prog ctx e e0 ->
    valid_blocks_prog e ->
    flatten name e0 = (name', Rret, p) ->
    Forall (in_range O name) (map snd ctx) ->
    NoDup (map snd ctx) ->
    Forall honest_args (map fst ctx) ->
    name <= name' /\
      in_range name name' Rret /\
      Forall (in_range name name') (flat_map concl_rels p) /\
      Forall (fun R => in_range name name' R \/ In R (map snd ctx) \/ R = false_rel) (flat_map all_rels p) /\
      forall args,
        interp_blocks_prog map.empty e args <->
          prog_impl p (fun f => exists R, In (R, rel_of f) ctx /\ R (args_of f))
            (fact_of Rret args).
  Proof.
    intros Hwf Hvalid. revert name name' Rret p.
    induction Hwf;
      intros name name' Rret p0 Hflat Hctx1 Hctx2 Hctx3;
      simpl in Hflat;
      fwd;
      simpl.
    - simpl in Hvalid. fwd.
      specialize (IHHwf ltac:(assumption)). epose_dep IHHwf.
      specialize (IHHwf ltac:(eassumption) ltac:(eassumption) ltac:(assumption) ltac:(eassumption)).
      fwd.
      rename H0 into IH'. specialize (IH' (interp_blocks_prog map.empty x1)).
      epose_dep IH'. specialize (IH' ltac:(eauto)). epose_dep IH'.
      specialize (IH' ltac:(eassumption)). specialize' IH'.
      { constructor.
        - eapply in_range_weaken; [eassumption| |]; lia.
        - eapply Forall_impl; [|eassumption].
          intros. eapply in_range_weaken; [eassumption| |]; lia. }
      specialize' IH'.
      { simpl. constructor; auto. rewrite Forall_forall in Hctx1.
        intros Hf. apply in_map_iff in Hf. destruct Hf as [(?, ?) Hf]. fwd.
        simpl in *. specialize (Hctx1 _ ltac:(eauto)).
        eauto using in_nonoverlapping_ranges. }
      specialize' IH'.
      { simpl. constructor; auto. eauto using interp_blocks_prog_honest. }
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
               specialize (Hctx1 _ ltac:(eauto)). simpl in H1.
               eapply in_nonoverlapping_ranges. 1: exact Hctx1. 1: exact H1. lia.
             - subst. cbv [in_range] in H1. contradiction. }
        rewrite IH'p4.
        apply prog_impl_hyp_ext_strong.
        { split; intros Hargs; simpl; fwd; exfalso.
          - destruct Hargsp0 as [Hargsp0|Hargsp0]; fwd.
            + apply IHHwfp4 in Hargsp1. rewrite fact_of_rel_of_args_of in Hargsp1.
              apply prog_impl_rel_of in Hargsp1. destruct Hargsp1 as [Hargsp1|Hargsp1].
              -- fwd. rewrite rel_of_fact_of in Hargsp1p0.
                 rewrite Forall_forall in Hctx1. apply in_snd in Hargsp1p0.
                 apply Hctx1 in Hargsp1p0.
                 eauto using in_nonoverlapping_ranges.
              -- rewrite rel_of_fact_of in Hargsp1.
                 rewrite Forall_forall in IHHwfp2.
                 apply IHHwfp2 in Hargsp1.
                 eauto using in_nonoverlapping_ranges.
            + rewrite rel_of_fact_of in Hargsp0.
              rewrite Forall_forall in Hctx1. apply in_snd in Hargsp0.
              apply Hctx1 in Hargsp0.
              eauto using in_nonoverlapping_ranges.
          - apply prog_impl_rel_of in Hargs. destruct Hargs as [Hargs|Hargs].
            + fwd. rewrite rel_of_fact_of in Hargsp0.
              rewrite Forall_forall in Hctx1. apply in_snd in Hargsp0.
              apply Hctx1 in Hargsp0.
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
              --- subst. simpl. eexists. split; eauto. apply IHHwfp4.
                  rewrite fact_of_rel_of_args_of. assumption.
              --- apply in_map_iff in HRf'. destruct HRf' as [[? ?] HRf'].
                  simpl in HRf'. fwd.
                  rewrite Forall_forall in Hctx1.
                  apply in_snd in HRf'p1. apply Hctx1 in HRf'p1.
                  exfalso. eauto using in_nonoverlapping_ranges.
              --- apply prog_impl_rel_of in Hf''. destruct Hf'' as [Hf''|Hf''].
                  { fwd. simpl. eauto. }
                  exfalso. rewrite HRf' in Hf''. apply IHHwfp2 in Hf''.
                  simpl in Hf''. contradiction.
    - simpl in Hvalid.
      eassert (inps_eq : map fst _ = map fst _).
      { apply Forall2_eq_eq. rewrite <- Forall2_map_l, <- Forall2_map_r.
        eapply Forall2_impl; [|eassumption]. intros (?, ?) (?, ?) ?. fwd. reflexivity. }
      ssplit.
      + lia.
      + lia.
      + simpl. lia.
      + apply Forall_flat_map. apply Forall_map. apply Forall_forall.
        intros r Hr. rewrite concl_rels_map_rule_rels. apply Forall_map.
        fwd. apply Forall_forall. intros R HR. destruct R.
        2: { exfalso. eapply Hvalidp2. apply in_flat_map. eauto. }
        simpl. lia.
      + apply Forall_flat_map. apply Forall_map. apply Forall_forall.
        intros r Hr. rewrite all_rels_map_rule_rels. apply Forall_map.
        apply Forall_forall. intros R HR.
        destruct R; try solve [simpl; auto]. simpl.
        destruct (map.get _ _) eqn:E; simpl.
        -- apply of_list_Some_in in E.
           apply Forall2_forget_l in H. rewrite Forall_forall in H.
           apply H in E. destruct E as [[? ?] ?]. fwd. eauto.
        -- auto.
      + intros args. erewrite prog_impl_map_rule_rels_iff with (f := flatten_rel _ _).
        -- rewrite map_fact_fact_of. simpl. apply prog_impl_hyp_ext_strong.
           ++ split; intros H'; fwd.
              --- apply Exists_exists in H'p1. fwd.
                  apply Forall2_forget_r in H. rewrite Forall_forall in H.
                  specialize (H _ ltac:(eassumption)). fwd.
                  rewrite Forall_forall in Hctx1. apply in_snd in Hp1p1.
                  specialize (Hctx1 _ ltac:(eassumption)).
                  simpl in Hctx1.
                  assert (H_rel : rel_of (fact_of (lvar_rel name ret) args) = rel_of (map_fact (flatten_rel name (map.of_list inps2)) f)) by congruence.
                  rewrite rel_of_fact_of, rel_of_map_fact in H_rel.
                  rewrite <- H'p1p1p0 in H_rel.
                  cbv [flatten_rel] in H_rel.
                  erewrite map.get_of_list_In_NoDup in H_rel; try eassumption.
                  2: { rewrite <- inps_eq. assumption. }
                  rewrite <- H_rel in Hp1p1.
                  destruct f0; simpl in Hctx1; try contradiction.
                  fwd.
                  lia.
              --- rewrite rel_of_fact_of in H'p0. rewrite args_of_fact_of in H'p1.
                  rewrite Forall_forall in Hctx1. apply in_snd in H'p0.
                  specialize (Hctx1 _ ltac:(eassumption)). simpl in Hctx1. lia.
           ++ intros f'. split; intros H'; fwd.
              --- rewrite rel_of_map_fact, args_of_map_fact.
                  apply Exists_exists in H'p1. fwd. apply Forall2_forget_r in H.
                  rewrite Forall_forall in H. apply H in H'p1p0. fwd.
                  rewrite <- H'p1p1p0. simpl.
                  erewrite map.get_of_list_In_NoDup; try eassumption.
                  2: { rewrite <- inps_eq. assumption. }
                  eauto.
              --- rewrite Forall_forall in Hctx1.
                  specialize (Hctx1 _ ltac:(eauto)).
                  simpl in Hctx1.
                  rewrite <- (fact_of_rel_of_args_of f').
                  destruct (rel_of f'); simpl in Hctx1; try contradiction.
                  rewrite in_flat_map in *. fwd. rewrite in_map_iff in *. fwd.
                  rewrite hyp_rels_map_rule_rels in *. rewrite in_map_iff in *.
                  fwd.
                  eexists (fact_of _ _). rewrite map_fact_fact_of.
                  rewrite H0p1p0. split; [reflexivity|].
                  match goal with
                  | H: flatten_rel _ _ ?x = lvar_rel _ _ |- _ => destruct x; simpl in H
                  end.
                  { fwd. lia. }
                  destruct (map.get _ _) eqn:E; subst; try discriminate.
                  apply of_list_Some_in in E.
                  apply Forall2_forget_l in H. rewrite Forall_forall in H.
                  specialize (H _ ltac:(eassumption)). destruct H as [(?, ?) H].
                  fwd.
                  epose proof NoDup_snd_In_inj as H'.
                  specialize (H' _ _ _ _ ltac:(eassumption) Hp2 H'p0). subst.
                  rewrite rel_of_fact_of, args_of_fact_of.
                 apply Exists_exists. eexists (_, _). eauto.
        -- fwd. assumption.
        -- intros f Hf. apply Exists_exists in Hf. fwd. rewrite <- Hfp1p0.
           auto.
        -- cbv [doesnt_lie]. intros mf_rel mf_args mf_set Hmf.
           apply Exists_exists in Hmf. fwd. simpl in *. subst.
           cbv [consistent]. intros nf_args Hnf_args.
           apply Forall2_forget_r in H. rewrite Forall_forall in H.
           specialize (H _ ltac:(eassumption)). fwd. rewrite Forall_forall in Hctx3.
           specialize (Hctx3 _ ltac:(eauto)).
           cbv [honest_args args_consistent] in Hctx3. rewrite Hctx3 by eassumption.
           simpl. split; intros Hnf_args'.
           ++ apply Exists_exists. eexists (_, _). eauto.
           ++ apply Exists_exists in Hnf_args'. fwd.
              eapply NoDup_fst_In_inj in Hnf_args'p0. 3: exact Hmfp0.
              2: assumption. subst. assumption.
        -- eenough _ as H'.
           { intros f1 f2 Hfs. epose proof (H' f1 f2 Hfs) as H1. split; [exact H1|].
             apply H'. symmetry. assumption. }

           intros f1 f2 Hequiv Hf1. apply Exists_exists in Hf1. fwd.
           cbv [fact_equiv] in Hequiv. do 2 rewrite map_fact_eq_fact_of in Hequiv.
           apply fact_of_inj in Hequiv. fwd. rewrite <- Hf1p1p0 in Hequivp0.
           pose proof H as H0.
           apply Forall2_forget_r in H. rewrite Forall_forall in H.
           specialize (H _ ltac:(eassumption)). fwd. simpl in Hequivp0.
           erewrite map.get_of_list_In_NoDup in Hequivp0; try eassumption.
           2: { rewrite <- inps_eq. assumption. }
           subst. clear Hp0. rewrite Forall_forall in Hctx1.
           specialize (Hctx1 _ ltac:(eauto)).
           destruct (rel_of f2); simpl in Hctx1, Hp1p1. 1: lia.
           destruct (map.get _ _) eqn:E.
           2: { simpl in Hctx1. contradiction. }
           apply of_list_Some_in in E.
           apply Forall2_forget_l in H0. rewrite Forall_forall in H0.
           apply H0 in E. destruct E as [[? ?] ?]. fwd. apply Exists_exists.
           eexists (_, _). split; [exact Hp0|]. split; [reflexivity|].
           eapply NoDup_snd_In_inj in Hp2. 3: exact Hp1p1. 2: assumption.
           subst. rewrite <- Hequivp1. assumption.
        -- fwd. apply Forall_forall. intros R HR. destruct R.
           2: { exfalso. eapply Hvalidp2. eassumption. }
           cbv [injective_on]. simpl. intros R' HR'.
           destruct R'; simpl in HR'; fwd; auto. exfalso.
           apply of_list_Some_in in E. apply Forall2_forget_l in H.
           rewrite Forall_forall in H. apply H in E. destruct E as [[? ?] ?]. fwd.
           rewrite Forall_forall in Hctx1. specialize (Hctx1 _ ltac:(eauto)).
           simpl in Hctx1. lia.
        -- rewrite rel_of_fact_of.
           cbv [injective_on]. simpl. intros R' HR'.
           destruct R'; simpl in HR'; fwd; auto. exfalso.
           apply of_list_Some_in in E. apply Forall2_forget_l in H.
           rewrite Forall_forall in H. apply H in E. destruct E as [[? ?] ?]. fwd.
           rewrite Forall_forall in Hctx1. specialize (Hctx1 _ ltac:(eauto)).
           simpl in Hctx1. lia.
  Qed.
End Blocks.
Arguments blocks_prog : clear implicits.
