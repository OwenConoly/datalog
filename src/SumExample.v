From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Stdlib Require Import ZArith.Zdiv.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics.

From coqutil Require Import Map.Interface Map.Properties Map.Solver.
From Datalog Require Import Datalog.
Import ListNotations.

Definition rel := string.
Definition var := string.
Inductive fn :=
| plus
| times
| range.
Inductive T :=
| nat_range (lo hi : nat)
| nat_val (n : nat).
Inductive aggregator :=
| sum
| prod.
Definition interp_fn (f : fn) (args : list T) : option T :=
  match f, args with
  | plus, [nat_val a; nat_val b] => Some (nat_val (a + b))
  | times, [nat_val a; nat_val b] => Some (nat_val (a * b))
  | range, [nat_val a; nat_val b] => Some (nat_range a b)
  | _, _ => None
  end.
Definition get_set (x : T) : option (list T) :=
  match x with
  | nat_range lo hi => Some (map nat_val (seq lo (hi - lo)))
  | nat_val _ => None
  end.
Definition agg_id (a : aggregator) :=
  match a with
  | sum => nat_val O
  | prod => nat_val (S O)
  end.
Definition interp_agg (a : aggregator) (x y : T) :=
  match a, x, y with
  | sum, nat_val x, nat_val y => nat_val (x + y)
  | prod, nat_val x, nat_val y => nat_val (x * y)
  | _, _, _ => nat_val 42 (*garbage*)
  end.

(* for 0 <= i <= n:
       A[i] = \sum_{0 <= j < i} B[j] * B[j]
 *)
(*the program above becomes the following rule.
  note that A(i, x) means that A[i] = x *)
Definition the_rule : rule rel var fn aggregator T :=
  {| rule_hyps := [];
    rule_concls := [
      {| fact_R := "A";
        fact_args := [
          var_expr "i";
          agg_expr
            sum
            "j" (*iteration variable*)
            ["x"] (*other variables that can appear in hyps*)
            (fun_expr range [lit_expr (nat_val 0); var_expr "i"]) (*set to iterate over*)
            (fun_expr times [var_expr "x"; var_expr "x"]) (*body of summation*)
            [{| fact_R := "B"; fact_args := [var_expr "j"; var_expr "x"] |}] (*hyps*)
        ] |}
    ] |}.
(*note: the rule above is bad because it has some variables that appear in the conclusion
  but not in the hypotheses.  this problem is beside the point here, so we ignore it
  for simplicity.*)

Definition set_b_i_to_x i x : rule rel var fn aggregator T :=
  {| rule_hyps := [];
    rule_concls := [{| fact_R := "B"; fact_args := [lit_expr (nat_val i); lit_expr (nat_val x)] |}] |}.

Lemma Forall2_map_Forall {A B : Type} (R : A -> B -> Prop) f l :
  Forall (fun x => R x (f x)) l ->
  Forall2 R l (map f l).
Proof. induction 1; constructor; auto. Qed.

Section withmap.
  Context {context : map.map var T} {context_ok : map.ok context}.
  Definition prog_impl_fact := prog_impl_fact (rel := rel) interp_fn get_set agg_id interp_agg context.

  Definition sum_of_squares l := fold_left Nat.add (map (fun x => x*x) l) O.

  (*says: if we start with a datalog program containing facts of the form B(i, nth i bs),
  then the program implies facts of the form A(i, \sum_{0 <= j < i} nth j bs * nth j bs).
   *)
  Lemma the_rule_works (bs : list nat) i :
    O <= i <= length bs ->
    prog_impl_fact (the_rule :: List.zip set_b_i_to_x (seq O (length bs)) bs)
      ("A", [nat_val i; nat_val (sum_of_squares (firstn i bs))]).
  Proof.
    intros H. eapply mk_pif.
    - apply Exists_cons_hd. exists (map.put map.empty "i" (nat_val i)). split.
      { cbv [the_rule]. simpl. apply Exists_cons_hd. constructor. simpl.
        constructor.
        { repeat econstructor. rewrite map.get_put_same. reflexivity. }
        constructor; [|solve[constructor]].
        econstructor.
        + repeat econstructor. 1: rewrite map.get_put_same. all: reflexivity.
        + reflexivity.
        + apply Forall2_map_Forall. apply Forall_map. apply Forall_forall.
          intros j Hj. apply in_seq in Hj. exists [nat_val (nth j bs O)].
          simpl. eexists. split; [|split].
          -- repeat econstructor.
             ++ rewrite <- map.put_putmany_commute.
                rewrite map.get_put_same. reflexivity.
             ++ Fail map_solver context_ok. (*what*) apply map.get_putmany_right.
                rewrite map.get_put_diff by congruence. rewrite map.get_put_same.
                reflexivity.
          -- constructor; [|solve[constructor]].
             simpl. apply mk_pif. apply Exists_cons_tl. cbv [List.zip].
             apply Exists_map. apply Exists_exists.
             exists (j, nth j bs O). split.
             { eassert ((_, _) = _) as ->. 2: apply nth_In with (n := j).
               - instantiate (1 := (O, O)). rewrite combine_nth.
                 + rewrite seq_nth by lia. reflexivity.
                 + rewrite length_seq. reflexivity.
               - rewrite length_combine, length_seq. lia. }
             simpl. exists map.empty. split.
             ++ repeat econstructor.
             ++ exists nil. repeat econstructor.
          -- econstructor.
             ++ repeat econstructor.
                --- apply map.get_putmany_right. rewrite map.get_put_diff by congruence.
                    apply map.get_put_same.
                --- apply map.get_putmany_right. rewrite map.get_put_diff by congruence.
                    apply map.get_put_same.
             ++ simpl. instantiate (1 := fun x =>
                                           match x with
                                           | nat_val j => _
                                           | _ => nat_val O
                                           end).
                simpl. reflexivity.
        + rewrite map_map. induction i.
          -- simpl. reflexivity.
          -- replace (S (S i) - 1) with (S i) by lia.
             rewrite <- List.firstn_nth with (d := O) by lia.
             replace (S i - 0) with (S i) by lia.
             rewrite seq_S. cbv [sum_of_squares]. do 2 rewrite map_app. simpl.
             do 2 rewrite fold_left_app. simpl. 
             simpl in IHi. replace (i - 0) with i in IHi by lia. rewrite <- IHi by lia.
             reflexivity. }
      simpl. exists nil. repeat econstructor.
  Qed.

End withmap.
