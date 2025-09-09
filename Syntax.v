From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Coq Require Import ZArith.Zdiv.
From Coq Require Import ZArith.Int.
From Coq Require Import ZArith.Znat.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.

Set Warnings "-deprecate-hint-without-locality,-deprecated".
Import ListNotations.

From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics.
From Lower Require Import Zexpr Bexpr Array Range Sexpr Result ListMisc
  Meshgrid VarGeneration Injective Constant InterpretReindexer
  WellFormedEnvironment.

Require Import ATLDeep.
Open Scope string_scope.

(*TODO is in coqutil, duplicated here*)
Definition option_map2 {X Y Z : Type} (f : X -> Y -> Z) x y :=
  match x, y with
  | Some x, Some y => Some (f x y)
  | _, _ => None
  end.

Definition option_unwrap {X : Type} (x : option (option X)) :=
  match x with
  | None => None
  | Some x => x
  end.

Definition option_all {X : Type} (l : list (option X)) :=
  fold_right (option_map2 cons) (Some nil) l.

Section __.
  Context (rel: Type) (var: Type) (fn: Type).
  (*constants are 0-ary functions*)
  Context (T : Type).
  (*None could mean number of args was wrong*)
  Context (interp_fun : fn -> (list T) -> option T).

  Inductive expr :=
  | fun_expr (f : fn) (args : list expr)
  | var_expr (v : var).

  Fixpoint interp_expr (e : expr) : option T :=
    match e with
    | fun_expr f args => option_unwrap (option_map (interp_fun f)
                                         (option_all (map interp_expr args)))
    | var_expr v => None
    end.
  
  Record fact :=
    { fact_R : rel; fact_args : list expr }.

  Definition interp_fact (f : fact) : option (rel * list T) :=
    option_map (fun x => (f.(fact_R), x)) (option_all (map interp_expr f.(fact_args))).

  Record rule :=
    { rule_hyps: list fact; rule_concl: fact }.

  Fixpoint subst_in_expr (s : var -> option expr) (e : expr) :=
    match e with
    | fun_expr f args => fun_expr f (map (subst_in_expr s) args)
    | var_expr v => match s v with
                   | Some e => e
                   | None => var_expr v
                   end
    end.

  Definition subst_in_fact (s : var -> option expr) (f : fact) : fact :=
    Build_fact f.(fact_R) (map (subst_in_expr s) f.(fact_args)).

  Definition subst_in_rule (s : var -> option expr) (r : rule) : rule :=
    Build_rule (map (subst_in_fact s) r.(rule_hyps)) (subst_in_fact s r.(rule_concl)).

  Fixpoint appears_in_expr (v : var) (e : expr) :=
    match e with
    | fun_expr _ args => fold_left (fun acc arg => acc \/ appears_in_expr v arg) args False
    | var_expr v0 => v0 = v
    end.

  Definition appears_in_fact (v : var) (f : fact) :=
    Exists (appears_in_expr v) f.(fact_args).

  Definition good_rule (r : rule) :=
    forall v, appears_in_fact v r.(rule_concl) ->
         Exists (appears_in_fact v) r.(rule_hyps).

  Definition good_prog (p : list rule) := Forall good_rule p.

  (*This version gives useless auto-generated induction principle*)

  (* Inductive prog_impl_fact (p : list rule) : rel * list T -> Prop := *)
  (* | impl_step f : Exists *)
  (*                   (fun r => exists s, *)
  (*                        let r' := subst_in_rule s r in *)
  (*                        interp_fact r'.(rule_concl) = Some f /\ *)
  (*                          exists s' hyps, *)
  (*                            option_all (map (fun x => interp_fact (subst_in_fact s' x)) r'.(rule_hyps)) = Some hyps /\ *)
  (*                              Forall (prog_impl_fact p) hyps) *)
  (*                   p -> *)
  (*                 prog_impl_fact p f. *)

  Inductive prog_impl_fact (p : list rule) : rel * list T -> Prop :=
  | impl_step f hyps s s' :
    Exists
      (fun r => let r' := subst_in_rule s r in
             interp_fact r'.(rule_concl) = Some f /\
               option_all (map (fun x => interp_fact (subst_in_fact s' x)) r'.(rule_hyps)) = Some hyps)
      p ->
    (forall hyp, In hyp hyps -> prog_impl_fact p hyp) ->
    prog_impl_fact p f.

  Lemma prog_impl_fact_subset (p1 p2 : list rule) f :
    (forall x, In x p1 -> In x p2) ->
    prog_impl_fact p1 f ->
    prog_impl_fact p2 f.
  Proof.
    intros ? H. induction H. apply Exists_exists in H.
    econstructor. 2: eassumption. apply Exists_exists. destruct H as (?&?&?). eauto.
  Qed.
End __.
Arguments Build_rule {_ _ _}.
Arguments Build_fact {_ _ _}.
Arguments fun_expr {_ _}.
Arguments var_expr {_ _}.
Arguments prog_impl_fact {_ _ _ _}.
Arguments fact_args {_ _ _}.
Search (?x + ?y -> option ?x)%type.
Definition get_inl {X Y : Type} (xy : X + Y) : option X :=
  match xy with
  | inl x => Some x
  | inr _ => None
  end.
Definition get_inr {X Y : Type} (xy : X + Y) : option Y :=
  match xy with
  | inl _ => None
  | inr y => Some y
  end.
(*p is target*)
(*f is reindexer*)
(*asn is StoreType += or =*)
(*sh is shape of something?*)
Search Zexpr.
Print eval_Zexpr.
(*just like Zexpr but no ZVar*)
Variant Zfn : Set :=
  fn_ZPlus | fn_ZMinus | fn_ZTimes | fn_ZDivf | fn_ZDivc | fn_ZMod | fn_ZLit (x : Z).
Definition interp_Zfn (f : Zfn) (l : list Z) : option Z :=
  match f, l with
  | fn_ZPlus, [x; y] => Some (x + y)
  | fn_ZMinus, [x; y] => Some (x - y)
  | fn_ZTimes, [x; y] => Some (x * y)
  | fn_ZDivf, [x; y] => Some (x / y)
  | fn_ZDivc, [x; y] => Some (x // y)
  | fn_ZMod, [x; y] => Some (x mod y)
  | fn_ZLit x, [] => Some x
  | _, _ => None
  end%Z.
(*just like Sstmt but no SVar, SGet*)
Variant Rfn : Set :=
  fn_SMul | fn_SAdd | fn_SDiv | fn_SSub | fn_SLit (x : R).

Definition interp_Rfn (f : Rfn) (l : list R) : option R :=
  match f, l with
  | fn_SMul, [x; y] => Some (x * y)
  | fn_SAdd, [x; y] => Some (x + y)
  | fn_SDiv, [x; y] => Some (x / y)
  | fn_SSub, [x; y] => Some (x - y)
  | fn_SLit x, [] => Some (x)
  | _, _ => None
  end%R.

Variant tfn : Set :=
  fn_Z (_ : Zfn) | fn_R (_ : Rfn).

Definition interp_fn (f : tfn) (l : list (Z+R)) : option (Z + R) :=
  match f with
  | fn_Z f => option_map inl (option_unwrap (option_map (interp_Zfn f) (option_all (map get_inl l))))
  | fn_R f => option_map inr (option_unwrap (option_map (interp_Rfn f) (option_all (map get_inr l))))
  end.

Definition rel : Set := string.
(*inl s is string representing indexing variable (e.g. i, j), which came directly from source program
  inr n is nat (that i generated) representing value in some intermediate thing
 *)
Definition var : Set := string + nat.
Definition trule := rule rel var tfn.

Search Sstmt. Print eval_Sstmt. Print context. Print fmap. Check Build_rule. Check Build_fact.

Fixpoint lower_idx (idx: Zexpr) : expr var tfn :=
  match idx with
  (*copy-pasted monstrosity*)
  | ZPlus x y => fun_expr (fn_Z fn_ZPlus) [lower_idx x; lower_idx y]
  | ZMinus x y => fun_expr (fn_Z fn_ZMinus) [lower_idx x; lower_idx y]
  | ZTimes x y => fun_expr (fn_Z fn_ZTimes) [lower_idx x; lower_idx y]
  | ZDivf x y => fun_expr (fn_Z fn_ZDivf) [lower_idx x; lower_idx y]
  | ZDivc x y => fun_expr (fn_Z fn_ZMod) [lower_idx x; lower_idx y]
  | ZMod x y => fun_expr (fn_Z fn_ZMod) [lower_idx x; lower_idx y]
  | ZLit x => fun_expr (fn_Z (fn_ZLit x)) []
  | ZVar x => var_expr (inl x)
  end.

Print Sexpr.
Fixpoint lower_Sexpr (next_varname : nat) (e : Sexpr) :
  expr var tfn (*value of expr*) *
    list (fact rel var tfn) (*hypotheses*) *
    nat (*next varname *) :=
  match e with
  | Var x => (var_expr (inr next_varname),
              [{| fact_R := x; fact_args := [var_expr (inr next_varname)] |}],
              succ next_varname)
  | Get x idxs => (var_expr (inr next_varname),
                   [{| fact_R := x; fact_args := var_expr (inr next_varname) :: map lower_idx idxs |}],
                   succ next_varname)
  (*copy-pasted monstrosity*)
  | Mul x y => let '(e1, hyps1, next_varname) := lower_Sexpr next_varname x in
              let '(e2, hyps2, next_varname) := lower_Sexpr next_varname y in
              (fun_expr (fn_R fn_SMul) [e1; e2],
                (hyps1 ++ hyps2)%list,
                next_varname)
  | Div x y => let '(e1, hyps1, next_varname) := lower_Sexpr next_varname x in
              let '(e2, hyps2, next_varname) := lower_Sexpr next_varname y in
              (fun_expr (fn_R fn_SDiv) [e1; e2],
                (hyps1 ++ hyps2)%list,
                next_varname)
  | Add x y => let '(e1, hyps1, next_varname) := lower_Sexpr next_varname x in
              let '(e2, hyps2, next_varname) := lower_Sexpr next_varname y in
              (fun_expr (fn_R fn_SAdd) [e1; e2],
                (hyps1 ++ hyps2)%list,
                next_varname)
  | Sub x y => let '(e1, hyps1, next_varname) := lower_Sexpr next_varname x in
              let '(e2, hyps2, next_varname) := lower_Sexpr next_varname y in
              (fun_expr (fn_R fn_SSub) [e1; e2],
                (hyps1 ++ hyps2)%list,
                next_varname)
  | Lit x => (fun_expr (fn_R (fn_SLit x)) [], [], next_varname)
  end.

Definition map_empty : var -> option (expr var tfn) := fun _ => None.
Search ((_ + _) -> (_ + _) -> bool).
Definition var_eqb (x y : var) : bool :=
  match x, y with
  | inl x, inl y => x =? y
  | inr x, inr y => Nat.eqb x y
  | _, _ => false
  end.
Definition map_cons (x : var) (y : option (expr var tfn)) (m : var -> option (expr var tfn)) :=
  fun v => if var_eqb x v then y else m v.
Search (scalar_result -> R).
Definition toR (s : scalar_result) :=
  match s with
  | SS s => s
  | SX => 0%R
  end.
  
Print rule. Print fact.
Fixpoint lower
  (e : ATLexpr)
  (out: rel)
  (*this list is backwards compared to the other lowering alg*)
  (*also, i don't use the bounds at all (yet)*)
  (idxs_bds : list (Zexpr * Zexpr))
  : list trule :=
  match e with
  | Gen i lo hi body =>
      lower body out ((ZMinus (ZVar i) lo, ZMinus hi lo) :: idxs_bds)
  | Scalar s =>
      let '(val, hyps, _) := lower_Sexpr O s in
      [{| rule_hyps := hyps; rule_concl := {| fact_R := out; fact_args := val :: (map lower_idx (map fst idxs_bds)) |} |}]
  | _ => nil end.
Print eval_expr. Print context. Print valuation.
Print prog_impl_fact.
Check eval_expr. Print result. Search result. Print result_lookup_Z_option.
Print lower_Sexpr. Print eval_Sexpr. Print expr_context. Print fmap. Locate "$?".

Lemma lower_Sexpr_correct sh v ec s val out datalog_ctx :
  (forall x r, ec $? x = Some (S r) ->
          sh $? x = Some [] ->
          prog_impl_fact interp_fn datalog_ctx (x, [inr (toR r)])) ->
        

  (* (forall x, ec $? x = Some (V rs) -> *)
        
  eval_Sexpr sh v ec s (SS val) ->
  prog_impl_fact interp_fn (lower (Scalar s) out [] ++ datalog_ctx) (out, [inr val]).
Proof.
  induction s.
  - simpl. intros. inversion H0. subst. econstructor.
    { constructor. simpl. cbv [subst_in_fact]. simpl.
      instantiate (2 := map_cons (inr O) (Some (fun_expr (fn_R (fn_SLit (toR r))) [])) map_empty). simpl.
      split; [|reflexivity]. cbv [interp_fact]. simpl. destruct r; inversion H2; reflexivity. }
    simpl. intros. destruct H1 as [H1|H1]; [|contradiction]. subst.
    eapply prog_impl_fact_subset. 2: eauto. intros. simpl. auto.
  - 
Qed.

Lemma lower_correct e out sh v ctx r :
  eval_expr sh v ctx e r ->
  forall idxs val,
    result_lookup_Z_option idxs r = Some val ->
    prog_impl_fact interp_fn (lower e out nil) (out, inr val :: (map inl idxs)).
Proof.
  intros H. induction H.
  { intros * H'. destruct idxs; simpl in H'; try solve [inversion H'].
    destruct z; simpl in H'; try rewrite nth_error_empty in H'; solve [inversion H']. }
  { intros * H'. admit. (*should be doable*) }
  15: { intros. destruct idxs; simpl in H0. 2: destruct z; simpl in H0; inversion H0.
        destruct r; inversion H0; subst. cbn -[lower]. simpl.  in H. simp

  - intros.
    
  | Sum i lo hi body =>
      For i lo hi
        (lower body f p Reduce sh)
  | Guard b body =>
      If b (lower body f p asn sh)
  | Lbind x e1 e2 =>
      match sizeof e1 with
      | [] =>
          Seq (AllocS x)
            (Seq (lower e1 (fun l => l) x Assign sh)
               (Seq (lower e2 f p asn (sh $+ (x,sizeof e1)))
                  (DeallocS x)))
      | _ =>
          Seq (AllocV x (flat_sizeof e1))
            (Seq (lower e1 (fun l => l) x Assign sh)
               (Seq (lower e2 f p asn (sh $+ (x,sizeof e1)))
                  (Free x)))
      end
  | Concat x y =>
      let xlen := match sizeof x with
                  | n::_ => n
                  | _ => ZLit 0
                  end in 
      let ylen := match sizeof y with
                  | n::_ => n
                  | _ => ZLit 0
                  end in   
      Seq (lower x (fun l =>
                      f (match l with
                         | (v,d)::xs =>
                             ((v,ZPlus d ylen)::xs)
                         | _ => l
                         end)) p asn sh)
        (lower y (fun l => f (match l with
                           | (v,d)::xs => ((ZPlus v xlen,ZPlus d xlen)::xs)
                           | _ => l
                           end)) p asn sh)
  | Transpose e =>
      lower e (fun l => f (match l with
                        | (v,d)::(vi,di)::xs => (vi,di)::(v,d)::xs
                        | _ => l
                        end)) p asn sh
  | Split k e =>
      lower e (fun l => f (match l with
                        | (v,d)::xs => (ZDivf v k,ZDivc d k)::(ZMod v k,k)::xs
                        | _ => l
                        end)) p asn sh
  | Flatten e =>
      lower e (fun l => f (match l with
                        | (v,d)::(vi,di)::xs =>
                            (ZPlus (ZTimes v di) vi,ZTimes d di)::xs
                        | _ => l
                        end)) p asn sh          
        p  | Truncr n e =>
               lower e (fun l => f (match l with
                                 | (v,d)::xs =>
                                     (v,ZMinus d n)::xs
                                 | _ => l
                                 end)) p asn sh
  | Truncl n e =>
      lower e (fun l => f (match l with
                        | (v,d)::xs =>
                            (ZMinus v n,
                              ZMinus d n)::xs
                        | _ => l
                        end)) p asn sh
  | Padr n e =>
      lower e (fun l => f (match l with
                        | (v,d)::xs =>
                            (v,ZPlus d n)::xs
                        | _ => l
                        end)) p asn sh
  | Padl n e =>
      lower e (fun l => f (match l with
                        | (v,d)::xs =>
                            (ZPlus v n,ZPlus d n)::xs
                        | _ => l
                        end)) p asn sh
  end.
