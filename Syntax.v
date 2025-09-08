From Coq Require Import Lists.List.

Section __.
Context (rel: Type) (var: Type) (fn: Type).
(*constants are 0-ary functions*)

Inductive expr :=
| fun_expr (f : fn) (args : list expr)
| var_expr (v : var).

Record fact :=
  { fact_R : rel; fact_args : list expr }.

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

Inductive prog_impl_fact (p : list rule) : fact -> Prop :=
| impl_step f : Exists
                  (fun r => exists s,
                       let r' := subst_in_rule s r in
                       r'.(rule_concl) = f /\
                         exists s', Forall (prog_impl_fact p) (map (subst_in_fact s') r'.(rule_hyps)))
                  p ->
                prog_impl_fact p f.
End __.
