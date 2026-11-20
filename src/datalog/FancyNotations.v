From Datalog Require Import Datalog.
From Stdlib Require Import String List.
From coqutil Require Import Macros.ident_to_string.
Import ListNotations.

(*heavily copied from bedrock2*)

Declare Custom Entry datalog_id.
Notation "x" := (ident_to_string! x) (in custom datalog_id at level 0, x ident, only parsing).
Notation "{ e }" := e (in custom datalog_id at level 0, e constr, format "{ e }").

Declare Custom Entry datalog_expr.
Notation "datalog_expr:( e )" := e (e custom datalog_expr, format "'datalog_expr:(' e ')'").
Notation "e" := e (in custom datalog_expr at level 1, e custom datalog_id).
Notation "$ x" := (expr.var x) (in custom datalog_expr at level 1, x custom datalog_id, format "'$' x").
(*declared after $ so that it wins in printing*)
Notation "# n" := (@expr.var nat _ n) (in custom datalog_expr at level 1, n bigint, format "'#' n").
Notation "f ()" := (expr.app f nil) (in custom datalog_expr at level 1, f custom datalog_id, format "f ()").
Notation "f ( x , .. , y )" := (expr.app f (cons x .. (cons y nil) ..))
  (in custom datalog_expr at level 1, f custom datalog_id, x custom datalog_expr, y custom datalog_expr,
   format "f ( x ,  .. ,  y )").

Declare Custom Entry datalog_clause.
Notation "datalog_clause:( c )" := c (c custom datalog_clause, format "'datalog_clause:(' c ')'").
Notation "c" := c (in custom datalog_clause at level 1, c custom datalog_id).
Notation "R ()" := {| clause.rel := R; clause.args := nil |}
  (in custom datalog_clause at level 1, R custom datalog_id, format "R ()").
Notation "R ( x , .. , y )" := {| clause.rel := R; clause.args := cons x .. (cons y nil) .. |}
  (in custom datalog_clause at level 1, R custom datalog_id, x custom datalog_expr, y custom datalog_expr,
   format "R ( x ,  .. ,  y )").

Declare Custom Entry datalog_clause_list.
Notation "[ ]" := nil (in custom datalog_clause_list, format "[ ]").
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..)
  (in custom datalog_clause_list, x custom datalog_clause, y custom datalog_clause).

Declare Custom Entry datalog_expr_pattern.
Notation "'_'" := expr_pattern.any (in custom datalog_expr_pattern at level 0).
Notation "e" := (expr_pattern.exactly e) (in custom datalog_expr_pattern at level 0, e custom datalog_expr at level 1).

Declare Custom Entry datalog_clause_pattern.
Notation "c" := c (in custom datalog_clause_pattern at level 1, c custom datalog_id).
Notation "R ()" := {| clause_pattern.rel := R; clause_pattern.args := nil |}
  (in custom datalog_clause_pattern at level 1, R custom datalog_id, format "R ()").
Notation "R ( x , .. , y )" := {| clause_pattern.rel := R; clause_pattern.args := cons x .. (cons y nil) .. |}
  (in custom datalog_clause_pattern at level 1, R custom datalog_id,
   x custom datalog_expr_pattern, y custom datalog_expr_pattern,
   format "R ( x ,  .. ,  y )").

Declare Custom Entry datalog_clause_pattern_list.
Notation "[ ]" := nil (in custom datalog_clause_pattern_list, format "[ ]").
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..)
  (in custom datalog_clause_pattern_list, x custom datalog_clause_pattern, y custom datalog_clause_pattern).

Declare Custom Entry datalog_rule.
Notation "datalog_rule:( r )" := r (r custom datalog_rule, format "'datalog_rule:(' r ')'").
Notation "concl := agg hyp" := (rule.agg concl agg hyp)
  (in custom datalog_rule at level 1, concl custom datalog_id, agg custom datalog_id, hyp custom datalog_id).
Notation "concls :- hyps" := (rule.impl concls hyps)
  (in custom datalog_rule at level 1, concls custom datalog_clause_list, hyps custom datalog_clause_list).

Declare Custom Entry datalog_rule_list.
Notation "[ ]" := nil (in custom datalog_rule_list, format "[ ]").
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..)
  (in custom datalog_rule_list, x custom datalog_rule, y custom datalog_rule).

Declare Custom Entry datalog_meta_rule.
Notation "datalog_meta_rule:( r )" := r (r custom datalog_meta_rule, format "'datalog_meta_rule:(' r ')'").
Notation "concls :- hyps" := {| meta_rule.concls := concls; meta_rule.hyps := hyps |}
  (in custom datalog_meta_rule at level 1,
   concls custom datalog_clause_pattern_list, hyps custom datalog_clause_pattern_list).

Declare Custom Entry datalog_meta_rule_list.
Notation "[ ]" := nil (in custom datalog_meta_rule_list, format "[ ]").
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..)
  (in custom datalog_meta_rule_list, x custom datalog_meta_rule, y custom datalog_meta_rule).

Notation "datalog_prog:( rs )" := {| program.rules := rs; program.meta_rules := nil |}
  (rs custom datalog_rule_list, format "'datalog_prog:(' rs ')'").
Notation "datalog_prog:( rs 'with' ms )" := {| program.rules := rs; program.meta_rules := ms |}
  (rs custom datalog_rule_list, ms custom datalog_meta_rule_list, format "'datalog_prog:(' rs  'with'  ms ')'").

Module Examples.
  #[local] Instance rel : relT := string.
  #[local] Instance var : exprvarT := string.
  #[local] Instance fn : fnT := string.
  #[local] Instance aggregator : aggregatorT := string.
  #[local] Open Scope string_scope.

  Check datalog_expr:( $x ).
  Check datalog_expr:( #0 ).
  Check datalog_expr:( f($x, $y, $z) ).
  Check datalog_expr:( f() ).
  Check datalog_expr:( f($x) ).
  Check datalog_expr:( ${"x"} ).
  Check datalog_expr:( {expr.var "x"} ).
  Check datalog_expr:( {"f"}($x) ).
  Check datalog_clause:( R($x) ).
  Check datalog_clause:( R() ).
  Check datalog_clause:( R(f($x, g($x, $z))) ).
  Check datalog_rule:( [path($x, $y)] :- [edge($x, $y)] ).
  Check datalog_rule:( path := sum edge ).
  Check datalog_meta_rule:( [path(_)] :- [edge(_, _)] ).
  Check datalog_prog:( [ [path($x, $y)] :- [edge($x, $y)] ] ).
  Check datalog_prog:( [ path := sum edge ] with [ [path(_)] :- [edge(_, _)] ] ).

  Definition graph_prog : program :=
    datalog_prog:(
                    [ [path($x, $y)] :- [edge($x, $y)];
                      [path($x, $y)] :- [path($x, $z); edge($z, $y)]
                    ]
                  ).
  Definition stupid_nat_enumerator : program :=
    datalog_prog:(
                    [ [nat''( S($x) )] :- [nat''($x)];
                      [nat''(O() )] :- [];
                      [nat'(nat_range(O(), $s))] :- [nat''($s)]
                    ]
                  ).
End Examples.
