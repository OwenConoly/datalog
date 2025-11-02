From Datalog Require Import Datalog.
From Stdlib Require Import String List.
From coqutil Require Import Macros.ident_to_string.
Import ListNotations.
Open Scope string_scope.

(*heavily copied from bedrock2; i have no idea how to use these fancy things*)
Declare Custom Entry datalog_id.
Notation "x" := (ident_to_string! x) (in custom datalog_id, x ident, only parsing).
Notation "# e #" := e (in custom datalog_id at level 0, e constr, format "'#' e '#'").
(* Notation "coq:( e )"          := e (in custom datalog_id, e constr, format "'coq:(' e ')'"). *)
(*I wish i could get away with just having the pound sign before and not after.  i thought putting it at highest precedence would do that but i guess not*)

Declare Custom Entry datalog_id_list.
Notation "[ ]" := nil (in custom datalog_id_list, format "[ ]").
Notation "[ x ]" := (cons x nil) (in custom datalog_id_list, x custom datalog_id).
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) (in custom datalog_id_list, x custom datalog_id, y custom datalog_id, z custom datalog_id).


Declare Custom Entry datalog_expr.
Notation "datalog_expr:( e )" := e (e custom datalog_expr, format "'datalog_expr:(' e ')'").
Notation "coq:( e )"          := e (in custom datalog_expr, e constr, format "'coq:(' e ')'").
Notation "$ x" := (var_expr x) (in custom datalog_expr at level 1, x custom datalog_id, format "'$' x").
Check datalog_expr:( $x ).
Notation "f ( )" := (fun_expr f nil) (in custom datalog_expr at level 1, f custom datalog_id).
Notation "f ( x )" := (fun_expr f (cons x nil)) (in custom datalog_expr at level 1, f custom datalog_id).
Notation "f ( x , y , .. , z )" := (fun_expr f (cons x (cons y .. (cons z nil) ..))) (in custom datalog_expr at level 1, f custom datalog_id).
Check datalog_expr:( f($x, $y, $z) ).
Check datalog_expr:( f( ) ).
Check datalog_expr:( f( $x ) ).
Check datalog_expr:( $#"x"# ).
Check datalog_expr:( #"f"# ( $x ) ).

(* why no pretty printing :( *)

Print fact.
Declare Custom Entry datalog_fact.
Notation "datalog_fact:( e )" := e (e custom datalog_expr, format "'datalog_fact:(' e ')'").
Notation "coq:( e )"          := e (in custom datalog_fact, e constr, format "'coq:(' e ')'").
Notation "R ( )" := ({| fact_R := R; fact_args := nil |}) (in custom datalog_fact, R custom datalog_id).
Notation "R ( x )" := ({| fact_R := R; fact_args := (cons x nil) |}) (in custom datalog_fact, x custom datalog_expr, R custom datalog_id).
Notation "R ( x , y , .. , z )" := ({| fact_R := R; fact_args := (cons x (cons y .. (cons z nil) ..)) |}) (in custom datalog_fact, x custom datalog_expr, y custom datalog_expr, z custom datalog_expr, R custom datalog_id).
Check datalog_fact:( R( $x ) ).
Check datalog_fact:( R( ) ).
Check datalog_fact:( R( f($x, g($x, $z)))).

Declare Custom Entry datalog_fact_list.
Notation "[ ]" := nil (in custom datalog_fact_list, format "[ ]").
Notation "[ x ]" := (cons x nil) (in custom datalog_fact_list, x custom datalog_fact).
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) (in custom datalog_fact_list, x custom datalog_fact, y custom datalog_fact, z custom datalog_fact).

Declare Custom Entry datalog_agg_expr.

Notation "datalog_agg_expr:( e )" := e (e custom datalog_agg_expr, format "'datalog_agg_expr:(' e ')'").
Notation "agg 'for' i '\in' S ( 'with' vs ) 'of' body : hyps" := ({| agg_agg := agg; agg_i := i; agg_vs := vs; agg_s := S; agg_body := body; agg_hyps := hyps|}) (in custom datalog_agg_expr at level 0, agg custom datalog_id, i custom datalog_id, vs custom datalog_id_list, S custom datalog_expr, body custom datalog_expr, hyps custom datalog_fact_list, format "agg  'for'  i  '\in'  S ( 'with'  vs )  'of'  body  :  hyps").
(*why is 'of' a keyword?*)
Check datalog_agg_expr:( sum for i \in $S (with [x]) of $x : [ R($x, $i) ] ).

Declare Custom Entry datalog_pair_expr.
Notation "x1 '\in' x2" := (x1, x2) (in custom datalog_pair_expr at level 0, x1 custom datalog_expr, x2 custom datalog_expr).

Declare Custom Entry datalog_pair_expr_list.
Notation "[ ]" := nil (in custom datalog_pair_expr_list, format "[ ]").
Notation "[ x ]" := (cons x nil) (in custom datalog_pair_expr_list, x custom datalog_pair_expr).
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) (in custom datalog_pair_expr_list, x custom datalog_pair_expr, y custom datalog_pair_expr, z custom datalog_pair_expr).

Declare Custom Entry datalog_rule.
Notation "datalog_rule:( e )" := e (e custom datalog_rule, format "'datalog_rule:(' e ')'").
Notation "concls ':-' hyps" := ({| rule_concls := concls; rule_hyps := hyps; rule_agg := None; rule_set_hyps := [] |}) (in custom datalog_rule at level 0, concls custom datalog_fact_list, hyps custom datalog_fact_list).
Notation "concls ':-' hyps 'and' set_hyps" := ({| rule_concls := concls; rule_hyps := hyps; rule_agg := None; rule_set_hyps := set_hyps |}) (in custom datalog_rule at level 0, concls custom datalog_fact_list, hyps custom datalog_fact_list, set_hyps custom datalog_pair_expr_list).
Notation "'let' x ':=' val 'in' concls ':-' hyps" := ({| rule_concls := concls; rule_hyps := hyps; rule_agg := Some (x, val); rule_set_hyps := [] |}) (in custom datalog_rule at level 0, x custom datalog_id, val custom datalog_agg_expr, concls custom datalog_fact_list, hyps custom datalog_fact_list).
Notation "'let' x ':=' val 'in' concls ':-' hyps 'and' set_hyps" := ({| rule_concls := concls; rule_hyps := hyps; rule_agg := Some (x, val); rule_set_hyps := set_hyps |}) (in custom datalog_rule at level 0, x custom datalog_id, val custom datalog_agg_expr, concls custom datalog_fact_list, hyps custom datalog_fact_list, set_hyps custom datalog_pair_expr_list).
Check datalog_rule:( [path($x, $y)] :- [edge($x, $y)] ).
Check datalog_rule:( let y := sum for i \in $S (with [x]) of $x : [ R($x, $i) ] in [R($x, $y)] :- [Q($x)]).

Declare Custom Entry datalog_prog.
Notation "datalog_prog:( e )" := e (e custom datalog_prog, format "'datalog_prog:(' e ')'").
Notation "[ ]" := nil (in custom datalog_prog, format "[ ]").
Notation "[ x ]" := (cons x nil) (in custom datalog_prog, x custom datalog_rule).
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) (in custom datalog_prog, x custom datalog_rule, y custom datalog_rule, z custom datalog_rule).
Check datalog_prog:( [ [path($x, $y)] :- [edge($x, $y)] ] ).


Module examples.
  Definition graph_prog : list (rule string string string string) :=
    datalog_prog:(
                    [ [path($x, $y)] :- [edge($x, $y)];
                      [path($x, $y)] :- [path($x, $z); edge($z, $y)]
                    ]
                  ).
  Definition stupid_nat_enumerator : list (rule string string string string) :=
    datalog_prog:(
                    [ [nat''( S($x) )] :- [nat''($x)];
                      [nat''(O( ) )] :- [] and [];
                      [nat'(nat_range(O ( ), $s))] :- [nat''($s)];
                      [nat($x)] :- [nat'($s)] and [$x \in $s]
                    ]
                  ).
End examples.
