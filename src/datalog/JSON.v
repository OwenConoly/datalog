From JSON Require Import Encode.
From Datalog Require Import Datalog.

Instance JEncode__prod {A B} `{JEncode A} `{JEncode B} : JEncode (A * B) :=
  fun '(a, b) => JSON__Object [("fst", encode a);
                          ("snd", encode b)].

Instance JEncode__expr {var fn} `{JEncode var} `{JEncode fn} : JEncode (expr var fn) :=
  fix encode_expr e :=
    match e with
    | var_expr v => JSON__Object [("var_name", encode v)]
    | fun_expr f args => JSON__Object [("fun_name", encode f);
                                    ("args", JEncode__list (map encode_expr args))]
    end.

Instance JEncode__fact {rel var fn} `{JEncode rel} `{JEncode var} `{JEncode fn} : JEncode (fact rel var fn) :=
  fun f =>
    JSON__Object [("rel_name", encode f.(fact_R));
                ("args", encode f.(fact_args))].

Instance JEncode__agg_expr {rel var fn aggregator} `{JEncode rel} `{JEncode var} `{JEncode fn} `{JEncode aggregator} : JEncode (agg_expr rel var fn aggregator) :=
  fun aexpr =>
    JSON__Object [("agg", encode aexpr.(agg_agg));
                ("i", encode aexpr.(agg_i));
                ("vs", encode aexpr.(agg_vs));
                ("s", encode aexpr.(agg_s));
                ("body", encode aexpr.(agg_body));
                ("hyps", encode aexpr.(agg_hyps))].

Instance JEncode__rule {rel var fn aggregator} `{JEncode rel} `{JEncode var} `{JEncode fn} `{JEncode aggregator} : JEncode (rule rel var fn aggregator) :=
  fun r =>
    JSON__Object [("agg", encode r.(rule_agg));
                ("concls", encode r.(rule_concls));
                ("hyps", encode r.(rule_hyps));
                ("set_hyps", encode r.(rule_set_hyps))].
