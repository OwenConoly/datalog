From JSON Require Import Encode Printer.
From Datalog Require Import JSON FancyNotations.
Import Examples.

Redirect "json_examples/graph_prog" Eval compute in (to_string (encode graph_prog)).
Redirect "json_examples/stupid_nat_enumerator" Eval compute in (to_string (encode stupid_nat_enumerator)).
