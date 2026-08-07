From Stdlib Require Import QArith.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Stdlib Require Import ZArith.Zdiv.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.

From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics.
From Lower Require Import Zexpr Bexpr Sexpr Array Result ListMisc
  Meshgrid ContextsAgree ATLDeep Range.
From Datalog Require Import Datalog Dag Map List Tactics (*Interpreter QueryableToRunnable*) (*ATLUtils*) (*ZeroLowerBounds*) Blocks.
From Inferpad Require Import ATLPhoas.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Map.OfFunc Tactics.fwd Tactics.destr Tactics Decidable Datatypes.List.

Import Datatypes.
Import ListNotations.

From datalog Require Import ATLToDatalog.

Print pATLexpr'.