# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

A Coq/Rocq 9.0 formalization of Datalog: core semantics, a verified interpreter, a distributed (multi-node) execution model with liveness proofs, and a verified compiler from ATL (a tensor language, in the `verified-scheduling` submodule) to Datalog. There is no test suite — compilation is verification.

## Build

Submodules must be checked out first: `git submodule update --init --recursive`.

- `make datalog` — the main dev target: builds `src/util` and the core `src/datalog` files (plus the coqutil and ATL prerequisites on first run, which is slow).
- `make util` — just `src/util` and submodule prerequisites.
- `make` (= `make all` = `make atl`) — everything, including verified-scheduling examples/codegen and `src/atl`. Slow; rarely needed for datalog work.
- Single file (preferred iteration loop; handles dependency order):
  `make -f Makefile.coq src/datalog/Node.vo`
- `Makefile.coq` is generated from `_CoqProject` via `coq_makefile`; regenerate by deleting it and running `make`, or edit `_CoqProject` and `make` will rebuild it.

Individual files compile fast (a couple of seconds each) — iterate with foreground `coqc`/`make -f Makefile.coq` rather than background builds. Check for incomplete proofs with `grep -rn "Admitted" src/`.

`src/datalog/JSON.v` needs the optional coq-json library and is not in the `datalog` target.

To search the compiled libraries for lemmas, write a scratch file containing `Require Import` + `Search ...` commands and compile it:

```
coqc -Q coqutil/src/coqutil coqutil -Q src/util Datalog -Q src/datalog Datalog /tmp/search.v
```

To see proof state at a point in a batch `coqc` run, insert `Show.` into the proof script.

## Architecture

Namespaces (`_CoqProject`): `src/util`, `src/datalog`, and `src/atl` ALL map to the single logical name `Datalog` (so `From Datalog Require Import List` gets `src/util/List.v`, and filenames must be unique across the three dirs). `coqutil/src/coqutil` maps to `coqutil`; the verified-scheduling submodule provides `ATL`, `Codegen`, `Lower`, `Examples`, etc.

Everything is parameterized by typeclasses declared in `src/datalog/Datalog.v` (`signature`, `type_signature`, `query_signature`) plus coqutil `map.map` instances, and developed inside `Section`s with `Context` variables — files state hypotheses abstractly and instantiation happens at usage sites. This design is deliberate; don't restructure it.

Layers, bottom to top:

- `src/util/` — general-purpose libraries extending coqutil (`Map.v`, `List.v`, `Eqb.v`, `Dag.v`, `Permutation.v`, `Tactics.v`), small-step machinery (`Smallstep.v`, `OmniSmallstep.v`), and `Graph.v` — a *generic* network-of-nodes semantics (nodes = `nat` ids exchanging messages, with `input_allowed`/`forward`/`output_visible` policies) with its liveness metatheory. `Graph.v` knows nothing about Datalog.
- `src/datalog/Datalog.v` — Datalog syntax and declarative semantics: rules, facts `R(x1..xn)`, aggregators, meta-facts.
- `src/datalog/Interpreter.v` — executable evaluation of rules/programs (rule graphs, stratification-adjacent machinery).
- Distributed execution stack: `Node.v` (a single Datalog node: `dfact` = normal or meta fact, `node_state`, per-node small-step; meta-facts carry expected-message counts for distributed termination detection) → `Distributed.v` (instantiates `util/Graph.v` with Datalog nodes; per-relation routing via `R_senders`, `rel_forward`, etc.) → `Operational.v` (whole-program operational semantics with IO; the largest proof file) → `OperationalToDistributed.v` (connects the two).
- Compilation pipeline: `src/atl/ATLToDatalog.v` compiles ATL to *queryable* Datalog; `QueryableToRunnable.v` compiles queryable → *runnable* programs. Program classes SuperNice ⊂ Runnable ⊂ Queryable are described in `subsets_of_datalog.md`. `Blocks.v`, `AggregatingProgram.v`, and `Local.v` are further program representations/implementations; `SumExample.v` is a worked example.

The `coqutil/` and `verified-scheduling/` directories are git submodules — don't edit them.

## Conventions

- Never change a theorem statement, `Context` hypothesis, or obligation definition to unblock a proof — ask first.
- New generic facts about maps/lists/folds belong in `src/util/Map.v` / `src/util/List.v`, not inlined into the proof that needs them. Search (coqutil and `src/util`) for an existing lemma before proving one.
- State lemma variables as named binders before the colon (no `forall` in statements); drop inferable type annotations; destructure tuples with descriptive names.
- Leave at least one blank line before each `Definition`/`Lemma`/`Theorem`.
- Close arithmetic goals with `lia`; prefer the shortest tactic invocation that works.
- No dependently typed code (`eq_rect`, dependent `match` on equality proofs).
