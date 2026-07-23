# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

A Coq/Rocq 9.0 formalization of Datalog: core semantics, a verified interpreter, a distributed (multi-node) execution model with liveness proofs, and a verified compiler from ATL (a tensor language, in the `verified-scheduling` submodule) to Datalog. There is no test suite — compilation is verification.

## Build

Submodules must be checked out first: `git submodule update --init --recursive`.

- `make datalog` — the main dev target: builds `src/util` and the core `src/datalog` files (plus the coqutil prerequisite on first run). Does not build the verified-scheduling ATL library — only `make`/`make atl` do.
- `make util` — just `src/util` and its coqutil prerequisite.
- `make` (= `make all` = `make atl`) — everything, including verified-scheduling examples/codegen and `src/atl`. Slow; rarely needed for datalog work.
- Single file (preferred iteration loop; handles dependency order):
  `make -f Makefile.coq src/datalog/Node.vo`
- `Makefile.coq` is generated from `_CoqProject` via `coq_makefile`; regenerate by deleting it and running `make`, or edit `_CoqProject` and `make` will rebuild it.

Individual files compile fast (a couple of seconds each) — iterate with foreground `coqc`/`make -f Makefile.coq` rather than background builds. Check for incomplete proofs with `grep -rn "Admitted" src/`.

Build status (July 2026): `src/atl/*.v` (the ATL→Datalog compiler) and `src/datalog/QueryableToRunnable.v` predate the core-API refactor (record facts, `prog_impl_fact`, `clause_R`, `node_prog`) and do not compile against the current `Datalog.v`/`Node.v`, so the full `make` cannot complete; work from `make datalog`. That target now also builds `Distributed.v`, `OperationalToDistributed.v`, and `OperationalWithIO.v` (all compile). But `src/datalog/Local.v` (also in the target, and listed before them) currently fails to rebuild — its `compiler_correct` is Aborted and it has a standing type error — so `make datalog` stops there; build individual files with `make -f Makefile.coq src/datalog/<file>.vo`. Stale `.vo` files may exist for the broken files; do not trust them.

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
- `src/datalog/Datalog.v` — Datalog syntax and declarative semantics (`prog_impl`, a proof-tree closure over rule instances). Three rule forms: `normal_rule`, `meta_rule`, and `agg_rule concl agg hyp`, the last with fixed column layout `hyp(index, value, shared…) → concl(aggregate, shared…)`: an aggregation's input is always a materialized relation, and its semantics folds over a duplicate-free enumeration of *all* matching facts, witnessed by a `meta_fact` completeness premise. Aggregators are meant to be commutative monoids — the `signature` class does not state those laws yet, so a rewrite that reassociates/splits an aggregation must currently take them as hypotheses. There is no primitive guard construct; the intended guard idiom (used throughout ATLToDatalog) is a `true_rel(⟨boolean fn-expr⟩)` hypothesis backed by the axiom rule `true_rel(true) :- .`, so a rule instance exists only when the expression evaluates to `true`.
- `src/datalog/Interpreter.v` — executable evaluation of rules/programs (rule graphs, stratification-adjacent machinery).
- Distributed execution stack: `Node.v` — one Datalog node, parameterized by its rule list and `node_id`. `meta_dfact R pattern source count` is a done-message ("source has sent exactly count facts matching pattern"); an aggregation fires only after done-messages from every entry of `R_senders R` (`None` = external input) have arrived and exactly the promised number of matching facts is present. A node learns even its own outputs only via self-forwarding plus a receive step. `Distributed.v` — deploys a `node_id ↦ rules` map over `util/Graph.v`. Routing (`rel_forward`, `rel_input_allowed`, `rel_visible`) is per-relation — it cannot depend on fact arguments — so the relation is the unit of placement and communication; `sends_concl_rels` requires each node to be a declared sender of every relation its rules conclude; multiple senders per relation are supported (done-counts are summed across senders). Liveness (`distributed_might_implies_will`) is proved; `Graph.v`'s soundness refinement `graphs_corresp_sound'` is Admitted. Messages queue per node and may reorder but never drop; emission is atomic multicast per the forward table.
- `Operational.v` — synchronous whole-program reference semantics (one positional node per rule, broadcast everywhere); soundness (`comp_steps_sound`) and completeness (`comp_step_complete`) are both proved. `OperationalWithIO.v` re-presents `comp_step` as an IO-labelled small-step (`step`, with `I_event`/`O_event`) and states the `produces`-based soundness/completeness theorems (Admitted). `OperationalToDistributed.v` is the in-progress bridge to the per-node/distributed semantics (now compiles).
- Compilation pipeline (stale — see build status; the compiler is currently being rewritten, with a revamped correctness proof, to target the `blocks_prog` intermediate language of `Blocks.v` instead of a flat rule list): `src/atl/ATLToDatalog.v` compiles the deep ATL AST (`ATLDeep` from verified-scheduling) to a `list rule`, and ATL structure transports directly into relation structure: `Gen` emits no rules (loop indices become fact columns; bounds are deliberately ignored — iteration is driven by which input facts exist), `Sum` emits an intermediate relation + a reindex rule + an `agg_rule`, `Lbind x` materializes its tensor as relation `str_rel x`, `Concat` gives each branch its own fresh relation, and guards/boundary conditions become `true_rel` premises. `Composition.v` composes with `QueryableToRunnable.v`'s `make_good` demand transform (program classes in `subsets_of_datalog.md`). Compiler correctness (`lower_correct`) currently covers closed terms only; free input tensors go through the `def_depth` hook.
- `Blocks.v` is the staging/composition layer (PHOAS `LetIn`/`Block` trees over rule fragments) and holds the proven program-rewrite machinery: relation renaming (`map_rule_rels`, `prog_impl_map_rule_rels_iff`) and inlining to one flat program (`flatten`, `flatten_correct'`); `Datalog.v`'s `staged_program_iff` composes conclusion-disjoint programs. `AggregatingProgram.v` compiles a small PHOAS aggregation DSL onto blocks (proven). `Local.v` is the indexed single-node implementation (per-relation `idx_struct` key/value column masks, incrementally maintained aggregates); its `compiler_correct` is stated but Aborted.
- ATL side (`verified-scheduling/`): scheduling rewrites are equality lemmas on the *shallow* embedding (`atl/ATL.v`), applied with the `rw`/`wrapid`/`inline` Ltac DSL inside `Derive` (see `examples/Matmul.v`: matmul plus two derived tiled schedules); the compiler consumes the *deep* AST (`verified_lowering/proof/ATLDeep.v`).

The `coqutil/` and `verified-scheduling/` directories are git submodules — don't edit them.

## Conventions

- Never change a theorem statement, `Context` hypothesis, or obligation definition to unblock a proof — ask first.
- New generic facts about maps/lists/folds belong in `src/util/Map.v` / `src/util/List.v`, not inlined into the proof that needs them. Search (coqutil and `src/util`) for an existing lemma before proving one.
- State lemma variables as named binders before the colon (no `forall` in statements); drop inferable type annotations; destructure tuples with descriptive names.
- Leave at least one blank line before each `Definition`/`Lemma`/`Theorem`.
- Close arithmetic goals with `lia`; prefer the shortest tactic invocation that works.
- No dependently typed code (`eq_rect`, dependent `match` on equality proofs).
- Don't write comments about obvious things: no restating what a definition/lemma already says, no narrating Coq/section/`Arguments` mechanics, no justifying routine constructs. Comment only a genuinely non-obvious *why*, and keep it short. Default to no comment.
