# Plan: prove `graph_can_implies_will_equiv` (Graph.v)

## Target
```coq
nodes_input_total -> Forall2_map node_good p initial_ns ->
can_implies_will_equiv gstep equiv_g well_formed_inputs initial_graph_state
```
Unfolds to: `forall t gs o, star gstep init t gs -> allowed well_formed_inputs (inputs_of t) ->
might_output gstep gs t o -> will_output_equiv gstep equiv_g gs t o`.

Same skeleton as the deleted `graph_can_implies_will`, but: conclusion is modulo
`equiv_g`; node obligations come from `node_good`; `A_total` is replaced by a real
allowedness lemma.

## Reused as-is (A-independent graph mechanics; also used by cross-graph `Section graphs`)
`find_producing_step(')`, `node_drive_delta`, `project_node_gen`, `node_run`,
`node_received(_mono)`, `queue_fate`, `saturated`/`sat_step`/`saturated_star`/
`graph_saturated`, `core_dom`/`dom_of_step`/`core_dom_{refl,trans,run}`,
`dom_preserved`, `reachable_state_initial`, `eventually_carry_inv(2)`,
`In_tag(_inv)`, **`force_deliver`** (delivery only — no liveness).

Lemmas carrying `A_total`/`nodes_ciw'` that need modulo `_equiv` variants:
`force_emit_list`, `drive_node_emit`, `node_will`, `node_cap_transfer`,
`force_dominator`, `pernode_spec`.

## Phase 0 — discharge helpers (new)
1. **`pernode_spec_good`** — from `Forall2_map node_good p initial_ns`, project the
   four per-node facts (`outputs_well_formed (well_formed n)`, `monotone_multiset`,
   `monotone_mod_equiv`, `can_implies_will_equiv`, all on `well_formed_g`) at a
   node's bare initial state. Mirrors `pernode_spec`.
2. **`node_inputs_allowed`** — *the `A_total` replacement.* At any reachable `gs`,
   node `n` with stored trace `tn`: `allowed well_formed_g (inputs_of tn)`.
   Witness pool `W = concat (per-node output bundles) ++ map fst (external inputs)`;
   `submultiset (inputs_of tn) W` from `graph_saturated`; `well_formed_g W` from
   `outputs_well_formed` (each producer's bundle is `well_formed n`) + the graph's
   `allowed well_formed_inputs` hypothesis. Biggest new lemma.

## Phase 1 — modulo node forcing (new)
3. **`node_will_equiv`** — `might_output (node_step np) ns t o` ->
   `eventually (will_step (node_step np) well_formed_g) (output-≈-o) (ns,t)`, via
   `can_implies_will_equiv`, discharging allowedness with `node_inputs_allowed`.
4. **`node_cap_transfer_equiv`** — *crux.* `might_output omsg` at `gs_pre` (inputs
   `t_o`) transfers to `might_output_equiv omsg` at a `core_dom`-dominating
   `gsStar`. `core_dom` gives set-`incl` => `incl_mod`; apply `monotone_mod_equiv`,
   composing with `monotone_multiset` per question (A).

## Phase 2 — modulo graph driving (new)
5. **`drive_node_emit_equiv` / `force_emit_list_equiv` / `force_dominator_equiv`** —
   mirror the existing chain but force emissions via `node_will_equiv` and discharge
   allowedness via `node_inputs_allowed`. `force_deliver` reused unchanged.
6. **`drive_node_must_equiv`** — lift node `will_output_equiv` to graph
   `will_output_equiv` with the carried reflection relation `R`, concluding
   `In (omsg,on) (outputs_of t')` up to `equiv_g`. Reuses `R`/`eventually_carry_inv2`.

## Phase 3 — assemble
Mirror the deleted skeleton: destruct `might_output` -> `find_producing_step` ->
`Harmed` -> set up `R` -> `force_dominator_equiv` -> `node_cap_transfer_equiv`
(-> `might_output_equiv`) -> destruct to `o' ≈ omsg`, `might_output o'` ->
`node_will_equiv` -> `drive_node_must_equiv` -> weaken `will_output_equiv … o'` to
`… (omsg,on)` via `equiv_g` transitivity.

## Settled / open
- **(A) [settled: use the composition, then investigate necessity]**
  `monotone_mod_equiv` needs `well_formed_g` of *both* source `t_o` and target
  `gsStar` inputs, but a node holds only a submultiset (`allowed`) of the pool.
  Compose **`monotone_multiset`** (complete `t_o` up to a `well_formed_g` superset —
  exact) **then `monotone_mod_equiv`** (equiv-jump to `gsStar`). The intermediate
  complete state is graph-constructible (demon delivers completing facts from the
  pool). **First prove using `monotone_multiset`; then investigate whether
  `can_implies_will_equiv` (whose `will_output` is already robust to the node demon
  pumping duplicates) makes `monotone_multiset` unnecessary.**
- **(B)** `core_dom` is set-`incl`, not `submultiset`: fine for `monotone_mod_equiv`
  (`incl -> incl_mod`); the completion step in (A) is argued at multiset level
  (added, never removed => submultiset), separate from `core_dom`.
- **(C)** Whether `node_inputs_allowed`/`force_dominator_equiv` must deliver
  *complete* bundles (=> `well_formed_g` of node inputs) as needed by (A), beyond the
  old `incl`-domination.

Load-bearing new work: `node_inputs_allowed` and `node_cap_transfer_equiv`.
Phases 2–3 are largely mechanical `_equiv` re-skins of retained lemmas.
