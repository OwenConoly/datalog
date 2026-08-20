Works with Rocq 9.1.1 (probably works with later versions too).

This repo contains:

- basic Datalog semantics, plus logical semantics for aggregation.
- some "intermediate Datalog" language, which is basically just Datalog plus let and let rec.
- some restricted version of "top-down Datalog", with the restriction being restrictive enough that I could write and verify a simple transformation from top-down Datalog to bottom-up Datalog.
- a (deficient, hence Elizabeth's project) verified ATL compiler, targeting top-down Datalog.
- some in-progress work on a verified transformation from Datalog-with-fancy-aggregation-features to some appropriate ISA-ish Datalog-ish language.

## Building

* to get dependencies: `opam install coq-json`
* cloning: pass `--recursive` to get the submodules
* run `dune build` to build

By default, `dune build` will skip the src/atl directory.
(Currently, mostly everything in that directory is broken.)
If you want to build stuff in that directory, you can either do `dune build src/atl` in the root directory, or you can do `cd src/atl && dune build`.
