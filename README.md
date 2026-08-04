Works with Rocq 9.0.0 (probably works with later versions too).

Requires https://github.com/liyishuai/coq-json if you want to use the JSON stuff.

This repo contains:

- basic Datalog semantics, plus logical semantics for aggregation.
- some "intermediate Datalog" language, which is basically just Datalog plus let and let rec.
- some restricted version of "top-down Datalog", with the restriction being restrictive enough that I could write and verify a simple transformation from top-down Datalog to bottom-up Datalog.
- a (deficient, hence Elizabeth's project) verified ATL compiler, targeting top-down Datalog.
- some in-progress work on a verified transformation from Datalog-with-fancy-aggregation-features to some appropriate ISA-ish Datalog-ish language.

## Building

`git clone --recursive` (to clone the submodules too)

Then run `make`.
