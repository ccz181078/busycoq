# Blank halting equivalence of snapshot rows 326 and 408

`BusyCoq.Eqv326408.original326_408_blank_halting_equivalence` proves blank halting equivalence of these exact original machines in the standard `Individual62` context:

```text
326: 1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---
408: 1RB0RE_0LC---_1RE1LD_0LE1LB_1LC0RF_1RA1LD
```

The row numbers refer to the [815-machine snapshot](https://wiki.bbchallenge.org/w/images/f/fe/BB6_holdouts_815.txt) published by @mxdys on 24 September 2026, SHA256 `1b81f5b1b9c8230ddf13662b5948f0f5483cb528faf90c2dff1586fd474c25ff`. The theorem identifies two snapshot classes. It gives no individual halting verdict, official live-count update, runtime relation, score relation, or equality of final head positions.

## Dependency and proof

This contribution is stacked on [PR #9](https://github.com/ccz181078/busycoq/pull/9), commit `3525b4bcc1b2ea859bfb5a13356f0aa6e0422864`, reusing `IndexedRegularInvariant62.v`. PR #9 in turn uses the halt-tolerant invariant checker from [PR #7](https://github.com/ccz181078/busycoq/pull/7). This change adds eight paths and duplicates none of those checker definitions. A comparison against the upstream `BB6` branch also contains the prerequisites' eighteen paths.

The proof first relates original 408 to the published intermediate machine

```text
Q: 1LB0RC_0LC1LF_1LD0RE_1RC1LB_1RA1LB_0LD---
```

After the A-fixing state map `[A,D,E,C,F,B]`, Q differs from original 408 only at A0. The 47-state DFA and 2,867-tuple invariant prove that source A0 always has right neighbor 0. Under that guard, source A0 takes three steps and the aligned Q takes one step to the same complete configuration; the tape outside the read window is arbitrary. Undefined source cells are permitted in the invariant, and both machines have the same undefined cells. The existing positive-progress `halts_iff` theorem gives both directions of blank halting equivalence.

Finally, the proof composes with the already published [Eqv_v2.TM617.eqv](https://github.com/ccz181078/busycoq/blob/605d26d30610615ebe09ec23fcea079d6ef6ef50/verify/Eqv_v2.v#L6288), relating Q to original 326. `EdgeTM617.v` isolates that proof and its small helper definitions so replay does not require building every individual equivalence in `Eqv_v2.v`. The proof uses the original `ECBADF` state map and exact 2,235/3,242-step startup witnesses. This map moves the initial A state, so the finite prefixes are essential; a bare table isomorphism is not used as a blank-start theorem. The original literals and the A-fixing intermediate alignment are checked in `Eqv326408.v`.

## Replay

Tested against upstream `BB6` commit `27b8b41fd5d7c5680477574ad29f9f721b2bfd5f` using Coq 8.20.1 / OCaml 5.3.0. With those tools on PATH, from the repository root:

```sh
bash verify/Eqv326408/check.sh
```

The script builds the complete 22-source cone and runs full recursive `coqchk`. Native compilation is disabled; the computations use `vm_compute`. `AllAssumptions.v` prints all 30 authored theorem/lemma declarations, each closed under the global context. No solver, generator, external certificate archive, new logical axiom, admit, or unchecked proof cast is needed.

Separate automated review rebuilt from source, checked every transition, all 2,867 tuples and 419 buckets, the one-bit projection, exact native table/blank bindings, the positive join and the published intermediate composition. It also compiled and recursively checked an independent fully qualified endpoint theorem, and rejected six deliberately false goals involving a changed original table, wrong state map, wrong blank DFA edge, missing invariant tuple, reversed guard bit, and zero-step join.

Developed with OpenAI assistance and contributed under the repository's MIT license. Construction and independent review were automated; external human review is welcome. The published TM617 proof remains credited to its upstream authors.
