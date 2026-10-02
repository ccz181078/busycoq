# Blank-halting equivalence of rows 759 and 808

`BusyCoq.Eqv759808.eqv` proves `halts tm c0 <-> halts tm' c0` for:

```text
1RB1LD_0RC1LE_1RD0LA_1RE0RC_1LF0LC_---1LB
1RB1LD_0RC1LE_1RD0LA_1RE0RF_1LF0LC_---1LB
```

These are the exact one-based rows 759 and 808 of the [815-row snapshot](https://wiki.bbchallenge.org/w/images/f/fe/BB6_holdouts_815.txt), SHA256 `1b81f5b1b9c8230ddf13662b5948f0f5483cb528faf90c2dff1586fd474c25ff`. Both `TM_from_str` bindings are definitional. Neither endpoint is individually classified; runtime and score equality are not claimed.

The source has a 134-state half-tape DFA observer and an 8,328-entry raw-step invariant, indexed by 405 exact lookup buckets. A one-bit projection checks all 322 D1 entries and proves that every blank-reachable source D1 has an immediate-right 1. Shared F0 remains a real permitted halt. At the changed D1 cell, the source reaches C1 in one step; the target reaches the same C1 configuration in three positive steps through F1 and B0, for arbitrary exterior tape streams. Source-step macro successors preserve source reachability. The existing constructive positive-progress `halts_iff` theorem gives both directions.

The invariant was discovered from an initialized counted mobile/reserve checkpoint language. The formal proof checks raw-step closure directly; neither the counted-language derivation, a generator, empirical traces nor bounded-unsatisfiability results are trusted premises.

This is a six-path application addition on [PR #9](https://github.com/ccz181078/busycoq/pull/9), whose recorded prerequisite head is `3525b4bcc1b2ea859bfb5a13356f0aa6e0422864`. It reuses `RegularInvariant62.v`, `IndexedRegularInvariant62.v` and `Eqv220723/EndpointEncoding.v` unchanged. It does not modify the default build or require the row 582 application. PR #9 must be present (or merged) first.

From the repository root, with Coq 8.20.1 available:

```sh
bash verify/Eqv759808/check.sh
```

All proof data is in these Coq sources. The script compiles the complete 20-unit cone with native compilation disabled, then runs full dependency-recursive `coqchk`; no `-admit` or `-norec` option is used. The author run passed with Coq 8.20.1 / OCaml 4.13.1, and all 24 authored printed assumption lists are closed under the global context. No authored axiom, admit, unchecked cast or native-evaluation premise is introduced. Independent mathematical and exact full-configuration-DFA review has accepted the guard argument. A separate source-only replay compiled all 20 units and passed full recursive `coqchk`, with all 24 authored assumptions closed. An independently written exact-statement audit also compiled and passed a second full recursive kernel check, with both additional assumption reports closed. Source/literal binding, all 16 dependency hashes and byte-exact generator reproduction were independently checked.

Developed with OpenAI assistance. Implementation and reviews are automated; external human review is welcome. These application sources are contributed under the repository's MIT license.
