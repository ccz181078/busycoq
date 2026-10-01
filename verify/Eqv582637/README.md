# Blank-halting equivalence of rows582 and637

`BusyCoq.Eqv582637.eqv` proves `halts tm c0 <-> halts tm' c0` for:

```
1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---1LC
1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA
```

These are the exact one-based rows582 and637 of the public815-row snapshot, SHA256 `1b81f5b1b9c8230ddf13662b5948f0f5483cb528faf90c2dff1586fd474c25ff`. Both original `TM_from_str` bindings are definitional. Neither endpoint is individually classified; runtime and score equality are not claimed.

The source has a74-state DFA observer and2462-entry raw-step invariant, with274 exact lookup buckets. The one-bit projection proves that each blank-reachable source F1 has immediate-left0. F0 remains a genuine permitted halt. Under this guard the source's F1/C0/D1 path reaches the target's F1 endpoint in3 versus1 positive steps, with arbitrary left/right streams. A target-step macro system preserving source reachability feeds the standard positive-progress halting-equivalence theorem.

The invariant was derived from a new encoded-block checkpoint language with explicit mod3 left-sweep phases. It was also independently validated as a97-state regular language of complete tape words. Neither empirical runs nor bounded-unsatisfiability results are premises of the formal proof.

This application reuses `RegularInvariant62.v`, `IndexedRegularInvariant62.v` and `Eqv220723/EndpointEncoding.v` without modifying them. It is a six-path addition on the existing regular/indexed-invariant prerequisite branch; it does not modify the default build.

From the repository root:

```
bash verify/Eqv582637/check.sh
```

The complete20-unit cone was rebuilt with Coq8.20.1/OCaml4.13.1, native compilation disabled, followed by full recursive `coqchk`. All24 authored printed theorem assumptions are closed under the global context. A separate source-only clean rebuild and semantic review passed the same gates. No authored admits, axioms, unchecked casts or native-evaluation premise is introduced.

Exact-table and pinned-source checks did not locate a prior completed582/637 equivalence. This is bounded overlap evidence, not a worldwide priority claim. The historical1003 source row for original815 row582 is710; original815 row710 is a different machine.

Developed with OpenAI assistance. Implementation and independent reviews are automated; external human review is welcome. These application sources are contributed under the repository's MIT license.
