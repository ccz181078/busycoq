# Four regular-invariant halting equivalences

This contribution applies the halt-tolerant checker in [PR #7](https://github.com/ccz181078/busycoq/pull/7) to four additional pairs. Its branch is based on prerequisite commit `0b30894abf9b5d21ab3320520cc2a66615fa436e`; it reuses `RegularInvariant62.v` and the one-bit projection lemmas rather than introducing another checker. Until #7 is merged, a comparison against `BB6` also includes that prerequisite commit.

Each public entry theorem has exactly the repository-native statement `halts tm c0 <-> halts tm' c0`, using `Individual62`, the literal original tables and blank initialization. State relabelings fix the initial state and are proved in both directions through the existing `Permute` interface.

| Snapshot rows | Native theorem | Source DFA states / invariant tuples |
| --- | --- | --- |
| 3 / 751 | `BusyCoq.EqvRegularPairs.Pair3_751.eqv` | 10 / 339 |
| 70 / 223 | `BusyCoq.EqvRegularPairs.Pair70_223.eqv` | 17 / 596 |
| 439 / 600 | `BusyCoq.EqvRegularPairs.Pair439_600.eqv` | 10 / 344 |
| 728 / 772 | `BusyCoq.EqvRegularPairs.Pair728_772.eqv` | 10 / 324 |

Row numbers refer to the [public 815-machine snapshot](https://wiki.bbchallenge.org/w/images/f/fe/BB6_holdouts_815.txt), SHA256 `1b81f5b1b9c8230ddf13662b5948f0f5483cb528faf90c2dff1586fd474c25ff`. The eight exact original tables are given below. These are four disjoint relations within that snapshot. No individual halting verdict, official live-count update, runtime relation or score relation is claimed.

## Proof structure

The certificate for each source includes all configurations reachable from blank, while allowing legitimate halting tuples. Finite DFA projections establish the local tape conditions needed at the changed transition. Every continuing macro step advances both machines positively, preserves arbitrary tape exteriors and returns to a common boundary. The common-boundary predicate is source reachability, so the source certificate is only used where its premise holds. Upstream `halts_iff` then gives both directions of halting equivalence.

For 3/751 the changed D0 cell has a three-versus-one-step join when its left neighbor is 0. For 439/600 and 728/772, the changed B0 cell has a three-versus-one-step join when its right neighbor is 0. The 728 certificate actually fixes the entire right half-tape to DFA class 0; only its immediate zero is needed for the join.

For 70/223, B0 has a five-versus-one-step join when its left neighbor is 1. The other reachable B0 case has an entirely blank left half-tape and immediate right bit 0. Both machines then halt in five defined steps, although their terminal tapes differ. The entire-left-blank fact follows from a checked unique incoming edge to DFA class 0, not merely a finite zero window. This paired terminal case is represented by a terminal macro branch whose two finite-halting obligations are separately proved.

`StateTransport.v` is a small adapter around the existing native `Permute.perm_halts`; it does not reimplement Turing-machine semantics. The four pair directories contain only their literal tables/certificates, projections, coupling proofs and rejection controls.

## Replay

Tested with Coq 8.20.1 / OCaml 5.3.0 against upstream BB6 `27b8b41fd5d7c5680477574ad29f9f721b2bfd5f`, with PR #7's prerequisite files present. From the repository root:

```sh
bash verify/EqvRegularPairs/check.sh
```

The script builds the minimal unchanged framework cone, the shared prerequisite checker/projection and all 21 new Coq sources, then runs full recursive `coqchk` for the four native entry points and their controls. Native compilation is disabled. No generator, solver or external certificate file is required. The native endpoint bindings and final equivalence theorems print closed assumption lists.

Controls include false local joins, incorrect tape guards/projections, omitted invariant entries, and incorrect forward/inverse state maps. The 70/223 controls additionally exercise the blank-half premise and both terminal branches. Runtime and score properties are outside these statements.

## Original machine tables

3:
```
1RB0LC_1LA1RF_1LD1RF_1LE0LA_0RB---_0RA1RE
```
751:
```
1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB---
```
70:
```
1RB1LF_1LC1RE_1LD1RD_1LA0LB_0RC---_1RC0LD
```
223:
```
1RB1LE_0RC1RF_1LD1RD_1LA0LB_1RC0LD_0RC---
```
439:
```
1RB1LE_1RC0RF_0LD---_1RF1LE_0LF1LC_1LD0RA
```
600:
```
1RB1LC_1LC0RF_0LF1LD_0LE---_1RF1LC_1LE0RA
```
728:
```
1RB0RF_0RC1RD_0LD---_1LE1RA_1LA0LF_0RD0RC
```
772:
```
1RB0RD_1LC1RE_1LA0LD_0RE0RF_1LC1RA_0LE---
```

At the pinned upstream head, 223 and 772 already occur separately in `Eqv_v3.v`. A bounded scan of all 541 `.v` files and 243,259 strict table literals found no literal or A-fixing renamed/reflected occurrence of the four source endpoints. This is source-overlap evidence, not a claim of global priority.

Developed with OpenAI assistance and contributed under the repository's MIT license. All sources needed for replay are public in this branch.
