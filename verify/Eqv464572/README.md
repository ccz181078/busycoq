# Indexed regular invariants and equivalence of rows 464 / 572

This contribution depends on the `RegularInvariant62.v` and literal-encoding
interface introduced by PR #7. It adds an equivalent indexed implementation of
that checker, plus a blank halting equivalence in the standard `Individual62`
six-state binary context. No existing framework or default build is modified.

The exact original machines are:

    464  1RB0RC_1LC0RB_1RE1LD_0LB0LF_---0RA_1LB0RC
    572  1RB0RC_1LC0RB_1RE1LD_0LB0LF_---0RA_1LB1LD

The native entry theorem is `BusyCoq.Eqv464572.eqv`:

    halts tm c0 <-> halts tm' c0

Both `TM_from_str` bindings are proved by reflexivity. These are physical
one-based rows of the [published 815-machine snapshot](https://wiki.bbchallenge.org/w/images/f/fe/BB6_holdouts_815.txt),
SHA256 `1b81f5b1b9c8230ddf13662b5948f0f5483cb528faf90c2dff1586fd474c25ff`.
The theorem does not decide either machine individually or assert an official
live holdout count, runtime relation, or score relation.

## Reachability and local repair

The literal DFA has 49 states. Its 3,676-tuple source invariant includes 98
legitimate E0 halting tuples. Undefined transitions impose no successor
obligation, so the proof remains compatible with either halting or nonhalting.

The exact two-bit projection proves that every reachable source F1 has
`tape[-2]=1`, `tape[-1]=0`, and scanned `tape[0]=1`. Thus its strict-left word
is `10` far-to-near or `01` nearest-to-farthest. The source takes one step to C,
moving right and writing zero. The target takes F1, D0, B1, B0, C0, E1, A1 in
seven steps and reaches the identical state, head and whole tape. Both exterior
streams are arbitrary parameters of the theorem.

All other cells agree, including the sole undefined E0 cell. The source's raw
reachability predicate is preserved at the common endpoints, every continuing
segment advances both machines positively, and upstream `halts_iff` supplies
the two implications from blank.

## Constructive membership index

`IndexedRegularInvariant62.v` groups right-class lists by control, scanned
symbol and left class. Its semantic theorem reuses the original
`certificate_ok` and reachable-configuration interface. In particular,
`indexed_check_same` proves exact Boolean equality with the original checker
on the flattened entries.

The application uses 216 nonempty buckets. Coq proves that their flattening
equals the full literal 3,676-tuple invariant, preserving duplicates and order
rather than assuming a set conversion. The index changes lookup cost only.
On the tested compiler, the original `vm_compute` calculation took about
1,153 seconds; the indexed calculation took about 4 seconds. These timings
are observations, not mathematical guarantees.

`IndexControls.v` covers legitimate halts, duplicate values, missing blank
membership, missing inverse-pop successors, out-of-range right values and
left keys, and an empty state domain. Duplicates are semantically harmless in
the generic list checker; the application's exact-flattening theorem still
pins its unchanged input list.

## Replay

From the repository root, with Coq 8.20.1:

    bash verify/Eqv464572/check.sh

The script freshly compiles the 21-unit dependency cone and performs full
recursive `coqchk`, with native compilation disabled. All data needed for
replay is included in the Coq sources; no generator, solver or private archive
is required. All 41 assumption lists printed by this script are closed under
the global context. There are no authored admits, axioms, unchecked casts or
native-evaluation premises.

Tested with Coq 8.20.1 / OCaml 5.3.0 against BB6 commit
`27b8b41fd5d7c5680477574ad29f9f721b2bfd5f`, with PR #7's unchanged prerequisite
files. Additional checks rejected nine deliberately false Coq goals, including
changed endpoints, shortened or zero-step repairs, altered projections,
missing or duplicated bucket entries, and malformed closure data.

At that upstream commit, neither original endpoint occurs among the 243,259
strict six-state table literals in 541 hash-verified Coq files under any of
the 240 A-preserving state-renaming/reflection variants, or in the indexed
3,565 equivalence edges. This is bounded overlap evidence, not a global
priority claim.

Developed with OpenAI assistance and contributed under the repository's MIT
license. The computational checks and separate proof review are automated;
they do not represent external human review.
