# Halt-tolerant regular reachability and a BB(6) equivalence

`RegularInvariant62.v` supplies a reusable finite-DFA reachable-configuration
invariant checker for arbitrary machines in the existing six-state binary
`Individual62` context. Undefined transition cells impose no successor
obligation: this is a reachability theorem and does not assert nonhalting.

The example is the native theorem `BusyCoq.Eqv220723.eqv`, proving blank halting
equivalence of the literal tables:

```
1RB1RE_0LC1RF_---1LD_1LE0LD_1LA1LB_1RE0RA
1RB1RE_0LC1RF_---1LD_1LE0LD_1LA1LB_1RF0RA
```

They are rows 220 and 723 of the public 815-machine snapshot, SHA256
`1b81f5b1b9c8230ddf13662b5948f0f5483cb528faf90c2dff1586fd474c25ff`.
The theorem uses upstream `TM_from_str`, `halts`, and blank `c0`; both table
bindings prove by reflexivity. No relabeling or reflection is used. Neither
machine is classified as halting or nonhalting, and no runtime/score theorem
or official live-count update is asserted.

## Generic checker

Each finite-support half-tape is represented by a nearest-first list, classified
by a total DFA read from the remote end toward the head. A checked blank-zero
self-loop makes arbitrary remote blank padding harmless. The Boolean checker
verifies bounded states, true blank initialization, and closure under every
inverse-DFA predecessor for every defined raw transition. It does not assume
that a summary has a unique predecessor.

The checker reflection theorem, one-step preservation, and induction over the
actual raw execution yield `check_reachable_invariant`. The immediate-halting
control deliberately passes its reachable invariant and separately proves that
it halts. Drifting and ambiguous-predecessor controls are included, along with
eight kernel-checked rejections for malformed or incomplete invariants.

## Example equivalence

The included 16-state DFA and 587-tuple invariant are literal untrusted data
checked by Coq. Sixteen included tuples are source-halting tuples; keeping them
is essential to the halt-tolerant interface. A one-bit observation lemma proves
that every reached source F0 has immediate right1.

At that guard, source F0=1RE, E1=1LB, B1=1RF is an exact three-step whole-tape
join with the target's single F0=1RF transition. All other table cells are identical,
including their sole undefined C0 cell. A common macro system advances both
machines positively and maintains source reachability at common boundaries.
Applying the existing `halts_iff` theorem in both directions completes the proof.

The local diamond permits arbitrary infinite exterior streams; the source
reachability invariant separately supplies finite-support blank-run witnesses.
No finite-window agreement is substituted for an exterior-preservation proof.

## Replay and trust boundary

Tested against BB6 head `27b8b41fd5d7c5680477574ad29f9f721b2bfd5f`,
Coq 8.20.1 / OCaml 5.3.0. From the repository root:

```sh
bash verify/Eqv220723/check.sh
```

This compiles the minimal unchanged framework cone and all eight new proof
sources, with native compilation disabled, then runs full recursive `coqchk`.
All 33 printed assumption lists, including the final native equivalence theorem,
are closed under the global context. There are no authored axioms, admits,
unchecked casts, or external-solver assumptions. The controls also reject a
wrong target transition, incorrect observation/guard labels, and a missing
right-neighbor premise.

All sources and certificate data needed for replay are included. No generator,
Python interpreter, SAT solver, download, or private evidence archive is needed.
The contribution adds new files without modifying the existing framework or its
default build. Developed with OpenAI assistance and offered under the existing
repository MIT license.
