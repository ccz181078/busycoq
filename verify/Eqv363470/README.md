# A CTL-guarded BB(6) equivalence

The entry point is `BusyCoq.Eqv363470.eqv` in `../Eqv363470.v`:

```coq
halts (TM_from_str "1RB1LC_1LC0RD_0LE1LA_0RF1RA_1RD0LA_---0RB") c0
<->
halts (TM_from_str "1RB1LC_1LC0RD_0LE1LA_---1RA_1RF0LA_0RF0RB") c0.
```

These are rows 363 and 470 of the public 815 file, SHA256
`1b81f5b1b9c8230ddf13662b5948f0f5483cb528faf90c2dff1586fd474c25ff`.
The names are only stable snapshot labels; the theorem binds literal tables.
Neither machine is classified as halting or nonhalting by this equivalence.

## Proof

1. A nine-state safety monitor follows the source computation. It reaches its
   undefined transition precisely when the forbidden source B1/right01 context
   is encountered. Original source halts are sent to a nonhalting sink.
2. Two literal base DFAs, with 4 and 7 states, discharge that monitor's nonhalting
   condition using the existing `CTL.MITMDFA` checker and specific soundness
   theorem. `vm_compute; reflexivity` checks the certificate in Coq.
3. `SourceSafety.v` proves the raw source-to-monitor simulation and the concrete
   reachable-context exclusion. The source uses the existing BB62 context and
   the exact `Individual62` raw semantics.
4. `TerminalCoupling.v` proves common, positive-progress macro steps, including
   the asymmetric two-step/one-step terminal branch. Source reachability is
   restored at every common boundary. Upstream `halts_iff` yields equivalence.
5. The entry point binds both tables by reflexivity and states the result in
   upstream `Individual62.halts` on its blank configuration.

The statement is only blank halting equivalence. Runtime, score and complete
terminal-tape claims are outside this theorem. Under the partial-machine stop
convention the computational analysis finds equal tapes at undefined cells;
appending a halting write at different head positions need not preserve that
full-tape equality. No count of currently unresolved community representatives
is asserted by this file.

## Replay

Tested against BB6 commit
`27b8b41fd5d7c5680477574ad29f9f721b2bfd5f`, Coq 8.20.1 / OCaml 5.3.0.
Only existing framework files and the Coq standard library are dependencies.
No SAT solver, Python runtime, network download or modified framework is needed.
From the repository root:

```sh
bash verify/Eqv363470/check.sh
```

The script builds the minimal dependency cone and all new proof sources with
native compilation disabled, then runs full dependency-recursive `coqchk`.
It intentionally does not change the repository's default framework build.
`Print Assumptions eqv` reports 28 Coq primitive integer/array operations and
specifications (PrimInt63, Uint63 and PArray). It has no dependency on general
UIP/`inj_pair2`, functional extensionality, admitted obligations, or an authored
logical axiom. The two table binding lemmas are closed under the global context.

## Provenance and contribution scope

The proof uses BusyCoq's existing raw semantics, CTL theorem and positive macro
interface. The DFA data and guard were discovered externally; they are checked
here rather than trusted. All proof sources and the complete certificate needed for replay are included
in this contribution. No external development archive is required.
This contribution was developed with OpenAI assistance and independently
reviewed. It adds a pair theorem without refactoring the framework or replacing
existing equivalence automation. The new files are contributed under the
repository's MIT license; existing upstream and LibTactics notices remain.
