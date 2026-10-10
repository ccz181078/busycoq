# Original815 row9: nonhalting from blank A

`Row9BlankA.nonhalt` proves the literal theorem

```coq
~ halts (TM_from_str "1RB0LA_0RC1LE_0RD1RE_1LA1RF_1RB0LD_1RC---") c0.
```

Here `c0` is BusyCoq's blank tape in its original starting state A. The undefined F1 transition is unchanged. No changed-start blank-F theorem, machine-equivalence result, or other individual proof is a premise.

## Check

From this directory, with Coq 8.20.1 on `PATH`:

```sh
./check_row9.sh
```

The script builds the existing framework with `make`, compiles the individual proof files, prints the assumptions of the final theorem, and independently checks its complete dependency closure with `coqchk`. The final assumptions report is `Closed under the global context`.

As with the other individual proofs in this repository, this theorem is not added to the default framework build. The script does not attempt to compile every other individual machine proof.

## Proof structure

- `Row9Eval.v`: exact strict finite-word evaluator, successful-return invariants, and constructive totality by lexicographic descent on a residue potential and word length
- `Row9Machine.v`: literal transition-table execution; universal carry/reset lemmas; exhaustive scanner cases; evaluator embedding; five-step blank-A startup; positive progress of each physical phase
- `Row9Algebra.v`, `Row9Operators.v`, `Row9Binary.v`, `Row9Four.v`: strict lifted operator identities, equivalence of finite halting under T and H, and the guarded root-0/root-3/root-4 transfer rules
- `Row9Numerals.v`, `Row9Family.v`: binary gap numerals and nonhalting of the universal productive family `K_(7*m-12)(N(m))`, for every `m >= 2`, by descent of a finite halting index
- `Row9Acceleration.v`: a fuel-bounded certificate evaluator with a proved sound binary-prefix accelerator
- `Row9CertificateCalls.v`: 222 explicit successful evaluator equations, each checked with `vm_compute` and `reflexivity` using the proved checker
- `Row9Certificate.v`: the fixed 47 quotient edges (3 T and 44 H) followed by 58 root rewrites (30 zero, 21 three, 7 four), from `K_3([])` to `K_63492([2;2;5;1;1;5;1;5;1;13])`
- `Row9Bridge.v`, `Row9BlankA.v`: the exact physical-to-abstract halting bridge and the final theorem

The endpoint is `K_63492(22N(9070))`, the successful H successor of the productive-family instance `m=9072`. The strict decrease in the family proof comes from a successful H step, not from an administrative equivalence cycle.

All certificate inputs and outputs are literal finite words in the Coq sources. No Python generator, external data file, previous computation receipt, or saved-search program is needed to build or check the theorem. The checker can fail when fuel is exhausted; fuel exhaustion is never interpreted as nonhalting. Abstract clocks other than the initialized T3 clock are not claimed to be raw machine trajectories.

No axioms, admitted obligations, unchecked casts, or native-computation tactics are introduced. All equality checks use kernel-checked computation.

## Source provenance

The source machine is original line 9 of the 815-machine dataset whose SHA-256 is `1b81f5b1b9c8230ddf13662b5948f0f5483cb528faf90c2dff1586fd474c25ff`. The source string in the theorem is the authoritative formal statement.

This is the formalization of the mathematical proof accepted on 2026-10-04. The fixed selected path was extracted from the quotient artifact with SHA-256 `39918516ff56d4f1627b443c9f420882ff06abffba3ca56d5e42e2f96c9c72aa` and normalization artifact with SHA-256 `f3b29a915a9f2788b62d2b03d215f598b7e8d133c9e11454da24cbc5dcafae63`. Those hashes document provenance only; no artifact or hash equality is a premise of the formal theorem.
