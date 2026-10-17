Nonhalting proofs of eleven BB(6) holdout machines (`Lemma nonhalt : ~ halts tm c0.`) that act as two-register call-stack transducers over word-level blocks `{V, K, Q}`. All eleven machines share the exact same 11-cell transducer core and differ only in a single transition cell that is entered during startup and turnaround. Up to LR mirror and state renaming, the eleven machines partition into three start-free transition tables:
- **Table 1** (`#6`, `#165`, `#507`, `#530`): `E0 = 1RB` in `#6`'s coordinates.
- **Table 2** (`#119`, `#209`, `#359`, `#504`): `E0 = 1LB` in `#6`'s coordinates.
- **Table 3** (`#37`, `#344`, `#396`): `E0 = 1LA` in `#6`'s coordinates.

**Eleven files**, each with a top-level `Lemma nonhalt : ~ halts tm c0.` for its own string. Each imports only `Individual62` from busycoq (plus Coq standard library modules).

| machine                                     | `#` in 663 | file                                                                 | tape & relation within family                                                                       |
| ------------------------------------------- | ---------: | -------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------- |
| `1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_0RB---` |          6 | `verify/M_1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_0RBHHH.v` (2,763 lines) | right-tape; Table 1 (`#507` renamed `A→B, B→C, C→D, D→E, E→A`, `F` fixed)                           |
| `1RB0RA_1RC0RD_1LD1LE_1LF0LC_0LD---_1RA1LD` |         37 | `verify/M_1RB0RA_1RC0RD_1LD1LE_1LF0LC_0LDHHH_1RA1LD.v` (2,956 lines) | left-tape; Table 3 (`#396` mirrored `L↔R` and renamed `A→C, B→D, C→F, D→A, E→B, F→E`)               |
| `1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA1RF_0RA---` |        119 | `verify/M_1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA1RF_0RAHHH.v` (2,957 lines) | right-tape; Table 2 (differs from `#507` only at `D0: 1LA` vs `1RA`)                                |
| `1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_0LD---` |        165 | `verify/M_1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_0LDHHH.v` (2,800 lines) | left-tape; Table 1 (`#530` renamed `A→B, B→C, C→D, D→E, E→A`, `F` fixed)                            |
| `1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB1LF_0LB---` |        209 | `verify/M_1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB1LF_0LBHHH.v` (2,956 lines) | left-tape; Table 2 (`#119` mirrored `L↔R` and renamed `A→B, B→C, C→D, D→A`, `E, F` fixed)           |
| `1RB0RC_1LC1LF_1LD0LB_1RE1LC_1RA0RE_0LC---` |        344 | `verify/M_1RB0RC_1LC1LF_1LD0LB_1RE1LC_1RA0RE_0LCHHH.v` (2,800 lines) | left-tape; Table 3 (`#396` mirrored `L↔R` and renamed `A→B, B→C, C→D, D→E, E→A`, `F` fixed)         |
| `1RB1RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB---` |        359 | `verify/M_1RB1RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RBHHH.v` (2,785 lines) | right-tape; Table 2 (`#119` renamed `A→B, B→C, C→D, D→E, E→A`, `F` fixed)                           |
| `1RB1RF_1RC0RA_1LD1RB_1LE0LD_1LA0LB_0RB---` |        396 | `verify/M_1RB1RF_1RC0RA_1LD1RB_1LE0LD_1LA0LB_0RBHHH.v` (2,721 lines) | right-tape; Table 3 (differs from `#6` only at `E0: 1LA` vs `1RB`)                                  |
| `1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC1LF_0LC---` |        504 | `verify/M_1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC1LF_0LCHHH.v` (3,468 lines) | left-tape; Table 2 (`#209` renamed `A→B, B→C, C→D, D→A`, `E, F` fixed)                              |
| `1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_0RA---` |        507 | `verify/M_1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_0RAHHH.v` (2,800 lines) | right-tape; Table 1 (`#530` mirrored `L↔R` and renamed `A→C, B→D, C→A, D→E, E→B`, `F` fixed)        |
| `1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_0LC---` |        530 | `verify/M_1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_0LCHHH.v` (2,956 lines) | left-tape; Table 1 base table                                                                       |

**Shared two-register call-stack transducer (`Side` / `Seg` / `Parse` / `Scan` / `Good`).**

Each file lifts its low-level tape trajectory to a deterministic macro-step system `Step u u'` over words in `{V, K, Q}` and closes an inductive invariant `Good u` after a finite startup prefix:

-   *Call-stack segments and turnaround (Section 1).* Two call symbols `ch` and `ca` act on half-tapes via `Side` and finite word segments `Seg`. Twelve atomic `Seg` lemmas (`seg_ch_V`..`seg_ca_QQ`) plus turnaround lemmas (`zP0`..`zP6` for `#37`, `#119`, `#165`, `#209`, `#344`, `#359`, `#396`, `#507`, `#530`; `zP0`..`zP14` for `#6`; `zP0`..`zP126` for `#504`) characterize how a call stream `[ch]^^a ++ [ca]^^b` crosses unprimed blocks `V_u = [1;1;0;0]`, `K_u = [0;0]`, `Q_u = [1;0]` and primed blocks `Vp = [0;1;1;0]`, `Kp = [0;0]`, `Qp = [0;1]`.
-   *Word encoding and transducer rules (Section 2).* Words `u : list Word` map to half-tapes via `zCf (zTs u 0inf)`, prefixed by a fixed header (`pref_cap`, `pref21`, `pref24`, or `pref28`). Binary digit words `zDg A H u` encode `H`-bit numbers `A < 2^H` over `{K, Q}`. The 5-rule parser `Parse a u a' g` and 7-rule two-register transducer `Scan a b u a' b' v g` lift `Seg` composition across word lists (`Seg_of_Scan`), giving `Step_exec : Step u u' -> zCf (zTs u 0inf) -->+ zCf (zTs u' 0inf)`.
-   *Universal parsing and executable trace checkers (Section 3).* `Parse_V_start` proves by 3-way structural induction (`Parse_all`) that every word starting with `V` parses from any input carry `a`. `Scan_of_Parse` upgrades `Parse a u a' g` to `Scan a b u a' b' v g` whenever `2 + 4 * z10 u < b`. Executable checkers `evalAffineScan` / `checkAffineScan` and `checkStep` (plus `evalTopTrace` / `checkTopTrace` in `#37`, `#119`, `#209`, `#530`) verify concrete and affine-parameterized scans by computation (`vm_compute`).
-   *Rational weight contraction and carry bounds (Section 4).* Rational summary functionals `z10`, `z12`, `z13`, and the 2-component weight `zW` / `zW_V` (`QArith`) satisfy `z13_Scan` (`z13 v * 2^(3 * g) = z13 u`), `Parse_la`, `Parse_zDg_a`, `Scan_delta`, and the strict contraction `Scan_zW_contract` (`zW_V v <= (15/16) * zW u + cPar b` or `(6/7) * zW u + cPar b`).
-   *Initial trajectory and concrete startup rounds (Section 5).*
    -   `#530` (441 startup steps), `#209` (363 steps), `#119` (979 steps), and `#37` (1,071 steps) reach `zCf (zTs u_0 0inf)` with `u_0 = [V; K; Q; Q]` and run 14 certified rounds (`step_0`..`step_13`) to `u_14`.
    -   `#507` (347 startup steps) and `#344` (274 steps) reach `u_0 = [K; K; Q]` and run 17 certified rounds (`step_0`..`step_16`) to `u_17`.
    -   `#359` (230 startup steps to `u_0 = [Q; Q]`) and `#165` (1,694 steps to `u_0 = [K; Q; Q]`) run 17 certified rounds (`step_0`..`step_16`) to `u_17`.
    -   `#396` (409 startup steps to `u_0 = [V; K; Q; Q]`) and `#504` (4,347 steps to `u_0 = [K; K; K; K; V; K; Q; Q]`) run 13 certified rounds (`step_0`..`step_12`) to `u_13`.
    -   `#6` (568 startup steps to `u_0 = [K; K; K; Q]`) runs 9 certified rounds (`step_0`..`step_8`) to `u_9`.
-   *Invariant closure and carry locking (Section 6).*
    -   In `#37`, `#119`, `#209`, and `#530`, `Good u` splits `u` as `head114 ++ p_114 ++ s17 ++ [K; Q; Q; K] ++ ds_core ++ [K; Q] ++ top35_ds ++ top27` with `z13 p_114 * 2^L = 2^45` and `zW p_114 <= 29/8`; `force_a35` locks the carry into `top35_ds` at `2^61`.
    -   In `#344` and `#507`, `Good u` splits `u` as `head103 ++ p_103 ++ s36 ++ [K; Q; K; Q; K; Q] ++ ds_core ++ [Q; Q] ++ top56` with `z13 p_103 * 2^m = 256` and `zW p_103 <= 13/4`; `force_a55` locks the carry into `top56` at `2^55`.
    -   In `#6`, `#165`, `#359`, `#396`, and `#504`, `Good u` splits `u` into five regions (`head ++ p ++ s ++ mid ++ ds_core ++ top`) with `z13 p * 2^m = const` and bounded `zW p`; `force_a19` / `force_a26` / `force_a_top` locks the carry entering `top` to a fixed power of two.
    -   In every file, `Good_step` produces `Step u u' /\ Good u'`, and `nonhalt` concludes `~ halts tm c0` via `multistep_nonhalt` and `progress_nonhalt_cond`.

**Checked** on `BB6 @ 2733f61` with Coq 8.20.1. Against the pre-built `busycoq` framework (`verify/Individual62.vo`), each file compiles standalone and passes an external kernel check pinning `tm = TM_from_str "<RLE>"` and `Print Assumptions`:

```sh
coqc -Q verify BusyCoq verify/M_<...>.v
```

| file                                                     | `Print Assumptions nonhalt`       |
| -------------------------------------------------------- | --------------------------------- |
| `verify/M_1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_0RBHHH.v`   | `Closed under the global context` |
| `verify/M_1RB0RA_1RC0RD_1LD1LE_1LF0LC_0LDHHH_1RA1LD.v`   | `Closed under the global context` |
| `verify/M_1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA1RF_0RAHHH.v`   | `Closed under the global context` |
| `verify/M_1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_0LDHHH.v`   | `Closed under the global context` |
| `verify/M_1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB1LF_0LBHHH.v`   | `Closed under the global context` |
| `verify/M_1RB0RC_1LC1LF_1LD0LB_1RE1LC_1RA0RE_0LCHHH.v`   | `Closed under the global context` |
| `verify/M_1RB1RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RBHHH.v`   | `Closed under the global context` |
| `verify/M_1RB1RF_1RC0RA_1LD1RB_1LE0LD_1LA0LB_0RBHHH.v`   | `Closed under the global context` |
| `verify/M_1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC1LF_0LCHHH.v`   | `Closed under the global context` |
| `verify/M_1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_0RAHHH.v`   | `Closed under the global context` |
| `verify/M_1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_0LCHHH.v`   | `Closed under the global context` |

**File names.** Each file is named `verify/M_<RLE>.v` with `---` written as `HHH` so the Coq module name starts with `M_` and contains no `-`. The exact RLE string is in `TM_from_str`. Happy to rename them if you prefer.

**AI disclosure:** These proofs were translated from Lean 4 and formalized in Rocq/Coq with AI assistance, and verified against unmodified `busycoq` (`Individual62.v`) with `coqc` and `Print Assumptions`. Extra verification and feedback are very welcome.
