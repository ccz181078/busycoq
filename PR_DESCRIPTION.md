Halting proof of one BB(6) holdout machine (`Lemma halt : halts tm c0.`) via a 2-mode digit-stack encoding, a 6-rule inductive tower algebra, and a 3-phase trajectory.

**One file**, with a top-level `Lemma halt : halts tm c0.` for its string. It imports only `Individual62` from busycoq (plus Coq standard library modules).

| machine                                     | `#` in 663 | file                                                                | mechanism                                                                                   |
| ------------------------------------------- | ---------: | ------------------------------------------------------------------- | ------------------------------------------------------------------------------------------- |
| `1RB0RC_1RC0LD_1LD1RA_1LF0LE_---0RD_1LB0LA` |         19 | `verify/M_1RB0RC_1RC0LD_1LD1RA_1LF0LE_HHH0RD_1LB0LA.v` (2,556 lines) | 2-mode (`F` / `AR`) stack encoding + 6-rule `A0`/`A3`/`B3` tower algebra + 3-phase schedule |

**Proof overview (`cfg_F` / `cfg_AR` stacks + `TowerA3` algebra + 3-phase trajectory).**

Holdout `#19` acts on unary digit stacks encoded on both half-tapes and develops a self-similar tower of stack wrappers (`A3` and `A0`) before halting from a large parametric body cycle. Binary `N` values represent all stack digits, RLE run lengths, and tower indices (up to `30,758,225` in Phase 1).

-   *Two-mode digit stacks and bulk contractions (Sections 1–2).* Each half-tape encodes a stack `a :: L` as `[1]^^(a + 1) *> (0 >> encLeft1 L)`. Two head configurations at the separator (`cfg_F L R` with head in `F` over `1` between `L` and `0 >> encRight1 R`, and `cfg_AR L R` with head in `A` over `0` between `encLeft1 L` and `encRight1 R`) obey 16 elementary rules (`rule_F_*` and `rule_AR_*`) plus one halting rule (`rule_F_one_halt : halts tm (cfg_F (1 :: L) R)`). Five iterated bulk contractions (`rule_F_step3_all`, `rule_AR_step2_all`, `rule_AR_add_two_zero_all`, `rule_F_zero4_all`, `rule_AR_ones_all`) compress arbitrary-modulus digit sweeps.
-   *Six-rule inductive tower algebra (Section 3).* Four stack wrappers
    -   `A3 k S = 6 :: 0 :: 0 :: 0 :: (3 * k + 3) :: 3 :: 0 :: S`,
    -   `A0 k S = 6 :: 0 :: 0 :: 0 :: (3 * k + 3) :: 0 :: 0 :: 0 :: S`,
    -   `B3 k S = 0 :: 3 :: 3 :: 0 :: 0 :: (3 * k + 3) :: 3 :: 0 :: S`,
    -   `B0 k S = 0 :: 3 :: 3 :: 0 :: 0 :: (3 * k + 3) :: 0 :: 0 :: 0 :: S`
    interact with two step relations: `SubStep S S'` (`forall R_bot, cfg_F (0 :: S) (9 :: R_bot) -->* cfg_AR (0 :: 0 :: 0 :: 0 :: 0 :: S') (0 :: R_bot)`) and `TopStep S S'` (`cfg_F (0 :: S) [5] -->* cfg_F (0 :: S') [5]`). Six algebraic rules (`subStep_A3`, `subStep_B3`, `subStep_A0`, `topStep_A3`, `topStep_B3`, `topStep_A0`) lift through arbitrary `TowerA3 ks S` stacks via `towerA3_topStep`, turning a single inner `SubStep` into a `TopStep` with `stepTowerAt 2 ks` (`k :: ks' -> (k + 2) :: stepTowerAt 8 ks'`). Outer `A0` wrappers absorb into `TowerA3` via `towerA3_absorb_A0` and `towerA3_absorb_towerA0Out`, while `SubHalt S` (`forall R_bot, halts tm (cfg_F (0 :: S) (9 :: R_bot))`) lifts through any non-empty `TowerA3 ks S` via `towerA3_halt`.
-   *RLE stack simulator (Section 4).* A total run-length encoded stack simulator (`stepGenRLE`, `runStepsRLE`, `runSubSim`) with open/closed bottom-stack flags (`evalRLEWith openL L L_bot`) is proved sound for both multi-step reductions (`runStepsRLE_sound_step`, `runSubSim_sound_closed`, `runSubSim_sound_open`) and halting (`runSubSim_sound_halt`).
-   *Three-phase trajectory to halt (Section 5).*
    -   *Phase 1 (`phase1_reach`).* Starting from `c0 = cfg_AR [] []`, one step enters `cfg_F [] [1]`. A 12-chunk schedule (`runPhase1Sched`, 11,728 RLE steps including 1,062 `tryJumpPhase1` tower jumps) reaches `cfg_F (0 :: TowerA0Out ksInitOut (bodyStack 56233 3)) [5]` with `ksInitOut = [30758225; 7689554; 1922386; 480594; 120146; 30034; 7506; 1874; 466; 114; 26; 4]`, which `towerA3_absorb_towerA0Out` folds into `TowerA3 ks0 (bodyStack 56233 3)`.
    -   *Phase 2 (`body_cycles_all`).* Each body cycle (`body_cycle_step`) takes `TowerA3 ks (bodyStack (8 * m + 9) (3 * (k + 1)))` to `TowerA3 ks' (bodyStack (8 * m + 1) (3 * (k + 2)))` via 10 open `SubStep` calls (`calls1to10_topStep`), a 5-stage 11th call (`partA_all`, `partB_step`, `partC_step`, `partD_step`, `partE_step`) across the fixed 39-run middle prefix `midPrefix`, and `A0 4` absorption. Iterating 7,029 cycles (`body_cycles_all 7029 0 0`) reduces `Z` from `56,233` to `1` and advances `b1` from `3` to `21,090`.
    -   *Phase 3 (`runPhase3_sound` and `halt`).* From `bodyStack 1 21090`, 186 closed `SubStep` calls (`runPhase3 186`) reach `SubHalt`, and `towerA3_halt` closes `Lemma halt : halts tm c0`.

**Checked** on `BB6 @ 2733f61` with Coq 8.20.1. Against the pre-built `busycoq` framework (`verify/Individual62.vo`), the file compiles standalone in ~20 seconds and passes an external kernel check pinning all 12 cells of `tm = TM_from_str "1RB0RC_1RC0LD_1LD1RA_1LF0LE_---0RD_1LB0LA"`, `c0`, and `Print Assumptions`:

```sh
coqc -Q verify BusyCoq verify/M_1RB0RC_1RC0LD_1LD1RA_1LF0LE_HHH0RD_1LB0LA.v
```

| file                                                     | `Print Assumptions halt`          |
| -------------------------------------------------------- | --------------------------------- |
| `verify/M_1RB0RC_1RC0LD_1LD1RA_1LF0LE_HHH0RD_1LB0LA.v`   | `Closed under the global context` |

**File names.** The file is named `verify/M_<RLE>.v` with `---` written as `HHH` so the Coq module name starts with `M_` and contains no `-`. The exact RLE string with `---` is in `TM_from_str`. Happy to rename it if you prefer.

**AI disclosure:** This proof was translated from Lean 4 and formalized in Rocq/Coq with AI assistance, and verified against unmodified `busycoq` (`Individual62.v`) with `coqc` and `Print Assumptions`. Extra verification and feedback are very welcome.
