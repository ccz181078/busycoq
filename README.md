# BusyCoq

This project contains partial proof of [BB(6)](https://wiki.bbchallenge.org/wiki/BB(6)), BB(2,5) and BB(3,3).

We focus on proving whether each TM of given size halt or not, and we don't care about the step count or sigma score for simplicity.

First, there are some proven correct [deciders](https://wiki.bbchallenge.org/wiki/Decider), that can decide whether a TM halts (or fail to decide). We run deciders to solve most of the TMs.

Then, for the rest of the TMs, we can write individual proof for them. If a TM (up to equivalence) haven't been proven, it becomes a holdout.

For BB(6), there're about 1600 holdouts, while about 150 individual proofs haven't been translated to Rocq.

For BB(2,5), there're about 70 holdouts, while about 10 individual proofs haven't been translated to Rocq.

For BB(3,3), see [BB(3,3) - BusyBeaverWiki](https://wiki.bbchallenge.org/wiki/BB(3,3)).

The correctness of [TNF enumeration](https://wiki.bbchallenge.org/wiki/Tree_Normal_Form) haven't been proven in Rocq.

This project is based on [meithecatte/busycoq: Busy Beaver deciders backed by Coq proof](https://github.com/meithecatte/busycoq), a framework of TM definition, simulation and deciders.

## Deciders

This part is relatively stable, and no new decider has been proposed recently.

### Inductive deciders

- [translated cycler](https://discord.com/channels/960643023006490684/1028753852238925834/1329879463751847946), O(tape size) memory and near-linear time in practice

  implemented in `TC.v`

- Inductive (see some sections of [Inductive_Proof_System](https://wiki.bbchallenge.org/wiki/Inductive_Proof_System))

  use "Tape Compression" method "Nested Repeater" by default

  also support "Fixed Length Repeater" and "Others" (requires some hints from human)

  use "Find New Rule by Specializing Known Rules" to find rules for acceleration (rules can be nested)

  this method decided "Finned", "helix", some of [bell eats counters](https://wiki.bbchallenge.org/wiki/Bell_eats_counter) and some of [sync bouncer counters](https://wiki.bbchallenge.org/wiki/Sync_bouncer_counter)

  implemented in `Inductive.v`

- [RWLAcc](https://discord.com/channels/960643023006490684/1239205785913790465/1333106708117196941)

  see also some sections of [Inductive_Proof_System](https://wiki.bbchallenge.org/wiki/Inductive_Proof_System):

  use "Tape Compression" method "Macro Machine"

  use "Find New Rule by Generalizing Known Rules" to find rules for acceleration (hardcoded two layers, for shift rule and bouncer rule)

  it has a low overhead when no acceleration is found

  implemented in `RWLAcc.v`

- Recursive record-breaking analysis (RRBA)

  see also section "Recursive Record-Breaking Analysis" of [Inductive_Proof_System](https://wiki.bbchallenge.org/wiki/Inductive_Proof_System):

  use "Find New Rule by Generalizing Known Rules" to find rules for acceleration (hardcoded two layers)

  this method decided "shift-recursive" (including "counter balanced", "counter inverting" that were decided by MITMWFAR), and [sync bi-counter](https://wiki.bbchallenge.org/wiki/Sync_bi-counter) (like Skelet10)

  implemented in `RRBA.v`

- UBRRBA

  similar to RRBA, but work on “Macro Machine”, only track record-breaking in one direction, and doesn't use any acceleration except shift rule and memoization

  only for halting

  implemented in `Inductive.v`

### MitMCTL deciders: 

see also [CTL](https://wiki.bbchallenge.org/wiki/Closed_Tape_Language_(CTL)) section "regular CTL"

- n-gram cps with fixed length or k-LRU history
- RWL_mod
- CPS_LRU
- certs from FAR

implemented in `CTL.v`

## Individual proofs (about 2000 TMs):

This part is under active development, but the basic definitions are stable.

### Methods

- Proof template (had been used in [BB4](https://www.ams.org/journals/mcom/1983-40-162/S0025-5718-1983-0689479-6/)):

  find a proof of nonhalt with parameters (natural numbers or tape segment) and some verifiable properties of these parameters (rules involving these parameters), and then search for parameters to prove TMs

- Copy and modify existing proofs (lightweight version of proof template)

- Rocq tactics for acceleration:

  `es` for running TM using shift rule

  `ind` for proving linear rules by induction

  see `Example.v` for some examples

- [Rocq framework for generalized longitudinal analysis](https://discord.com/channels/960643023006490684/1344693543788347482/1344703755815485480)

### Cheat Sheet

| Tactic         | Usage                                    |
| -------------- | ---------------------------------------- |
| `es`           | run using shift rule when possible, stop after last used shift rule or solved |
| `follow`       | use given rule to run                    |
| `follow10`     | use given rule to run                    |
| `finish`       | solve `a -->* a`                         |
| `step1`        | run one step                             |
| `er`           | run multiple steps                       |
| `sr`           | use shift rule                           |
| `ind`          | prove rule by induction                  |
| `simpl_rotate` | move repeaters towards the edge of the tape |
| `simpl_tape`   | simplify tape                            |
| `solve_init`   | solve `c0 -->* a` in 1000000 steps       |
| `mid`          | run to specific configuration            |
| `mid10`        | run to specific configuration            |

| Lemma                           | Usage                         |
| ------------------------------- | ----------------------------- |
| `progress_nonhalt_simple`       | prove nonhalt                 |
| `progress_nonhalt_cond`         | prove nonhalt by invariant    |
| `sigma_score_unbounded_nonhalt` | prove nonhalt by score        |
| `multistep_nonhalt`             | run before nonhalt            |
| `halted_halts`                  | prove halt                    |
| `halts_evstep`                  | run before halt               |
| `sideRLs_trans`                 | [<br />[                      |
| `segRLs_trans`                  | □<br />□                      |
| `segRLs_sideRLs_concat`         | □[                            |
| `segRLs_concat`                 | □□                            |
| `sideRLs_concat`                | ][                            |
| `lpow_add`                      | `a^^(b+c) = a^^b ++ a^^c`     |
| `Str_app_assoc`                 | `(a ++ b) *> c = a *> b *> c` |
| `lpow_mul`                      | `a^^(b*c) = (a^^c)^^b`        |



## Equivalence classes

The basic method (`Eqv_v2.v`): two TMs are in the same equivalence class iff they (after state/direction permutation) reach the same configuration and have the same transition table.

A stronger method (mainly in `Eqv_v3.v`) is to do the back-symbol transform on TMs first, then simplify the transition table by removing unreachable transitions using CTL, and use the basic method to check equivalence.

If any TM in the equivalence class is decided, all TMs in this class are also decided.

If none of TMs in the equivalence class is decided, one TM in this class is selected to be in the holdout list and other TMs in this class are ignored.

## Compile

**All Rocq files are in the `verify` folder.**

Use `make` to compile the framework. (tested on Coq 8.20)

Individual proofs, hard-coded decider parameters for some TMs, and decider pipeline running on TNF enumeration won't be compiled by `make` because they'll take about **a month** (they depend on the part compiled by `make`, so **don't refactor anything** unless you know what you're doing).

