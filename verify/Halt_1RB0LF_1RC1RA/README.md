# 1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA halts

`Final.v` proves, for `tm` = `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA` (`Rules.v`) and busycoq's `c0` and `halts`:

```coq
Theorem bb6_holdout_halts : halts tm c0.
```

This folder is the `halts` proof only. The exact step count (also a Rocq theorem), the slower first proof and the full write-up are at https://github.com/Yeyito777/bbchallenge-discoveries/tree/main/bb6-holdout

## Method

- `Rules.v` and `Map.v` prove the machine's rule map on A(a,b) from the raw machine, every branch, and that reaching the map's halting case means `halts tm c0`.
- `Num.v` to `Check.v`, `Ints.v` and `HLines.v` to `HTop.v` define a checker that runs the orbit with block lemmas: a block lemma covers every state in a region given by exact integer inequalities, and a table reuses them. `run_seg_sound` and `run_halt_at_sound` (`HTop.v`) prove it sound.
- `Cuts.v` holds the cut points. `jobs/J0000.v` to `jobs/J0311.v` each check `run_seg ... = true` for one stretch, and `jobs/JHalt.v` the stretch that ends in the halt, with `native_cast_no_check`. `Final.v` chains the 313 jobs.
- The cut points are untrusted: a wrong one makes its job fail. `gen/gen_final.py chunks.tsv . 1024` (run in this folder) rewrites `Cuts.v`, `jobs/` and `Final.v` from the chunk table, `bb6-holdout/rocq/bb6/cert/chunks.tsv` in the `bb6-chunks` release asset of the repository above.

## Run

Rocq 8.20.1 with native compilation, ideally on an OCaml 4.14 flambda switch (about 2x faster). In `verify/`:

```sh
make                              # the framework; only Individual62.vo and its dependencies are needed
Halt_1RB0LF_1RC1RA/run.sh 8       # the checker, 8 jobs at a time, then Final.v
```

The script works from any directory and sets `ulimit -s unlimited`. A job is done when its `.vo` exists, so the script can be restarted. `run.sh 8 J0000 JHalt` runs only the named jobs.

## Cost

275 core-hours: jobs take 12 to 117 min (median 57) and at most 1.55 GB, measured with flambda on a 128-core AWS c7a.32xlarge (2 h 40 min wall). `JHalt` takes about a second and `Final.v` 1.5 s. On an 8-core desktop that is about 34 hours and 13 GB (scaled, not measured). Per-job times and memory: `evidence/times.txt`.

## What is trusted

`Print Assumptions bb6_holdout_halts` lists 41 items, all primitive integers and arrays and their specifications: `PrimInt63.*` (16), `Uint63.*` (13) and `PArray.*` (12) (`evidence/Final.out`). The jobs run under `native_compute`, so `ocamlopt` is trusted along with the kernel, as in Coq-BB5. The kernel VM avoids that, at about 1,500 core-hours (extrapolated, not run). `coqchk` was not run.
