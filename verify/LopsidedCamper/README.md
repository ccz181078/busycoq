# Lopsided Camper halts

`Halts273.v` proves, for `tm` = `1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE` (`Rules273.v`) and busycoq's `c0` and `halts`:

```coq
Theorem c273_halts : halts tm c0.
```

The machine halts after about 8.31×10^41 steps (that count is not part of the theorem). Full write-up, with the other checks: https://github.com/Yeyito777/bbchallenge-discoveries/blob/main/bb6-holdout-2/HALT.md

## Method

- `Rules273.v` proves Shawn Ligocki's rule map on A(a,b,c) = `0^inf 1^a (10)^b C> 1^c 0^inf` from the raw machine, every branch, and `halts_of_orbit`: if the map's orbit from A(0,1,0) ends, the machine halts.
- `Kernel273.v` runs the map on primitive 63-bit integers and proves it agrees with the map while the numbers stay below 2^61. `Final273.v` proves `halts_of_chain`.
- `jobs/J0000.v` to `jobs/J0521.v` each check 2^37 map steps from one checkpoint to the next with `native_cast_no_check`; `jobs/J0522.v` checks the last 11,914,461,873 steps to the halt. `Chain.v` composes the 523 jobs.
- The checkpoints are untrusted: a wrong one makes its job fail. `gen/gen_jobs.py gen/ckpt.txt gen/halt.txt .` (run in this folder) rewrites `jobs/`, `Chain.v` and `Halts273.v` from them.

## Run

Rocq 8.20.1 with native compilation. In `verify/`:

```sh
make                         # the framework; only Individual62.vo and its dependencies are needed
LopsidedCamper/run.sh 8      # 8 jobs at a time, then Chain.v and Halts273.v
```

The script works from any directory. A job is done when its `.vo` exists, so the script can be restarted. `run.sh 8 J0000 J0001` runs only the named jobs.

## Cost

280 core-hours: each job takes about 1,930 s and under 450 MB, measured on a 128-core AWS m7a.32xlarge (EPYC 9R14). On an 8-core desktop that is about 35 hours and 4 GB (scaled, not measured). Per-job times and memory: `evidence/times.txt`.

## What is trusted

`Print Assumptions c273_halts` lists only primitive integers and their specifications: `PrimInt63.{int,add,sub,mul,div,ltb,eqb,land,lsr}` and `Uint63.{add,sub,mul,div,ltb}_spec` (`evidence/Halts273.out`). The jobs run under `native_compute`, so `ocamlopt` is trusted along with the kernel, as in Coq-BB5. `coqchk` was not run.
