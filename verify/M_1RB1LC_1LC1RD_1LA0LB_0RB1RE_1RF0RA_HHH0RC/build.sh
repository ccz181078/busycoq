#!/bin/sh
# Build the halting proof of 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC. Run from verify/ after `make`.
# Needs a coqc built with the native compiler (-native-compiler yes, Coq 8.20) and an OCaml toolchain for it.
# The 400 segment files J000.v ... J399.v take about 37 minutes each (about 250 core-hours in all); set JOBS to
# the number of cores to use for them.
set -e
D=M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC
F="-Q . BusyCoq"
coqc -native-compiler yes $F $D/Check.v
for f in Visits Block Tab Arith Cmp Ex1 Blk BlkOk Run Rules; do coqc $F $D/$f.v; done
ls $D/J*.v | xargs -P "${JOBS:-4}" -n 1 coqc -native-compiler yes $F
coqc $F $D/Final.v
