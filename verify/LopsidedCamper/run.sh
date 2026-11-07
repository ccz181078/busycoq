#!/bin/bash
# Prove c273_halts : halts tm c0. Usage: LopsidedCamper/run.sh [PARALLEL_JOBS] [JOB...], from any directory.
# Build the framework first (make in verify/). Compiles from verify/ with the flags of verify/_CoqProject.
# PARALLEL_JOBS defaults to one per core; a job needs about 450 MB. A job is done when jobs/Jnnnn.vo exists, so the
# script can be restarted. With JOB names (J0000 ...) it runs only those jobs and stops.
set -u
P=${1:-$(nproc)}; [ $# -gt 0 ] && shift
D=$(cd "$(dirname "$0")" && pwd); N=$(basename "$D"); cd "$D/.." || exit 1
die() { echo "run.sh: $*" >&2; exit 1; }
command -v coqc >/dev/null || die "coqc not found (Rocq 8.20.1 with native compilation)"
[ -f Individual62.vo ] || die "build the framework first: make in verify/"
ls .coq-native/NBusyCoq_Individual62.* >/dev/null 2>&1 || die "the framework has no native code; rebuild it with native compilation on"
Q="-Q . BusyCoq -Q ./BigInt BigInt -native-compiler yes"
for f in Rules273 Kernel273 Final273; do
  [ -f $N/$f.vo ] || coqc $Q $N/$f.v || die "compiling $N/$f.v failed"
done
run1() {
  j=$1; [ -f $N/jobs/$j.vo ] && exit 0; s=$(date +%s)
  if coqc $Q $N/jobs/$j.v > $N/jobs/$j.log 2>&1; then echo "ok $j $(( $(date +%s) - s ))s"; else echo "FAILED $j"; exit 1; fi
}
export -f run1; export N Q
if [ $# -gt 0 ]; then printf '%s\n' "$@"; else ls $N/jobs | sed -n 's/^\(J[0-9]*\)\.v$/\1/p'; fi |
  xargs -P "$P" -n 1 bash -c 'run1 "$0"' || die "a job failed (see $N/jobs/J*.log)"
[ $# -gt 0 ] && exit 0
coqc $Q $N/Chain.v || die "compiling $N/Chain.v failed"
coqc $Q $N/Halts273.v > $N/Halts273.log 2>&1 || { cat $N/Halts273.log >&2; die "compiling $N/Halts273.v failed"; }
cat $N/Halts273.log
