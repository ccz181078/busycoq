#!/usr/bin/env bash
# Build the unchanged BusyCoq framework, then kernel-check the row9 theorem.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

make -j "${JOBS:-2}"
for source in \
  Row9Eval.v Row9Algebra.v Row9Operators.v Row9Numerals.v \
  Row9Binary.v Row9Four.v Row9Family.v Row9Acceleration.v \
  Row9CertificateCalls.v Row9Certificate.v Row9Machine.v \
  Row9Bridge.v Row9BlankA.v
do
  "${COQC:-coqc}" -Q . BusyCoq "$source"
done
"${COQCHK:-coqchk}" -silent -Q . BusyCoq BusyCoq.Row9BlankA
