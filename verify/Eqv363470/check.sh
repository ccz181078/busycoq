#!/usr/bin/env bash
# Run from any directory in a BusyCoq BB6 checkout with Coq8.20 on PATH.
set -euo pipefail
cd "$(dirname "$0")/.."
for source in LibTactics Eqb Helper HashTable TM DHTM CTL Compute Flip Permute Pigeonhole Enumerate Individual BB62 Individual62 Eqv363470/BB92 Eqv363470/GuardCertificate Eqv363470/GuardDirect Eqv363470/SourceCtx Eqv363470/SourceSafety Eqv363470/TerminalCoupling Eqv363470; do
  echo "Compiling $source.v"
  coqc -native-compiler no -Q . BusyCoq "$source.v"
done
coqchk -Q . BusyCoq BusyCoq.Eqv363470
