#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
for source in LibTactics Eqb Helper HashTable TM Compute Flip Permute Pigeonhole Enumerate Individual BB62 Individual62 RegularInvariant62 IndexedRegularInvariant62 Eqv220723/EndpointEncoding EdgeTM617 Eqv326408/Frozen408 Eqv326408/Projection Eqv326408/Pair408 Eqv326408 Eqv326408/AllAssumptions; do
  echo "Compiling $source.v"
  coqc -native-compiler no -Q . BusyCoq "$source.v"
done
coqchk -Q . BusyCoq BusyCoq.Eqv326408 BusyCoq.Eqv326408.AllAssumptions
