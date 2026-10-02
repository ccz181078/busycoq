#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
for unit in LibTactics Eqb Helper HashTable TM Compute Flip Permute Pigeonhole Enumerate Individual BB62 Individual62 RegularInvariant62 Eqv220723/EndpointEncoding IndexedRegularInvariant62 Eqv759808/Frozen759 Eqv759808/Projection Eqv759808/Pair759 Eqv759808; do
  echo "Compiling $unit.v"
  coqc -native-compiler no -Q . BusyCoq "$unit.v"
done
coqchk -Q . BusyCoq BusyCoq.Eqv759808
