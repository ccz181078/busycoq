#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
for source in LibTactics Eqb Helper HashTable TM Compute Flip Permute Pigeonhole Enumerate Individual BB62 Individual62 RegularInvariant62 Eqv220723/EndpointEncoding Eqv220723/Frozen220 Eqv220723/InvariantControls Eqv220723/Projection Eqv220723/Pair220 Eqv220723/PairControls Eqv220723; do
  echo "Compiling $source.v"
  coqc -native-compiler no -Q . BusyCoq "$source.v"
done
coqchk -Q . BusyCoq BusyCoq.RegularInvariant62 BusyCoq.Eqv220723.InvariantControls BusyCoq.Eqv220723.PairControls BusyCoq.Eqv220723
