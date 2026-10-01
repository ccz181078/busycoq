#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
for source in LibTactics Eqb Helper HashTable TM Compute Flip Permute Pigeonhole Enumerate Individual BB62 Individual62 RegularInvariant62 Eqv220723/EndpointEncoding IndexedRegularInvariant62 Eqv464572/IndexControls Eqv464572/Frozen464Indexed Eqv464572/Projection Eqv464572/Pair464 Eqv464572; do
  echo "Compiling $source.v"
  coqc -native-compiler no -Q . BusyCoq "$source.v"
done
coqchk -Q . BusyCoq BusyCoq.Eqv464572.IndexControls BusyCoq.Eqv464572
