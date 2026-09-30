#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
# Shared framework and checker/projection from the prerequisite contribution.
for source in LibTactics Eqb Helper HashTable TM Compute Flip Permute Pigeonhole Enumerate Individual BB62 Individual62 RegularInvariant62 Eqv220723/EndpointEncoding Eqv220723/Frozen220 Eqv220723/Projection EqvRegularPairs/StateTransport; do
  echo "Compiling $source.v"
  coqc -native-compiler no -Q . BusyCoq "$source.v"
done
for row in 3 70 439 728; do
  for source in Frozen$row Projection Pair$row Controls; do
    echo "Compiling EqvRegularPairs/Pair$row/$source.v"
    coqc -native-compiler no -Q . BusyCoq "EqvRegularPairs/Pair$row/$source.v"
  done
done
for pair in 3_751 70_223 439_600 728_772; do
  echo "Compiling EqvRegularPairs/Pair$pair.v"
  coqc -native-compiler no -Q . BusyCoq "EqvRegularPairs/Pair$pair.v"
done
coqchk -Q . BusyCoq \
  BusyCoq.EqvRegularPairs.Pair3_751 BusyCoq.EqvRegularPairs.Pair70_223 \
  BusyCoq.EqvRegularPairs.Pair439_600 BusyCoq.EqvRegularPairs.Pair728_772 \
  BusyCoq.EqvRegularPairs.Pair3.Controls BusyCoq.EqvRegularPairs.Pair70.Controls \
  BusyCoq.EqvRegularPairs.Pair439.Controls BusyCoq.EqvRegularPairs.Pair728.Controls
