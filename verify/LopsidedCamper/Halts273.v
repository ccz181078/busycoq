From BusyCoq Require Import Individual62.
From BusyCoq.LopsidedCamper Require Import Rules273 Final273.
From BusyCoq.LopsidedCamper Require Chain.

Theorem c273_halts : halts tm c0.
Proof. apply halts_of_chain. exact Chain.c273_chain. Qed.
Check c273_halts.
Print Assumptions c273_halts.
