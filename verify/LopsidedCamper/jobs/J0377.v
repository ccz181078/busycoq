From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 51814485458944 to 51951924412416 *)
Lemma J0377 : job_ok 137438953472 171555205773490 2 61609980038032 6473512604729 1 227310148379735.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 6473512604729 1 227310148379735))]. Qed.
