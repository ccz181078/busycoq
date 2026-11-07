From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 51951924412416 to 52089363365888 *)
Lemma J0378 : job_ok 137438953472 6473512604729 1 227310148379735 192206566411186 2 42195569499955.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 192206566411186 2 42195569499955))]. Qed.
