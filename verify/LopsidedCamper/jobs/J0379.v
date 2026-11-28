From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 52089363365888 to 52226802319360 *)
Lemma J0379 : job_ok 137438953472 192206566411186 2 42195569499955 110627043212391 1 124393566850875.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 110627043212391 1 124393566850875))]. Qed.
