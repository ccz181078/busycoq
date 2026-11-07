From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 13469017440256 to 13606456393728 *)
Lemma J0098 : job_ok 137438953472 2725728112141 1 57884849605936 51132103113317 1 10096950095835.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 51132103113317 1 10096950095835))]. Qed.
