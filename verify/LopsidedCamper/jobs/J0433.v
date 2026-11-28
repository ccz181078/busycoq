From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 59511066853376 to 59648505806848 *)
Lemma J0433 : job_ok 137438953472 175188729385640 2 92611069264745 98400826473882 2 170017447583840.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 98400826473882 2 170017447583840))]. Qed.
