From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 59648505806848 to 59785944760320 *)
Lemma J0434 : job_ok 137438953472 98400826473882 2 170017447583840 161333069957205 1 107703679347780.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 161333069957205 1 107703679347780))]. Qed.
