From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 39719857553408 to 39857296506880 *)
Lemma J0289 : job_ok 137438953472 135482108016577 1 43257246812413 159201521332895 1 20156308744988.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 159201521332895 1 20156308744988))]. Qed.
