From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 39857296506880 to 39994735460352 *)
Lemma J0290 : job_ok 137438953472 159201521332895 1 20156308744988 87802124593410 2 92174180719604.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 87802124593410 2 92174180719604))]. Qed.
