From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 49340584296448 to 49478023249920 *)
Lemma J0359 : job_ok 137438953472 188861791031082 2 33170838070337 106249268933205 1 116401835585312.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 106249268933205 1 116401835585312))]. Qed.
