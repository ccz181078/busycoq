From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 63496796504064 to 63634235457536 *)
Lemma J0462 : job_ok 137438953472 35053933291170 2 250681649259417 190739342413458 2 95614716055943.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 190739342413458 2 95614716055943))]. Qed.
