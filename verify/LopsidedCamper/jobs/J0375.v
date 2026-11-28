From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 51539607552000 to 51677046505472 *)
Lemma J0375 : job_ok 137438953472 98738836646682 2 133189398700567 26586924014147 1 205959786735254.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 26586924014147 1 205959786735254))]. Qed.
