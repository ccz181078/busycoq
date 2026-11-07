From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 17592186044416 to 17729624997888 *)
Lemma J0128 : job_ok 137438953472 33420733410683 1 45744106089963 10438777548514 2 69344537282923.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 10438777548514 2 69344537282923))]. Qed.
