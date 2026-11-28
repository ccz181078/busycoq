From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 48653389529088 to 48790828482560 *)
Lemma J0354 : job_ok 137438953472 160836789009839 1 58103462760537 127679689334815 1 91879037773048.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 127679689334815 1 91879037773048))]. Qed.
