From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 48790828482560 to 48928267436032 *)
Lemma J0355 : job_ok 137438953472 127679689334815 1 91879037773048 202119344408197 1 18057858207212.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 202119344408197 1 18057858207212))]. Qed.
