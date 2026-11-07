From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 25013889531904 to 25151328485376 *)
Lemma J0182 : job_ok 137438953472 19153353355135 1 93409146569337 88775042228159 1 24405932697941.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 88775042228159 1 24405932697941))]. Qed.
