From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 24876450578432 to 25013889531904 *)
Lemma J0181 : job_ok 137438953472 103237530090064 2 8706494749328 19153353355135 1 93409146569337.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 19153353355135 1 93409146569337))]. Qed.
