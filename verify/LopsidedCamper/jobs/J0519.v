From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 71330816851968 to 71468255805440 *)
Lemma J0519 : job_ok 137438953472 145444844338170 2 175543831390441 184476995359834 2 137130154855298.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 184476995359834 2 137130154855298))]. Qed.
