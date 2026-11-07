From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 31610959298560 to 31748398252032 *)
Lemma J0230 : job_ok 137438953472 14692580597373 1 127556731473756 91286196057567 1 51581591044073.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 91286196057567 1 51581591044073))]. Qed.
