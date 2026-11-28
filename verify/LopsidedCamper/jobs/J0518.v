From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 71193377898496 to 71330816851968 *)
Lemma J0518 : job_ok 137438953472 184213800276771 1 136156399561455 145444844338170 2 175543831390441.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 145444844338170 2 175543831390441))]. Qed.
