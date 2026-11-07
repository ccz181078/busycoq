From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 41918880808960 to 42056319762432 *)
Lemma J0305 : job_ok 137438953472 71709643213381 1 116925316504988 103020149669810 2 86233285669932.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 103020149669810 2 86233285669932))]. Qed.
