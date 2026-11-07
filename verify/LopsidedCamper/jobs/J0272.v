From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 37383395344384 to 37520834297856 *)
Lemma J0272 : job_ok 137438953472 77610000526501 1 90615274162731 3154745360290 2 165689004043033.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 3154745360290 2 165689004043033))]. Qed.
