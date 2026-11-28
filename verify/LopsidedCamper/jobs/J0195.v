From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 26800595927040 to 26938034880512 *)
Lemma J0195 : job_ok 137438953472 31631949550351 1 88970729167273 10616616787159 1 110604536799978.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 10616616787159 1 110604536799978))]. Qed.
