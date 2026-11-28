From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 58411555225600 to 58548994179072 *)
Lemma J0425 : job_ok 137438953472 230369203160687 1 32482794432617 136773916463939 1 126696555808070.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 136773916463939 1 126696555808070))]. Qed.
