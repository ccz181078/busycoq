From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 16492674416640 to 16630113370112 *)
Lemma J0120 : job_ok 137438953472 56627665012689 1 17589371133425 54911156144929 1 19924355671475.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 54911156144929 1 19924355671475))]. Qed.
