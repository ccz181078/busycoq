From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 58274116272128 to 58411555225600 *)
Lemma J0424 : job_ok 137438953472 98024603783443 1 164208918130020 230369203160687 1 32482794432617.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 230369203160687 1 32482794432617))]. Qed.
