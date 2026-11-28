From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 52776558133248 to 52913997086720 *)
Lemma J0384 : job_ok 137438953472 214734354057607 1 22760157813912 173290161130451 1 64822825678224.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 173290161130451 1 64822825678224))]. Qed.
