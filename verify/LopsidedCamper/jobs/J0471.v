From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 64733747085312 to 64871186038784 *)
Lemma J0471 : job_ok 137438953472 264870184648485 1 26431676246443 226904077791639 1 65016259321487.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 226904077791639 1 65016259321487))]. Qed.
