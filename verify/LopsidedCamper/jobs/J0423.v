From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 58136677318656 to 58274116272128 *)
Lemma J0423 : job_ok 137438953472 95928092123501 1 165686954720249 98024603783443 1 164208918130020.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 98024603783443 1 164208918130020))]. Qed.
