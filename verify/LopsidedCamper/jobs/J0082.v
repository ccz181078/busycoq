From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 11269994184704 to 11407433138176 *)
Lemma J0082 : job_ok 137438953472 31506128153203 1 19208847697131 8789443491657 1 42544007590259.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 8789443491657 1 42544007590259))]. Qed.
