From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 69956427317248 to 70093866270720 *)
Lemma J0509 : job_ok 137438953472 308059140793915 1 6744783585304 185158256960187 1 130264142257912.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 185158256960187 1 130264142257912))]. Qed.
