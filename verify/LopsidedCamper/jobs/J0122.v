From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 16767552323584 to 16904991277056 *)
Lemma J0122 : job_ok 137438953472 74760902479825 1 693085071501 22722938111043 1 53349524488392.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 22722938111043 1 53349524488392))]. Qed.
