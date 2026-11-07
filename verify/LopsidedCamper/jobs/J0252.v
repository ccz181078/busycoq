From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 34634616274944 to 34772055228416 *)
Lemma J0252 : job_ok 137438953472 70026155559739 1 85829612217805 5148675474675 1 151325568405826.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 5148675474675 1 151325568405826))]. Qed.
