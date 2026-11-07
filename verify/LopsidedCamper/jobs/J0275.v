From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 37795712204800 to 37933151158272 *)
Lemma J0275 : job_ok 137438953472 64717795511333 1 105362904298378 8765802088265 1 161933373379955.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 8765802088265 1 161933373379955))]. Qed.
