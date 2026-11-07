From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 15805479649280 to 15942918602752 *)
Lemma J0115 : job_ok 137438953472 57419390152783 1 13705267844927 16455873889954 2 55287260110081.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 16455873889954 2 55287260110081))]. Qed.
