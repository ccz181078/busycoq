From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 15942918602752 to 16080357556224 *)
Lemma J0116 : job_ok 137438953472 16455873889954 2 55287260110081 16879327626807 1 55482282105010.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 16879327626807 1 55482282105010))]. Qed.
