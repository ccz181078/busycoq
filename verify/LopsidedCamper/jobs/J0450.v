From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 61847529062400 to 61984968015872 *)
Lemma J0450 : job_ok 137438953472 242909516643911 1 35404362222116 186782125060241 1 92150229240888.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 186782125060241 1 92150229240888))]. Qed.
