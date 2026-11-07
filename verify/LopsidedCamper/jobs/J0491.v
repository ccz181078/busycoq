From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 67482526154752 to 67619965108224 *)
Lemma J0491 : job_ok 137438953472 52128217791344 2 251543151412153 240691931244781 1 63597913368406.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 240691931244781 1 63597913368406))]. Qed.
