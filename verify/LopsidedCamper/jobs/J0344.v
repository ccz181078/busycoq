From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 47278999994368 to 47416438947840 *)
Lemma J0344 : job_ok 137438953472 22035522524667 1 190719976845131 201145901474248 2 12228072866920.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 201145901474248 2 12228072866920))]. Qed.
