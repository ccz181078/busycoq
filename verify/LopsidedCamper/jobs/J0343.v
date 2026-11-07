From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 47141561040896 to 47278999994368 *)
Lemma J0343 : job_ok 137438953472 43714141988643 1 168422881102338 22035522524667 1 190719976845131.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 22035522524667 1 190719976845131))]. Qed.
