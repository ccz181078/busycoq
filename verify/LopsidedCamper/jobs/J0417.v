From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 57312043597824 to 57449482551296 *)
Lemma J0417 : job_ok 137438953472 173197623546999 1 84706571250144 165435818822517 1 93086852302422.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 165435818822517 1 93086852302422))]. Qed.
