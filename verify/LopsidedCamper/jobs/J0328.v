From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 45079976738816 to 45217415692288 *)
Lemma J0328 : job_ok 137438953472 31035715341633 1 171824178093637 63015185410267 1 140463182824222.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 63015185410267 1 140463182824222))]. Qed.
