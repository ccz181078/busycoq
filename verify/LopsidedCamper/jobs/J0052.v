From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 7146825580544 to 7284264534016 *)
Lemma J0052 : job_ok 137438953472 9893546954768 2 22267164827984 9935984435947 1 22843203368000.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 9935984435947 1 22843203368000))]. Qed.
