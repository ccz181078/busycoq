From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 6184752906240 to 6322191859712 *)
Lemma J0045 : job_ok 137438953472 16454123545265 1 11377261991905 1156589690869 1 27293270574670.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 1156589690869 1 27293270574670))]. Qed.
