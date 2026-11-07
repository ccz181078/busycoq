From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 9758165696512 to 9895604649984 *)
Lemma J0071 : job_ok 137438953472 5735564395635 1 38176181745512 2947032382169 1 41583189320779.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 2947032382169 1 41583189320779))]. Qed.
