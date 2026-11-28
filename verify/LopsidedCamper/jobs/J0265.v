From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 36421322670080 to 36558761623552 *)
Lemma J0265 : job_ok 137438953472 87985238511051 1 75910708462499 8680128813594 2 155834293235858.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 8680128813594 2 155834293235858))]. Qed.
