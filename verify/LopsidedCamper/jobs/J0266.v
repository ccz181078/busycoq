From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 36558761623552 to 36696200577024 *)
Lemma J0266 : job_ok 137438953472 8680128813594 2 155834293235858 38769273221789 1 126363624098014.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 38769273221789 1 126363624098014))]. Qed.
