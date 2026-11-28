From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 4260607557632 to 4398046511104 *)
Lemma J0031 : job_ok 137438953472 12202592116683 1 6970141175305 4788353513863 1 15002854670219.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 4788353513863 1 15002854670219))]. Qed.
