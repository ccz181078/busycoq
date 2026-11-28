From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 4398046511104 to 4535485464576 *)
Lemma J0032 : job_ok 137438953472 4788353513863 1 15002854670219 6686185365211 1 13723497675247.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 6686185365211 1 13723497675247))]. Qed.
