From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 10857677324288 to 10995116277760 *)
Lemma J0079 : job_ok 137438953472 21888315842951 1 26971233865771 33438437326301 1 16039588091542.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 33438437326301 1 16039588091542))]. Qed.
