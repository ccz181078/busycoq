From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 65970697666560 to 66108136620032 *)
Lemma J0480 : job_ok 137438953472 142658604989776 2 154209535108615 149327596986983 1 148159018917497.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 149327596986983 1 148159018917497))]. Qed.
