From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 65833258713088 to 65970697666560 *)
Lemma J0479 : job_ok 137438953472 151297154145355 1 144952510713144 142658604989776 2 154209535108615.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 142658604989776 2 154209535108615))]. Qed.
