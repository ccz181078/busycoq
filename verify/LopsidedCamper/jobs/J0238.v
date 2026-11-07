From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 32710470926336 to 32847909879808 *)
Lemma J0238 : job_ok 137438953472 137537130179997 1 9659984036508 112917970633521 1 34897618943057.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 112917970633521 1 34897618943057))]. Qed.
