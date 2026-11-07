From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 32573031972864 to 32710470926336 *)
Lemma J0237 : job_ok 137438953472 143129244934298 2 3449393729055 137537130179997 1 9659984036508.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 137537130179997 1 9659984036508))]. Qed.
