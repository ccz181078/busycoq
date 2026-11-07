From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 44117904064512 to 44255343017984 *)
Lemma J0321 : job_ok 137438953472 196975474721705 1 1555089959963 79156782454896 2 119992256805897.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 79156782454896 2 119992256805897))]. Qed.
