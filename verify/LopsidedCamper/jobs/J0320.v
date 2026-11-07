From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 43980465111040 to 44117904064512 *)
Lemma J0320 : job_ok 137438953472 18410891047881 1 179501198003043 196975474721705 1 1555089959963.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 196975474721705 1 1555089959963))]. Qed.
