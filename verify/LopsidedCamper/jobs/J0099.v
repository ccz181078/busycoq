From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 13606456393728 to 13743895347200 *)
Lemma J0099 : job_ok 137438953472 51132103113317 1 10096950095835 14848419364297 1 46999108962520.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 14848419364297 1 46999108962520))]. Qed.
