From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 13743895347200 to 13881334300672 *)
Lemma J0100 : job_ok 137438953472 14848419364297 1 46999108962520 47910097563130 2 14555905964318.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 47910097563130 2 14555905964318))]. Qed.
