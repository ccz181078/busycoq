From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 13881334300672 to 14018773254144 *)
Lemma J0101 : job_ok 137438953472 47910097563130 2 14555905964318 39173722102849 1 23910756799093.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 39173722102849 1 23910756799093))]. Qed.
