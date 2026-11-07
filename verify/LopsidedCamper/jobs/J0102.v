From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 14018773254144 to 14156212207616 *)
Lemma J0102 : job_ok 137438953472 39173722102849 1 23910756799093 52717077215771 1 10985877653859.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 52717077215771 1 10985877653859))]. Qed.
