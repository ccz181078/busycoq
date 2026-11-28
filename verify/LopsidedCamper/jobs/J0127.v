From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 17454747090944 to 17592186044416 *)
Lemma J0127 : job_ok 137438953472 48162755389127 1 30383608642809 33420733410683 1 45744106089963.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 33420733410683 1 45744106089963))]. Qed.
