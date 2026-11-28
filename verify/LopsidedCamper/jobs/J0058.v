From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 7971459301376 to 8108898254848 *)
Lemma J0058 : job_ok 137438953472 13465758121271 1 22405807155856 34226778534378 2 2263261525349.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 34226778534378 2 2263261525349))]. Qed.
