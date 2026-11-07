From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 66795331387392 to 66932770340864 *)
Lemma J0486 : job_ok 137438953472 13014722264090 2 287564271297420 51718901289314 2 249478567613765.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 51718901289314 2 249478567613765))]. Qed.
