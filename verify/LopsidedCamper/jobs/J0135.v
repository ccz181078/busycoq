From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 18554258718720 to 18691697672192 *)
Lemma J0135 : job_ok 137438953472 4352944840290 2 79141220709622 72802621540043 1 11310018719530.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 72802621540043 1 11310018719530))]. Qed.
