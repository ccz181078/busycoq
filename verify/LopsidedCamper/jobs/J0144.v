From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 19791209299968 to 19928648253440 *)
Lemma J0144 : job_ok 137438953472 82927055448418 2 6133384680109 67209670429149 1 22469244511018.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 67209670429149 1 22469244511018))]. Qed.
