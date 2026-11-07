From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 55250459295744 to 55387898249216 *)
Lemma J0402 : job_ok 137438953472 204593034069936 2 44034033745364 40683433518141 1 208562110277861.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 40683433518141 1 208562110277861))]. Qed.
