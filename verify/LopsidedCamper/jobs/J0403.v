From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 55387898249216 to 55525337202688 *)
Lemma J0403 : job_ok 137438953472 40683433518141 1 208562110277861 121320331184975 1 128543687174916.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 121320331184975 1 128543687174916))]. Qed.
