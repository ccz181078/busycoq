From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 3023656976384 to 3161095929856 *)
Lemma J0022 : job_ok 137438953472 12361691234498 2 1244765571946 3819878392953 1 10405053971019.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 3819878392953 1 10405053971019))]. Qed.
