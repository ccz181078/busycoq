From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 3161095929856 to 3298534883328 *)
Lemma J0023 : job_ok 137438953472 3819878392953 1 10405053971019 7224124137629 1 7619283053996.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 7224124137629 1 7619283053996))]. Qed.
