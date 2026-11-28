From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 61435212201984 to 61572651155456 *)
Lemma J0447 : job_ok 137438953472 195062373769011 1 81396078705000 125004076657759 1 152072851496795.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 125004076657759 1 152072851496795))]. Qed.
