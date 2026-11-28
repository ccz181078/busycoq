From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 19516331393024 to 19653770346496 *)
Lemma J0142 : job_ok 137438953472 17669107348162 2 70154383651450 25597071468255 1 62844894192093.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 25597071468255 1 62844894192093))]. Qed.
