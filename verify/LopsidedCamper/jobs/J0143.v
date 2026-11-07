From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 19653770346496 to 19791209299968 *)
Lemma J0143 : job_ok 137438953472 25597071468255 1 62844894192093 82927055448418 2 6133384680109.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 82927055448418 2 6133384680109))]. Qed.
