From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 60198261620736 to 60335700574208 *)
Lemma J0438 : job_ok 137438953472 159288102618737 1 111604072288083 94070634611547 1 177440015494288.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 94070634611547 1 177440015494288))]. Qed.
