From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 60335700574208 to 60473139527680 *)
Lemma J0439 : job_ok 137438953472 94070634611547 1 177440015494288 142909450460015 1 129219674874381.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 142909450460015 1 129219674874381))]. Qed.
