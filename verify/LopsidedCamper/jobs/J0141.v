From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 19378892439552 to 19516331393024 *)
Lemma J0141 : job_ok 137438953472 57292289313407 1 29912727227200 17669107348162 2 70154383651450.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 17669107348162 2 70154383651450))]. Qed.
