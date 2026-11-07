From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 19241453486080 to 19378892439552 *)
Lemma J0140 : job_ok 137438953472 17059370706867 1 69527170574680 57292289313407 1 29912727227200.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 57292289313407 1 29912727227200))]. Qed.
