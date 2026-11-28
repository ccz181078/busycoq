From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 19104014532608 to 19241453486080 *)
Lemma J0139 : job_ok 137438953472 42309958869297 1 43658107431859 17059370706867 1 69527170574680.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 17059370706867 1 69527170574680))]. Qed.
