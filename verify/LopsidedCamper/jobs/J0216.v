From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 29686813949952 to 29824252903424 *)
Lemma J0216 : job_ok 137438953472 9872080931219 1 123718576938136 79706055818195 1 54503077200220.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 79706055818195 1 54503077200220))]. Qed.
