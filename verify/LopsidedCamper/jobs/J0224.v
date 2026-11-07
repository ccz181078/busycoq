From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 30786325577728 to 30923764531200 *)
Lemma J0224 : job_ok 137438953472 126829215019581 1 11709245927250 84597103281194 2 54559833232719.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 84597103281194 2 54559833232719))]. Qed.
