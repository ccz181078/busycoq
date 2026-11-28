From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 14293651161088 to 14431090114560 *)
Lemma J0104 : job_ok 137438953472 15074218720362 2 49247211009724 20892215592629 1 44047689547280.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 20892215592629 1 44047689547280))]. Qed.
