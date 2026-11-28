From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 14156212207616 to 14293651161088 *)
Lemma J0103 : job_ok 137438953472 52717077215771 1 10985877653859 15074218720362 2 49247211009724.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 15074218720362 2 49247211009724))]. Qed.
