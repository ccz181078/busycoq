From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 57037165690880 to 57174604644352 *)
Lemma J0415 : job_ok 137438953472 104091641596825 1 152575603242863 150563805156567 1 106721914672943.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 150563805156567 1 106721914672943))]. Qed.
