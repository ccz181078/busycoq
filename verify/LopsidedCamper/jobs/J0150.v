From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 20615843020800 to 20753281974272 *)
Lemma J0150 : job_ok 137438953472 3929904546993 1 88841386049912 44824171546827 1 48565594275265.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 44824171546827 1 48565594275265))]. Qed.
