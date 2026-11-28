From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 50989851738112 to 51127290691584 *)
Lemma J0371 : job_ok 137438953472 38409788401803 1 191044545628764 30731438613135 1 199341371358025.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 30731438613135 1 199341371358025))]. Qed.
