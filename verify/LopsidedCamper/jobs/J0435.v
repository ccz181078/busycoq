From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 59785944760320 to 59923383713792 *)
Lemma J0435 : job_ok 137438953472 161333069957205 1 107703679347780 126155747926089 1 143499476496319.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 126155747926089 1 143499476496319))]. Qed.
