From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 16355235463168 to 16492674416640 *)
Lemma J0119 : job_ok 137438953472 63696777417981 1 9901782639765 56627665012689 1 17589371133425.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 56627665012689 1 17589371133425))]. Qed.
