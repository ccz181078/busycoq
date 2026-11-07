From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 31061203484672 to 31198642438144 *)
Lemma J0226 : job_ok 137438953472 50321617094393 1 89453794534918 16297459075495 1 124096427697025.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 16297459075495 1 124096427697025))]. Qed.
