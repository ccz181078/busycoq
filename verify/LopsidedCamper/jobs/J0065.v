From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 8933531975680 to 9070970929152 *)
Lemma J0065 : job_ok 137438953472 8695204894757 1 31505687138762 14939783912733 1 25879583989538.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 14939783912733 1 25879583989538))]. Qed.
