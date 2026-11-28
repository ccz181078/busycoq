From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 9070970929152 to 9208409882624 *)
Lemma J0066 : job_ok 137438953472 14939783912733 1 25879583989538 38105758580106 2 3332085299063.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 38105758580106 2 3332085299063))]. Qed.
