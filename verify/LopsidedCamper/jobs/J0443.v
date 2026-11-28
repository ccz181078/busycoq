From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 60885456388096 to 61022895341568 *)
Lemma J0443 : job_ok 137438953472 186619213529093 1 87365336535708 167781528154162 2 106821498464633.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 167781528154162 2 106821498464633))]. Qed.
