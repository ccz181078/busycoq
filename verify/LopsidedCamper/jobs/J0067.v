From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 9208409882624 to 9345848836096 *)
Lemma J0067 : job_ok 137438953472 38105758580106 2 3332085299063 11235848623191 1 30820470968979.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 11235848623191 1 30820470968979))]. Qed.
