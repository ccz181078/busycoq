From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 55937654063104 to 56075093016576 *)
Lemma J0407 : job_ok 137438953472 160180493458707 1 91538951013543 171021176655210 2 81316742943691.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 171021176655210 2 81316742943691))]. Qed.
