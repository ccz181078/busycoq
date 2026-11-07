From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 64596308131840 to 64733747085312 *)
Lemma J0470 : job_ok 137438953472 247780565415402 2 42902820325917 264870184648485 1 26431676246443.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 264870184648485 1 26431676246443))]. Qed.
