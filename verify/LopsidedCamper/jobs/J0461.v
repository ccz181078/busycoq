From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 63359357550592 to 63496796504064 *)
Lemma J0461 : job_ok 137438953472 37204526581657 1 247912581067121 35053933291170 2 250681649259417.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 35053933291170 2 250681649259417))]. Qed.
