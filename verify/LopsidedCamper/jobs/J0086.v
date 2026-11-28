From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 11819749998592 to 11957188952064 *)
Lemma J0086 : job_ok 137438953472 29006413437003 1 24182463054403 32125163133123 1 21682188822828.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 32125163133123 1 21682188822828))]. Qed.
