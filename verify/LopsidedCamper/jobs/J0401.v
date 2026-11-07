From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 55113020342272 to 55250459295744 *)
Lemma J0401 : job_ok 137438953472 62544637580197 1 185463954834552 204593034069936 2 44034033745364.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 204593034069936 2 44034033745364))]. Qed.
