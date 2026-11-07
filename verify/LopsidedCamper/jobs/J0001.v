From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 137438953472 to 274877906944 *)
Lemma J0001 : job_ok 137438953472 349018790754 2 269456661313 828590691805 1 408359980468.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 828590691805 1 408359980468))]. Qed.
