From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 56899726737408 to 57037165690880 *)
Lemma J0414 : job_ok 137438953472 134082567316737 1 121966202497973 104091641596825 1 152575603242863.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 104091641596825 1 152575603242863))]. Qed.
