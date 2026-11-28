From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 36009005809664 to 36146444763136 *)
Lemma J0262 : job_ok 137438953472 44945938629171 1 117094583344234 47045335765813 1 115613660644360.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 47045335765813 1 115613660644360))]. Qed.
