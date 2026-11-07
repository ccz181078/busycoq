From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 35871566856192 to 36009005809664 *)
Lemma J0261 : job_ok 137438953472 104011703059120 2 57410343429002 44945938629171 1 117094583344234.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 44945938629171 1 117094583344234))]. Qed.
