From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 19928648253440 to 20066087206912 *)
Lemma J0145 : job_ok 137438953472 67209670429149 1 22469244511018 74118795152539 1 16178594439862.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 74118795152539 1 16178594439862))]. Qed.
