From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 62947040690176 to 63084479643648 *)
Lemma J0458 : job_ok 137438953472 73681771729466 2 209579909167914 275384654460963 1 8495501951593.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 275384654460963 1 8495501951593))]. Qed.
