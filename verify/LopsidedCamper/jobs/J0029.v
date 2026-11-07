From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 3985729650688 to 4123168604160 *)
Lemma J0029 : job_ok 137438953472 4039513774371 1 13896269395025 11436468006043 1 7117790191295.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 11436468006043 1 7117790191295))]. Qed.
