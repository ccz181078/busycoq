From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 33397665693696 to 33535104647168 *)
Lemma J0243 : job_ok 137438953472 37379195397791 1 112910295159478 95317609668159 1 55590355614261.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 95317609668159 1 55590355614261))]. Qed.
