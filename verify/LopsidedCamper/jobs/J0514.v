From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 70643622084608 to 70781061038080 *)
Lemma J0514 : job_ok 137438953472 317560596933626 2 335702917754 164139818268527 1 154374956809630.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 164139818268527 1 154374956809630))]. Qed.
