From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 68582037782528 to 68719476736000 *)
Lemma J0499 : job_ok 137438953472 216546965671067 1 92072205075949 198301674575243 1 110935971649129.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 198301674575243 1 110935971649129))]. Qed.
