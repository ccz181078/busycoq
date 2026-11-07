From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 10995116277760 to 11132555231232 *)
Lemma J0080 : job_ok 137438953472 33438437326301 1 16039588091542 46572961021329 1 3523539948021.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 46572961021329 1 3523539948021))]. Qed.
