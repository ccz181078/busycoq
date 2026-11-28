From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 12506944765952 to 12644383719424 *)
Lemma J0091 : job_ok 137438953472 24776919233895 1 31504333427335 11606372338535 1 45293355392788.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 11606372338535 1 45293355392788))]. Qed.
