From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 6047313952768 to 6184752906240 *)
Lemma J0044 : job_ok 137438953472 26396582699208 2 816327845789 16454123545265 1 11377261991905.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 16454123545265 1 11377261991905))]. Qed.
