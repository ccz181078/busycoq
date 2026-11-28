From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 53876069761024 to 54013508714496 *)
Lemma J0392 : job_ok 137438953472 104684409352583 1 137757903931868 228931290095258 2 14129499258536.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 228931290095258 2 14129499258536))]. Qed.
