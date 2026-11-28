From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 8108898254848 to 8246337208320 *)
Lemma J0059 : job_ok 137438953472 34226778534378 2 2263261525349 6460627542426 2 30647888168926.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 6460627542426 2 30647888168926))]. Qed.
