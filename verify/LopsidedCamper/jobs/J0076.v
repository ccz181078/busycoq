From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 10445360463872 to 10582799417344 *)
Lemma J0076 : job_ok 137438953472 42275565450369 1 4728558568247 13205903124803 1 34416696810884.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 13205903124803 1 34416696810884))]. Qed.
