From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 10307921510400 to 10445360463872 *)
Lemma J0075 : job_ok 137438953472 16286286016529 1 30099362599545 42275565450369 1 4728558568247.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 42275565450369 1 4728558568247))]. Qed.
