From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 66520453480448 to 66657892433920 *)
Lemma J0484 : job_ok 137438953472 98624971725858 2 200717071125050 85271645091986 2 214688873335903.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 85271645091986 2 214688873335903))]. Qed.
