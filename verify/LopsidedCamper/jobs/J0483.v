From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 66383014526976 to 66520453480448 *)
Lemma J0483 : job_ok 137438953472 34393888948055 1 264329678223661 98624971725858 2 200717071125050.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 98624971725858 2 200717071125050))]. Qed.
