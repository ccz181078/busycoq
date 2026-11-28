From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 9345848836096 to 9483287789568 *)
Lemma J0068 : job_ok 137438953472 11235848623191 1 30820470968979 41017063204605 1 1657731458899.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 41017063204605 1 1657731458899))]. Qed.
