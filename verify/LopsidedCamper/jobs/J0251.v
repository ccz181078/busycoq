From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 34497177321472 to 34634616274944 *)
Lemma J0251 : job_ok 137438953472 6613969887799 1 148623322406178 70026155559739 1 85829612217805.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 70026155559739 1 85829612217805))]. Qed.
