From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 56349970923520 to 56487409876992 *)
Lemma J0410 : job_ok 137438953472 10142856136567 1 243432013170067 97329537171139 1 156863807074196.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 97329537171139 1 156863807074196))]. Qed.
