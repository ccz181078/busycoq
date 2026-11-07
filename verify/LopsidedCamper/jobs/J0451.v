From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 61984968015872 to 62122406969344 *)
Lemma J0451 : job_ok 137438953472 186782125060241 1 92150229240888 87319272744816 2 192231556448143.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 87319272744816 2 192231556448143))]. Qed.
