From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 62122406969344 to 62259845922816 *)
Lemma J0452 : job_ok 137438953472 87319272744816 2 192231556448143 256002824011346 2 24166480990729.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 256002824011346 2 24166480990729))]. Qed.
