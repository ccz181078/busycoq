From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 45629732552704 to 45767171506176 *)
Lemma J0332 : job_ok 137438953472 192735764429885 1 12598029179768 102945899875034 2 103006368809786.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 102945899875034 2 103006368809786))]. Qed.
