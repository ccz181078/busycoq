From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 45767171506176 to 45904610459648 *)
Lemma J0333 : job_ok 137438953472 102945899875034 2 103006368809786 129921924606509 1 76648820594296.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 129921924606509 1 76648820594296))]. Qed.
