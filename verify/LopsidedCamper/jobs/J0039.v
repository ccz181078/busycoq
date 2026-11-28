From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 5360119185408 to 5497558138880 *)
Lemma J0039 : job_ok 137438953472 13669813533650 2 10450721723678 10916345146059 1 13822664752975.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 10916345146059 1 13822664752975))]. Qed.
