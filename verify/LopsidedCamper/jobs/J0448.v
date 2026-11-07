From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 61572651155456 to 61710090108928 *)
Lemma J0448 : job_ok 137438953472 125004076657759 1 152072851496795 220118247816391 1 57577156132857.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 220118247816391 1 57577156132857))]. Qed.
