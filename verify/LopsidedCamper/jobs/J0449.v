From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 61710090108928 to 61847529062400 *)
Lemma J0449 : job_ok 137438953472 220118247816391 1 57577156132857 242909516643911 1 35404362222116.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 242909516643911 1 35404362222116))]. Qed.
