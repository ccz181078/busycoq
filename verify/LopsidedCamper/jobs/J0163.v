From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 22402549415936 to 22539988369408 *)
Lemma J0163 : job_ok 137438953472 73107069885858 2 27704399120341 82462532523760 2 18967410947065.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 82462532523760 2 18967410947065))]. Qed.
