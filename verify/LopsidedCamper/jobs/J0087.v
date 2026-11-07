From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 11957188952064 to 12094627905536 *)
Lemma J0087 : job_ok 137438953472 32125163133123 1 21682188822828 5704451007373 1 48721375934753.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 5704451007373 1 48721375934753))]. Qed.
