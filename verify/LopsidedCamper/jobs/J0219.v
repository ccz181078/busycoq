From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 30099130810368 to 30236569763840 *)
Lemma J0219 : job_ok 137438953472 114679469044331 1 20766615475911 43336058476805 1 92728501320786.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 43336058476805 1 92728501320786))]. Qed.
