From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 50577534877696 to 50714973831168 *)
Lemma J0368 : job_ok 137438953472 121175914208889 1 106422993471025 196523086226047 1 31694297285635.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 196523086226047 1 31694297285635))]. Qed.
