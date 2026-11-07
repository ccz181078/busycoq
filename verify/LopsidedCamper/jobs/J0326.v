From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 44805098831872 to 44942537785344 *)
Lemma J0326 : job_ok 137438953472 166603447928525 1 35019494463032 30182298244944 2 172059119784062.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 30182298244944 2 172059119784062))]. Qed.
