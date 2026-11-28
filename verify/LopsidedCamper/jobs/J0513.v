From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 70506183131136 to 70643622084608 *)
Lemma J0513 : job_ok 137438953472 31825887802191 1 285451937518684 317560596933626 2 335702917754.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 317560596933626 2 335702917754))]. Qed.
