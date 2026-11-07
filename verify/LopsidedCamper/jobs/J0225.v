From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 30923764531200 to 31061203484672 *)
Lemma J0225 : job_ok 137438953472 84597103281194 2 54559833232719 50321617094393 1 89453794534918.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 50321617094393 1 89453794534918))]. Qed.
