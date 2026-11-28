From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 2886218022912 to 3023656976384 *)
Lemma J0021 : job_ok 137438953472 10947268209697 1 2040713695477 12361691234498 2 1244765571946.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 12361691234498 2 1244765571946))]. Qed.
