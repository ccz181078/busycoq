From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 20203526160384 to 20340965113856 *)
Lemma J0147 : job_ok 137438953472 79227738566579 1 11688126762401 53534525208562 2 37999815180223.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 53534525208562 2 37999815180223))]. Qed.
