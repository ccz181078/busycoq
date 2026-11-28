From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 24601572671488 to 24739011624960 *)
Lemma J0179 : job_ok 137438953472 8031222374365 1 102675851440278 7705474686322 2 103620074559906.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 7705474686322 2 103620074559906))]. Qed.
