From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 56075093016576 to 56212531970048 *)
Lemma J0408 : job_ok 137438953472 171021176655210 2 81316742943691 197944139364394 2 55012255081263.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 197944139364394 2 55012255081263))]. Qed.
