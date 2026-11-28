From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 46591805227008 to 46729244180480 *)
Lemma J0339 : job_ok 137438953472 59195443153437 1 150467678745099 183189748922447 1 27091848107841.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 183189748922447 1 27091848107841))]. Qed.
