From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 56212531970048 to 56349970923520 *)
Lemma J0409 : job_ok 137438953472 197944139364394 2 55012255081263 10142856136567 1 243432013170067.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 10142856136567 1 243432013170067))]. Qed.
