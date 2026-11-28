From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 67345087201280 to 67482526154752 *)
Lemma J0490 : job_ok 137438953472 273948178006133 1 29104715965538 52128217791344 2 251543151412153.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 52128217791344 2 251543151412153))]. Qed.
