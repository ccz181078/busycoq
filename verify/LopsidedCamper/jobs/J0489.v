From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 67207648247808 to 67345087201280 *)
Lemma J0489 : job_ok 137438953472 259424513729883 1 43009904831109 273948178006133 1 29104715965538.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 273948178006133 1 29104715965538))]. Qed.
