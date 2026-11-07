From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 44942537785344 to 45079976738816 *)
Lemma J0327 : job_ok 137438953472 30182298244944 2 172059119784062 31035715341633 1 171824178093637.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 31035715341633 1 171824178093637))]. Qed.
