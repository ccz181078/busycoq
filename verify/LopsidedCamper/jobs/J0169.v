From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 23227183136768 to 23364622090240 *)
Lemma J0169 : job_ok 137438953472 89035407501901 1 15486912470724 63464919785947 1 41675875707067.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 63464919785947 1 41675875707067))]. Qed.
