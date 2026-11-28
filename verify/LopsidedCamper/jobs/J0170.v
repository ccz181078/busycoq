From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 23364622090240 to 23502061043712 *)
Lemma J0170 : job_ok 137438953472 63464919785947 1 41675875707067 90633769333928 2 15125500936220.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 90633769333928 2 15125500936220))]. Qed.
