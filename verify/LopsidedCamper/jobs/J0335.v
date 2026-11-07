From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 46042049413120 to 46179488366592 *)
Lemma J0335 : job_ok 137438953472 81643096375696 2 125546124443736 20636839707083 1 187170856803031.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 20636839707083 1 187170856803031))]. Qed.
