From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 17317308137472 to 17454747090944 *)
Lemma J0126 : job_ok 137438953472 26913461999312 2 51014426362683 48162755389127 1 30383608642809.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 48162755389127 1 30383608642809))]. Qed.
