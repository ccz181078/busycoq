From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 45904610459648 to 46042049413120 *)
Lemma J0334 : job_ok 137438953472 129921924606509 1 76648820594296 81643096375696 2 125546124443736.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 81643096375696 2 125546124443736))]. Qed.
