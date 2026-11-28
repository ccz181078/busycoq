From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 4947802324992 to 5085241278464 *)
Lemma J0036 : job_ok 137438953472 4072769283529 1 18192340233611 10092748123427 1 12790836975444.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 10092748123427 1 12790836975444))]. Qed.
