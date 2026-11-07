From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 4810363371520 to 4947802324992 *)
Lemma J0035 : job_ok 137438953472 9000666487255 1 12645967532692 4072769283529 1 18192340233611.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 4072769283529 1 18192340233611))]. Qed.
