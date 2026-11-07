From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 21165598834688 to 21303037788160 *)
Lemma J0154 : job_ok 137438953472 49065254522002 2 46179935928375 49178374257887 1 46685291041485.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 49178374257887 1 46685291041485))]. Qed.
