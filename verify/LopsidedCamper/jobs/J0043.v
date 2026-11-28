From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 5909874999296 to 6047313952768 *)
Lemma J0043 : job_ok 137438953472 13754716583843 1 12839718978107 26396582699208 2 816327845789.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 26396582699208 2 816327845789))]. Qed.
