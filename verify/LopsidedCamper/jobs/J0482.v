From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 66245575573504 to 66383014526976 *)
Lemma J0482 : job_ok 137438953472 192758943024619 1 105346148329073 34393888948055 1 264329678223661.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 34393888948055 1 264329678223661))]. Qed.
