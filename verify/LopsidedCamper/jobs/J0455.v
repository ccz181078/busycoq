From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 62534723829760 to 62672162783232 *)
Lemma J0455 : job_ok 137438953472 5396198400719 1 276010056587490 276457980030683 1 5566749848751.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 276457980030683 1 5566749848751))]. Qed.
