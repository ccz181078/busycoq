From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 37933151158272 to 38070590111744 *)
Lemma J0276 : job_ok 137438953472 8765802088265 1 161933373379955 53984199125064 2 117333451510000.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 53984199125064 2 117333451510000))]. Qed.
