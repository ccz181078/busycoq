From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 6459630813184 to 6597069766656 *)
Lemma J0047 : job_ok 137438953472 11738310889751 1 17330024875731 18565310764034 2 11121499612095.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 18565310764034 2 11121499612095))]. Qed.
