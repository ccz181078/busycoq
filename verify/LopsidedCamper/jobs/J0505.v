From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 69406671503360 to 69544110456832 *)
Lemma J0505 : job_ok 137438953472 280593979825135 1 31736043064789 107952239176849 1 204996259319945.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 107952239176849 1 204996259319945))]. Qed.
