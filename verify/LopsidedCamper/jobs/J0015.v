From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 2061584302080 to 2199023255552 *)
Lemma J0015 : job_ok 137438953472 469485035986 2 8807643944623 3615483462207 1 6280121028490.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 3615483462207 1 6280121028490))]. Qed.
