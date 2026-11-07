From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 43843026157568 to 43980465111040 *)
Lemma J0319 : job_ok 137438953472 32828397975213 1 164465215845414 18410891047881 1 179501198003043.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 18410891047881 1 179501198003043))]. Qed.
