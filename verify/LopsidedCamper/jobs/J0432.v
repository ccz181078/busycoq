From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 59373627899904 to 59511066853376 *)
Lemma J0432 : job_ok 137438953472 97407226558929 1 169774096990617 175188729385640 2 92611069264745.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 175188729385640 2 92611069264745))]. Qed.
