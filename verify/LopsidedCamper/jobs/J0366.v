From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 50302656970752 to 50440095924224 *)
Lemma J0366 : job_ok 137438953472 69059756916757 1 157302200034095 62449277073722 2 164531155158450.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 62449277073722 2 164531155158450))]. Qed.
