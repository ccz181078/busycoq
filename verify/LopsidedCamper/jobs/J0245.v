From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 33672543600640 to 33809982554112 *)
Lemma J0245 : job_ok 137438953472 119366428565658 2 32160012269054 99186430904634 2 52958484384276.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 99186430904634 2 52958484384276))]. Qed.
