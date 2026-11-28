From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 33809982554112 to 33947421507584 *)
Lemma J0246 : job_ok 137438953472 99186430904634 2 52958484384276 50811527066346 2 101951863790715.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 50811527066346 2 101951863790715))]. Qed.
