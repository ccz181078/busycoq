From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 17867063951360 to 18004502904832 *)
Lemma J0130 : job_ok 137438953472 46581161445776 2 33820628704890 11233496443535 1 69786768958801.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 11233496443535 1 69786768958801))]. Qed.
