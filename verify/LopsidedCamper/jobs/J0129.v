From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 17729624997888 to 17867063951360 *)
Lemma J0129 : job_ok 137438953472 10438777548514 2 69344537282923 46581161445776 2 33820628704890.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 46581161445776 2 33820628704890))]. Qed.
