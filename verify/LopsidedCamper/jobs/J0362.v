From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 49752901156864 to 49890340110336 *)
Lemma J0362 : job_ok 137438953472 205218094625079 1 18669961130720 16822873632247 1 207683658179308.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 16822873632247 1 207683658179308))]. Qed.
