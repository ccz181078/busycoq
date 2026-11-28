From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 49615462203392 to 49752901156864 *)
Lemma J0361 : job_ok 137438953472 153287018754627 1 69982561075156 205218094625079 1 18669961130720.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 205218094625079 1 18669961130720))]. Qed.
