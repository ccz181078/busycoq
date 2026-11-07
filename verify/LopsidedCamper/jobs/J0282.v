From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 38757784879104 to 38895223832576 *)
Lemma J0282 : job_ok 137438953472 83308863784921 1 91101161633365 98729100798861 1 76299400561714.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 98729100798861 1 76299400561714))]. Qed.
