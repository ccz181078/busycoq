From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 66657892433920 to 66795331387392 *)
Lemma J0485 : job_ok 137438953472 85271645091986 2 214688873335903 13014722264090 2 287564271297420.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 13014722264090 2 287564271297420))]. Qed.
