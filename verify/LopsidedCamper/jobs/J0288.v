From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 39582418599936 to 39719857553408 *)
Lemma J0288 : job_ok 137438953472 107232449416337 1 70888430699177 135482108016577 1 43257246812413.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 135482108016577 1 43257246812413))]. Qed.
