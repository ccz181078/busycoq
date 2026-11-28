From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 4535485464576 to 4672924418048 *)
Lemma J0033 : job_ok 137438953472 6686185365211 1 13723497675247 6344292002701 1 14683866701432.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 6344292002701 1 14683866701432))]. Qed.
