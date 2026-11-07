From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 57999238365184 to 58136677318656 *)
Lemma J0422 : job_ok 137438953472 260154287193744 2 842284728423 95928092123501 1 165686954720249.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 95928092123501 1 165686954720249))]. Qed.
