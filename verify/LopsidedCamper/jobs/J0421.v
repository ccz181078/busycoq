From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 57861799411712 to 57999238365184 *)
Lemma J0421 : job_ok 137438953472 117681097437993 1 142696999725499 260154287193744 2 842284728423.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 260154287193744 2 842284728423))]. Qed.
