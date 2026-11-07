From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 26250840113152 to 26388279066624 *)
Lemma J0191 : job_ok 137438953472 39741460473890 2 78387316580293 42734894837603 1 76012357030938.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 42734894837603 1 76012357030938))]. Qed.
