From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 38895223832576 to 39032662786048 *)
Lemma J0283 : job_ok 137438953472 98729100798861 1 76299400561714 85343706716762 2 90303270659220.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 85343706716762 2 90303270659220))]. Qed.
