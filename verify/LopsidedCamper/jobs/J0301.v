From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 41369124995072 to 41506563948544 *)
Lemma J0301 : job_ok 137438953472 86274871111887 1 99886186049282 8697514351577 1 178082018488615.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 8697514351577 1 178082018488615))]. Qed.
