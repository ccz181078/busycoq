From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 52639119179776 to 52776558133248 *)
Lemma J0383 : job_ok 137438953472 225422167615395 1 11453868846747 214734354057607 1 22760157813912.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 214734354057607 1 22760157813912))]. Qed.
