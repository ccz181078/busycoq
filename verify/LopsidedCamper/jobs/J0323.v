From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 44392781971456 to 44530220924928 *)
Lemma J0323 : job_ok 137438953472 36708547886914 2 163058967738555 99909078800547 1 100476911880268.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 99909078800547 1 100476911880268))]. Qed.
