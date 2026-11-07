From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 33260226740224 to 33397665693696 *)
Lemma J0242 : job_ok 137438953472 103820239114517 1 45850776679104 37379195397791 1 112910295159478.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 37379195397791 1 112910295159478))]. Qed.
