From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 2473901162496 to 2611340115968 *)
Lemma J0018 : job_ok 137438953472 3975268304025 1 7157287172457 529329021242 2 11221702170606.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 529329021242 2 11221702170606))]. Qed.
