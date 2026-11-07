From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 2611340115968 to 2748779069440 *)
Lemma J0019 : job_ok 137438953472 529329021242 2 11221702170606 8273418736899 1 4096087886541.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 8273418736899 1 4096087886541))]. Qed.
