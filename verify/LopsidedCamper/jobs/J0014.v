From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 1924145348608 to 2061584302080 *)
Lemma J0014 : job_ok 137438953472 1948522853711 1 6710130740078 469485035986 2 8807643944623.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 469485035986 2 8807643944623))]. Qed.
