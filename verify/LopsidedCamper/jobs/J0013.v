From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 1786706395136 to 1924145348608 *)
Lemma J0013 : job_ok 137438953472 4517005138283 1 3523173390350 1948522853711 1 6710130740078.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 1948522853711 1 6710130740078))]. Qed.
