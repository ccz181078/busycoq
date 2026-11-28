From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 45492293599232 to 45629732552704 *)
Lemma J0331 : job_ok 137438953472 68116619149768 2 136598699761096 192735764429885 1 12598029179768.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 192735764429885 1 12598029179768))]. Qed.
