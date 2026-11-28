From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 48928267436032 to 49065706389504 *)
Lemma J0356 : job_ok 137438953472 202119344408197 1 18057858207212 211755130810011 1 9040547167722.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 211755130810011 1 9040547167722))]. Qed.
