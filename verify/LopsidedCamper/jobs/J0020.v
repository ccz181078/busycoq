From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 2748779069440 to 2886218022912 *)
Lemma J0020 : job_ok 137438953472 8273418736899 1 4096087886541 10947268209697 1 2040713695477.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 10947268209697 1 2040713695477))]. Qed.
