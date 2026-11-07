From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 43155831390208 to 43293270343680 *)
Lemma J0314 : job_ok 137438953472 173199025406554 2 21002212145586 41055954775469 1 153763758086858.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 41055954775469 1 153763758086858))]. Qed.
