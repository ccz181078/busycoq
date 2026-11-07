From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 10582799417344 to 10720238370816 *)
Lemma J0077 : job_ok 137438953472 13205903124803 1 34416696810884 24390832151039 1 23850242765976.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 24390832151039 1 23850242765976))]. Qed.
