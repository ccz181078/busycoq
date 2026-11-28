From Coq Require Import Uint63.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import HTop.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Cuts.
Lemma seg : run_seg Cuts.z153 Cuts.b153 Cuts.z154 Cuts.b154 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
