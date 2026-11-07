From Coq Require Import Uint63.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import HTop.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Cuts.
Lemma seg : run_seg Cuts.z89 Cuts.b89 Cuts.z90 Cuts.b90 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
