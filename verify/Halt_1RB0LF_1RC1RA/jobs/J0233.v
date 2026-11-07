From Coq Require Import Uint63.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import HTop.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Cuts.
Lemma seg : run_seg Cuts.z233 Cuts.b233 Cuts.z234 Cuts.b234 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
