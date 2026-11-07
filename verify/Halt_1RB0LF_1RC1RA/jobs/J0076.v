From Coq Require Import Uint63.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import HTop.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Cuts.
Lemma seg : run_seg Cuts.z76 Cuts.b76 Cuts.z77 Cuts.b77 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
