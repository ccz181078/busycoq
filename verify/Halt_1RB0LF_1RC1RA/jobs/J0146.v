From Coq Require Import Uint63.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import HTop.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Cuts.
Lemma seg : run_seg Cuts.z146 Cuts.b146 Cuts.z147 Cuts.b147 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
