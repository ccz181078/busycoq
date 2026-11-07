From Coq Require Import Uint63.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import HTop.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Cuts.
Lemma seg : run_seg Cuts.z105 Cuts.b105 Cuts.z106 Cuts.b106 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
