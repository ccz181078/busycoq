From Coq Require Import Uint63.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import HTop.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Cuts.
Lemma seg : run_seg Cuts.z223 Cuts.b223 Cuts.z224 Cuts.b224 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
