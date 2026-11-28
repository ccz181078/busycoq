From Coq Require Import Uint63.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import HTop.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Cuts.
Lemma seg : run_halt_at Cuts.z312 Cuts.b312 Cuts.y_end Cuts.a_halt = true.
Proof. native_cast_no_check (eq_refl true). Qed.
