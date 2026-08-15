(** * BB(6) holdout 1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA ("the Odometer") halts.

    Equivalence class TM1714 (Eqv_v2.v). The proof chain is
    Odometer.v -> OdometerDip.v -> OdometerOrbit.v -> OdometerBase.v ->
    OdometerLedger.v; OdometerCrisis.v is a mechanics-only side note.
    Development history, ground-truth testbenches, and the conjectured
    exact step count (~6.79e169): https://github.com/JacobRSchwartz-AI/bb6-holdouts

    Jacob Schwartz & Claude Fable 5, joint work. *)

From BusyCoq Require Import Individual62 Odometer OdometerLedger.
Require Import String.
Set Default Goal Selector "!".

Definition tm' := Eval compute in
  (TM_from_str "1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA").

Lemma tm_eq : tm' = Odometer.tm.
Proof. reflexivity. Qed.

Theorem halt : halts tm' c0.
Proof. rewrite tm_eq. exact odometer_halts. Qed.
