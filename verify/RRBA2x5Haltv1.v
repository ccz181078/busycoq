From BusyCoq Require Import Individual25.
From BusyCoq Require Import RRBA.
Module RRBA25 := RRBA BB25.
Export RRBA25.
Require Import NArith.
Require Import String.


Ltac solve_halt' T1 T2 :=
  match goal with
  | |- halts_at_trans (TM_from_str ?x) c0 ?tr =>
    idtac x;
    apply (decide_halt_spec' _ T1 T2 tr);
    native_cast_no_check (eq_refl (Some tr))
  end.

Ltac solve_halt :=
  solve_halt' 50000%N 10000%N.

Lemma tm1: halts_at_trans (TM_from_str "1RB4LA1LA---2RB_2LB3LA1LB2RA0RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm2: halts_at_trans (TM_from_str "1RB3LA1LA4LA1RA_2LB2RA---0RA0RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm3: halts_at_trans (TM_from_str "1RB2LA0RB4LB1RA_1LA3RA1RA---1LB") c0 (B,3).
Proof. solve_halt. Time Qed.

