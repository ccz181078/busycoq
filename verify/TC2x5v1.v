Require Import List.
From BusyCoq Require Import Individual25.
Require Import NArith.
From BusyCoq Require Import TC25.

Definition TC_param (T:N) := [([T],O)].

Ltac solve_TC T :=
  apply (decide_TC_spec _ (TC_param T));
  native_cast_no_check (eq_refl true).

Lemma tm1: ~halts (TM_from_str "1RB3LA1LA4RB2RA_2LA1RA4LA2RB---") c0.
Proof. solve_TC 1273285866%N. Time Qed.

Lemma tm2: ~halts (TM_from_str "1RB3RA4LA2LA1RB_1LB2LA2RA---3RB") c0.
Proof. solve_TC 1273131120%N. Time Qed.

Lemma tm3: ~halts (TM_from_str "1RB2LB3LA4RA1RA_2LA3LB3RA---4LA") c0.
Proof. solve_TC 1273249547%N. Time Qed.

