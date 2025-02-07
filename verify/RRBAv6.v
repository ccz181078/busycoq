From BusyCoq Require Import Individual62.
From BusyCoq Require Import RRBA.
Module RRBA62 := RRBA BB62.
Export RRBA62.
Require Import NArith.
Require Import String.


Ltac solve_loop2'' min_b n_skip k T :=
  match goal with
  | |- ~halts (TM_from_str ?x) c0 =>
    idtac x;
    apply (decide_loop2_spec' _ (min_b,16%nat) n_skip k T);
    native_cast_no_check (eq_refl true)
  end.
Ltac solve_loop2' n_skip k T := solve_loop2'' O n_skip k T.
Ltac solve_loop2 k T := solve_loop2' O k T.

Close Scope sym.

(* previously solved by MITMWFAR, but now we use RRBA(loop2) to solve them *)

Lemma tm2199: ~halts (TM_from_str "1RB1RD_0RC0RD_1LD---_1LE1LF_1RA0LF_0RA0LE") c0.
Proof. solve_loop2 6 3000%N. Time Qed.

Lemma tm1440: ~halts (TM_from_str "1RB1RF_0LC0RB_0LE1LD_1LA0LA_1RA---_1LC0RF") c0.
Proof. solve_loop2 6 3000%N. Time Qed.

Lemma tm1439: ~halts (TM_from_str "1RB1RE_0LC0RE_0LF1LD_1LA0LA_1LC0RB_1RA---") c0.
Proof. solve_loop2 6 3000%N. Time Qed.

Lemma tm1078: ~halts (TM_from_str "1RB---_1RC1RF_0LD0RF_0LA1LE_1LB0LB_1LD0RC") c0.
Proof. solve_loop2 6 3000%N. Time Qed.

Lemma tm1077: ~halts (TM_from_str "1RB---_1RC1RF_0LD0RC_0LA1LE_1LB0LB_1LD0RF") c0.
Proof. solve_loop2 6 3000%N. Time Qed.

Lemma tm1010: ~halts (TM_from_str "1RB1RA_0RC1RC_0LD1RE_1LE1LD_---1LF_0RA0LF") c0.
Proof. solve_loop2 6 3000%N. Time Qed.

Lemma tm751: ~halts (TM_from_str "1RB1RE_0LC1RB_1LC1LD_1LA0LA_0RF0RE_---0RB") c0.
Proof. solve_loop2 6 3000%N. Time Qed.

Lemma tm655: ~halts (TM_from_str "1RB0RB_1LC1LE_0RD1LC_1RD1RA_0LF0LE_---0LC") c0.
Proof. solve_loop2 6 3000%N. Time Qed.

Lemma tm438: ~halts (TM_from_str "1RB1RA_0RC1RC_0LD0LF_1LE1LD_---1LF_0RA1LB") c0.
Proof. solve_loop2 6 3000%N. Time Qed.

Lemma tm422: ~halts (TM_from_str "1RB1RA_0RC1RC_0LD0LF_1LE1LD_---1LF_0RA0LC") c0.
Proof. solve_loop2 6 3000%N. Time Qed.

Lemma tm237: ~halts (TM_from_str "1RB1RA_0RC1RC_0LD0LF_1LE1LD_---1LF_0RA0LF") c0.
Proof. solve_loop2 6 3000%N. Time Qed.

