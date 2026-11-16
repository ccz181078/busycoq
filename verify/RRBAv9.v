From BusyCoq Require Import Individual62.
From BusyCoq Require Import RRBA.
From BusyCoq Require Import TMLocalHistory.
Module BB62' := TMLocalHistoryCtx BB62.
Module RRBA62 := RRBA BB62'.
Module BB62'spec := TMLocalHistory BB62.
Require Import NArith.
Require Import String.


Ltac solve_loop2' len_h n_skip k T :=
  rewrite halts_halts';
  apply (BB62'spec.from_nonhalt len_h);
  rewrite <-RRBA62.TM.halts_halts';
  apply (RRBA62.decide_loop2_spec' _ (O,O) n_skip k T);
  native_cast_no_check (eq_refl true).

Ltac solve_loop2 len_h k T := solve_loop2' len_h O k T.
Close Scope sym.

Lemma tm1: ~halts (TM_from_str "1RB1LC_1LC0RD_1RD1RC_1LE0RB_0LE0LF_---0LA") c0.
Proof. solve_loop2 3 6 6000%N. Time Qed.

Lemma tm2: ~halts (TM_from_str "1RB1RC_1LC0RD_1RD1RA_1LE0RB_0LE0LF_---0LA") c0.
Proof. solve_loop2' 4 1 6 10000%N. Time Qed.

Lemma tm3: ~halts (TM_from_str "1RB1RC_1LC0RD_1RD1RC_1LE0RB_0LE0LF_---0LA") c0.
Proof. solve_loop2' 4 1 6 10000%N. Time Qed.

Lemma tm4: ~halts (TM_from_str "1RB---_1LC1LB_1RA0LD_1RE0LC_0RE0RF_1LA0LA") c0.
Proof. solve_loop2' 5 1 6 10000%N. Time Qed.

Lemma tm5: ~halts (TM_from_str "1RB---_1LC1LB_1RA0LD_1RE0LC_0RE1RF_1LB1LC") c0.
Proof. solve_loop2' 5 1 7 10000%N. Time Qed.

Lemma tm6: ~halts (TM_from_str "1RB---_1LC0LD_1RA0LD_1RE0LC_0RE1RF_1LF1LB") c0.
Proof. solve_loop2' 5 1 7 10000%N. Time Qed.

Lemma tm7: ~halts (TM_from_str "1RB1LB_1LC---_1RA0LD_1RE0LC_0RE1RF_1LA1LC") c0.
Proof. solve_loop2' 5 1 7 10000%N. Time Qed.

Lemma tm8: ~halts (TM_from_str "1RB---_0LC1RC_1LC1LD_1RE0LF_0RE0RC_1LA0LD") c0.
Proof. solve_loop2' 4 1 6 10000%N. Time Qed.

Lemma tm9: ~halts (TM_from_str "1RB---_0RC1RC_1LC1LD_1RE0LF_0RE0RC_1LA0LD") c0.
Proof. solve_loop2' 4 1 6 10000%N. Time Qed.

Lemma tm10: ~halts (TM_from_str "1RB---_1LC1RD_0RC0RD_1LD1LE_1RC0LF_1LA0LE") c0.
Proof. solve_loop2' 4 1 6 10000%N. Time Qed.

Lemma tm11: ~halts (TM_from_str "1RB---_1RC1LD_0LC1LB_1RE0LF_0RE0RB_1LA0LD") c0.
Proof. solve_loop2' 4 1 6 10000%N. Time Qed.

Lemma tm12: ~halts (TM_from_str "1RB1LC_0LB1LA_1RD0LE_0RD0RA_1LF0LC_0LE---") c0.
Proof. solve_loop2' 4 1 6 10000%N. Time Qed.

Lemma tm13: ~halts (TM_from_str "1RB1LD_1LC0RE_0LC0LD_1RD1RB_1RF0RB_1LA---") c0.
Proof. solve_loop2' 4 1 6 10000%N. Time Qed.

Lemma tm14: ~halts (TM_from_str "1RB0RE_1LC0RF_0LC1LD_1RA1LD_---0LD_1LA0RB") c0.
Proof. solve_loop2' 4 1 7 10000%N. Time Qed.

Lemma tm15: ~halts (TM_from_str "1RB1RE_1LC0RF_0LC1LD_1RA1LD_---1RB_1LA0RB") c0.
Proof. solve_loop2' 4 1 7 10000%N. Time Qed.

Lemma tm16: ~halts (TM_from_str "1RB1LD_1LC1RB_---1LA_1LD0LE_1RF0LD_0RF0RB") c0.
Proof. solve_loop2' 3 1 6 10000%N. Time Qed.

