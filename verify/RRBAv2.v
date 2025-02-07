From BusyCoq Require Import Individual62.
From BusyCoq Require Import RRBA.
From BusyCoq Require Import TMLR.
Module BB62' := TMLRCtx BB62.
Module RRBA62 := RRBA BB62'.
Module BB62'spec := TMLR BB62.
Require Import NArith.
Require Import String.


Ltac solve_loop2' n_skip k T :=
  rewrite halts_halts';
  apply BB62'spec.from_nonhalt;
  rewrite <-RRBA62.TM.halts_halts';
  apply (RRBA62.decide_loop2_spec' _ (O,O) n_skip k T);
  native_cast_no_check (eq_refl true).

Ltac solve_loop2 k T := solve_loop2' O k T.
Close Scope sym.

Lemma tm1: ~halts (TM_from_str "1RB1RA_0RC1LB_1LD0RA_0LE0LD_0LF1LD_0RA---") c0.
Proof. solve_loop2 5 2000%N. Time Qed.

Lemma tm2: ~halts (TM_from_str "1RB0RF_1LC0RA_1RA0LD_1LE1LD_0LC1RE_---0RB") c0.
Proof. solve_loop2 5 2000%N. Time Qed.

Lemma tm3: ~halts (TM_from_str "1RB1RA_0RC1LB_1RD0RA_1LE---_1RB1LF_0LE0LF") c0.
Proof. solve_loop2 5 2000%N. Time Qed.

Lemma tm4: ~halts (TM_from_str "1RB0RA_1LC0RF_1LA0LD_1LE1LD_0LC1RE_1RA---") c0.
Proof. solve_loop2 5 4000%N. Time Qed.

