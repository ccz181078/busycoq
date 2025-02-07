From BusyCoq Require Import Individual25.
From BusyCoq Require Import RRBA.
From BusyCoq Require Import TMAddOneSymbol.
Module BB25' := TMAddOneSymbolCtx BB25.
Module RRBA25 := RRBA BB25'.
Module BB25'spec := TMAddOneSymbol BB25.
Require Import NArith.
Require Import String.


Ltac solve_loop1'' min_b n_skip k T :=
  rewrite halts_halts';
  apply BB25'spec.from_nonhalt;
  rewrite <-RRBA25.TM.halts_halts';
  apply (RRBA25.decide_loop1_spec' _ (min_b,8%nat) n_skip k T).
Ltac solve_loop1' n_skip k T := solve_loop1'' 8 n_skip k T.
Ltac solve_loop1 T := solve_loop1' 1%nat O T; native_cast_no_check (eq_refl true).

Lemma tm1: ~halts (TM_from_str "1RB3LA1RB0RB---_2LB3LA4LB1RA0LA") c0.
Proof. solve_loop1 2000%N. Time Qed.

Lemma tm2: ~halts (TM_from_str "1RB3LA0LB1RA0RB_2LB2LA1RB4RA---") c0.
Proof. solve_loop1 1000%N. Time Qed.

Lemma tm3: ~halts (TM_from_str "1RB3LA1RB0RB---_2LA3LA4LB1RA0LB") c0.
Proof. solve_loop1 2000%N. Time Qed.

Lemma tm4: ~halts (TM_from_str "1RB2LA3RA4LB1LA_1LA0RB1RA2LB---") c0.
Proof. solve_loop1 1000%N. Time Qed.

Lemma tm5: ~halts (TM_from_str "1RB2LA3RA4LB1LA_0LA0RB1RA2LB---") c0.
Proof. solve_loop1 1000%N. Time Qed.


