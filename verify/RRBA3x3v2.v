From BusyCoq Require Import Individual33.
From BusyCoq Require Import RRBA.
Module RRBA33 := RRBA BB33.
Export RRBA33.
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

Lemma tm1: ~halts (TM_from_str "1RB2LA0LA_1LA2RC0RC_---2RB0RB") c0.
Proof. solve_loop2 6 2000%N. Time Qed.

Lemma tm2: ~halts (TM_from_str "1RB1LB0LB_2LA1RB0RC_---1RC2RB") c0.
Proof. solve_loop2 6 2000%N. Time Qed.

Lemma tm3: ~halts (TM_from_str "1RB1LA0LA_2LA0RC2RC_---0RB2RB") c0.
Proof. solve_loop2 6 2000%N. Time Qed.

Lemma tm4: ~halts (TM_from_str "1RB0LC2LA_2LC0RA2RA_---1LA2LC") c0.
Proof. solve_loop2 6 2000%N. Time Qed.

Lemma tm5: ~halts (TM_from_str "1RB2LA0RC_1LA0LA1RA_---1LB0RB") c0.
Proof. solve_loop2 9 6000%N. Time Qed.

