From BusyCoq Require Import Individual25.
From BusyCoq Require Import RRBA.
Module RRBA25 := RRBA BB25.
Export RRBA25.
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

Lemma tm1: ~halts (TM_from_str "1RB3LB---0LA2LA_2LB3LA4RA0RB3RA") c0.
Proof. solve_loop2 6 1000%N. Time Qed.

Lemma tm2: ~halts (TM_from_str "1RB0RA0RB3RB---_2LB3LA1LB4RA3LB") c0.
Proof. solve_loop2' 1 6 2000%N. Time Qed.

Lemma tm3: ~halts (TM_from_str "1RB2RB1LA4RB3LB_2LB3LA1RA2RA---") c0.
Proof. solve_loop2 5 2000%N. Time Qed.

Lemma tm4: ~halts (TM_from_str "1RB3LB4LA0LA---_2LA3LA4LB0RB2RA") c0.
Proof. solve_loop2'' 8 2 6 40000%N. Time Qed.

Lemma tm5: ~halts (TM_from_str "1RB3LB---1RB0RA_2LA4LB4RA0LA1RB") c0.
Proof. solve_loop2 6 1000%N. Time Qed.

Lemma tm6: ~halts (TM_from_str "1RB3LB4RB0RB0LA_2LA---4RA0RA0RB") c0.
Proof. solve_loop2' 2 7 40000%N. Time Qed.

Lemma tm7: ~halts (TM_from_str "1RB3LB3RA2LA0RB_2LA---4RA0LB1RB") c0.
Proof. solve_loop2 6 1000%N. Time Qed.

Lemma tm8: ~halts (TM_from_str "1RB3LB4RB1RA0LA_2LA---4RA1RB0RB") c0.
Proof. solve_loop2 6 2000%N. Time Qed.

Lemma tm9: ~halts (TM_from_str "1RB3LB---0LA0LB_2LA3LA4RA0RB0LA") c0.
Proof. solve_loop2' 2 7 40000%N. Time Qed.

Lemma tm10: ~halts (TM_from_str "1RB0LB4LA0RA0LB_2LA3LB3RA1RB---") c0.
Proof. solve_loop2 6 1000%N. Time Qed.

Lemma tm11: ~halts (TM_from_str "1RB0LB1LA0RA---_2LA4RA3RA0LB3LB") c0.
Proof. solve_loop2 6 1000%N. Time Qed.

Lemma tm12: ~halts (TM_from_str "1RB3LA0RB1RA2RA_2LA---4LB4RB0LA") c0.
Proof. solve_loop2 6 1000%N. Time Qed.

Lemma tm13: ~halts (TM_from_str "1RB3LA1RA4LA0RB_2LA3RA---2RA1LA") c0.
Proof. solve_loop2 6 2000%N. Time Qed.

Lemma tm14: ~halts (TM_from_str "1RB3LA4LA0RB2RB_2LA2RA---1RA1LA") c0.
Proof. solve_loop2' 1 6 2000%N. Time Qed.

Lemma tm15: ~halts (TM_from_str "1RB3LA4LA0RB---_2LA0LA2RB1RA1LA") c0.
Proof. solve_loop2'' 6 1 8 40000%N. Time Qed.

Lemma tm16: ~halts (TM_from_str "1RB3LA1LA0RB---_2LA0LA4LA1RA2RB") c0.
Proof. solve_loop2'' 6 1 8 40000%N. Time Qed.

Lemma tm17: ~halts (TM_from_str "1RB3RA4LB3RB2RB_2LA---4RA4LA0LA") c0.
Proof. solve_loop2 6 4000%N. Time Qed.

Lemma tm18: ~halts (TM_from_str "1RB3RA3LA1LA---_2LA0RB4LB2LA2RB") c0.
Proof. solve_loop2 6 2000%N. Time Qed.

Lemma tm19: ~halts (TM_from_str "1RB2LA0RB2LA1LB_1LA4RB3RA---0LA") c0.
Proof. solve_loop2 6 2000%N. Time Qed.

