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

(* previously solved by a weaker version of RRBA(loop1) that only keep track of record-breaking in one direction, but are likely not CTLable, now we use RRBA(loop2) *)

Lemma tm58: ~halts (TM_from_str "1RB0LE_0RC0LB_0LD---_0LE1LE_1RF1LD_0RA0RF") c0.
Proof. solve_loop2 6 3000%N. Time Qed.

Lemma tm49: ~halts (TM_from_str "1RB0LD_1RC0LB_0LA---_1RF1LE_0LD1LD_0RA0RF") c0.
Proof. solve_loop2 6 3000%N. Time Qed.

Lemma tm47: ~halts (TM_from_str "1RB1LE_0RC0LA_1RD0LD_0LE---_1RF1LA_1RB0RF") c0.
Proof. solve_loop2 6 3000%N. Time Qed.

Lemma tm44: ~halts (TM_from_str "1RB0RA_0RC0LF_1RD0LD_0LE---_1RA1LF_1RB1LE") c0.
Proof. solve_loop2 6 3000%N. Time Qed.

Lemma tm40: ~halts (TM_from_str "1RB0LA_0LC---_1RA0LD_1RE1LF_0RC0RE_0LD1LD") c0.
Proof. solve_loop2 6 3000%N. Time Qed.

Lemma tm31: ~halts (TM_from_str "1RB1LF_0RC0RB_1RD0LA_0RE0LD_0LF---_0LA1LA") c0.
Proof. solve_loop2 6 3000%N. Time Qed.

Lemma tm21: ~halts (TM_from_str "1RB0LB_0LC---_1RF1LD_1RE1LC_0RA0LD_1RE0RF") c0.
Proof. solve_loop2 6 3000%N. Time Qed.

Lemma tm16: ~halts (TM_from_str "1RB1LF_1RC0RB_0RD0LF_1RE0LE_0LA---_1RC1LA") c0.
Proof. solve_loop2 6 3000%N. Time Qed.

Lemma tm13: ~halts (TM_from_str "1RB1LF_0RC0RB_1RD0LA_1RE0LD_0LC---_0LA1LA") c0.
Proof. solve_loop2 6 3000%N. Time Qed.

