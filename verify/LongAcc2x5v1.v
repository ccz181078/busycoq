From BusyCoq Require Import Individual25.
From BusyCoq Require Import LongAcc.

Module LongAcc25 := LongAcc BB25.
Import LongAcc25.

Require Import String PeanoNat NArith.
Open Scope sym.

Lemma tm1: ~halts (TM_from_str "1LB3RA1RA4RA2LA_2RB2LA---0LA0LB") c0.
Proof.
  eapply decide_loop' with (D:=20) (PP:=180%N) (P':=6) (P:=2%N) (T0:=(10^5)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.


