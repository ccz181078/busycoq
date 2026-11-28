From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LCHHH.
From Coq Require Import List.
Import ListNotations.

Module Engine := M_1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LCHHH.M448.

Definition blank_seed (q : Q) : Engine.FastState :=
  Engine.MkFastState [] (Engine.MkRTape [] [] [] []) (Engine.RAW q R).

Definition check_start (k : nat) (q : Q) : bool :=
  Engine.is_none (Engine.run_pow k (blank_seed q)).

Lemma check_start_sound k q : check_start k q = true -> halts Engine.src_tm (q;; tape0).
Proof.
  unfold check_start.
  pose proof (Engine.run_pow_spec k (blank_seed q)) as Hrun.
  destruct (Engine.run_pow k (blank_seed q)); [discriminate | intros _; exact Hrun].
Qed.
