From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.

Definition tm := Eval compute in (TM_from_str "1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Open Scope list.


Lemma CR l r n:
  l {{C}}> [0;1]^^n *> r -->*
  l <* [1;1]^^n {{C}}> r.
Proof.
  shift_rule.
  execute.
Qed.


Lemma BL l r n:
  l <* [1;1]^^n <{{B}} r -->*
  l <{{B}} [0;1]^^n *> r.
Proof.
  shift_rule.
  execute.
Qed.


Lemma LInc n r:
  const 0 {{C}}> [0;1]^^n *> [1;0;1;0;1] *> r -->*
  const 0 {{C}}> [0;1]^^(n+3) *> [1] *> r.
Proof.
  follow CR.
  execute.
  follow BL.
  do 1 step.
  repeat rewrite lpow_shift2.
  finish.
Qed.

Lemma LIncs n k r:
  const 0 {{C}}> [0;1]^^n *> [1] *> [0;1]^^(k*2) *> r -->*
  const 0 {{C}}> [0;1]^^(n+k*3) *> [1] *> r.
Proof.
  gen n r.
  induction k; intros.
  - finish.
  - replace (S k * 2) with (2+k*2) by lia.
    rewrite lpow_add,Str_app_assoc.
    cbn.
    follow LInc.
    follow IHk.
    finish.
Qed.

Definition S0 n m :=
  const 0 {{C}}> [0;1]^^2 *> [1] *> [0;1]^^n *> [1] *> [0;1]^^m *> const 0.

Lemma LOverflow n m:
  const 0 {{C}}> [0;1]^^(n+1) *> [1;0;1;1] *> [0;1]^^m *> const 0 -->*
  S0 (n+2) (m+2).
Proof.
  unfold S0.
  follow CR.
  execute.
  follow CR.
  execute.
  follow BL.
  rewrite <-lpow_shift21.
  execute.
  follow BL.
  repeat rewrite lpow_shift2.
  rewrite const_unfold.
  rewrite const_unfold.
  do 6 step.
  finish.
Qed.

Lemma LOverflow' n m:
  const 0 {{C}}> [0;1]^^(n+1) *> [1;1] *> [0;1]^^(m+1) *> const 0 -->*
  S0 (n+2) (m).
Proof.
  unfold S0.
  follow CR.
  replace (m+1) with (1+m) by lia.
  simpl_tape.
  cbn.
  rewrite <-lpow_shift21.
  execute.
  follow BL.
  execute.
Qed.

Lemma LOverflow'' n:
  const 0 {{C}}> [0;1]^^(n+1) *> [1;1] *> const 0 -->*
  const 0 {{C}}> [0;1]^^2 *> [1] *> [0;1]^^(n+2) *> const 0.
Proof.
  follow CR.
  replace (n+1) with (1+n) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn.
  rewrite <-lpow_shift21.
  execute.
  follow BL.
  execute.
Qed.

Lemma LHalt n:
  halts tm (const 0 {{C}}> [0;1]^^(n*2+1) *> [1;1] *> const 0).
Proof.
  unfold halts,halts_in.
  eapply halts_evstep.
  2:{
    follow LOverflow''.
    replace (n*2+2) with ((n+1)*2) by lia.
    follow LIncs.
    follow CR.
    repeat step.
    constructor.
  }
  apply halted_halts.
  constructor.
Qed.

Lemma LReset n:
  const 0 {{C}}> [0;1]^^(n*2+2) *> [1;1] *> const 0 -->*
  S0 (n*3+6) 1.
Proof.
  unfold S0.
  replace (n*3+6) with ((n+1)*3+3) by lia.
  replace (n*2+2) with (n*2+1+1) by lia.
  follow LOverflow''.
  replace (n*2+1+2) with ((n+1)*2+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LIncs.
  follow CR.
  rewrite lpow_add,Str_app_assoc.
  cbn.
  rewrite <-lpow_shift21.
  execute.
  follow BL.
  repeat rewrite lpow_shift2.
  execute.
Qed.

Lemma R1 n m:
  S0 (n*2+1) m -->*
  S0 (n*3+3) (m+2).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LIncs.
  replace (2+n*3) with (n*3+1+1) by lia.
  follow LOverflow.
  unfold S0.
  finish.
Qed.

Lemma R2 n m:
  S0 (n*2) (m+1) -->*
  S0 (n*3+3) (m).
Proof.
  unfold S0.
  follow LIncs.
  replace (2+n*3) with (n*3+1+1) by lia.
  follow LOverflow'.
  unfold S0.
  finish.
Qed.

Lemma R3 n:
  S0 (n*4) 0 -->* S0 (n*9+6) 1.
Proof.
  unfold S0.
  replace (n*4) with (n*2*2) by lia.
  follow LIncs.
  replace (2+n*2*3) with (n*3*2+2) by lia.
  follow LReset.
  unfold S0.
  finish.
Qed.

Lemma R4 n:
  halts tm (S0 (n*4+2) 0).
Proof.
  replace (n*4+2) with ((n*2+1)*2) by lia.
  eapply halts_evstep.
  2:{
    follow LIncs.
    replace (2+(n*2+1)*3) with ((n*3+2)*2+1) by lia.
    constructor.
  }
  apply LHalt.
Qed.

Lemma init:
  c0 -->* S0 3 1.
Proof.
  unfold S0.
  cbn.
  execute.
Qed.


Check init.
Check R1.
Check R2.
Check R3.
Check R4.

(*
```
antihydra variant:
1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA

(n,m) := 0^inf C> 01011 01^n 1 01^m 0^inf

start from (3,1)
(2n+1,m) --> (3n+3,m+2)
(2n,m+1) --> (3n+3,m)
(4n,0) --> (9n+6,1)
(4n+2,0) --> halt
```
*)



