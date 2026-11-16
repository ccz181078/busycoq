From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.




Definition tm := Eval compute in (TM_from_str "1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Open Scope list.


Lemma DL l r n:
  l <* [1;1]^^n <{{D}} r -->*
  l <{{D}} [1;1]^^n *> r.
Proof.
  shift_rule.
  execute.
Qed.

Lemma BR l r n:
  l {{B}}> [1;1]^^n *> r -->*
  l <* [1;1]^^n {{B}}> r.
Proof.
  shift_rule.
  execute.
Qed.

Lemma ER l r n:
  l {{E}}> [1;1]^^n *> r -->*
  l <* [1;1]^^n {{E}}> r.
Proof.
  shift_rule.
  execute.
Qed.


Definition S1 a b c :=
  const 0 <* [1]^^a <* [1;0] <* [1;1]^^b <{{D}} [0] *> [1]^^c *> const 0.

Lemma Inc1 a b c:
  S1 a (b+1) c -->*
  S1 (a+1) b (c+1).
Proof.
  rewrite (Nat.add_comm c 1).
  unfold S1.
  follow DL.
  execute.
  follow BR.
  execute.
  rewrite lpow_shift2.
  rewrite <-lpow_shift21.
  execute.
Qed.

Lemma Inc1s a b c:
  S1 a b c -->*
  S1 (a+b) 0 (c+b).
Proof.
  gen a c.
  induction b; intros.
  - finish.
  - replace (S b) with (b+1) by lia.
    follow Inc1.
    follow IHb.
    finish.
Qed.

Lemma Rst10 a c:
  S1 (a*2+2) 0 c -->*
  S1 0 a (c+3).
Proof.
  rewrite (Nat.add_comm c 3).
  unfold S1.
  execute.
  rewrite lpow_mul.
  cbn.
  rewrite lpow_shift2.
  rewrite <-lpow_shift21.
  execute.
Qed.

Definition S0 a b c :=
  const 0 <* [1]^^a <* [0] <* [1;1]^^b <{{D}} [0] *> [1]^^c *> const 0.

Lemma Rst11 a c:
  S1 (a*2+1) 0 c -->*
  S0 0 a (c+3).
Proof.
  unfold S0,S1.
  execute.
  rewrite lpow_mul.
  cbn.
  repeat rewrite lpow_shift1.
  finish.
Qed.

Lemma Inc0 a b c:
  S0 a (b+1) (c+1) -->*
  S0 (a+1) (b+1) c.
Proof.
  rewrite (Nat.add_comm c 1).
  unfold S0.
  follow DL.
  execute.
  follow ER.
  do 2 step.
  rewrite lpow_shift21e.
  finish.
Qed.

Lemma Inc0s a b c:
  S0 a (b+1) c -->*
  S0 (a+c) (b+1) 0.
Proof.
  gen a b.
  induction c; intros.
  - finish.
  - replace (S c) with (c+1) by lia.
    follow Inc0.
    follow IHc.
    finish.
Qed.

Lemma Inc2 a b:
  S0 a (b+1) 0 -->*
  S0 (a+1) b 2.
Proof.
  unfold S0.
  follow DL.
  execute.
  follow ER.
  rewrite <-lpow_shift21e.
  execute.
Qed.

Lemma Inc2' a b:
  S0 a (b+2) 0 -->*
  S0 (a+3) (b+1) 0.
Proof.  
  replace (b+2) with (b+1+1) by lia.
  follow Inc2.
  follow Inc0s.
  finish.
Qed.

Lemma Inc2s a b:
  S0 a (b+1) 0 -->*
  S0 (a+b*3) 1 0.
Proof.
  gen a.
  induction b; intros.
  - finish.
  - replace (S b + 1) with (b+2) by lia.
    follow Inc2'.
    follow IHb.
    finish.
Qed.

Lemma Rst20 a:
  S0 (a*2) 1 0 -->*
  S0 0 (a+2) 1.
Proof.
  unfold S0.
  do 15 step.
  rewrite lpow_mul.
  cbn.
  repeat rewrite lpow_shift2.
  finish.
Qed.

Lemma Rst21 a:
  S0 (a*2+1) 1 0 -->*
  S1 0 (a+2) 1.
Proof.
  unfold S0,S1.
  do 15 step.
  rewrite lpow_mul.
  cbn.
  repeat rewrite <-lpow_shift21e.
  finish.
Qed.


(*

S1(a,b,c) = 1^a 0 1^(2b+1) <D 0 1^c
S0(a,b,c) = 1^a 0 1^(2b+0) <D 0 1^c

S1(a,b,c) --> S1(a+b,0,c+b)    (split)
S0(a,b+1,c) --> S0(a+c,b+1,0)  (swap)
S0(a,b+1,0) --> S0(a+3b,1,0)   (mult)

S1(2a+2,0,c) --> S1(0,a,c+3)   (split->split)
S1(2a+1,0,c) --> S0(0,a,c+3)   (split->swap)
S0(2a,1,0) --> S0(0,a+2,1)     (mult->mult)
S0(2a+1,1,0) --> S1(0,a+2,1)   (mult->split)

*)

Definition P a := S0 a 1 0.
Definition Q a b := S1 0 a b.

Lemma Init:
  c0 -->* P 2.
Proof.
  unfold P,S0.
  execute.
Qed.

Lemma PP a:
  P (a*2) -->* P (a*3+4).
Proof.
  unfold P.
  follow Rst20.
  replace (a+2) with (a+1+1) by lia.
  follow (Inc0 0 (a+1) 0).
  follow Inc2s.
  finish.
Qed.

Lemma PQ a:
  P (a*2+1) -->*
  Q (a+2) 1.
Proof.
  unfold P,Q.
  follow Rst21.
  finish.
Qed.

Lemma QQ a b:
  Q (a*2+2) b -->*
  Q a (b+a*2+5).
Proof.
  unfold Q.
  follow Inc1s.
  follow Rst10.
  finish.
Qed.

Lemma QP a b:
  Q (a*2+3) b -->*
  P (b+a*5+6).
Proof.
  unfold P,Q.
  follow Inc1s.
  replace (0+(a*2+3)) with ((a+1)*2+1) by lia.
  follow Rst11.
  follow Inc0s.
  follow Inc2s.
  finish.
Qed.

Lemma QQ' b:
  Q 1 (b*2) -->*
  Q (b+2) 1.
Proof.
  unfold Q.
  follow Inc1s.
  cbn.
  unfold S1,S0.
  execute.
  rewrite lpow_mul.
  follow BR.
  execute.
  rewrite lpow_shift2.
  rewrite <-lpow_shift21.
  execute.
Qed.

Lemma QP'0 b:
  Q 1 (b*2+1) -->*
  S0 0 (b+3) 2.
Proof.
  unfold Q.
  follow Inc1s.
  cbn.
  unfold S1,S0.
  cbn.
  replace (b*2+1+1) with ((b+1)*2) by lia.
  rewrite lpow_mul.
  execute.
  follow ER.
  execute.
  rewrite lpow_shift2.
  rewrite <-lpow_shift21.
  execute.
Qed.

Lemma QP' b:
  Q 1 (b*2+1) -->*
  P (b*3+8).
Proof.
  unfold P,Q.
  follow QP'0.
  replace (b+3) with (b+2+1) by lia.
  follow Inc0s.
  follow Inc2s.
  finish.
Qed.

Lemma Halt b:
  halts tm (Q 0 b).
Proof.
  eapply halts_evstep.
  2:{
    unfold Q,S1.
    repeat step.
    constructor.
  }
  apply halted_halts.
  constructor.
Qed.


Check Init.
Check PP.
Check PQ.
Check QP.
Check QQ.
Check QP'.
Check QQ'.
Check Halt.

(*

P(2a)   -> P(3a+4)
P(2a+1) -> Q(a+2,1)

Q(2a+3,b) -> P(b+5a+6)
Q(2a+2,b) -> Q(a,b+2a+5)

Q(1,2b+1) -> P(3b+8)
Q(1,2b)   -> Q(b+2,1)

Q(0,b)    -> halt

*)







