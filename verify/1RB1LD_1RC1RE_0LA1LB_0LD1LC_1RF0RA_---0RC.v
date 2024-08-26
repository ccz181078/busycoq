From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.

Definition tm := Eval compute in (TM_from_str "1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Open Scope list.

Lemma BL l r n:
  l <* [0;1;1;1;1;1]^^n <{{B}} [1;1] *> r -->*
  l <{{B}} [1;1] *> [0;1;0;1;0;1]^^n *> r.
Proof.
  shift_rule.
  execute.
Qed.

Lemma CR l r n:
  l <* [0;1] {{C}}> [0;1;0;1;0;1]^^n *> r -->*
  l <* [1;1;0;1;1;1]^^n <* [0;1] {{C}}> r.
Proof.
  shift_rule.
  execute.
Qed.

Lemma AR l r n:
  l {{A}}> [0;1;0;1;0;1]^^n *> r -->*
  l <* [0;1;1;1;1;1]^^n {{A}}> r.
Proof.
  shift_rule.
  execute.
Qed.

Lemma AR' l r n:
  l {{A}}> [0;1;1]^^n *> r -->*
  l <* [0;1;1]^^n {{A}}> r.
Proof.
  shift_rule.
  execute.
Qed.

Lemma CL' l r n:
  l <* [0;1;1]^^n <{{C}} r -->*
  l <{{C}} [1;1;0]^^n *> r.
Proof.
  shift_rule.
  execute.
Qed.

Definition S0 a b c :=
  const 0 <* [0;1;1] <* [0;1;1;1;1;1]^^a <{{B}} [1;1] *> [0;1;1] *> [0;1]^^b *> [0;1;1]^^c *> const 0.

Lemma LInc n m k:
  S0 (n+1) m k -->*
  S0 n (m+4) k.
Proof.
  unfold S0.
  rewrite (Nat.add_comm m 4).
  follow BL.
  execute.
  follow CR.
  do 8 (rewrite lpow_rotate; cbn).
  execute.
Qed.

Lemma LIncs n m k:
  S0 n m k -->*
  S0 0 (m+n*4) k.
Proof.
  gen m.
  induction n; intros.
  - finish.
  - replace (S n) with (n+1) by lia.
    follow LInc.
    follow IHn.
    finish.
Qed.

Lemma LRst n c k:
  S0 0 (n*3+c) k -->*
  const 0 <* [0;1;1] <* [0;1;1;1;1;1]^^(n+2) {{A}}> [0;1]^^c *> [0;1;1]^^k *> const 0.
Proof.
  execute.
  rewrite lpow_mul.
  cbn.
  follow AR.
  finish.
Qed.

Lemma RInc2 m n:
  S0 0 (m*3+2) (1+n) -->*
  S0 (m+1) 4 n.
Proof.
  unfold S0.
  follow LRst.
  replace (m+2) with (1+(m+1)) by lia.
  remember (m+1) as x.
  execute.
Qed.

Lemma RInc1 m n:
  S0 0 (m*3+1) (1+n) -->*
  S0 (m+1) 1 (2+n).
Proof.
  unfold S0.
  follow LRst.
  execute.
  follow AR'.
  execute.
  follow CL'.
  execute.
  do 6 (rewrite lpow_rotate; cbn).
  execute.
  repeat (rewrite lpow_rotate; cbn).
  finish.
Qed.

Lemma RInc0 m n:
  S0 0 (m*3+0) (1+n) -->*
  S0 (m+1) 0 (2+n).
Proof.
  unfold S0.
  follow LRst.
  execute.
  follow AR'.
  execute.
  follow CL'.
  do 6 (rewrite lpow_rotate; cbn).
  execute.
  repeat (rewrite lpow_rotate; cbn).
  finish.
Qed.

Lemma RInc2' m:
  S0 0 (m*3+2) 0 -->*
  S0 (m+2) 0 0.
Proof.
  unfold S0.
  follow LRst.
  execute.
Qed.

Lemma RInc1' m:
  halts tm (S0 0 (m*3+1) 0).
Proof.
  eapply halts_evstep.
  2:{
    follow LRst.
    repeat step.
    constructor.
  }
  apply halted_halts.
  constructor.
Qed.

Lemma RInc0' m:
  S0 0 (m*3+0) 0 -->* S0 (m+1) 0 1.
Proof.
  unfold S0.
  follow LRst.
  execute.
  do 6 (rewrite lpow_rotate; cbn).
  execute.
  repeat (rewrite lpow_rotate; cbn).
  finish.
Qed.

Definition R x y := S0 0 x y.

Lemma R0 x y:
  R (x*3+0) y -->* R (x*4+4) (y+1).
Proof.
  unfold R.
  destruct y as [|y].
  - follow RInc0'.
    follow LIncs.
    finish.
  - follow RInc0.
    follow LIncs.
    finish.
Qed.

Lemma R1 x y:
  R (x*3+1) (1+y) -->* R (x*4+5) (2+y).
Proof.
  unfold R.
  follow RInc1.
  follow LIncs.
  finish.
Qed.

Lemma R2 x y:
  R (x*3+2) y -->* R (x*4+8) (y-1).
Proof.
  unfold R.
  destruct y as [|y].
  - follow RInc2'.
    follow LIncs.
    finish.
  - follow RInc2.
    follow LIncs.
    finish.
Qed.

Lemma R1' x:
  halts tm (R (x*3+1) 0).
Proof.
  apply RInc1'.
Qed.

Lemma init:
  c0 -->* R 0 0.
Proof.
  execute.
Qed.

Check init.
Check R0.
Check R1.
Check R2.
Check R1'.
(*
```
1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC

start: (0,0)

(3x+0,y)   --> (4x+4,y+1)
(3x+1,y+1) --> (4x+5,y+2)
(3x+2,y)   --> (4x+8,max(0,y-1))

(3x+1,0)   --> halt

(x,y) := 0^inf 110 <B 11011 01^x 011^y 0^inf
```

*)

