
From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.




Definition tm := Eval compute in (TM_from_str "1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA1LD_---0LC").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Open Scope list.


Lemma DL l r n:
  l <* [1]^^(n*2) <{{D}} r -->*
  l <{{D}} [1]^^(n*2) *> r.
Proof.
  gen l r.
  induction n; intros l r.
  - finish.
  - simpl_tape.
    execute.
    follow IHn.
    change (1>>1>>r) with ([1] *> [1] *> r).
    do 2 rewrite lpow_shift'.
    finish.
Qed.

Lemma AR l r n:
  l {{A}}> [1]^^n *> r -->*
  l <* [1]^^n {{A}}> r.
Proof.
  shift_rule.
  execute.
Qed.

Lemma FL l r n:
  l <* [1]^^(n*2) <{{F}} r -->*
  l <{{F}} [0]^^(n*2) *> r.
Proof.
  gen l r.
  induction n; intros l r.
  - finish.
  - simpl_tape.
    execute.
    follow IHn.
    change (0>>0>>r) with ([0] *> [0] *> r).
    do 2 rewrite lpow_shift'.
    finish.
Qed.

Lemma CL l r n:
  l <* [1]^^(n*2) <{{C}} r -->*
  l <{{C}} [0]^^(n*2) *> r.
Proof.
  gen l r.
  induction n; intros l r.
  - finish.
  - simpl_tape.
    execute.
    follow IHn.
    change (0>>0>>r) with ([0] *> [0] *> r).
    do 2 rewrite lpow_shift'.
    finish.
Qed.

Lemma EL l r n:
  l <* [1]^^(n*2) <{{E}} r -->*
  l <{{E}} [1]^^(n*2) *> r.
Proof.
  gen l r.
  induction n; intros l r.
  - finish.
  - simpl_tape.
    execute.
    follow IHn.
    change (1>>1>>r) with ([1] *> [1] *> r).
    do 2 rewrite lpow_shift'.
    finish.
Qed.

Lemma LInc0 n r:
  const 0 <* [1] <* [1]^^(n*2) {{A}}> [0;1;0] *> r -->*
  const 0 <* [1] <* [1]^^((n+2)*2) {{A}}> r.
Proof.
  replace ((n+2)*2) with (n*2+4) by lia.
  execute.
  follow DL.
  execute.
  follow AR.
  execute.
  change (1 >> 1 >> 1 >> 1 >> 1 >> const 0) with
  ([1] *> [1] *> [1] *> [1] *> [1] *> const 0).
  do 3 rewrite lpow_shift'.
  finish.
Qed.

Lemma LInc1 n r:
  const 0 <* [1] <* [1]^^(n*2) {{A}}> [0;0;0;0] *> r -->*
  const 0 <* [1] <* [1]^^((n+1)*2) {{A}}> [0;1;0] *> r.
Proof.
  execute.
  follow DL.
  execute.
  follow AR.
  step.
  replace ((n+1)*2) with (n*2+2) by lia.
  simpl_tape. cbn.
  change (1 >> 1 >> 1 >> const 0) with
  ([1] *> [1] *> [1] *> const 0).
  rewrite lpow_shift'.
  finish.
Qed.

Lemma LInc n r:
  const 0 <* [1] <* [1]^^(n*2) {{A}}> [0;0;0;0] *> r -->*
  const 0 <* [1] <* [1]^^((n+3)*2) {{A}}> r.
Proof.
  follow LInc1.
  follow LInc0.
  finish.
Qed.

Lemma LIncs n m i r:
  const 0 <* [1] <* [1]^^(n*2) {{A}}> [0]^^(m+i*4) *> r -->*
  const 0 <* [1] <* [1]^^((n+i*3)*2) {{A}}> [0]^^m *> r.
Proof.
  gen n m.
  induction i; intros n m.
  - finish.
  - replace (m+S i*4) with (4+(m+i*4)) by lia.
    rewrite lpow_add,Str_app_assoc.
    follow LInc.
    follow IHi.
    finish.
Qed.


Lemma LOverflow n r:
  const 0 <* [1] <* [1]^^(n*2) {{A}}> [0;1;1] *> r -->*
  const 0 <* [1] <* [1]^^(2*2) {{A}}> [0]^^(n*2+3) *> r.
Proof.
  execute.
  follow FL.
  execute.
Qed.

Lemma LOverflow' n r:
  const 0 <* [1] <* [1]^^(n*2) {{A}}> [0;0;0;1] *> r -->*
  const 0 <* [1] <* [1]^^(2*2) {{A}}> [0]^^(n*2+5) *> r.
Proof.
  execute.
  follow DL.
  execute.
  follow AR.
  execute.
  follow CL.
  do 16 step.
  change ([0] ^^ (n * 2) *> 0 >> 0 >> 0 >> 0 >> 0 >> r)
  with ([0]^^(n*2) *> [0] *> [0] *> [0] *> [0] *> [0] *> r).
  do 1 rewrite lpow_shift'. 
  finish.
Qed.

Definition LS0 m r :=
  const 0 <* [1] <* [1]^^(2*2) {{A}}> [0]^^(m) *> r.

Definition LS1 m (r:Stream Sym) :=
  const 0 <* [1]^^m {{A}}> r.



Lemma RInc_3_eat1 m k r:
  LS0 (m*4+3) ([1]^^(1+k) *> r) -->*
  LS0 (m*6+9) ([1]^^(k) *> r).
Proof.
  unfold LS0.
  replace (m*4+3) with (3+m*4) by lia.
  follow LIncs.
  remember (2+m*3) as c.
  simpl_tape.
  pose proof LOverflow' as H.
  cbn in H.
  follow H.
  subst.
  replace ((2+m*3)*2+5) with (m*6+9) by lia.
  simpl_tape.
  finish.
Qed.


Lemma RInc_3_pass0 m r:
  LS0 (m*4+3) ([0] *> r) -->*
  LS1 (m*6+11) r.
Proof.
  unfold LS0,LS1.
  replace (m*4+3) with (3+m*4) by lia.
  replace (m*6+11) with (8+m*6+3) by lia.
  follow LIncs.
  execute.
  follow DL.
  execute.
  follow AR.
  execute.
  follow EL.
  execute.
  follow AR.
  execute.
Qed.



Lemma RInc_1_eat11 m k r:
  LS0 (m*4+1) ([1]^^(2+k) *> r) -->*
  LS0 (m*6+7) ([1]^^(k) *> r).
Proof.
  unfold LS0.
  replace (m*4+1) with (1+m*4) by lia.
  follow LIncs.
  remember (2+m*3) as c.
  simpl_tape.
  pose proof LOverflow as H.
  cbn in H.
  follow H.
  subst.
  replace ((2+m*3)*2+3) with (m*6+7) by lia.
  simpl_tape.
  finish.
Qed.

Lemma RInc_1_pass10 m r:
  LS0 (m*4+1) ([1;0] *> r) -->*
  LS1 (m*6+9) r.
Proof.
  unfold LS0,LS1.
  replace (m*4+1) with (1+m*4) by lia.
  replace (m*6+9) with (7+m*6+2) by lia.
  follow LIncs.
  execute.
  follow DL.
  execute.
  follow AR.
  execute.
Qed.


Lemma RInc_1_halt01 m r:
  halts tm (LS0 (m*4+1) ([0;1] *> r)).
Proof.
  unfold LS0,halts,halts_in.
  replace (m*4+1) with (1+m*4) by lia.
  eapply halts_evstep.
  2:{
    follow LIncs.
    repeat step.
    constructor.
  }
  apply halted_halts.
  constructor.
Qed.

Lemma pass1 m r:
  LS1 m ([1] *> r) -->* LS1 (m+1) r.
Proof.
  unfold LS1.
  execute.
Qed.

Lemma reset000' m r:
  LS1 (m*2+10) ([0;0;0] *> r) -->*
  LS0 9 ([1]^^(m*2+8) *> [0;1] *> r).
Proof.
  unfold LS0,LS1.
  execute.
  follow DL.
  do 75 step.
  repeat rewrite <-lpow_shift1.
  finish.
Qed.



Definition N n m :=
  LS0 (n*2+1) ([1]^^m *> [0;1] *> const 0).

Lemma Inc0 n m:
  N (n*2) (m+2) -->* N (n*3+3) m.
Proof.
  unfold N.
  replace (n*2*2) with (n*4) by lia.
  replace (m+2) with (2+m) by lia.
  follow RInc_1_eat11.
  finish.
Qed.

Lemma Inc1 n m:
  N (n*2+1) (m+1) -->* N (n*3+4) m.
Proof.
  unfold N.
  replace ((n*2+1)*2+1) with (n*4+3) by lia.
  replace (m+1) with (1+m) by lia.
  follow RInc_3_eat1.
  finish.
Qed.

Lemma Halt n:
  halts tm (N (n*2) 0).
Proof.
  unfold N.
  replace (n*2*2) with (n*4) by lia.
  apply RInc_1_halt01.
Qed.

Lemma Rst0 n:
  N (n*2+5) 0 -->* N 4 (n*6+22).
Proof.
  unfold N.
  cbn.
  replace ((n*2+5)*2+1) with ((n+2)*4+3) by lia.
  follow RInc_3_pass0.
  follow pass1.
  replace ((n+2)*6+11+1) with (((n+2)*3+1)*2+10) by lia.
  replace (const 0) with ([0;0;0] *> const 0).
  2: cbn; do 3 rewrite <-const_unfold; reflexivity.
  follow reset000'.
  cbn.
  do 3 rewrite <-const_unfold.
  finish.
Qed.

Lemma Rst1 n:
  N (n*2+4) 1 -->* N 4 (n*6+20).
Proof.
  unfold N.
  cbn.
  replace ((n*2+4)*2+1) with ((n+2)*4+1) by lia.
  change (1>>0>>1>>const 0) with ([1;0] *> 1>>const 0).
  follow RInc_1_pass10.
  follow pass1.
  replace ((n+2)*6+9+1) with (((n+2)*3)*2+10) by lia.
  replace (const 0) with ([0;0;0] *> const 0).
  2: cbn; do 3 rewrite <-const_unfold; reflexivity.
  follow reset000'.
  cbn.
  do 3 rewrite <-const_unfold.
  finish.
Qed.

Lemma init':
  c0 -->* N 1 5.
Proof.
  unfold N,LS0.
  do 52 step.
  finish.
Qed.

Lemma init:
  c0 -->* N 4 4.
Proof.
  follow init'.
  apply (Inc1 0 4).
Qed.

Check init.
Check Inc0.
Check Inc1.
Check Rst0.
Check Rst1.
Check Halt.

(*
```
halting cryptid candidate:
1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA1LD_---0LC

start from N(4,4)
N(2n,m+2)   --> N(3n+3,m)
N(2n+1,m+1) --> N(3n+4,m)
N(2n+4,0)   --> halt
N(2n+4,1)   --> N(4,6n+20)
N(2n+5,0)   --> N(4,6n+22)

example:
(4,4),(9,2),(16,1),(4,56),(9,54),(16,53),(27,51),(43,50),(67,49),(103,48),(157,47),(238,46),(360,44)
```
*)

Goal c0 -->* c0.
pose N.
unfold N,LS0 in p.
follow init.
follow (Inc0 2 2); cbn.
follow (Inc1 4 1); cbn.
follow (Rst1 6); cbn.
follow (Inc0 2 54); cbn.
follow (Inc1 4 53); cbn.
follow (Inc0 8 51); cbn.
follow (Inc1 13 50); cbn.
follow (Inc1 21 49); cbn.
follow (Inc1 33 48); cbn.
follow (Inc1 51 47); cbn.
follow (Inc1 78 46); cbn.
follow (Inc0 119 44); cbn.
Abort.

