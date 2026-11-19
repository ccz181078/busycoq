From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.

Definition tm := Eval compute in (TM_from_str "1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Open Scope list.


Lemma AR l r n:
  l {{A}}> [0;1]^^n *> r -->*
  l <* [0;1]^^n {{A}}> r.
Proof.
  shift_rule.
  execute.
Qed.

Lemma ER l r n:
  l {{E}}> [0;1]^^n *> r -->*
  l <* [0;1]^^n {{E}}> r.
Proof.
  shift_rule.
  execute.
Qed.


Lemma DL l r n:
  l <* [0;1]^^n <{{D}} r -->*
  l <{{D}} [0;1]^^n *> r.
Proof.
  shift_rule.
  execute.
Qed.

Lemma AL l r n:
  l <* [1;0]^^n <{{A}} r -->*
  l <{{A}} [1;0]^^n *> r.
Proof.
  shift_rule.
  execute.
Qed.

Lemma BL l r n:
  l <* [0;1]^^n <{{B}} r -->*
  l <{{B}} [1;1]^^n *> r.
Proof.
  shift_rule.
  execute.
Qed.

Definition S3 a b c :=
  const 0 <* [1;0]^^a <* [1] <* [0;1]^^b {{A}}> [1;1]^^c *> [1] *> const 0.

Definition S2 a b :=
  const 0 <* [0;1]^^a {{A}}> [1;1]^^b *> const 0.

Lemma Inc1 a b c:
  S3 (a+1) b (c+1) -->*
  S3 a (b+2) c.
Proof.
  rewrite (Nat.add_comm c 1).
  unfold S3.
  execute.
  follow DL.
  execute.
  follow AR.
  execute.
  rewrite <-lpow_shift2.
  finish.
Qed.

Lemma Inc1s1 a b c:
  S3 (a+c) b c -->*
  S3 a (b+c*2) 0.
Proof.
  gen a b.
  induction c; intros a b.
  - finish.
  - replace (a+S c) with (a+c+1) by lia.
    replace (S c) with (c+1) by lia.
    follow Inc1.
    follow IHc.
    finish.
Qed.

Lemma Inc1s2 a b c:
  S3 a b (c+a) -->*
  S3 0 (b+a*2) c.
Proof.
  gen b c.
  induction a; intros b c.
  - finish.
  - replace (c+S a) with (c+a+1) by lia.
    replace (S a) with (a+1) by lia.
    follow Inc1.
    follow IHa.
    finish.
Qed.

Lemma Inc2 a b:
  S2 a (b+1) -->*
  S2 (a+2) b.
Proof.
  rewrite (Nat.add_comm b 1).
  unfold S2.
  execute.
  follow DL.
  execute.
  follow AR.
  execute.
  rewrite <-lpow_shift2.
  finish.
Qed.

Lemma Inc2s a b:
  S2 a b -->*
  S2 (a+b*2) 0.
Proof.
  gen a.
  induction b; intros a.
  - finish.
  - replace (S b) with (b+1) by lia.
    follow Inc2.
    follow IHb.
    finish.
Qed.

Lemma LOverflow1 n m:
  S3 0 n (m+2) -->*
  S3 (n+2) 1 m.
Proof.
  rewrite (Nat.add_comm m 2).
  unfold S3.
  execute.
  follow DL.
  execute.
  follow ER.
  execute.
  rewrite lpow_shift21.
  rewrite lpow_shift2.
  finish.
Qed.

Lemma LOverflow1' n:
  S3 0 n 1 -->*
  S3 2 1 (n+3).
Proof.
  unfold S3.
  execute.
  follow DL.
  execute.
  follow ER.
  execute.
  follow DL.
  execute.
  follow AR.
  execute.
  follow BL.
  do 16 step.
  repeat rewrite lpow_shift2.
  rewrite lpow_shift21.
  finish.
Qed.

Lemma LOverflow1'' n:
  halts tm (S3 0 n 0).
Proof.
  unfold S3.
  unfold halts,halts_in.
  eapply halts_evstep.
  2:{
    repeat step.
    follow DL.
    repeat step.
    follow ER.
    repeat step.
    constructor.
  }
  apply halted_halts.
  constructor.
Qed.

Lemma ROverflow1 m n:
  S3 (m+1) n 0 -->*
  S2 (m+2) (n+1).
Proof.
  unfold S3,S2.
  execute.
  follow DL.
  execute.
  follow AR.
  execute.
  follow BL.
  execute.
  follow AL.
  rewrite lpow_shift2.
  rewrite <-lpow_shift21.
  execute.
  follow AR.
  execute.
  repeat rewrite lpow_shift2.
  finish.
Qed.

Lemma ROverflow2 n:
  S2 (n+1) 0 -->*
  S3 2 1 n.
Proof.
  unfold S2,S3.
  execute.
  follow BL.
  rewrite lpow_shift2.
  rewrite lpow_shift21.
  execute.
Qed.

Definition N a b := S3 a 1 b.

Lemma MOv a:
  N a (a+1) -->*
  N 2 (a*2+4).
Proof.
  unfold N.
  rewrite (Nat.add_comm a 1).
  follow Inc1s2.
  follow LOverflow1'.
  finish.
Qed.

Lemma LOv a b:
  N a (b+a+2) -->*
  N (a*2+3) b.
Proof.
  unfold N.
  replace (b+a+2) with (b+2+a) by lia.
  follow Inc1s2.
  follow LOverflow1.
  finish.
Qed.

Lemma ROv a b:
  N (a+b+1) b -->*
  N 2 (a+b*4+5).
Proof.
  unfold N.
  replace (a+b+1) with (a+1+b) by lia.
  follow Inc1s1.
  follow ROverflow1.
  follow Inc2s.
  replace (a+2+(1+b*2+1)*2) with (a+b*4+5+1) by lia.
  follow ROverflow2.
  finish.
Qed.

Lemma init:
  c0 -->* N 2 3.
Proof.
  unfold N,S3.
  do 54 step.
  finish.
Qed.

Lemma Halt a:
  halts tm (N a a).
Proof.
  unfold N.
  eapply halts_evstep.
  2:{
    follow (Inc1s2 a 1 0).
    constructor.
  }
  apply LOverflow1''.
Qed.

Check MOv.
Check LOv.
Check ROv.
Check init.
Check Halt.

(*
```
1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE

start from (2,3)
(a,b+a+2) --> (2a+3,b)
(a+b+1,b) --> (2,a+4b+5)
(a,a) --> halt          not used?
(a,a+1) --> (2,2a+4)    only used once?

(a,b) := 0^inf 01^a 110 A> 1^(2b+1) 0^inf

example:
(2,3)-->
(2,8)-->(7,4)-->
(2,23)-->(7,19)-->(17,10)-->
(2,51)-->(7,47)-->(17,38)-->(37,19)-->
(2,98)-->(7,94)-->(17,85)-->(37,66)-->(77,27)-->
(2,162)-->(7,158)-->(17,149)-->(37,130)-->(77,91)-->(157,12)-->
(2,197)-->(7,193)-->(17,184)-->(37,165)-->(77,126)-->(157,47)-->
(2,302)-->(7,298)-->(17,289)-->(37,270)-->(77,231)-->(157,152)-->
(2,617)-->(7,613)-->(17,604)-->(37,585)-->(77,546)-->(157,467)-->(317,308)-->
...
```
*)

Goal N 2 3 -->* N 2 51.
Proof.
  follow MOv; cbn.
  follow (LOv 2 4); cbn.
  follow (ROv 2 4); cbn.
  follow (LOv 2 19); cbn.
  follow (LOv 7 10); cbn.
  follow (ROv 6 10); cbn.
  finish.
Qed.


Fixpoint ai i :=
  match i with
  | O => 7
  | S i0 => (ai i0)*2+3
  end.

Lemma ai_spec i:
  ai i + 3 = 10*2^i.
Proof.
  induction i.
  - reflexivity.
  - cbn[ai].
    rewrite Nat.pow_succ_r'.
    lia.
Qed.

Fixpoint Si i :=
  match i with
  | O => O
  | S i0 => Si i0 + ((ai i0)+2)
  end.

Lemma Si_spec i:
  Si i + i + 10 = 10*2^i.
Proof.
  induction i.
  - reflexivity.
  - cbn[Si].
    pose proof (ai_spec i).
    rewrite Nat.pow_succ_r'.
    lia.
Qed.


Definition N' i b := N (ai i) b.

Lemma LOv' i b:
  N' i (b+(ai i)+2) -->*
  N' (S i) b.
Proof.
  unfold N'.
  follow LOv.
  finish.
Qed.

Lemma LOv'' i b:
  N' 0 (b+(Si i)) -->*
  N' i b.
Proof.
  gen b.
  induction i; intros b.
  - cbn.
    finish.
  - cbn[Si].
    replace (b+(Si i+(ai i+2))) with (b+ai i+2+Si i) by lia.
    follow IHi.
    follow LOv'.
    finish.
Qed.

Lemma ROv' i b:
  b < ai i ->
  N' i b -->*
  N' 0 ((ai i)+b*3).
Proof.
  intro H.
  unfold N'.
  replace (N (ai i) b) with (N (ai i-b-1+b+1) b) by (f_equal; lia).
  follow ROv.
  remember (ai i-b-1) as a.
  replace (a+b*4+5) with (a+b*4+1+2+2) by lia.
  follow LOv.
  subst.
  finish.
Qed.

Lemma ai_Si i:
  ai i = Si i + i + 7.
Proof.
  pose proof (ai_spec i).
  pose proof (Si_spec i).
  lia.
Qed.

Lemma ROv'' i b:
  b < ai i ->
  N' i b -->*
  N' i (b*3+i+7).
Proof.
  intro H.
  follow ROv'.
  rewrite ai_Si.
  replace (Si i+i+7+b*3) with (b*3+i+7+Si i) by lia.
  follow LOv''.
  finish.
Qed.

Lemma LOv''' i b:
  b >= ai i + 2 ->
  N' i b -->*
  N' (S i) (b-((ai i)+2)).
Proof.
  intro H.
  replace (N' i b) with (N' i (b-(ai i+2)+ai i+2)) by (f_equal; lia).
  follow LOv'.
  finish.
Qed.

Lemma Halt' i b:
  b = ai i ->
  halts tm (N' i b).
Proof.
  intro H.
  subst.
  apply Halt.
Qed.

Lemma MOv' i b:
  b = ai i + 1 ->
  N' i b -->*
  N' 0 ((ai i)*2).
Proof.
  intro H.
  subst.
  unfold N'.
  follow MOv.
  replace (ai i*2+4) with (ai i*2+2+2) by lia.
  follow LOv.
  finish.
Qed.

Lemma MOv'' i b:
  b = ai i + 1 ->
  N' i b -->*
  N' i (ai i + i + 7).
Proof.
  intro H.
  follow MOv'.
  clear H.
  rewrite ai_Si.
  replace ((Si i+i+7)*2) with ((Si i+i*2+14)+Si i) by lia.
  follow LOv''.
  finish.
Qed.

Lemma MOv''' i b:
  b = ai i + 1 ->
  N' i b -->*
  N' (S i) (i + 5).
Proof.
  intro H.
  follow MOv''.
  replace (ai i+i+7) with (i+5+ai i+2) by lia.
  follow LOv'.
  finish.
Qed.

Lemma init':
  c0 -->* N' 0 4.
Proof.
  follow init.
  follow MOv; cbn.
  follow (LOv 2 4); cbn.
  finish.
Qed.

Check init'.
Check LOv'''.
Check ROv''.
Check Halt'.
Check MOv'''.

(*
```
start from <0,4>
b >= a(i)+2: <i,b> --> <i+1,b-a(i)-2>
b <= a(i)-1: <i,b> --> <i,3b+i+7>
b =  a(i)+0: <i,b> --> halt
b =  a(i)+1: <i,b> --> <i+1,i+5>

<i,b> = (a(i),b)
a(i) = 10*2^i-3
```
*)



