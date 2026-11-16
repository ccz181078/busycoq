From BusyCoq Require Import Individual33.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB2LA1RA_1LC2RC2RB_---1RA1LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1] <* [2]^^a <* <[1]^^b {{A}}> [1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (1+c) -->*
  S1 a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n+c) -->*
  S1 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Inc2 a b:
  S1 (1+a) b 0 -->*
  S1 a (3+b) 0.
Proof.
  es.
Qed.

Lemma Incs2 a b:
  S1 a b 0 -->*
  S1 0 (a*3+b) 0.
Proof.
  gen b.
  ind a Inc2.
Qed.

Lemma Rst a:
  S1 0 a 0 -->+
  S1 0 0 (4+a).
Proof.
  es.
Qed.

Lemma Rst1 b c:
  S1 0 b (3+c) -->*
  S1 (3+b) 1 c.
Proof.
  es.
Qed.

Definition P a b :=
  forall c,
  S1 0 0 (b+c) -->*
  S1 0 a c.

Lemma P_S a b:
  P a b ->
  P (a*2+7) (a+b+6).
Proof.
  unfold P.
  intros HP c.
  specialize (HP (3+(a+c+3))).
  eapply evstep_trans.
  2: follow HP.
  1: finish.
  follow Rst1.
  mid (S1 ((3+a)+0) 1 ((3+a)+c)).
  1: finish.
  follow Incs1.
  finish.
Qed.

Definition S n := S1 0 n 0.

Lemma BigStep a b n:
  b<=1+n<=3+a+b ->
  P a b ->
  S n -->+
  S (a*3+b+9-n).
Proof.
  unfold S,P.
  intros Hn HP.
  follow10 Rst.
  mid (S1 0 0 (b+(3+(1+n-b)))).
  1: finish.
  follow HP.
  follow Rst1.
  remember (1+n-b) as v1.
  mid (S1 (v1+(3+a-v1)) 1 (v1+0)).
  1: finish.
  follow Incs1.
  follow Incs2.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 10).
  1: es.
  eapply progress_nonhalt_cond with (P:=fun n => exists a b, P a b /\ (b<=1+n<=3+a+b /\ n<=4+a*2)).
  2: exists 7,6; split.
  2: unfold P; es.
  2: lia.
  intros n [a [b [HP [Hn Hn0]]]].
  eexists; split.
  1: eapply BigStep; eassumption.
  eexists _,_; split.
  1: apply P_S,HP.
  lia.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB2LA1RA_1LC1RC2RB_---1RA1LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1] <* [2]^^a <* <[1]^^b {{A}}> [1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (1+c) -->*
  S1 a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n+c) -->*
  S1 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Inc2 a b:
  S1 (1+a) b 0 -->*
  S1 a (3+b) 0.
Proof.
  es.
Qed.

Lemma Incs2 a b:
  S1 a b 0 -->*
  S1 0 (a*3+b) 0.
Proof.
  gen b.
  ind a Inc2.
Qed.

Lemma Rst a:
  S1 0 a 0 -->+
  S1 0 0 (4+a).
Proof.
  es.
Qed.

Lemma Rst1 b c:
  S1 0 b (3+c) -->*
  S1 (2+b) 2 c.
Proof.
  es.
Qed.

Definition P a b :=
  forall c,
  S1 0 0 (b+c) -->*
  S1 0 a c.

Lemma P_S a b:
  P a b ->
  P (a*2+6) (a+b+5).
Proof.
  unfold P.
  intros HP c.
  specialize (HP (3+(a+c+2))).
  eapply evstep_trans.
  2: follow HP.
  1: finish.
  follow Rst1.
  mid (S1 ((2+a)+0) 2 ((2+a)+c)).
  1: finish.
  follow Incs1.
  finish.
Qed.

Definition S n := S1 0 n 0.

Lemma BigStep a b n:
  b<=1+n<=2+a+b ->
  P a b ->
  S n -->+
  S (a*3+b+7-n).
Proof.
  unfold S,P.
  intros Hn HP.
  follow10 Rst.
  mid (S1 0 0 (b+(3+(1+n-b)))).
  1: finish.
  follow HP.
  follow Rst1.
  remember (1+n-b) as v1.
  mid (S1 (v1+(2+a-v1)) 2 (v1+0)).
  1: finish.
  follow Incs1.
  follow Incs2.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 8).
  1: es.
  eapply progress_nonhalt_cond with (P:=fun n => exists a b, P a b /\ (b<=1+n<=2+a+b /\ n<=3+a*2)).
  2: exists 6,5; split.
  2: unfold P; es.
  2: lia.
  intros n [a [b [HP [Hn Hn0]]]].
  eexists; split.
  1: eapply BigStep; eassumption.
  eexists _,_; split.
  1: apply P_S,HP.
  lia.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB2LA1RA_2LC2RC2RB_---2LA1LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1] <* [2]^^a <* <[1]^^b {{A}}> [1]^^c *> [2] *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (1+c) -->*
  S1 a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n+c) -->*
  S1 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Inc2 a b:
  S1 (1+a) b 0 -->*
  S1 a (3+b) 0.
Proof.
  unfold S1.
  er; sr.
  rewrite <-(lpow_rotate [] 2).
  step1s; sr.
  er.
Qed.

Lemma Incs2 a b:
  S1 a b 0 -->*
  S1 0 (a*3+b) 0.
Proof.
  gen b.
  ind a Inc2.
Qed.

Lemma Rst a:
  S1 0 a 0 -->+
  S1 1 2 (2+a).
Proof.
  es.
Qed.

Lemma Rst1 b c:
  S1 0 b (3+c) -->*
  S1 (2+b) 2 c.
Proof.
  es.
Qed.

Definition P a b :=
  forall c,
  S1 1 2 (b+c) -->*
  S1 0 a c.

Lemma P_S a b:
  P a b ->
  P (a*2+6) (a+b+5).
Proof.
  unfold P.
  intros HP c.
  specialize (HP (3+(a+c+2))).
  eapply evstep_trans.
  2: follow HP.
  1: finish.
  follow Rst1.
  mid (S1 ((2+a)+0) 2 ((2+a)+c)).
  1: finish.
  follow Incs1.
  finish.
Qed.

Definition S n := S1 0 n 0.

Lemma BigStep a b n:
  b+1<=n<=3+a+b ->
  P a b ->
  S n -->+
  S (a*3+b+9-n).
Proof.
  unfold S,P.
  intros Hn HP.
  follow10 Rst.
  mid (S1 1 2 (b+(3+(n-1-b)))).
  1: finish.
  follow HP.
  follow Rst1.
  remember (n-1-b) as v1.
  mid (S1 (v1+(2+a-v1)) 2 (v1+0)).
  1: finish.
  follow Incs1.
  follow Incs2.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 5).
  1: es.
  eapply progress_nonhalt_cond with (P:=fun n => exists a b, P a b /\ (b+1<=n<=3+a+b /\ n<=3+a*2)).
  2: exists 4,1%nat; split.
  2: unfold P; es.
  2: lia.
  intros n [a [b [HP [Hn Hn0]]]].
  eexists; split.
  1: eapply BigStep; eassumption.
  eexists _,_; split.
  1: apply P_S,HP.
  lia.
Qed.

End TM3.


