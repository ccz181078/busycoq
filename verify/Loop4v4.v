From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require ES_v2 ES_v3.

Ltac es_v2 := ES_v2.es.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1LB0RF_1LC1LA_1RD0LE_1RB1RD_---1LC_1LC1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1;1]^^a <* <[0;1]^^b {{A}}> [0;1]^^c *> 0inf.

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
  S1 0 3 a.
Proof.
  es.
Qed.

Lemma Rst1 b c:
  S1 0 b (2+c) -->*
  S1 (2+b) 1 c.
Proof.
  es.
Qed.

Definition P a b :=
  forall c,
  S1 0 3 (b+c) -->*
  S1 0 a c.

Lemma P_O: P 3 0.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S a b:
  P a b ->
  P (a*2+5) (a+b+4).
Proof.
  unfold P.
  intros HP c.
  specialize (HP (2+(a+c+2))).
  eapply evstep_trans.
  2: follow HP.
  1: finish.
  follow Rst1.
  mid (S1 ((2+a)+0) 1 ((2+a)+c)).
  1: finish.
  follow Incs1.
  finish.
Qed.

Definition S n := S1 0 n 0.

Lemma BigStep a b n:
  b+2<=n<=4+a+b ->
  P a b ->
  S n -->+
  S (a*3+b+9-n).
Proof.
  unfold S,P.
  intros Hn HP.
  follow10 Rst.
  mid (S1 0 3 (b+(2+(n-b-2)))).
  1: finish.
  follow HP.
  follow Rst1.
  remember (n-b-2) as v1.
  mid (S1 (v1+(2+a-v1)) 1 (v1+0)).
  1: finish.
  follow Incs1.
  follow Incs2.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 15).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a b, P a b /\ (b+2<=n<=4+a+b /\ n<=a*2+3)).
  2: exists 11,7; split.
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
Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC1RB_1LA1LE_---1LA_1LC0RF_1LA1RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1;1]^^a <* <[0;1]^^b {{E}}> [0;1]^^c *> 0inf.

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
  S1 0 3 a.
Proof.
  es.
Qed.

Lemma Rst1 b c:
  S1 0 b (2+c) -->*
  S1 (2+b) 1 c.
Proof.
  es.
Qed.

Definition P a b :=
  forall c,
  S1 0 3 (b+c) -->*
  S1 0 a c.

Lemma P_O: P 3 0.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S a b:
  P a b ->
  P (a*2+5) (a+b+4).
Proof.
  unfold P.
  intros HP c.
  specialize (HP (2+(a+c+2))).
  eapply evstep_trans.
  2: follow HP.
  1: finish.
  follow Rst1.
  mid (S1 ((2+a)+0) 1 ((2+a)+c)).
  1: finish.
  follow Incs1.
  finish.
Qed.

Definition S n := S1 0 n 0.

Lemma BigStep a b n:
  b+2<=n<=4+a+b ->
  P a b ->
  S n -->+
  S (a*3+b+9-n).
Proof.
  unfold S,P.
  intros Hn HP.
  follow10 Rst.
  mid (S1 0 3 (b+(2+(n-b-2)))).
  1: finish.
  follow HP.
  follow Rst1.
  remember (n-b-2) as v1.
  mid (S1 (v1+(2+a-v1)) 1 (v1+0)).
  1: finish.
  follow Incs1.
  follow Incs2.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 14).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a b, P a b /\ (b+2<=n<=4+a+b /\ n<=a*2+3)).
  2: exists 11,7; split.
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
Definition tm := Eval compute in (TM_from_str "1RB0LE_1LC1RD_1LA0LB_0RB0RC_1LD0LF_---1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1]^^a <* <[1;0]^^b <* [1] {{D}}> [1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (3+c) -->*
  S1 a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n*3+c) -->*
  S1 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition S2 a b c :=
  0inf <* [1]^^(1+a) <* <[0;1] <* <[0;1;1;1]^^b <* <[0;1]^^c <* <[0;1;1;1;0] {{B}}> 0inf.

Lemma Inc2 a b c:
  S2 a (1+b) c -->*
  S2 a b (5+c).
Proof.
  es.
Qed.

Lemma Incs2 a b c:
  S2 a b c -->*
  S2 a 0 (b*5+c).
Proof.
  gen c.
  ind b Inc2.
Qed.

Lemma Inc3 a c:
  S2 (1+a) 0 c -->*
  S2 a 0 (2+c).
Proof.
  es.
Qed.

Lemma Incs3 a c:
  S2 a 0 c -->*
  S2 0 0 (a*2+c).
Proof.
  gen c.
  ind a Inc3.
Qed.

Lemma Rst3 a:
  S2 0 0 a -->*
  S1 0 7 (a*2).
Proof.
  es.
Qed.

Lemma Rst1 b c:
  S1 0 b (2+c) -->*
  S1 (5+b*2) 0 c.
Proof.
  es.
Qed.

Lemma Rst a b:
  S1 (3+a) (b*2) 0 -->+
  S1 0 7 (a*4+b*10).
Proof.
  mid10 (S2 a b 0).
  1: es.
  follow Incs2.
  follow Incs3.
  follow Rst3.
  finish.
Qed.

Definition P a b :=
  forall c,
  S1 0 7 (b+c) -->*
  S1 0 a c.

Lemma P_O: P 7 0.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S a b:
  P a b ->
  P (a*4+10) (a*6+b+17).
Proof.
  unfold P.
  intros HP c.
  specialize (HP (2+((5+a*2)*3+c))).
  eapply evstep_trans.
  2: follow HP.
  1: finish.
  follow Rst1.
  mid (S1 ((5+a*2)+0) 0 ((5+a*2)*3+c)).
  1: finish.
  follow Incs1.
  finish.
Qed.

Definition S n := S1 0 7 n.

Lemma BigStep a b c n:
  b+2<=n ->
  n-b-2=c*3 ->
  c<=2+a*2 ->
  P a b ->
  S n -->+
  S (8+a*8+c*6).
Proof.
  unfold S,P.
  intros Hn Hc Hc0 HP.
  mid01 (S1 0 7 (b+(2+(n-b-2)))).
  1: finish.
  follow HP.
  follow Rst1.
  rewrite Hc.
  mid01 (S1 (c+(3+(2+a*2-c))) 0 (c*3+0)).
  1: finish.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Rst.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 8).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a b c d, P a b /\ (b+2<=n /\ n-b-2=c*3 /\ c<=2+a*2 /\ a*2+c*6-b-11=d*3 /\ b*2+13<=a*2+n)).
  2: exists 7,O,2,5; split.
  2: unfold P; es.
  2: lia.
  intros n [a [b [c [d [HP Hn]]]]].
  eexists; split.
  1: eapply (BigStep a b c n); try assumption; lia.
  eexists _,_,d,((a*2+d*6-b-8)/3); split.
  1: apply P_S,HP.
  repeat split; lia.
Qed.

End TM3.


Module TM4.
Definition tm := Eval compute in (TM_from_str "1RB0LE_1LC1RD_1LA0LB_0RB0RC_1LD1LF_---0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1]^^a <* <[1;0]^^b <* [1] {{D}}> [1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (3+c) -->*
  S1 a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n*3+c) -->*
  S1 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition S2 a b c :=
  0inf <* [1]^^(1+a) <* <[0;1] <* <[0;1;1;1]^^b <* <[0;1]^^c <* <[0;1;1;1;0] {{B}}> 0inf.

Lemma Inc2 a b c:
  S2 a (1+b) c -->*
  S2 a b (5+c).
Proof.
  es.
Qed.

Lemma Incs2 a b c:
  S2 a b c -->*
  S2 a 0 (b*5+c).
Proof.
  gen c.
  ind b Inc2.
Qed.

Lemma Inc3 a c:
  S2 (1+a) 0 c -->*
  S2 a 0 (2+c).
Proof.
  es.
Qed.

Lemma Incs3 a c:
  S2 a 0 c -->*
  S2 0 0 (a*2+c).
Proof.
  gen c.
  ind a Inc3.
Qed.

Lemma Rst3 a:
  S2 0 0 a -->*
  S1 0 7 (a*2).
Proof.
  es.
Qed.

Lemma Rst1 b c:
  S1 0 b (2+c) -->*
  S1 (5+b*2) 0 c.
Proof.
  es.
Qed.

Lemma Rst a b:
  S1 (3+a) (b*2) 0 -->+
  S1 0 7 (a*4+b*10).
Proof.
  mid10 (S2 a b 0).
  1: es.
  follow Incs2.
  follow Incs3.
  follow Rst3.
  finish.
Qed.

Definition P a b :=
  forall c,
  S1 0 7 (b+c) -->*
  S1 0 a c.

Lemma P_O: P 7 0.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S a b:
  P a b ->
  P (a*4+10) (a*6+b+17).
Proof.
  unfold P.
  intros HP c.
  specialize (HP (2+((5+a*2)*3+c))).
  eapply evstep_trans.
  2: follow HP.
  1: finish.
  follow Rst1.
  mid (S1 ((5+a*2)+0) 0 ((5+a*2)*3+c)).
  1: finish.
  follow Incs1.
  finish.
Qed.

Definition S n := S1 0 7 n.

Lemma BigStep a b c n:
  b+2<=n ->
  n-b-2=c*3 ->
  c<=2+a*2 ->
  P a b ->
  S n -->+
  S (8+a*8+c*6).
Proof.
  unfold S,P.
  intros Hn Hc Hc0 HP.
  mid01 (S1 0 7 (b+(2+(n-b-2)))).
  1: finish.
  follow HP.
  follow Rst1.
  rewrite Hc.
  mid01 (S1 (c+(3+(2+a*2-c))) 0 (c*3+0)).
  1: finish.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Rst.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 8).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a b c d, P a b /\ (b+2<=n /\ n-b-2=c*3 /\ c<=2+a*2 /\ a*2+c*6-b-11=d*3 /\ b*2+13<=a*2+n)).
  2: exists 7,O,2,5; split.
  2: unfold P; es.
  2: lia.
  intros n [a [b [c [d [HP Hn]]]]].
  eexists; split.
  1: eapply (BigStep a b c n); try assumption; lia.
  eexists _,_,d,((a*2+d*6-b-8)/3); split.
  1: apply P_S,HP.
  repeat split; lia.
Qed.

End TM4.


Module TM5.
Definition tm := Eval compute in (TM_from_str "1RB0LE_1LC1RD_1LA0LB_0RB0RC_0LF1LC_---1LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1]^^a <* <[1;0]^^b <* [1] {{D}}> [1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (3+c) -->*
  S1 a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n*3+c) -->*
  S1 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition S2 a b c :=
  0inf <* [1]^^(1+a) <* <[0;1] <* <[0;1;1;1]^^b <* <[0;1]^^c <* <[0;1;1;1;0] {{B}}> 0inf.

Lemma Inc2 a b c:
  S2 a (1+b) c -->*
  S2 a b (5+c).
Proof.
  es.
Qed.

Lemma Incs2 a b c:
  S2 a b c -->*
  S2 a 0 (b*5+c).
Proof.
  gen c.
  ind b Inc2.
Qed.

Lemma Inc3 a c:
  S2 (1+a) 0 c -->*
  S2 a 0 (2+c).
Proof.
  es.
Qed.

Lemma Incs3 a c:
  S2 a 0 c -->*
  S2 0 0 (a*2+c).
Proof.
  gen c.
  ind a Inc3.
Qed.

Lemma Rst3 a:
  S2 0 0 a -->*
  S1 0 7 (a*2).
Proof.
  es.
Qed.

Lemma Rst1 b c:
  S1 0 b (2+c) -->*
  S1 (5+b*2) 0 c.
Proof.
  es.
Qed.

Lemma Rst a b:
  S1 (3+a) (b*2) 0 -->+
  S1 0 7 (a*4+b*10).
Proof.
  mid10 (S2 a b 0).
  1: es.
  follow Incs2.
  follow Incs3.
  follow Rst3.
  finish.
Qed.

Definition P a b :=
  forall c,
  S1 0 7 (b+c) -->*
  S1 0 a c.

Lemma P_O: P 7 0.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S a b:
  P a b ->
  P (a*4+10) (a*6+b+17).
Proof.
  unfold P.
  intros HP c.
  specialize (HP (2+((5+a*2)*3+c))).
  eapply evstep_trans.
  2: follow HP.
  1: finish.
  follow Rst1.
  mid (S1 ((5+a*2)+0) 0 ((5+a*2)*3+c)).
  1: finish.
  follow Incs1.
  finish.
Qed.

Definition S n := S1 0 7 n.

Lemma BigStep a b c n:
  b+2<=n ->
  n-b-2=c*3 ->
  c<=2+a*2 ->
  P a b ->
  S n -->+
  S (8+a*8+c*6).
Proof.
  unfold S,P.
  intros Hn Hc Hc0 HP.
  mid01 (S1 0 7 (b+(2+(n-b-2)))).
  1: finish.
  follow HP.
  follow Rst1.
  rewrite Hc.
  mid01 (S1 (c+(3+(2+a*2-c))) 0 (c*3+0)).
  1: finish.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Rst.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 8).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a b c d, P a b /\ (b+2<=n /\ n-b-2=c*3 /\ c<=2+a*2 /\ a*2+c*6-b-11=d*3 /\ b*2+13<=a*2+n)).
  2: exists 7,O,2,5; split.
  2: unfold P; es.
  2: lia.
  intros n [a [b [c [d [HP Hn]]]]].
  eexists; split.
  1: eapply (BigStep a b c n); try assumption; lia.
  eexists _,_,d,((a*2+d*6-b-8)/3); split.
  1: apply P_S,HP.
  repeat split; lia.
Qed.

End TM5.


Module TM6.
Definition tm := Eval compute in (TM_from_str "1RB0LE_1LC1RD_1LA0LB_0RB0RC_0LF1RE_---1LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1]^^a <* <[1;0]^^b <* [1] {{D}}> [1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (3+c) -->*
  S1 a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n*3+c) -->*
  S1 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition S2 a b c :=
  0inf <* [1]^^(1+a) <* <[0;1] <* <[0;1;1;1]^^b <* <[0;1]^^c <* <[0;1;1;1;0] {{B}}> 0inf.

Lemma Inc2 a b c:
  S2 a (1+b) c -->*
  S2 a b (5+c).
Proof.
  es.
Qed.

Lemma Incs2 a b c:
  S2 a b c -->*
  S2 a 0 (b*5+c).
Proof.
  gen c.
  ind b Inc2.
Qed.

Lemma Inc3 a c:
  S2 (1+a) 0 c -->*
  S2 a 0 (2+c).
Proof.
  es.
Qed.

Lemma Incs3 a c:
  S2 a 0 c -->*
  S2 0 0 (a*2+c).
Proof.
  gen c.
  ind a Inc3.
Qed.

Lemma Rst3 a:
  S2 0 0 a -->*
  S1 0 7 (a*2).
Proof.
  es.
Qed.

Lemma Rst1 b c:
  S1 0 b (2+c) -->*
  S1 (5+b*2) 0 c.
Proof.
  es.
Qed.

Lemma Rst a b:
  S1 (3+a) (b*2) 0 -->+
  S1 0 7 (a*4+b*10).
Proof.
  mid10 (S2 a b 0).
  1: es.
  follow Incs2.
  follow Incs3.
  follow Rst3.
  finish.
Qed.

Definition P a b :=
  forall c,
  S1 0 7 (b+c) -->*
  S1 0 a c.

Lemma P_O: P 7 0.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S a b:
  P a b ->
  P (a*4+10) (a*6+b+17).
Proof.
  unfold P.
  intros HP c.
  specialize (HP (2+((5+a*2)*3+c))).
  eapply evstep_trans.
  2: follow HP.
  1: finish.
  follow Rst1.
  mid (S1 ((5+a*2)+0) 0 ((5+a*2)*3+c)).
  1: finish.
  follow Incs1.
  finish.
Qed.

Definition S n := S1 0 7 n.

Lemma BigStep a b c n:
  b+2<=n ->
  n-b-2=c*3 ->
  c<=2+a*2 ->
  P a b ->
  S n -->+
  S (8+a*8+c*6).
Proof.
  unfold S,P.
  intros Hn Hc Hc0 HP.
  mid01 (S1 0 7 (b+(2+(n-b-2)))).
  1: finish.
  follow HP.
  follow Rst1.
  rewrite Hc.
  mid01 (S1 (c+(3+(2+a*2-c))) 0 (c*3+0)).
  1: finish.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Rst.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 8).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a b c d, P a b /\ (b+2<=n /\ n-b-2=c*3 /\ c<=2+a*2 /\ a*2+c*6-b-11=d*3 /\ b*2+13<=a*2+n)).
  2: exists 7,O,2,5; split.
  2: unfold P; es.
  2: lia.
  intros n [a [b [c [d [HP Hn]]]]].
  eexists; split.
  1: eapply (BigStep a b c n); try assumption; lia.
  eexists _,_,d,((a*2+d*6-b-8)/3); split.
  1: apply P_S,HP.
  repeat split; lia.
Qed.

End TM6.


Module TM7.
Definition tm := Eval compute in (TM_from_str "1RB0LE_1LC1RD_1LA0LB_0RB0RC_1LF1LC_---1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1]^^a <* <[1;0]^^b <* [1] {{D}}> [1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (3+c) -->*
  S1 a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n*3+c) -->*
  S1 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition S2 a b c :=
  0inf <* [1]^^(1+a) <* <[0;1] <* <[0;1;1;1]^^b <* <[0;1]^^c <* <[0;1;1;1;0] {{B}}> 0inf.

Lemma Inc2 a b c:
  S2 a (1+b) c -->*
  S2 a b (5+c).
Proof.
  es.
Qed.

Lemma Incs2 a b c:
  S2 a b c -->*
  S2 a 0 (b*5+c).
Proof.
  gen c.
  ind b Inc2.
Qed.

Lemma Inc3 a c:
  S2 (1+a) 0 c -->*
  S2 a 0 (2+c).
Proof.
  es.
Qed.

Lemma Incs3 a c:
  S2 a 0 c -->*
  S2 0 0 (a*2+c).
Proof.
  gen c.
  ind a Inc3.
Qed.

Lemma Rst3 a:
  S2 0 0 a -->*
  S1 0 7 (a*2).
Proof.
  es.
Qed.

Lemma Rst1 b c:
  S1 0 b (2+c) -->*
  S1 (5+b*2) 0 c.
Proof.
  es.
Qed.

Lemma Rst a b:
  S1 (3+a) (b*2) 0 -->+
  S1 0 7 (a*4+b*10).
Proof.
  mid10 (S2 a b 0).
  1: es.
  follow Incs2.
  follow Incs3.
  follow Rst3.
  finish.
Qed.

Definition P a b :=
  forall c,
  S1 0 7 (b+c) -->*
  S1 0 a c.

Lemma P_O: P 7 0.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S a b:
  P a b ->
  P (a*4+10) (a*6+b+17).
Proof.
  unfold P.
  intros HP c.
  specialize (HP (2+((5+a*2)*3+c))).
  eapply evstep_trans.
  2: follow HP.
  1: finish.
  follow Rst1.
  mid (S1 ((5+a*2)+0) 0 ((5+a*2)*3+c)).
  1: finish.
  follow Incs1.
  finish.
Qed.

Definition S n := S1 0 7 n.

Lemma BigStep a b c n:
  b+2<=n ->
  n-b-2=c*3 ->
  c<=2+a*2 ->
  P a b ->
  S n -->+
  S (8+a*8+c*6).
Proof.
  unfold S,P.
  intros Hn Hc Hc0 HP.
  mid01 (S1 0 7 (b+(2+(n-b-2)))).
  1: finish.
  follow HP.
  follow Rst1.
  rewrite Hc.
  mid01 (S1 (c+(3+(2+a*2-c))) 0 (c*3+0)).
  1: finish.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Rst.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 8).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a b c d, P a b /\ (b+2<=n /\ n-b-2=c*3 /\ c<=2+a*2 /\ a*2+c*6-b-11=d*3 /\ b*2+13<=a*2+n)).
  2: exists 7,O,2,5; split.
  2: unfold P; es.
  2: lia.
  intros n [a [b [c [d [HP Hn]]]]].
  eexists; split.
  1: eapply (BigStep a b c n); try assumption; lia.
  eexists _,_,d,((a*2+d*6-b-8)/3); split.
  1: apply P_S,HP.
  repeat split; lia.
Qed.

End TM7.


Module TM8.
Definition tm := Eval compute in (TM_from_str "1RB0LE_1LC1RD_1LA0LB_0RB0RC_1LF1LC_---0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1]^^a <* <[1;0]^^b <* [1] {{D}}> [1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (3+c) -->*
  S1 a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n*3+c) -->*
  S1 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition S2 a b c :=
  0inf <* [1]^^(1+a) <* <[0;1] <* <[0;1;1;1]^^b <* <[0;1]^^c <* <[0;1;1;1;0] {{B}}> 0inf.

Lemma Inc2 a b c:
  S2 a (1+b) c -->*
  S2 a b (5+c).
Proof.
  es.
Qed.

Lemma Incs2 a b c:
  S2 a b c -->*
  S2 a 0 (b*5+c).
Proof.
  gen c.
  ind b Inc2.
Qed.

Lemma Inc3 a c:
  S2 (1+a) 0 c -->*
  S2 a 0 (2+c).
Proof.
  es.
Qed.

Lemma Incs3 a c:
  S2 a 0 c -->*
  S2 0 0 (a*2+c).
Proof.
  gen c.
  ind a Inc3.
Qed.

Lemma Rst3 a:
  S2 0 0 a -->*
  S1 0 7 (a*2).
Proof.
  es.
Qed.

Lemma Rst1 b c:
  S1 0 b (2+c) -->*
  S1 (5+b*2) 0 c.
Proof.
  es.
Qed.

Lemma Rst a b:
  S1 (3+a) (b*2) 0 -->+
  S1 0 7 (a*4+b*10).
Proof.
  mid10 (S2 a b 0).
  1: es.
  follow Incs2.
  follow Incs3.
  follow Rst3.
  finish.
Qed.

Definition P a b :=
  forall c,
  S1 0 7 (b+c) -->*
  S1 0 a c.

Lemma P_O: P 7 0.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S a b:
  P a b ->
  P (a*4+10) (a*6+b+17).
Proof.
  unfold P.
  intros HP c.
  specialize (HP (2+((5+a*2)*3+c))).
  eapply evstep_trans.
  2: follow HP.
  1: finish.
  follow Rst1.
  mid (S1 ((5+a*2)+0) 0 ((5+a*2)*3+c)).
  1: finish.
  follow Incs1.
  finish.
Qed.

Definition S n := S1 0 7 n.

Lemma BigStep a b c n:
  b+2<=n ->
  n-b-2=c*3 ->
  c<=2+a*2 ->
  P a b ->
  S n -->+
  S (8+a*8+c*6).
Proof.
  unfold S,P.
  intros Hn Hc Hc0 HP.
  mid01 (S1 0 7 (b+(2+(n-b-2)))).
  1: finish.
  follow HP.
  follow Rst1.
  rewrite Hc.
  mid01 (S1 (c+(3+(2+a*2-c))) 0 (c*3+0)).
  1: finish.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Rst.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 8).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a b c d, P a b /\ (b+2<=n /\ n-b-2=c*3 /\ c<=2+a*2 /\ a*2+c*6-b-11=d*3 /\ b*2+13<=a*2+n)).
  2: exists 7,O,2,5; split.
  2: unfold P; es.
  2: lia.
  intros n [a [b [c [d [HP Hn]]]]].
  eexists; split.
  1: eapply (BigStep a b c n); try assumption; lia.
  eexists _,_,d,((a*2+d*6-b-8)/3); split.
  1: apply P_S,HP.
  repeat split; lia.
Qed.

End TM8.


Module TM9.
Definition tm := Eval compute in (TM_from_str "1RB0LE_1LC1RD_1LA0LB_0RB0RC_1LF1RE_---0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1]^^a <* <[1;0]^^b <* [1] {{D}}> [1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (3+c) -->*
  S1 a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n*3+c) -->*
  S1 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition S2 a b c :=
  0inf <* [1]^^(1+a) <* <[0;1] <* <[0;1;1;1]^^b <* <[0;1]^^c <* <[0;1;1;1;0] {{B}}> 0inf.

Lemma Inc2 a b c:
  S2 a (1+b) c -->*
  S2 a b (5+c).
Proof.
  es.
Qed.

Lemma Incs2 a b c:
  S2 a b c -->*
  S2 a 0 (b*5+c).
Proof.
  gen c.
  ind b Inc2.
Qed.

Lemma Inc3 a c:
  S2 (1+a) 0 c -->*
  S2 a 0 (2+c).
Proof.
  es.
Qed.

Lemma Incs3 a c:
  S2 a 0 c -->*
  S2 0 0 (a*2+c).
Proof.
  gen c.
  ind a Inc3.
Qed.

Lemma Rst3 a:
  S2 0 0 a -->*
  S1 0 7 (a*2).
Proof.
  es.
Qed.

Lemma Rst1 b c:
  S1 0 b (2+c) -->*
  S1 (5+b*2) 0 c.
Proof.
  es.
Qed.

Lemma Rst a b:
  S1 (3+a) (b*2) 0 -->+
  S1 0 7 (a*4+b*10).
Proof.
  mid10 (S2 a b 0).
  1: es.
  follow Incs2.
  follow Incs3.
  follow Rst3.
  finish.
Qed.

Definition P a b :=
  forall c,
  S1 0 7 (b+c) -->*
  S1 0 a c.

Lemma P_O: P 7 0.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S a b:
  P a b ->
  P (a*4+10) (a*6+b+17).
Proof.
  unfold P.
  intros HP c.
  specialize (HP (2+((5+a*2)*3+c))).
  eapply evstep_trans.
  2: follow HP.
  1: finish.
  follow Rst1.
  mid (S1 ((5+a*2)+0) 0 ((5+a*2)*3+c)).
  1: finish.
  follow Incs1.
  finish.
Qed.

Definition S n := S1 0 7 n.

Lemma BigStep a b c n:
  b+2<=n ->
  n-b-2=c*3 ->
  c<=2+a*2 ->
  P a b ->
  S n -->+
  S (8+a*8+c*6).
Proof.
  unfold S,P.
  intros Hn Hc Hc0 HP.
  mid01 (S1 0 7 (b+(2+(n-b-2)))).
  1: finish.
  follow HP.
  follow Rst1.
  rewrite Hc.
  mid01 (S1 (c+(3+(2+a*2-c))) 0 (c*3+0)).
  1: finish.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Rst.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 8).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a b c d, P a b /\ (b+2<=n /\ n-b-2=c*3 /\ c<=2+a*2 /\ a*2+c*6-b-11=d*3 /\ b*2+13<=a*2+n)).
  2: exists 7,O,2,5; split.
  2: unfold P; es.
  2: lia.
  intros n [a [b [c [d [HP Hn]]]]].
  eexists; split.
  1: eapply (BigStep a b c n); try assumption; lia.
  eexists _,_,d,((a*2+d*6-b-8)/3); split.
  1: apply P_S,HP.
  repeat split; lia.
Qed.

End TM9.


Module TM10.
Definition tm := Eval compute in (TM_from_str "1RB0RF_0RC1LD_1RD0RA_0LE1RC_0LB1LE_---0LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1]^^(1+a) <* <[0;1;0;1]^^b <* [0] {{A}}> [1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (3+c) -->*
  S1 a (1+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n*3+c) -->*
  S1 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Rst1 b c:
  S1 0 b (4+c) -->*
  S1 (7+b*4) 0 c.
Proof.
  es.
Qed.

Definition S2 a b :=
  0inf <* [1]^^(1+a) <* <[0;1;0;1]^^(1+b) {{B}}> 0inf.

Lemma Rst2 a b:
  S1 (1+a) b 2 -->*
  S2 a b.
Proof.
  es.
Qed.

Lemma Inc2 a b:
  S2 (1+a) b -->*
  S2 a (1+b).
Proof.
  es.
Qed.

Lemma Incs2 a b:
  S2 a b -->*
  S2 0 (a+b).
Proof.
  gen b.
  ind a Inc2.
Qed.

Lemma Rst a:
  S2 0 a -->+
  S1 0 1 (6+a*4).
Proof.
  es.
Qed.

Definition P a b :=
  forall c,
  S1 0 1 (b+c) -->*
  S1 0 a c.

Lemma P_O: P 1 0.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S a b:
  P a b ->
  P (a*4+7) (a*12+b+25).
Proof.
  unfold P.
  intros HP c.
  specialize (HP (4+((7+a*4)*3+c))).
  eapply evstep_trans.
  2: follow HP.
  1: finish.
  follow Rst1.
  mid (S1 ((7+a*4)+0) 0 ((7+a*4)*3+c)).
  1: finish.
  follow Incs1.
  finish.
Qed.

Definition S n := S1 0 1 n.

Lemma BigStep a b c n:
  b+4<=n ->
  n-b-4=c*3+2 ->
  c<=a*4+6 ->
  P a b ->
  S n -->+
  S (a*16+30).
Proof.
  unfold S,P.
  intros Hn Hc Hc0 HP.
  mid01 (S1 0 1 (b+(4+(n-b-4)))).
  1: finish.
  follow HP.
  follow Rst1.
  mid01 (S1 (c+(1+(6+a*4-c))) 0 (c*3+2)).
  1: finish.
  follow Incs1.
  follow Rst2.
  follow Incs2.
  follow10 Rst.
  finish.
Qed.

Close Scope sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 6).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a b c d, P a b /\ (b+4<=n /\ n-b-4=c*3+2 /\ c<=a*4+6 /\ b+d*3+2=a*4+1)).
  2: exists 1,0,0,1; split.
  2: unfold P; es.
  2: lia.
  intros n [a [b [c [d [HP Hn]]]]].
  eexists; split.
  1: eapply (BigStep a b c n); try assumption; lia.
  eexists _,_,d,((a*4+2-b)/3); split.
  1: apply P_S,HP.
  repeat split; lia.
Qed.

End TM10.


Module TM11.
Definition tm := Eval compute in (TM_from_str "1RB0RF_0RC1LD_1RD0RA_0LE1RC_0LB1LE_---0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1]^^(1+a) <* <[0;1;0;1]^^b <* [0] {{A}}> [1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (3+c) -->*
  S1 a (1+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n*3+c) -->*
  S1 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Rst1 b c:
  S1 0 b (4+c) -->*
  S1 (7+b*4) 0 c.
Proof.
  es.
Qed.

Definition S2 a b :=
  0inf <* [1]^^(1+a) <* <[0;1;0;1]^^(1+b) {{B}}> 0inf.

Lemma Rst2 a b:
  S1 (1+a) b 2 -->*
  S2 a b.
Proof.
  es.
Qed.

Lemma Inc2 a b:
  S2 (1+a) b -->*
  S2 a (1+b).
Proof.
  es.
Qed.

Lemma Incs2 a b:
  S2 a b -->*
  S2 0 (a+b).
Proof.
  gen b.
  ind a Inc2.
Qed.

Lemma Rst a:
  S2 0 a -->+
  S1 0 1 (6+a*4).
Proof.
  es.
Qed.

Definition P a b :=
  forall c,
  S1 0 1 (b+c) -->*
  S1 0 a c.

Lemma P_O: P 1 0.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S a b:
  P a b ->
  P (a*4+7) (a*12+b+25).
Proof.
  unfold P.
  intros HP c.
  specialize (HP (4+((7+a*4)*3+c))).
  eapply evstep_trans.
  2: follow HP.
  1: finish.
  follow Rst1.
  mid (S1 ((7+a*4)+0) 0 ((7+a*4)*3+c)).
  1: finish.
  follow Incs1.
  finish.
Qed.

Definition S n := S1 0 1 n.

Lemma BigStep a b c n:
  b+4<=n ->
  n-b-4=c*3+2 ->
  c<=a*4+6 ->
  P a b ->
  S n -->+
  S (a*16+30).
Proof.
  unfold S,P.
  intros Hn Hc Hc0 HP.
  mid01 (S1 0 1 (b+(4+(n-b-4)))).
  1: finish.
  follow HP.
  follow Rst1.
  mid01 (S1 (c+(1+(6+a*4-c))) 0 (c*3+2)).
  1: finish.
  follow Incs1.
  follow Rst2.
  follow Incs2.
  follow10 Rst.
  finish.
Qed.

Close Scope sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 6).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a b c d, P a b /\ (b+4<=n /\ n-b-4=c*3+2 /\ c<=a*4+6 /\ b+d*3+2=a*4+1)).
  2: exists 1,0,0,1; split.
  2: unfold P; es.
  2: lia.
  intros n [a [b [c [d [HP Hn]]]]].
  eexists; split.
  1: eapply (BigStep a b c n); try assumption; lia.
  eexists _,_,d,((a*4+2-b)/3); split.
  1: apply P_S,HP.
  repeat split; lia.
Qed.

End TM11.


Module TM12.
Definition tm := Eval compute in (TM_from_str "1RB1RF_0RC1LD_1RD0RA_0LE1RC_0LB1LE_---0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1]^^(1+a) <* <[0;1;0;1]^^b <* [0] {{A}}> [1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (3+c) -->*
  S1 a (1+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n*3+c) -->*
  S1 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Rst1 b c:
  S1 0 b (4+c) -->*
  S1 (7+b*4) 0 c.
Proof.
  es.
Qed.

Definition S2 a b :=
  0inf <* [1]^^(1+a) <* <[0;1;0;1]^^(1+b) {{B}}> 0inf.

Lemma Rst2 a b:
  S1 (1+a) b 2 -->*
  S2 a b.
Proof.
  es.
Qed.

Lemma Inc2 a b:
  S2 (1+a) b -->*
  S2 a (1+b).
Proof.
  es.
Qed.

Lemma Incs2 a b:
  S2 a b -->*
  S2 0 (a+b).
Proof.
  gen b.
  ind a Inc2.
Qed.

Lemma Rst a:
  S2 0 a -->+
  S1 0 1 (6+a*4).
Proof.
  es.
Qed.

Definition P a b :=
  forall c,
  S1 0 1 (b+c) -->*
  S1 0 a c.

Lemma P_O: P 1 0.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S a b:
  P a b ->
  P (a*4+7) (a*12+b+25).
Proof.
  unfold P.
  intros HP c.
  specialize (HP (4+((7+a*4)*3+c))).
  eapply evstep_trans.
  2: follow HP.
  1: finish.
  follow Rst1.
  mid (S1 ((7+a*4)+0) 0 ((7+a*4)*3+c)).
  1: finish.
  follow Incs1.
  finish.
Qed.

Definition S n := S1 0 1 n.

Lemma BigStep a b c n:
  b+4<=n ->
  n-b-4=c*3+2 ->
  c<=a*4+6 ->
  P a b ->
  S n -->+
  S (a*16+30).
Proof.
  unfold S,P.
  intros Hn Hc Hc0 HP.
  mid01 (S1 0 1 (b+(4+(n-b-4)))).
  1: finish.
  follow HP.
  follow Rst1.
  mid01 (S1 (c+(1+(6+a*4-c))) 0 (c*3+2)).
  1: finish.
  follow Incs1.
  follow Rst2.
  follow Incs2.
  follow10 Rst.
  finish.
Qed.

Close Scope sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 6).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a b c d, P a b /\ (b+4<=n /\ n-b-4=c*3+2 /\ c<=a*4+6 /\ b+d*3+2=a*4+1)).
  2: exists 1,0,0,1; split.
  2: unfold P; es.
  2: lia.
  intros n [a [b [c [d [HP Hn]]]]].
  eexists; split.
  1: eapply (BigStep a b c n); try assumption; lia.
  eexists _,_,d,((a*4+2-b)/3); split.
  1: apply P_S,HP.
  repeat split; lia.
Qed.

End TM12.


Module TM13.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LA_1RA0LE_0RA0RB_1LD0LF_---1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1]^^a <* <[1;0]^^b <* [1] {{D}}> [1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (3+c) -->*
  S1 a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n*3+c) -->*
  S1 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition S2 a b c :=
  0inf <* [1]^^(1+a) <* <[0;1] <* <[0;1;1;1]^^b <* <[0;1]^^c <* <[0;1;1;1;0] {{A}}> 0inf.

Lemma Inc2 a b c:
  S2 a (1+b) c -->*
  S2 a b (5+c).
Proof.
  es.
Qed.

Lemma Incs2 a b c:
  S2 a b c -->*
  S2 a 0 (b*5+c).
Proof.
  gen c.
  ind b Inc2.
Qed.

Lemma Inc3 a c:
  S2 (1+a) 0 c -->*
  S2 a 0 (2+c).
Proof.
  es.
Qed.

Lemma Incs3 a c:
  S2 a 0 c -->*
  S2 0 0 (a*2+c).
Proof.
  gen c.
  ind a Inc3.
Qed.

Lemma Rst3 a:
  S2 0 0 a -->*
  S1 0 7 (a*2).
Proof.
  es.
Qed.

Lemma Rst1 b c:
  S1 0 b (2+c) -->*
  S1 (5+b*2) 0 c.
Proof.
  es.
Qed.

Lemma Rst a b:
  S1 (3+a) (b*2) 0 -->+
  S1 0 7 (a*4+b*10).
Proof.
  mid10 (S2 a b 0).
  1: es.
  follow Incs2.
  follow Incs3.
  follow Rst3.
  finish.
Qed.

Definition P a b :=
  forall c,
  S1 0 7 (b+c) -->*
  S1 0 a c.

Lemma P_O: P 7 0.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S a b:
  P a b ->
  P (a*4+10) (a*6+b+17).
Proof.
  unfold P.
  intros HP c.
  specialize (HP (2+((5+a*2)*3+c))).
  eapply evstep_trans.
  2: follow HP.
  1: finish.
  follow Rst1.
  mid (S1 ((5+a*2)+0) 0 ((5+a*2)*3+c)).
  1: finish.
  follow Incs1.
  finish.
Qed.

Definition S n := S1 0 7 n.

Lemma BigStep a b c n:
  b+2<=n ->
  n-b-2=c*3 ->
  c<=2+a*2 ->
  P a b ->
  S n -->+
  S (8+a*8+c*6).
Proof.
  unfold S,P.
  intros Hn Hc Hc0 HP.
  mid01 (S1 0 7 (b+(2+(n-b-2)))).
  1: finish.
  follow HP.
  follow Rst1.
  rewrite Hc.
  mid01 (S1 (c+(3+(2+a*2-c))) 0 (c*3+0)).
  1: finish.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Rst.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 130).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a b c d, P a b /\ (b+2<=n /\ n-b-2=c*3 /\ c<=2+a*2 /\ a*2+c*6-b-11=d*3 /\ b*2+13<=a*2+n)).
  2: eexists _,_,23,48; split.
  2: apply P_S,P_O.
  2: lia.
  intros n [a [b [c [d [HP Hn]]]]].
  eexists; split.
  1: eapply (BigStep a b c n); try assumption; lia.
  eexists _,_,d,((a*2+d*6-b-8)/3); split.
  1: apply P_S,HP.
  repeat split; lia.
Qed.

End TM13.


Module TM14.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LA_1RA0LE_0RA0RB_1LD1LF_---0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1]^^a <* <[1;0]^^b <* [1] {{D}}> [1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (3+c) -->*
  S1 a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n*3+c) -->*
  S1 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition S2 a b c :=
  0inf <* [1]^^(1+a) <* <[0;1] <* <[0;1;1;1]^^b <* <[0;1]^^c <* <[0;1;1;1;0] {{A}}> 0inf.

Lemma Inc2 a b c:
  S2 a (1+b) c -->*
  S2 a b (5+c).
Proof.
  es.
Qed.

Lemma Incs2 a b c:
  S2 a b c -->*
  S2 a 0 (b*5+c).
Proof.
  gen c.
  ind b Inc2.
Qed.

Lemma Inc3 a c:
  S2 (1+a) 0 c -->*
  S2 a 0 (2+c).
Proof.
  es.
Qed.

Lemma Incs3 a c:
  S2 a 0 c -->*
  S2 0 0 (a*2+c).
Proof.
  gen c.
  ind a Inc3.
Qed.

Lemma Rst3 a:
  S2 0 0 a -->*
  S1 0 7 (a*2).
Proof.
  es.
Qed.

Lemma Rst1 b c:
  S1 0 b (2+c) -->*
  S1 (5+b*2) 0 c.
Proof.
  es.
Qed.

Lemma Rst a b:
  S1 (3+a) (b*2) 0 -->+
  S1 0 7 (a*4+b*10).
Proof.
  mid10 (S2 a b 0).
  1: es.
  follow Incs2.
  follow Incs3.
  follow Rst3.
  finish.
Qed.

Definition P a b :=
  forall c,
  S1 0 7 (b+c) -->*
  S1 0 a c.

Lemma P_O: P 7 0.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S a b:
  P a b ->
  P (a*4+10) (a*6+b+17).
Proof.
  unfold P.
  intros HP c.
  specialize (HP (2+((5+a*2)*3+c))).
  eapply evstep_trans.
  2: follow HP.
  1: finish.
  follow Rst1.
  mid (S1 ((5+a*2)+0) 0 ((5+a*2)*3+c)).
  1: finish.
  follow Incs1.
  finish.
Qed.

Definition S n := S1 0 7 n.

Lemma BigStep a b c n:
  b+2<=n ->
  n-b-2=c*3 ->
  c<=2+a*2 ->
  P a b ->
  S n -->+
  S (8+a*8+c*6).
Proof.
  unfold S,P.
  intros Hn Hc Hc0 HP.
  mid01 (S1 0 7 (b+(2+(n-b-2)))).
  1: finish.
  follow HP.
  follow Rst1.
  rewrite Hc.
  mid01 (S1 (c+(3+(2+a*2-c))) 0 (c*3+0)).
  1: finish.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Rst.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 130).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a b c d, P a b /\ (b+2<=n /\ n-b-2=c*3 /\ c<=2+a*2 /\ a*2+c*6-b-11=d*3 /\ b*2+13<=a*2+n)).
  2: eexists _,_,23,48; split.
  2: apply P_S,P_O.
  2: lia.
  intros n [a [b [c [d [HP Hn]]]]].
  eexists; split.
  1: eapply (BigStep a b c n); try assumption; lia.
  eexists _,_,d,((a*2+d*6-b-8)/3); split.
  1: apply P_S,HP.
  repeat split; lia.
Qed.

End TM14.


Module TM15.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LA_1RA0LE_0RA0RB_0LF1LB_---1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1]^^a <* <[1;0]^^b <* [1] {{D}}> [1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (3+c) -->*
  S1 a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n*3+c) -->*
  S1 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition S2 a b c :=
  0inf <* [1]^^(1+a) <* <[0;1] <* <[0;1;1;1]^^b <* <[0;1]^^c <* <[0;1;1;1;0] {{A}}> 0inf.

Lemma Inc2 a b c:
  S2 a (1+b) c -->*
  S2 a b (5+c).
Proof.
  es.
Qed.

Lemma Incs2 a b c:
  S2 a b c -->*
  S2 a 0 (b*5+c).
Proof.
  gen c.
  ind b Inc2.
Qed.

Lemma Inc3 a c:
  S2 (1+a) 0 c -->*
  S2 a 0 (2+c).
Proof.
  es.
Qed.

Lemma Incs3 a c:
  S2 a 0 c -->*
  S2 0 0 (a*2+c).
Proof.
  gen c.
  ind a Inc3.
Qed.

Lemma Rst3 a:
  S2 0 0 a -->*
  S1 0 7 (a*2).
Proof.
  es.
Qed.

Lemma Rst1 b c:
  S1 0 b (2+c) -->*
  S1 (5+b*2) 0 c.
Proof.
  es.
Qed.

Lemma Rst a b:
  S1 (3+a) (b*2) 0 -->+
  S1 0 7 (a*4+b*10).
Proof.
  mid10 (S2 a b 0).
  1: es.
  follow Incs2.
  follow Incs3.
  follow Rst3.
  finish.
Qed.

Definition P a b :=
  forall c,
  S1 0 7 (b+c) -->*
  S1 0 a c.

Lemma P_O: P 7 0.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S a b:
  P a b ->
  P (a*4+10) (a*6+b+17).
Proof.
  unfold P.
  intros HP c.
  specialize (HP (2+((5+a*2)*3+c))).
  eapply evstep_trans.
  2: follow HP.
  1: finish.
  follow Rst1.
  mid (S1 ((5+a*2)+0) 0 ((5+a*2)*3+c)).
  1: finish.
  follow Incs1.
  finish.
Qed.

Definition S n := S1 0 7 n.

Lemma BigStep a b c n:
  b+2<=n ->
  n-b-2=c*3 ->
  c<=2+a*2 ->
  P a b ->
  S n -->+
  S (8+a*8+c*6).
Proof.
  unfold S,P.
  intros Hn Hc Hc0 HP.
  mid01 (S1 0 7 (b+(2+(n-b-2)))).
  1: finish.
  follow HP.
  follow Rst1.
  rewrite Hc.
  mid01 (S1 (c+(3+(2+a*2-c))) 0 (c*3+0)).
  1: finish.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Rst.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 130).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a b c d, P a b /\ (b+2<=n /\ n-b-2=c*3 /\ c<=2+a*2 /\ a*2+c*6-b-11=d*3 /\ b*2+13<=a*2+n)).
  2: eexists _,_,23,48; split.
  2: apply P_S,P_O.
  2: lia.
  intros n [a [b [c [d [HP Hn]]]]].
  eexists; split.
  1: eapply (BigStep a b c n); try assumption; lia.
  eexists _,_,d,((a*2+d*6-b-8)/3); split.
  1: apply P_S,HP.
  repeat split; lia.
Qed.

End TM15.


Module TM16.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LA_1RA0LE_0RA0RB_0LF1RE_---1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1]^^a <* <[1;0]^^b <* [1] {{D}}> [1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (3+c) -->*
  S1 a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n*3+c) -->*
  S1 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition S2 a b c :=
  0inf <* [1]^^(1+a) <* <[0;1] <* <[0;1;1;1]^^b <* <[0;1]^^c <* <[0;1;1;1;0] {{A}}> 0inf.

Lemma Inc2 a b c:
  S2 a (1+b) c -->*
  S2 a b (5+c).
Proof.
  es.
Qed.

Lemma Incs2 a b c:
  S2 a b c -->*
  S2 a 0 (b*5+c).
Proof.
  gen c.
  ind b Inc2.
Qed.

Lemma Inc3 a c:
  S2 (1+a) 0 c -->*
  S2 a 0 (2+c).
Proof.
  es.
Qed.

Lemma Incs3 a c:
  S2 a 0 c -->*
  S2 0 0 (a*2+c).
Proof.
  gen c.
  ind a Inc3.
Qed.

Lemma Rst3 a:
  S2 0 0 a -->*
  S1 0 7 (a*2).
Proof.
  es.
Qed.

Lemma Rst1 b c:
  S1 0 b (2+c) -->*
  S1 (5+b*2) 0 c.
Proof.
  es.
Qed.

Lemma Rst a b:
  S1 (3+a) (b*2) 0 -->+
  S1 0 7 (a*4+b*10).
Proof.
  mid10 (S2 a b 0).
  1: es.
  follow Incs2.
  follow Incs3.
  follow Rst3.
  finish.
Qed.

Definition P a b :=
  forall c,
  S1 0 7 (b+c) -->*
  S1 0 a c.

Lemma P_O: P 7 0.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S a b:
  P a b ->
  P (a*4+10) (a*6+b+17).
Proof.
  unfold P.
  intros HP c.
  specialize (HP (2+((5+a*2)*3+c))).
  eapply evstep_trans.
  2: follow HP.
  1: finish.
  follow Rst1.
  mid (S1 ((5+a*2)+0) 0 ((5+a*2)*3+c)).
  1: finish.
  follow Incs1.
  finish.
Qed.

Definition S n := S1 0 7 n.

Lemma BigStep a b c n:
  b+2<=n ->
  n-b-2=c*3 ->
  c<=2+a*2 ->
  P a b ->
  S n -->+
  S (8+a*8+c*6).
Proof.
  unfold S,P.
  intros Hn Hc Hc0 HP.
  mid01 (S1 0 7 (b+(2+(n-b-2)))).
  1: finish.
  follow HP.
  follow Rst1.
  rewrite Hc.
  mid01 (S1 (c+(3+(2+a*2-c))) 0 (c*3+0)).
  1: finish.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Rst.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 130).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a b c d, P a b /\ (b+2<=n /\ n-b-2=c*3 /\ c<=2+a*2 /\ a*2+c*6-b-11=d*3 /\ b*2+13<=a*2+n)).
  2: eexists _,_,23,48; split.
  2: apply P_S,P_O.
  2: lia.
  intros n [a [b [c [d [HP Hn]]]]].
  eexists; split.
  1: eapply (BigStep a b c n); try assumption; lia.
  eexists _,_,d,((a*2+d*6-b-8)/3); split.
  1: apply P_S,HP.
  repeat split; lia.
Qed.

End TM16.


Module TM17.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LA_1RA0LE_0RA0RB_1LF1LB_---0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1]^^a <* <[1;0]^^b <* [1] {{D}}> [1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (3+c) -->*
  S1 a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n*3+c) -->*
  S1 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition S2 a b c :=
  0inf <* [1]^^(1+a) <* <[0;1] <* <[0;1;1;1]^^b <* <[0;1]^^c <* <[0;1;1;1;0] {{A}}> 0inf.

Lemma Inc2 a b c:
  S2 a (1+b) c -->*
  S2 a b (5+c).
Proof.
  es.
Qed.

Lemma Incs2 a b c:
  S2 a b c -->*
  S2 a 0 (b*5+c).
Proof.
  gen c.
  ind b Inc2.
Qed.

Lemma Inc3 a c:
  S2 (1+a) 0 c -->*
  S2 a 0 (2+c).
Proof.
  es.
Qed.

Lemma Incs3 a c:
  S2 a 0 c -->*
  S2 0 0 (a*2+c).
Proof.
  gen c.
  ind a Inc3.
Qed.

Lemma Rst3 a:
  S2 0 0 a -->*
  S1 0 7 (a*2).
Proof.
  es.
Qed.

Lemma Rst1 b c:
  S1 0 b (2+c) -->*
  S1 (5+b*2) 0 c.
Proof.
  es.
Qed.

Lemma Rst a b:
  S1 (3+a) (b*2) 0 -->+
  S1 0 7 (a*4+b*10).
Proof.
  mid10 (S2 a b 0).
  1: es.
  follow Incs2.
  follow Incs3.
  follow Rst3.
  finish.
Qed.

Definition P a b :=
  forall c,
  S1 0 7 (b+c) -->*
  S1 0 a c.

Lemma P_O: P 7 0.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S a b:
  P a b ->
  P (a*4+10) (a*6+b+17).
Proof.
  unfold P.
  intros HP c.
  specialize (HP (2+((5+a*2)*3+c))).
  eapply evstep_trans.
  2: follow HP.
  1: finish.
  follow Rst1.
  mid (S1 ((5+a*2)+0) 0 ((5+a*2)*3+c)).
  1: finish.
  follow Incs1.
  finish.
Qed.

Definition S n := S1 0 7 n.

Lemma BigStep a b c n:
  b+2<=n ->
  n-b-2=c*3 ->
  c<=2+a*2 ->
  P a b ->
  S n -->+
  S (8+a*8+c*6).
Proof.
  unfold S,P.
  intros Hn Hc Hc0 HP.
  mid01 (S1 0 7 (b+(2+(n-b-2)))).
  1: finish.
  follow HP.
  follow Rst1.
  rewrite Hc.
  mid01 (S1 (c+(3+(2+a*2-c))) 0 (c*3+0)).
  1: finish.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Rst.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 130).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a b c d, P a b /\ (b+2<=n /\ n-b-2=c*3 /\ c<=2+a*2 /\ a*2+c*6-b-11=d*3 /\ b*2+13<=a*2+n)).
  2: eexists _,_,23,48; split.
  2: apply P_S,P_O.
  2: lia.
  intros n [a [b [c [d [HP Hn]]]]].
  eexists; split.
  1: eapply (BigStep a b c n); try assumption; lia.
  eexists _,_,d,((a*2+d*6-b-8)/3); split.
  1: apply P_S,HP.
  repeat split; lia.
Qed.

End TM17.


Module TM18.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LA_1RA0LE_0RA0RB_1LF1LB_---1RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1]^^a <* <[1;0]^^b <* [1] {{D}}> [1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (3+c) -->*
  S1 a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n*3+c) -->*
  S1 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition S2 a b c :=
  0inf <* [1]^^(1+a) <* <[0;1] <* <[0;1;1;1]^^b <* <[0;1]^^c <* <[0;1;1;1;0] {{A}}> 0inf.

Lemma Inc2 a b c:
  S2 a (1+b) c -->*
  S2 a b (5+c).
Proof.
  es.
Qed.

Lemma Incs2 a b c:
  S2 a b c -->*
  S2 a 0 (b*5+c).
Proof.
  gen c.
  ind b Inc2.
Qed.

Lemma Inc3 a c:
  S2 (1+a) 0 c -->*
  S2 a 0 (2+c).
Proof.
  es.
Qed.

Lemma Incs3 a c:
  S2 a 0 c -->*
  S2 0 0 (a*2+c).
Proof.
  gen c.
  ind a Inc3.
Qed.

Lemma Rst3 a:
  S2 0 0 a -->*
  S1 0 7 (a*2).
Proof.
  es.
Qed.

Lemma Rst1 b c:
  S1 0 b (2+c) -->*
  S1 (5+b*2) 0 c.
Proof.
  es.
Qed.

Lemma Rst a b:
  S1 (3+a) (b*2) 0 -->+
  S1 0 7 (a*4+b*10).
Proof.
  mid10 (S2 a b 0).
  1: es.
  follow Incs2.
  follow Incs3.
  follow Rst3.
  finish.
Qed.

Definition P a b :=
  forall c,
  S1 0 7 (b+c) -->*
  S1 0 a c.

Lemma P_O: P 7 0.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S a b:
  P a b ->
  P (a*4+10) (a*6+b+17).
Proof.
  unfold P.
  intros HP c.
  specialize (HP (2+((5+a*2)*3+c))).
  eapply evstep_trans.
  2: follow HP.
  1: finish.
  follow Rst1.
  mid (S1 ((5+a*2)+0) 0 ((5+a*2)*3+c)).
  1: finish.
  follow Incs1.
  finish.
Qed.

Definition S n := S1 0 7 n.

Lemma BigStep a b c n:
  b+2<=n ->
  n-b-2=c*3 ->
  c<=2+a*2 ->
  P a b ->
  S n -->+
  S (8+a*8+c*6).
Proof.
  unfold S,P.
  intros Hn Hc Hc0 HP.
  mid01 (S1 0 7 (b+(2+(n-b-2)))).
  1: finish.
  follow HP.
  follow Rst1.
  rewrite Hc.
  mid01 (S1 (c+(3+(2+a*2-c))) 0 (c*3+0)).
  1: finish.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Rst.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 130).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a b c d, P a b /\ (b+2<=n /\ n-b-2=c*3 /\ c<=2+a*2 /\ a*2+c*6-b-11=d*3 /\ b*2+13<=a*2+n)).
  2: eexists _,_,23,48; split.
  2: apply P_S,P_O.
  2: lia.
  intros n [a [b [c [d [HP Hn]]]]].
  eexists; split.
  1: eapply (BigStep a b c n); try assumption; lia.
  eexists _,_,d,((a*2+d*6-b-8)/3); split.
  1: apply P_S,HP.
  repeat split; lia.
Qed.

End TM18.


Module TM19.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LA_1RA0LE_0RA0RB_1LF1RE_---0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1]^^a <* <[1;0]^^b <* [1] {{D}}> [1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (3+c) -->*
  S1 a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n*3+c) -->*
  S1 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition S2 a b c :=
  0inf <* [1]^^(1+a) <* <[0;1] <* <[0;1;1;1]^^b <* <[0;1]^^c <* <[0;1;1;1;0] {{A}}> 0inf.

Lemma Inc2 a b c:
  S2 a (1+b) c -->*
  S2 a b (5+c).
Proof.
  es.
Qed.

Lemma Incs2 a b c:
  S2 a b c -->*
  S2 a 0 (b*5+c).
Proof.
  gen c.
  ind b Inc2.
Qed.

Lemma Inc3 a c:
  S2 (1+a) 0 c -->*
  S2 a 0 (2+c).
Proof.
  es.
Qed.

Lemma Incs3 a c:
  S2 a 0 c -->*
  S2 0 0 (a*2+c).
Proof.
  gen c.
  ind a Inc3.
Qed.

Lemma Rst3 a:
  S2 0 0 a -->*
  S1 0 7 (a*2).
Proof.
  es.
Qed.

Lemma Rst1 b c:
  S1 0 b (2+c) -->*
  S1 (5+b*2) 0 c.
Proof.
  es.
Qed.

Lemma Rst a b:
  S1 (3+a) (b*2) 0 -->+
  S1 0 7 (a*4+b*10).
Proof.
  mid10 (S2 a b 0).
  1: es.
  follow Incs2.
  follow Incs3.
  follow Rst3.
  finish.
Qed.

Definition P a b :=
  forall c,
  S1 0 7 (b+c) -->*
  S1 0 a c.

Lemma P_O: P 7 0.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S a b:
  P a b ->
  P (a*4+10) (a*6+b+17).
Proof.
  unfold P.
  intros HP c.
  specialize (HP (2+((5+a*2)*3+c))).
  eapply evstep_trans.
  2: follow HP.
  1: finish.
  follow Rst1.
  mid (S1 ((5+a*2)+0) 0 ((5+a*2)*3+c)).
  1: finish.
  follow Incs1.
  finish.
Qed.

Definition S n := S1 0 7 n.

Lemma BigStep a b c n:
  b+2<=n ->
  n-b-2=c*3 ->
  c<=2+a*2 ->
  P a b ->
  S n -->+
  S (8+a*8+c*6).
Proof.
  unfold S,P.
  intros Hn Hc Hc0 HP.
  mid01 (S1 0 7 (b+(2+(n-b-2)))).
  1: finish.
  follow HP.
  follow Rst1.
  rewrite Hc.
  mid01 (S1 (c+(3+(2+a*2-c))) 0 (c*3+0)).
  1: finish.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Rst.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 130).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a b c d, P a b /\ (b+2<=n /\ n-b-2=c*3 /\ c<=2+a*2 /\ a*2+c*6-b-11=d*3 /\ b*2+13<=a*2+n)).
  2: eexists _,_,23,48; split.
  2: apply P_S,P_O.
  2: lia.
  intros n [a [b [c [d [HP Hn]]]]].
  eexists; split.
  1: eapply (BigStep a b c n); try assumption; lia.
  eexists _,_,d,((a*2+d*6-b-8)/3); split.
  1: apply P_S,HP.
  repeat split; lia.
Qed.

End TM19.

Module TM20.
Definition tm := Eval compute in (TM_from_str "1RB1LF_1RC1RD_1LD0RB_---1LE_1LD1RF_1RE0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* <[1;1] <* <[0;1]^^a <* <[1;1]^^b {{F}}> [1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (2+c) -->*
  S1 a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n*2+c) -->*
  S1 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Rst1 b c:
  S1 0 b (4+c) -->*
  S1 (2+b) 0 (1+c).
Proof.
  es.
Qed.

Lemma Rst2 a b:
  S1 (1+a) b 1 -->*
  S1 a (1+b) 0.
Proof.
  unfold S1.
  es_v2.
Qed.

Lemma Inc2 a b:
  S1 (1+a) b 0 -->*
  S1 a (2+b) 0.
Proof.
  unfold S1.
  es_v2.
Qed.

Lemma Incs2 a b:
  S1 a b 0 -->*
  S1 0 (a*2+b) 0.
Proof.
  gen b.
  ind a Inc2.
Qed.

Lemma Rst a:
  S1 0 a 0 -->+
  S1 0 1 (4+a*2).
Proof.
  es.
Qed.

Definition P a b :=
  forall c,
  S1 0 1 (b+c) -->*
  S1 0 a c.

Lemma P_O: P 1 0.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S a b:
  P a b ->
  P (a*2+4) (a*2+b+7).
Proof.
  unfold P.
  intros HP c.
  specialize (HP (4+(3+a*2+c))).
  eapply evstep_trans.
  2: follow HP.
  1: finish.
  follow Rst1.
  mid (S1 ((2+a)+0) 0 ((2+a)*2+c)).
  1: finish.
  follow Incs1.
  finish.
Qed.

Definition S n := S1 0 1 n.

Lemma BigStep0 a b c n:
  n=b+4+c*2 ->
  c<=a+1 ->
  P a b ->
  S n -->+
  S (a*4+10).
Proof.
  unfold S,P.
  intros Hc Hc0 HP.
  mid01 (S1 0 1 (b+(4+(n-b-4)))).
  1: finish.
  follow HP.
  follow Rst1.
  mid01 (S1 (c+(1+(1+a-c))) 0 (c*2+1)).
  1: finish.
  follow Incs1.
  follow Rst2.
  follow Incs2.
  follow10 Rst.
  finish.
Qed.

Lemma BigStep1 a b c n:
  n=b+4+c*2+1 ->
  c<=a+1 ->
  P a b ->
  S n -->+
  S (a*4+12).
Proof.
  unfold S,P.
  intros Hc Hc0 HP.
  mid01 (S1 0 1 (b+(4+(n-b-4)))).
  1: finish.
  follow HP.
  follow Rst1.
  mid01 (S1 ((c+1)+((1+a-c))) 0 ((c+1)*2+0)).
  1: finish.
  follow Incs1.
  follow Incs2.
  follow10 Rst.
  finish.
Qed.

Lemma BigStep a b n:
  b+4<=n ->
  (n-b-4)/2<=a+1 ->
  P a b ->
  S n -->+
  S (a*4+10+((n-b-4) mod 2)*2).
Proof.
  intros.
  remember (n-b-4) as v1.
  remember (v1/2) as c.
  remember (v1 mod 2) as c1.
  destruct c1 as [|[|]].
  3: lia.
  - applys_eq (BigStep0 a b c n); try assumption; flia.
  - applys_eq (BigStep1 a b c n); try assumption; flia.
Qed.

Close Scope sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 6).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a b, P a b /\ (b+4<=n /\ (n-b-4)/2<=a+1) /\ b+1<=a*2).
  2: exists 1,0; split.
  2: unfold P; es.
  2: lia.
  intros n [a [b [HP Hn]]].
  eexists; split.
  1: eapply (BigStep a b n); try assumption; lia.
  eexists _,_; split.
  1: apply P_S,HP.
  repeat split; lia.
Qed.

End TM20.


Module TM21.
Definition tm := Eval compute in (TM_from_str "1RB1LD_1RC1RF_0RD0RB_1RE0LA_1LF1RD_---1LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* <[1;1] <* <[0;1]^^a <* <[1;1]^^b {{D}}> [1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (2+c) -->*
  S1 a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n*2+c) -->*
  S1 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Rst1 b c:
  S1 0 b (4+c) -->*
  S1 (2+b) 0 (1+c).
Proof.
  es.
Qed.

Lemma Rst2 a b:
  S1 (1+a) b 1 -->*
  S1 a (1+b) 0.
Proof.
  unfold S1.
  es_v2.
Qed.

Lemma Inc2 a b:
  S1 (1+a) b 0 -->*
  S1 a (2+b) 0.
Proof.
  unfold S1.
  es_v2.
Qed.

Lemma Incs2 a b:
  S1 a b 0 -->*
  S1 0 (a*2+b) 0.
Proof.
  gen b.
  ind a Inc2.
Qed.

Lemma Rst a:
  S1 0 a 0 -->+
  S1 0 1 (6+a*2).
Proof.
  es.
Qed.

Definition P a b :=
  forall c,
  S1 0 1 (b+c) -->*
  S1 0 a c.

Lemma P_O: P 1 0.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S a b:
  P a b ->
  P (a*2+4) (a*2+b+7).
Proof.
  unfold P.
  intros HP c.
  specialize (HP (4+(3+a*2+c))).
  eapply evstep_trans.
  2: follow HP.
  1: finish.
  follow Rst1.
  mid (S1 ((2+a)+0) 0 ((2+a)*2+c)).
  1: finish.
  follow Incs1.
  finish.
Qed.

Definition S n := S1 0 1 n.

Lemma BigStep0 a b c n:
  n=b+4+c*2 ->
  c<=a+1 ->
  P a b ->
  S n -->+
  S (a*4+12).
Proof.
  unfold S,P.
  intros Hc Hc0 HP.
  mid01 (S1 0 1 (b+(4+(n-b-4)))).
  1: finish.
  follow HP.
  follow Rst1.
  mid01 (S1 (c+(1+(1+a-c))) 0 (c*2+1)).
  1: finish.
  follow Incs1.
  follow Rst2.
  follow Incs2.
  follow10 Rst.
  finish.
Qed.

Lemma BigStep1 a b c n:
  n=b+4+c*2+1 ->
  c<=a+1 ->
  P a b ->
  S n -->+
  S (a*4+14).
Proof.
  unfold S,P.
  intros Hc Hc0 HP.
  mid01 (S1 0 1 (b+(4+(n-b-4)))).
  1: finish.
  follow HP.
  follow Rst1.
  mid01 (S1 ((c+1)+((1+a-c))) 0 ((c+1)*2+0)).
  1: finish.
  follow Incs1.
  follow Incs2.
  follow10 Rst.
  finish.
Qed.

Lemma BigStep a b n:
  b+4<=n ->
  (n-b-4)/2<=a+1 ->
  P a b ->
  S n -->+
  S (a*4+12+((n-b-4) mod 2)*2).
Proof.
  intros.
  remember (n-b-4) as v1.
  remember (v1/2) as c.
  remember (v1 mod 2) as c1.
  destruct c1 as [|[|]].
  3: lia.
  - applys_eq (BigStep0 a b c n); try assumption; flia.
  - applys_eq (BigStep1 a b c n); try assumption; flia.
Qed.

Close Scope sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 8).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a b, P a b /\ (b+4<=n /\ (n-b-4)/2<=a+1) /\ b+1<=a*2).
  2: exists 1,0; split.
  2: unfold P; es.
  2: lia.
  intros n [a [b [HP Hn]]].
  eexists; split.
  1: eapply (BigStep a b n); try assumption; lia.
  eexists _,_; split.
  1: apply P_S,HP.
  repeat split; lia.
Qed.

End TM21.


Module TM23.
Definition tm := Eval compute in (TM_from_str "1RB1LE_1LC0RA_1RD0LB_1LE1RC_0RC1LF_---1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* <[1;1]^^a <* <[1;0]^^(1+b) {{A}}> [1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (2+c) -->*
  S1 a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n*2+c) -->*
  S1 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Rst1 b c:
  S1 0 b (4+c) -->*
  S1 (2+b) 1 c.
Proof.
  es.
Qed.

Lemma Rst2 a b:
  S1 (1+a) b 1 -->*
  S1 a (1+b) 0.
Proof.
  es_v2.
Qed.

Lemma Inc2 a b:
  S1 (1+a) b 0 -->*
  S1 a (2+b) 0.
Proof.
  es_v2.
Qed.

Lemma Incs2 a b:
  S1 a b 0 -->*
  S1 0 (a*2+b) 0.
Proof.
  gen b.
  ind a Inc2.
Qed.

Lemma IRI0 a b c:
  c<=a ->
  S1 a b (c*2) -->*
  S1 0 (a*2+b) 0.
Proof.
  intros.
  follow (Incs1 c (a-c) b 0).
  follow Incs2.
  finish.
Qed.

Lemma IRI1 a b c:
  c+1<=a ->
  S1 a b (c*2+1) -->*
  S1 0 (a*2+b-1) 0.
Proof.
  intros.
  follow (Incs1 c (1+(a-c-1)) b 1).
  follow Rst2.
  follow Incs2.
  finish.
Qed.

Lemma Rst_1 a:
  S1 0 (1+a*3) 0 -->+
  S1 1 1 (6+a*6).
Proof.
  es.
Qed.

Lemma Rst_2 a:
  S1 0 (2+a*3) 0 -->*
  S1 0 0 (11+a*6).
Proof.
  es.
Qed.

Definition P0 a b :=
  forall c,
  S1 0 0 (b+c) -->*
  S1 a 1 c.

Definition P1 a b :=
  forall c,
  S1 1 1 (b+c) -->*
  S1 a 1 c.

Lemma P0_O: P0 2 4.
Proof.
  unfold P0.
  es.
Qed.

Lemma P1_O: P1 1 0.
Proof.
  unfold P1.
  es.
Qed.

Lemma P0_S a b:
  P0 a b ->
  P0 (a*2+3) (4+a*2+b).
Proof.
  unfold P0.
  intros HP c.
  specialize (HP (a*2+4+c)).
  follow HP.
  mid (S1 (a+0) 1 (a*2+(4+c))).
  1: finish.
  follow Incs1.
  follow Rst1.
  finish.
Qed.

Lemma P1_S a b:
  P1 a b ->
  P1 (a*2+3) (4+a*2+b).
Proof.
  unfold P1.
  intros HP c.
  specialize (HP (a*2+4+c)).
  follow HP.
  mid (S1 (a+0) 1 (a*2+(4+c))).
  1: finish.
  follow Incs1.
  follow Rst1.
  finish.
Qed.

Definition S1' n := S1 1 1 n.
Definition S0' n := S1 0 0 n.

Lemma BigStep100 a b n:
  b<=n /\ (n-b) mod 2 = 0%nat /\ (n-b)/2<=a /\ a mod 3 = 2 ->
  P1 a b ->
  S1' n -->*
  S0' (a*4+9).
Proof.
  unfold S0',S1',P1.
  intros Hn HP.
  follow (HP (n-b)).
  follow (IRI0 a 1 ((n-b)/2)).
  1: lia.
  follow (Rst_2 ((a*2+1)/3)).
  finish.
Qed.

Lemma BigStep010 a b n:
  b<=n /\ (n-b) mod 2 = 1%nat /\ (n-b)/2+1<=a /\ a mod 3 = 1%nat ->
  P0 a b ->
  S0' n -->*
  S0' (a*4+7).
Proof.
  unfold S0',S1',P0.
  intros Hn HP.
  follow (HP (n-b)).
  follow (IRI1 a 1 ((n-b)/2)).
  1: lia.
  follow (Rst_2 ((a*2)/3)).
  finish.
Qed.

Lemma BigStep011 a b n:
  b<=n /\ (n-b) mod 2 = 1%nat /\ (n-b)/2+1<=a /\ a mod 3 = 2 ->
  P0 a b ->
  S0' n -->+
  S1' (a*4+4).
Proof.
  unfold S0',S1',P0.
  intros Hn HP.
  follow (HP (n-b)).
  follow (IRI1 a 1 ((n-b)/2)).
  1: lia.
  applys_eq (Rst_1 ((a*2)/3)); flia.
Qed.

Definition S' i := S1' (2^(i*2)*80-8).

Lemma pow2_lt i:
  i<2^i.
Proof.
  induction i; cbn; lia.
Qed.

Lemma pow2_mod3 i:
  2^(i*2) mod 3 = 1%nat.
Proof.
  induction i.
  1: cbn; lia.
  change (S i*2) with (S(S(i*2))).
  cbn[Nat.pow]; lia.
Qed.

Lemma P0_n i:
  P0 (2^i*5-3) (2^i*10-i*2-6).
Proof.
  induction i.
  1: apply P0_O.
  apply P0_S in IHi.
  cbn[Nat.pow].
  epose proof (pow2_lt i).
  applys_eq IHi; flia.
Qed.

Lemma P1_n i:
  P1 (2^i*4-3) (2^i*8-i*2-8).
Proof.
  induction i.
  1: apply P1_O.
  apply P1_S in IHi.
  cbn[Nat.pow].
  epose proof (pow2_lt i).
  applys_eq IHi; flia.
Qed.

Lemma BigStep i:
  S' i -->+ S' (S i).
Proof.
  unfold S'.
  epose proof (P1_n (i*2+3)) as HP1.
  epose proof (P0_n (i*2+3)) as HP0.
  epose proof (P0_n (i*2+4)) as HP0'.
  replace (S i*2) with (i*2+2) by lia.
  repeat rewrite Nat.pow_add_r in * by lia.
  epose proof (pow2_lt (i*2)).
  epose proof (pow2_mod3 i).
  unshelve epose proof (BigStep100 _ _ _ _ HP1) as I1.
  3: follow I1.
  1: repeat split; try lia.
  unshelve epose proof (BigStep010 _ _ _ _ HP0) as I2.
  3: follow I2.
  1: repeat split; try lia.
  unshelve epose proof (BigStep011 _ _ _ _ HP0') as I3.
  3: follow10 I3.
  1: repeat split; lia.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' 0).
  1: unfold S',S1',S1; esx.
  eapply progress_nonhalt_simple.
  intro i.
  exists (S i).
  apply BigStep.
Qed.

End TM23.


Module TM24.
Definition tm := Eval compute in (TM_from_str "1LB1LE_1RC1RF_1RD0RB_1RE---_1LA0RF_0LC0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 i a b c :=
  0inf <* [1]^^i <* <[0;0] <* <[1;0]^^a <* <[1;1]^^b <* [0] {{F}}> [1]^^c *> [0;1] *> 0inf.

Lemma Inc1 i a b c:
  S1 i (1+a) b (2+c) -->*
  S1 i a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n i a b c:
  S1 i (n+a) b (n*2+c) -->*
  S1 i a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Rst1 i b c:
  S1 i 0 b (5+c) -->*
  S1 (1+i) (1+b) 1 c.
Proof.
  es.
Qed.

Definition S2 i a b :=
  0inf <* [1]^^i <* <[0;0] <* <[1;0]^^a <* <[1;1]^^b {{E}}> 0inf.

Lemma Rst2_1 i a b:
  S1 i (2+a) b 1 -->*
  S2 i a (3+b).
Proof.
  es.
Qed.

Lemma Rst2_0 i a b:
  S1 i a b 0 -->*
  S2 i a (2+b).
Proof.
  es.
Qed.

Lemma Inc2 i a b:
  S2 i (1+a) b -->*
  S2 i a (2+b).
Proof.
  es.
Qed.

Lemma Incs2 i a b:
  S2 i a b -->*
  S2 i 0 (a*2+b).
Proof.
  gen b.
  ind a Inc2.
Qed.

Lemma IRI0 i a b c:
  c<=a ->
  S1 i a b (c*2) -->*
  S2 i 0 (a*2+b+2).
Proof.
  intros.
  follow (Incs1 c i (a-c) b 0).
  follow Rst2_0.
  follow Incs2.
  finish.
Qed.

Lemma IRI1 i a b c:
  c+2<=a ->
  S1 i a b (c*2+1) -->*
  S2 i 0 (a*2+b-1).
Proof.
  intros.
  follow (Incs1 c i (2+(a-c-2)) b 1).
  follow Rst2_1.
  follow Incs2.
  finish.
Qed.

Lemma Rst_0 i a:
  S2 (i*2) 0 (2+a) -->+
  S1 1 (2+i) 1 (1+a*2).
Proof.
  es.
Qed.

Lemma Rst_1 i a:
  S2 (i*2+1) 0 (4+a) -->*
  S1 1 (6+i) 1 (1+a*2).
Proof.
  es.
Qed.

Definition P i a0 a b :=
  forall c,
  S1 1 a0 1 (b+c) -->*
  S1 (1+i) a 1 c.

Lemma P_O a0: P 0 a0 a0 0.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S i a0 a b:
  P i a0 a b ->
  P (1+i) a0 (a*2+2) (5+a*2+b).
Proof.
  unfold P.
  intros HP c.
  specialize (HP (a*2+5+c)).
  follow HP.
  mid (S1 (1+i) (a+0) 1 (a*2+(5+c))).
  1: finish.
  follow Incs1.
  follow Rst1.
  finish.
Qed.

Definition S1' a c := S1 1 a 1 c.

Lemma BigStep01 i a0 a b n:
  b<=n /\ (n-b) mod 2 = 1%nat /\ (n-b)/2+2<=a ->
  P (i*2) a0 a b ->
  S1' a0 n -->*
  S1' (6+i) (a*4-7).
Proof.
  unfold P,S1'.
  intros Hn HP.
  follow (HP (n-b)).
  follow (IRI1 (1+i*2) a 1 ((n-b)/2)).
  1: lia.
  follow (Rst_1 i (a*2-4)).
  finish.
Qed.

Lemma BigStep10 i a0 a b n:
  b<=n /\ (n-b) mod 2 = 0%nat /\ (n-b)/2<=a /\ 1<=a ->
  P (i*2+1) a0 a b ->
  S1' a0 n -->+
  S1' (3+i) (a*4+3).
Proof.
  unfold P,S1'.
  intros Hn HP.
  follow (HP (n-b)).
  follow (IRI0 (2+i*2) a 1 ((n-b)/2)).
  1: lia.
  applys_eq (Rst_0 (1+i) (a*2+1)); flia.
Qed.

Lemma P_n i a0:
  P i a0 ((a0+2)*((2^i-1)+1)-2) ((a0+2)*((2^i-1)*2)+i).
Proof.
  induction i.
  1: applys_eq (P_O a0); flia.
  remember (2^i-1) as x.
  replace (2^(S i)-1) with (x*2+1) in * by (cbn; lia).
  apply P_S in IHi.
  applys_eq IHi; flia.
Qed.

Definition S' i := S1' (i*2+7) ((i*2+5)*2^(i*4)*16-15).

Ltac rw_pa := repeat rewrite Nat.pow_add_r in *.
Ltac spl := repeat split; try lia.
Ltac follow10 H :=
  eapply progress_evstep_trans; [applys_eq H; try solve[flia] | ].


Lemma BigStep i:
  S' i -->+
  S' (S i).
Proof.
  unfold S'.
  unshelve epose proof (BigStep01 (i*2+1) (i*2+7) _ _ _ _ _) as I1.
  5: apply P_n.
  3: follow I1.
  all: replace ((i*2+1)*2) with (i*4+2) by lia.
  1: rw_pa; spl.
  clear I1.
  unshelve epose proof (BigStep10 (i*2+1) (i*2+7) _ _ _ _ _) as I1.
  5: apply P_n.
  3: follow10 I1.
  all: replace ((i*2+1)*2) with (i*4+2) by lia.
  1: rw_pa; spl.
  clear I1.
  unshelve epose proof (BigStep01 (i*2+2) (i*2+4) _ _ _ _ _) as I1.
  5: apply P_n.
  3: follow I1.
  all: replace ((i*2+2)*2) with (i*4+4) by lia.
  1: rw_pa; spl.
  clear I1.
  unshelve epose proof (BigStep01 (i*2+2) (i*2+8) _ _ _ _ _) as I1.
  5: apply P_n.
  3: follow I1.
  all: replace ((i*2+2)*2) with (i*4+4) by lia.
  1: rw_pa; spl.
  clear I1.
  unshelve epose proof (BigStep10 (i*2+2) (i*2+8) _ _ _ _ _) as I1.
  5: apply P_n.
  3: apply progress_evstep.
  3: follow10 I1.
  all: replace ((i*2+2)*2) with (i*4+4) by lia.
  1: rw_pa; spl.
  clear I1.
  unshelve epose proof (BigStep01 (i*2+3) (i*2+5) _ _ _ _ _) as I1.
  5: apply P_n.
  3: follow I1.
  all: replace ((i*2+3)*2) with (i*4+6) by lia.
  1: rw_pa; spl.
  clear I1.
  replace (S i*4) with (i*4+4) by lia.
  rw_pa.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' 0).
  1: unfold S',S1',S1; esx.
  eapply progress_nonhalt_simple.
  intros i.
  eexists.
  apply BigStep.
Qed.

End TM24.


