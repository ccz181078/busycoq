From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import Longitudinal.

Ltac stepn n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; simpl_tape; reflexivity.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC0RE_0RD0RB_1LA0RF_1RB0LD_0RA---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c d r :=
  0inf <* [1]^^a <* [0] <{{B}} [1] *> [1;0]^^b *> [0] *> [1;0]^^c *> [0]^^d *> r.

Lemma Inc1 a b c d r:
  S1 a (1+b) c (3+d) r -->*
  S1 (1+a) b (2+c) d r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c d r:
  S1 a (n+b) c (n*3+d) r -->*
  S1 (n+a) b (n*2+c) d r.
Proof.
  gen a b c d.
  ind n Inc1.
Qed.

Lemma Ov1b c d r:
  S1 17 0 (c*2) (23+d) r -->*
  S1 2 (14+c*2) 11 d r.
Proof.
  es.
Qed.

Definition S2 a r :=
  0inf <{{A}} [0]^^a *> r.

Lemma Ov1b' a c d r:
  S1 (a) 0 c (3+d) r -->*
  S2 a ([1;0]^^(3+c)*>[0]^^d*>r).
Proof.
  es.
Qed.

Lemma Ov1d a b c c' d' r:
  S1 a (1+b) c 1 ([1;0]^^(c'*2)*>[0]^^(2+d')*>r) -->*
  S1 (1+a) b (2+c+c'*2) d' r.
Proof.
  es.
Qed.

Lemma Ov1d_0 a b c c' d' r:
  S1 a b c 0 ([1;0]^^c'*>[0]^^d'*>r) -->*
  S1 a b (c+c') d' r.
Proof.
  es.
Qed.

Definition P1 a c :=
  forall r,
  S2 a r -->*
  S1 17 0 (c*2) 0 r.

Lemma P1_0:
  P1 76 17.
Proof.
  unfold P1.
  intros.
  stepn 3150%N.
Qed.

Definition P2 a d c' :=
  forall r k,
  S1 a 0 (1+k*2) d r -->*
  S1 17 0 (c'*2+k*2) 0 r.

Lemma S1_add a b c d r:
  S1 a b c d r = S1 a b c 0 ([0]^^d*>r).
Proof.
  unfold S1.
  st; reflexivity.
Qed.

Lemma S2_add a b r:
  S2 (a+b) r = S2 a ([0]^^b*>r).
Proof.
  unfold S2.
  st; reflexivity.
Qed.

Lemma P2_O:
  P2 50 29 19.
Proof.
  unfold P2.
  intros r k.
  follow Ov1b'.
  unfold S2.
  mid (S1 0 (8+(1+(8+0))) 0 (8*3+1) ([1;0]^^(4+k*2)*>[0]^^(2+(8*3+0))*>r)).
  stepn 481%N.
  follow Incs1.
  replace (4+k*2) with ((2+k)*2) by lia.
  follow Ov1d.
  follow Incs1.
  finish.
Qed.

Lemma P2_S [a0 c0 d c'] a1:
  P1 a0 c0 ->
  P2 (16+c0*2) d c' ->
  a1<=13+c0*2 ->
  P2 (a0+(23+(a1*3+1))) (3+(2+((13+c0*2-a1)*3+d))) (21+c0*2+c').
Proof.
  unfold P1,P2.
  intros HP1 HP2 Ha1 r k.
  follow Ov1b'.
  rewrite S2_add.
  follow HP1.
  rewrite <-S1_add.
  follow Ov1b.
  replace (14+c0*2) with (a1+(1+(13+c0*2-a1+0))) by lia.
  follow Incs1.
  replace (3+(1+k*2)) with ((2+k)*2) by lia.
  follow Ov1d.
  follow Incs1.
  follow (HP2 r (21+c0*2+k)).
  finish.
Qed.

Lemma P2_S_0 [a0 c0 d c'] a1:
  P1 a0 c0 ->
  P2 (16+c0*2) d c' ->
  a1<=14+c0*2 ->
  P2 (a0+(23+(a1*3+0))) (3+(((14+c0*2-a1)*3+d))) (21+c0*2+c').
Proof.
  unfold P1,P2.
  intros HP1 HP2 Ha1 r k.
  follow Ov1b'.
  rewrite S2_add.
  follow HP1.
  rewrite <-S1_add.
  follow Ov1b.
  replace (14+c0*2) with (a1+((14+c0*2-a1+0))) by lia.
  follow Incs1.
  follow Ov1d_0.
  replace (a1+((14+c0*2-a1+0))) with (14+c0*2) by lia.
  follow Incs1.
  follow (HP2 r (21+c0*2+k)).
  finish.
Qed.

Lemma P1_S [a0 c0 d c']:
  P1 a0 c0 ->
  P2 (16+c0*2) d c' ->
  P1 (a0+(23+((14+c0*2)*3+d))) (19+c0*2+c').
Proof.
  unfold P1,P2.
  intros HP1 HP2 r.
  rewrite S2_add.
  follow HP1.
  rewrite <-S1_add.
  follow Ov1b.
  follow (Incs1 (14+c0*2) 2 0 11 d r).
  follow (HP2 r (19+c0*2)).
  finish.
Qed.

Definition P3 a0 c0 d c' := P1 a0 c0 /\ P2 (16+c0*2) d c'.

Lemma P3_O: P3 76 17 29 19.
Proof.
  split.
  - apply P1_0.
  - apply P2_O.
Qed.

Lemma P3_S a0 c0 d c' a1:
  P3 a0 c0 d c' ->
  a0+a1*3 = 30+c0*4+c'*2 ->
  a1<=13+c0*2 ->
  P3 (a0+c0*6+d+65) (19+c0*2+c') (5+d+(13+c0*2-a1)*3) (21+c0*2+c').
Proof.
  intros [HP1 HP2] Ha1 Ha1'.
  split.
  - applys_eq (P1_S HP1 HP2); lia.
  - applys_eq (P2_S a1 HP1 HP2); lia.
Qed.

Lemma P3_1: P3 272 72 115 74.
Proof.
  epose proof P3_O.
  apply P3_S with (a1:=20) in H.
  2,3: lia.
  apply H.
Qed.

Lemma P3_S' a0 c0 d c' a1:
  P3 a0 c0 d c' ->
  a0+a1*3 = 31+c0*4+c'*2 ->
  a1<=14+c0*2 ->
  P3 (a0+c0*6+d+65) (19+c0*2+c') (3+d+(14+c0*2-a1)*3) (21+c0*2+c').
Proof.
  intros [HP1 HP2] Ha1 Ha1'.
  split.
  - applys_eq (P1_S HP1 HP2); lia.
  - applys_eq (P2_S_0 a1 HP1 HP2); lia.
Qed.

Inductive P: nat->Prop :=
| P_intro n a0 c0 d:
  P3 (2+a0*3) c0 (1+d*3) (2+c0) ->
  a0<=11+c0*2 ->
  a0+d<=31+c0*4 ->
  n<=c0 ->
  P n.

Lemma P_n n: P n.
Proof.
  induction n.
  - eapply P_intro with (a0:=90) (d:=38).
    1: apply P3_1.
    all: lia.
  - inverts IHn.
    apply P3_S' with (a1:=11+c1*2-a0) in H.
    2,3: lia.
    eapply P_intro with (a0:=a0+c1*2+d+22) (d:=d+a0+4).
    1: applys_eq H; lia.
    all: lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_n n) as HP.
  inverts HP.
  destruct H as [HP1 _].
  specialize (HP1 0inf).
  unfold S1,S2 in HP1.
  rewrite lpow_all0 in HP1 by solve_const0_eq.
  eexists _,_; split.
  - apply HP1.
  - split.
    + solve_sigma_score.
    + lia.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC0RA_0RD0RB_1LE0RF_1LB0LE_0RE---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c d r :=
  0inf <* [1]^^a <* [0] <{{B}} [1] *> [1;0]^^b *> [0] *> [1;0]^^c *> [0]^^d *> r.

Lemma Inc1 a b c d r:
  S1 a (1+b) c (3+d) r -->*
  S1 (1+a) b (2+c) d r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c d r:
  S1 a (n+b) c (n*3+d) r -->*
  S1 (n+a) b (n*2+c) d r.
Proof.
  gen a b c d.
  ind n Inc1.
Qed.

Lemma Ov1b c d r:
  S1 17 0 (c*2) (23+d) r -->*
  S1 2 (14+c*2) 11 d r.
Proof.
  es.
Qed.

Definition S2 a r :=
  0inf <{{E}} [0]^^a *> r.

Lemma Ov1b' a c d r:
  S1 (a) 0 c (3+d) r -->*
  S2 a ([1;0]^^(3+c)*>[0]^^d*>r).
Proof.
  es.
Qed.

Lemma Ov1d a b c c' d' r:
  S1 a (1+b) c 1 ([1;0]^^(c'*2)*>[0]^^(2+d')*>r) -->*
  S1 (1+a) b (2+c+c'*2) d' r.
Proof.
  es.
Qed.

Lemma Ov1d_0 a b c c' d' r:
  S1 a b c 0 ([1;0]^^c'*>[0]^^d'*>r) -->*
  S1 a b (c+c') d' r.
Proof.
  es.
Qed.

Definition P1 a c :=
  forall r,
  S2 a r -->*
  S1 17 0 (c*2) 0 r.

Lemma P1_0:
  P1 76 17.
Proof.
  unfold P1.
  intros.
  stepn 3150%N.
Qed.

Definition P2 a d c' :=
  forall r k,
  S1 a 0 (1+k*2) d r -->*
  S1 17 0 (c'*2+k*2) 0 r.

Lemma S1_add a b c d r:
  S1 a b c d r = S1 a b c 0 ([0]^^d*>r).
Proof.
  unfold S1.
  st; reflexivity.
Qed.

Lemma S2_add a b r:
  S2 (a+b) r = S2 a ([0]^^b*>r).
Proof.
  unfold S2.
  st; reflexivity.
Qed.

Lemma P2_0:
  P2 50 29 19.
Proof.
  unfold P2.
  intros r k.
  follow Ov1b'.
  unfold S2.
  mid (S1 0 (8+(1+(8+0))) 0 (8*3+1) ([1;0]^^(4+k*2)*>[0]^^(2+(8*3+0))*>r)).
  stepn 481%N.
  follow Incs1.
  replace (4+k*2) with ((2+k)*2) by lia.
  follow Ov1d.
  follow Incs1.
  finish.
Qed.

Lemma P2_S [a0 c0 d c'] a1:
  P1 a0 c0 ->
  P2 (16+c0*2) d c' ->
  a1<=13+c0*2 ->
  P2 (a0+(23+(a1*3+1))) (3+(2+((13+c0*2-a1)*3+d))) (21+c0*2+c').
Proof.
  unfold P1,P2.
  intros HP1 HP2 Ha1 r k.
  follow Ov1b'.
  rewrite S2_add.
  follow HP1.
  rewrite <-S1_add.
  follow Ov1b.
  replace (14+c0*2) with (a1+(1+(13+c0*2-a1+0))) by lia.
  follow Incs1.
  replace (3+(1+k*2)) with ((2+k)*2) by lia.
  follow Ov1d.
  follow Incs1.
  follow (HP2 r (21+c0*2+k)).
  finish.
Qed.

Lemma P2_S_0 [a0 c0 d c'] a1:
  P1 a0 c0 ->
  P2 (16+c0*2) d c' ->
  a1<=14+c0*2 ->
  P2 (a0+(23+(a1*3+0))) (3+(((14+c0*2-a1)*3+d))) (21+c0*2+c').
Proof.
  unfold P1,P2.
  intros HP1 HP2 Ha1 r k.
  follow Ov1b'.
  rewrite S2_add.
  follow HP1.
  rewrite <-S1_add.
  follow Ov1b.
  replace (14+c0*2) with (a1+((14+c0*2-a1+0))) by lia.
  follow Incs1.
  follow Ov1d_0.
  replace (a1+((14+c0*2-a1+0))) with (14+c0*2) by lia.
  follow Incs1.
  follow (HP2 r (21+c0*2+k)).
  finish.
Qed.

Lemma P1_S [a0 c0 d c']:
  P1 a0 c0 ->
  P2 (16+c0*2) d c' ->
  P1 (a0+(23+((14+c0*2)*3+d))) (19+c0*2+c').
Proof.
  unfold P1,P2.
  intros HP1 HP2 r.
  rewrite S2_add.
  follow HP1.
  rewrite <-S1_add.
  follow Ov1b.
  follow (Incs1 (14+c0*2) 2 0 11 d r).
  follow (HP2 r (19+c0*2)).
  finish.
Qed.

Definition P4 c :=
  c0 -->* S1 17 0 (c*2) 0 0inf.

Lemma P4_S [c1 d c']:
  P4 c1 ->
  P2 (16+c1*2) d c' ->
  P4 (19+c1*2+c').
Proof.
  unfold P4,P2.
  intros HP1 HP2.
  follow HP1.
  rewrite <-(lpow_all0 [0] (23+((14+c1*2)*3+d))) by solve_const0_eq.
  follow Ov1b.
  follow (Incs1 (14+c1*2) 2 0 11 d 0inf).
  follow (HP2 0inf (19+c1*2)).
  rewrite lpow_all0 by solve_const0_eq.
  finish.
Qed.

Lemma P1_1: P1 272 72.
Proof.
  apply (P1_S P1_0 P2_0).
Qed.

Lemma P2_1: P2 160 115 74.
Proof.
  apply (P2_S 20 P1_0 P2_0); lia.
Qed.

Lemma P4_0: P4 48.
Proof.
  unfold P4,S1.
  esx.
Qed.

Lemma P2'_0:
  P2 112 163 74.
Proof.
  apply (P2_S 4 P1_0 P2_0); lia.
Qed.

Inductive P: nat->Prop :=
| P_intro n a0 c0 d c1 d1
  (HP1:P1 (2+a0*3) (c0*3))
  (HP2:P2 (16+c0*3*2) (1+d*3) (2+c0*3))
  (HP4:P4 (c1*3))
  (HP2':P2 (16+c1*3*2) d1 (2+c0*3)):
  a0<=11+c0*3*2 ->
  a0<=11+c1*4+c0*2 ->
  c1*4<=3+c0*4+a0 ->
  a0+d<=31+c0*3*4 ->
  a0+d<=31+c1*8+c0*4 ->
  n<=c1 ->
  P n.

Lemma P_n n: P n.
Proof.
  induction n.
  - eapply P_intro with (a0:=90) (d:=38) (c0:=24) (c1:=16).
    1: apply P1_1.
    1: apply P2_1.
    1: apply P4_0.
    1: apply P2'_0.
    all: lia.
  - inverts IHn.
    eapply P_intro with (a0:=a0+c1*3*2+d+22) (d:=d+a0+4) (c0:=7+c1*3) (c1:=7+c2*2+c1).
    1: applys_eq (P1_S HP1 HP2); lia.
    1: applys_eq (P2_S_0 (11+c1*3*2-a0) HP1 HP2); lia.
    1: applys_eq (P4_S HP4 HP2'); lia.
    1: applys_eq (P2_S_0 (11+c2*4+c1*2-a0) HP1 HP2); lia.
    all: lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_n n) as HP.
  inverts HP.
  unfold P4,S1 in HP4.
  eexists _,_; split.
  - apply HP4.
  - split.
    + solve_sigma_score.
    + lia.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1LB0RF_1LC0LB_1RD0RE_0RA0RC_1RC0LA_0RB---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c d r :=
  0inf <* [1]^^a <* [0] <{{C}} [1] *> [1;0]^^b *> [0] *> [1;0]^^c *> [0]^^d *> r.

Lemma Inc1 a b c d r:
  S1 a (1+b) c (3+d) r -->*
  S1 (1+a) b (2+c) d r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c d r:
  S1 a (n+b) c (n*3+d) r -->*
  S1 (n+a) b (n*2+c) d r.
Proof.
  gen a b c d.
  ind n Inc1.
Qed.

Lemma Ov1b c d r:
  S1 17 0 (c*2) (23+d) r -->*
  S1 2 (14+c*2) 11 d r.
Proof.
  es.
Qed.

Definition S2 a r :=
  0inf <{{B}} [0]^^a *> r.

Lemma Ov1b' a c d r:
  S1 (a) 0 c (3+d) r -->*
  S2 a ([1;0]^^(3+c)*>[0]^^d*>r).
Proof.
  es.
Qed.

Lemma Ov1d a b c c' d' r:
  S1 a (1+b) c 1 ([1;0]^^(c'*2)*>[0]^^(2+d')*>r) -->*
  S1 (1+a) b (2+c+c'*2) d' r.
Proof.
  es.
Qed.

Lemma Ov1d_0 a b c c' d' r:
  S1 a b c 0 ([1;0]^^c'*>[0]^^d'*>r) -->*
  S1 a b (c+c') d' r.
Proof.
  es.
Qed.

Definition P1 a c :=
  forall r,
  S2 a r -->*
  S1 17 0 (c*2) 0 r.

Lemma P1_0:
  P1 76 17.
Proof.
  unfold P1.
  intros.
  stepn 3150%N.
Qed.

Definition P2 a d c' :=
  forall r k,
  S1 a 0 (1+k*2) d r -->*
  S1 17 0 (c'*2+k*2) 0 r.

Lemma S1_add a b c d r:
  S1 a b c d r = S1 a b c 0 ([0]^^d*>r).
Proof.
  unfold S1.
  st; reflexivity.
Qed.

Lemma S2_add a b r:
  S2 (a+b) r = S2 a ([0]^^b*>r).
Proof.
  unfold S2.
  st; reflexivity.
Qed.

Lemma P2_0:
  P2 50 29 19.
Proof.
  unfold P2.
  intros r k.
  follow Ov1b'.
  unfold S2.
  mid (S1 0 (8+(1+(8+0))) 0 (8*3+1) ([1;0]^^(4+k*2)*>[0]^^(2+(8*3+0))*>r)).
  stepn 481%N.
  follow Incs1.
  replace (4+k*2) with ((2+k)*2) by lia.
  follow Ov1d.
  follow Incs1.
  finish.
Qed.

Lemma P2_S [a0 c0 d c'] a1:
  P1 a0 c0 ->
  P2 (16+c0*2) d c' ->
  a1<=13+c0*2 ->
  P2 (a0+(23+(a1*3+1))) (3+(2+((13+c0*2-a1)*3+d))) (21+c0*2+c').
Proof.
  unfold P1,P2.
  intros HP1 HP2 Ha1 r k.
  follow Ov1b'.
  rewrite S2_add.
  follow HP1.
  rewrite <-S1_add.
  follow Ov1b.
  replace (14+c0*2) with (a1+(1+(13+c0*2-a1+0))) by lia.
  follow Incs1.
  replace (3+(1+k*2)) with ((2+k)*2) by lia.
  follow Ov1d.
  follow Incs1.
  follow (HP2 r (21+c0*2+k)).
  finish.
Qed.

Lemma P2_S_0 [a0 c0 d c'] a1:
  P1 a0 c0 ->
  P2 (16+c0*2) d c' ->
  a1<=14+c0*2 ->
  P2 (a0+(23+(a1*3+0))) (3+(((14+c0*2-a1)*3+d))) (21+c0*2+c').
Proof.
  unfold P1,P2.
  intros HP1 HP2 Ha1 r k.
  follow Ov1b'.
  rewrite S2_add.
  follow HP1.
  rewrite <-S1_add.
  follow Ov1b.
  replace (14+c0*2) with (a1+((14+c0*2-a1+0))) by lia.
  follow Incs1.
  follow Ov1d_0.
  replace (a1+((14+c0*2-a1+0))) with (14+c0*2) by lia.
  follow Incs1.
  follow (HP2 r (21+c0*2+k)).
  finish.
Qed.

Lemma P1_S [a0 c0 d c']:
  P1 a0 c0 ->
  P2 (16+c0*2) d c' ->
  P1 (a0+(23+((14+c0*2)*3+d))) (19+c0*2+c').
Proof.
  unfold P1,P2.
  intros HP1 HP2 r.
  rewrite S2_add.
  follow HP1.
  rewrite <-S1_add.
  follow Ov1b.
  follow (Incs1 (14+c0*2) 2 0 11 d r).
  follow (HP2 r (19+c0*2)).
  finish.
Qed.

Definition P4 c :=
  c0 -->* S1 17 0 (c*2) 0 0inf.

Lemma P4_S [c1 d c']:
  P4 c1 ->
  P2 (16+c1*2) d c' ->
  P4 (19+c1*2+c').
Proof.
  unfold P4,P2.
  intros HP1 HP2.
  follow HP1.
  rewrite <-(lpow_all0 [0] (23+((14+c1*2)*3+d))) by solve_const0_eq.
  follow Ov1b.
  follow (Incs1 (14+c1*2) 2 0 11 d 0inf).
  follow (HP2 0inf (19+c1*2)).
  rewrite lpow_all0 by solve_const0_eq.
  finish.
Qed.

Lemma P1_1: P1 272 72.
Proof.
  apply (P1_S P1_0 P2_0).
Qed.

Lemma P2_1: P2 160 115 74.
Proof.
  apply (P2_S 20 P1_0 P2_0); lia.
Qed.

Lemma P4_0: P4 54.
Proof.
  unfold P4,S1.
  esx.
Qed.

Lemma P2'_0:
  P2 124 151 74.
Proof.
  apply (P2_S 8 P1_0 P2_0); lia.
Qed.

Inductive P: nat->Prop :=
| P_intro n a0 c0 d c1 d1
  (HP1:P1 (2+a0*3) (c0*3))
  (HP2:P2 (16+c0*3*2) (1+d*3) (2+c0*3))
  (HP4:P4 (c1*3))
  (HP2':P2 (16+c1*3*2) d1 (2+c0*3)):
  a0<=11+c0*3*2 ->
  a0<=11+c1*4+c0*2 ->
  c1*4<=3+c0*4+a0 ->
  a0+d<=31+c0*3*4 ->
  a0+d<=31+c1*8+c0*4 ->
  n<=c1 ->
  P n.

Lemma P_n n: P n.
Proof.
  induction n.
  - eapply P_intro with (a0:=90) (d:=38) (c0:=24) (c1:=18).
    1: apply P1_1.
    1: apply P2_1.
    1: apply P4_0.
    1: apply P2'_0.
    all: lia.
  - inverts IHn.
    eapply P_intro with (a0:=a0+c1*3*2+d+22) (d:=d+a0+4) (c0:=7+c1*3) (c1:=7+c2*2+c1).
    1: applys_eq (P1_S HP1 HP2); lia.
    1: applys_eq (P2_S_0 (11+c1*3*2-a0) HP1 HP2); lia.
    1: applys_eq (P4_S HP4 HP2'); lia.
    1: applys_eq (P2_S_0 (11+c2*4+c1*2-a0) HP1 HP2); lia.
    all: lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_n n) as HP.
  inverts HP.
  unfold P4,S1 in HP4.
  eexists _,_; split.
  - apply HP4.
  - split.
    + solve_sigma_score.
    + lia.
Qed.

End TM3.


Module TM4.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC0RE_0RD0RB_1LA0RF_1RB0LD_0LB---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 l a b c d r :=
  l <* [1]^^a <* [0] <{{B}} [1] *> [1;0]^^b *> [0] *> [1;0]^^c *> [0]^^d *> r.

Lemma Inc1 l a b c d r:
  S1 l a (1+b) c (3+d) r -->*
  S1 l (1+a) b (2+c) d r.
Proof.
  es.
Qed.

Lemma Incs1 n l a b c d r:
  S1 l a (n+b) c (n*3+d) r -->*
  S1 l (n+a) b (n*2+c) d r.
Proof.
  gen a b c d.
  ind n Inc1.
Qed.

Notation lh := (0inf<*[1]^^10<*[0;0]<*<[1;0]^^7<*[1]<*<[1;0]^^17).

Lemma Ov1b' a c d r:
  S1 lh (32+a) 0 c (3+d) r -->*
  S1 0inf 0 51 0 a ([1;0]^^(3+c)*>[0]^^d*>r).
Proof.
  unfold S1.
  do 3 (er; sr).
  stepn 2726%N.
Qed.

Lemma Ov1b c d r:
  S1 0inf 51 0 c (7+d) r -->*
  S1 lh 1 (2+c) 2 d r.
Proof.
  unfold S1.
  do 2 (er; sr).
  mid (lh <* <[1;0] {{B}}> [1;0]^^(3+c)*>[0]^^(4+d)*>r).
  1: stepn 1783%N.
  es.
Qed.

Lemma Ov1d_0 l a b c c' d' r:
  S1 l a b c 0 ([1;0]^^c'*>[0]^^d'*>r) -->*
  S1 l a b (c+c') d' r.
Proof.
  es.
Qed.

Lemma Ov1d_1 l a b c c' d' r:
  S1 l a (1+b) c 1 ([1;0]^^c'*>[0]^^(2+d')*>r) -->*
  S1 l (1+a) b (2+c+c') d' r.
Proof.
  es.
Qed.

Definition P1 a c :=
  forall r,
  S1 0inf 0 51 0 a r -->*
  S1 0inf 51 0 c 0 r.

Definition P2 a d c' :=
  forall r k,
  S1 lh a 0 k d r -->*
  S1 0inf 51 0 (c'+k) 0 r.

Lemma P1_0: P1 153 102.
Proof.
  unfold P1.
  intros.
  follow (Incs1 51).
  finish.
Qed.

Lemma P2_0: P2 105 83 105.
Proof.
  unfold P2.
  intros.
  follow Ov1b'.
  follow (Incs1 24).
  follow Ov1d_1.
  follow (Incs1 26).
  finish.
Qed.

Lemma S1_add l a b c d d0 r:
  S1 l a b c (d+d0) r = S1 l a b c d ([0]^^d0*>r).
Proof.
  unfold S1.
  st; reflexivity.
Qed.

Lemma P1_S [a0 c0 d c']:
  P1 a0 c0 ->
  P2 (3+c0) d c' ->
  P1 (a0+(7+((2+c0)*3+d))) (6+c0*2+c').
Proof.
  unfold P1,P2.
  intros HP1 HP2 r.
  rewrite S1_add.
  follow HP1.
  rewrite <-S1_add.
  follow Ov1b.
  follow (Incs1 (2+c0) lh 1 0 2 d r).
  follow (HP2 r (6+c0*2)).
  finish.
Qed.

Lemma P2_S [a0 c0 d c'] a1:
  P1 a0 c0 ->
  P2 (3+c0) d c' ->
  a1<=2+c0 ->
  P2 (32+(a0+(7+(a1*3+0)))) (3+(((2+c0-a1)*3+d))) (9+c0*2+c').
Proof.
  unfold P1,P2.
  intros HP1 HP2 Ha1 r k.
  follow Ov1b'.
  rewrite S1_add.
  follow HP1.
  rewrite <-S1_add.
  follow Ov1b.
  replace (2+c0) with (a1+((2+c0-a1+0))) by lia.
  follow Incs1.
  replace (a1+((2+c0-a1+0))) with (2+c0) by lia.
  follow Ov1d_0.
  follow Incs1.
  epose proof (HP2 _ _) as HP2.
  follow HP2.
  finish.
Qed.

Definition P4 c :=
  c0 -->* S1 0inf 51 0 c 0 0inf.

Lemma P4_0: P4 327.
Proof.
  stepn 205580%N.
Qed.

Lemma P4_S [c d c']:
  P4 c ->
  P2 (3+c) d c' ->
  P4 (6+c*2+c').
Proof.
  unfold P4,P2.
  intros HP4 HP2.
  follow HP4.
  remember (S1 0inf) as v1.
  rewrite <-(lpow_all0 [0] (7+((2+c)*3+d))) by solve_const0_eq.
  subst v1.
  rewrite <-S1_add.
  follow Ov1b.
  follow (Incs1 (2+c) lh 1 0 2 d 0inf).
  epose proof (HP2 _ _) as HP2.
  follow HP2.
  rewrite lpow_all0 by solve_const0_eq.
  finish.
Qed.

Lemma P2'_0: P2 330 260 318.
Proof.
  apply (P2_S 46 P1_0 P2_0); lia.
Qed.

Inductive P: nat->Prop :=
| P_intro n a c d c1 d1
  (HP1:P1 (a*3) (c*3))
  (HP2:P2 (3+c*3) (2+d*3) (3+c*3))
  (HP4:P4 (c1*3))
  (HP2':P2 (3+c1*3) (2+d1*3) (3+c*3)):
  9+a<=c*3 ->
  9 + (5 + a + c * 3 + d) <= (3 + c * 3) * 3 ->
  9+a<=c1*2+c ->
  c1*2<=11+a+c*2 ->
  9 + (5 + a + c * 3 + d) <= (3 + c1 * 2 + c) * 2 + (3 + c * 3) ->
  n<=c1 ->
  P n.

Lemma P_n n: P n.
Proof.
  induction n.
  - eapply P_intro with (a:=185) (c:=105) (d:=90) (c1:=109) (d1:=86).
    1: apply (P1_S P1_0 P2_0).
    1: apply (P2_S 42 P1_0 P2_0); lia.
    1: apply (P4_0).
    1: apply (P2'_0).
    all: lia.
  - inverts IHn.
    eapply P_intro with (a:=5+a+c*3+d) (c:=3+c*3) (d:=12+a+d) (c1:=3+c1*2+c) (d1:=12+a+c*2+d-c1*2).
    1: applys_eq (P1_S HP1 HP2); lia.
    1: applys_eq (P2_S (c*3-(9+a)) HP1 HP2); lia.
    1: applys_eq (P4_S HP4 HP2'); lia.
    1: applys_eq (P2_S (c1*2+c-(9+a)) HP1 HP2); lia.
    all: lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_n n) as HP.
  inverts HP.
  unfold P4,S1 in HP4.
  eexists _,_; split.
  - apply HP4.
  - split.
    + solve_sigma_score.
    + lia.
Qed.

End TM4.


Module TM5.
Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC0RA_0RD0RB_1LE0RF_1LB0LE_0LB---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 l a b c d r :=
  l <* [1]^^a <* [0] <{{B}} [1] *> [1;0]^^b *> [0] *> [1;0]^^c *> [0]^^d *> r.

Lemma Inc1 l a b c d r:
  S1 l a (1+b) c (3+d) r -->*
  S1 l (1+a) b (2+c) d r.
Proof.
  es.
Qed.

Lemma Incs1 n l a b c d r:
  S1 l a (n+b) c (n*3+d) r -->*
  S1 l (n+a) b (n*2+c) d r.
Proof.
  gen a b c d.
  ind n Inc1.
Qed.

Notation lh := (0inf<*[1]^^10<*[0;0]<*<[1;0]^^7<*[1]<*<[1;0]^^17).

Lemma Ov1b' a c d r:
  S1 lh (32+a) 0 c (3+d) r -->*
  S1 0inf 0 51 0 a ([1;0]^^(3+c)*>[0]^^d*>r).
Proof.
  unfold S1.
  do 3 (er; sr).
  stepn 2726%N.
Qed.

Lemma Ov1b c d r:
  S1 0inf 51 0 c (7+d) r -->*
  S1 lh 1 (2+c) 2 d r.
Proof.
  unfold S1.
  do 2 (er; sr).
  mid (lh <* <[1;0] {{B}}> [1;0]^^(3+c)*>[0]^^(4+d)*>r).
  1: stepn 1783%N.
  es.
Qed.

Lemma Ov1d_0 l a b c c' d' r:
  S1 l a b c 0 ([1;0]^^c'*>[0]^^d'*>r) -->*
  S1 l a b (c+c') d' r.
Proof.
  es.
Qed.

Lemma Ov1d_1 l a b c c' d' r:
  S1 l a (1+b) c 1 ([1;0]^^c'*>[0]^^(2+d')*>r) -->*
  S1 l (1+a) b (2+c+c') d' r.
Proof.
  es.
Qed.

Definition P1 a c :=
  forall r,
  S1 0inf 0 51 0 a r -->*
  S1 0inf 51 0 c 0 r.

Definition P2 a d c' :=
  forall r k,
  S1 lh a 0 k d r -->*
  S1 0inf 51 0 (c'+k) 0 r.

Lemma P1_0: P1 153 102.
Proof.
  unfold P1.
  intros.
  follow (Incs1 51).
  finish.
Qed.

Lemma P2_0: P2 105 83 105.
Proof.
  unfold P2.
  intros.
  follow Ov1b'.
  follow (Incs1 24).
  follow Ov1d_1.
  follow (Incs1 26).
  finish.
Qed.

Lemma S1_add l a b c d d0 r:
  S1 l a b c (d+d0) r = S1 l a b c d ([0]^^d0*>r).
Proof.
  unfold S1.
  st; reflexivity.
Qed.

Lemma P1_S [a0 c0 d c']:
  P1 a0 c0 ->
  P2 (3+c0) d c' ->
  P1 (a0+(7+((2+c0)*3+d))) (6+c0*2+c').
Proof.
  unfold P1,P2.
  intros HP1 HP2 r.
  rewrite S1_add.
  follow HP1.
  rewrite <-S1_add.
  follow Ov1b.
  follow (Incs1 (2+c0) lh 1 0 2 d r).
  follow (HP2 r (6+c0*2)).
  finish.
Qed.

Lemma P2_S [a0 c0 d c'] a1:
  P1 a0 c0 ->
  P2 (3+c0) d c' ->
  a1<=2+c0 ->
  P2 (32+(a0+(7+(a1*3+0)))) (3+(((2+c0-a1)*3+d))) (9+c0*2+c').
Proof.
  unfold P1,P2.
  intros HP1 HP2 Ha1 r k.
  follow Ov1b'.
  rewrite S1_add.
  follow HP1.
  rewrite <-S1_add.
  follow Ov1b.
  replace (2+c0) with (a1+((2+c0-a1+0))) by lia.
  follow Incs1.
  replace (a1+((2+c0-a1+0))) with (2+c0) by lia.
  follow Ov1d_0.
  follow Incs1.
  epose proof (HP2 _ _) as HP2.
  follow HP2.
  finish.
Qed.

Definition P4 c :=
  c0 -->* S1 0inf 51 0 c 0 0inf.

Lemma P4_0: P4 231.
Proof.
  stepn 112219%N.
Qed.

Lemma P4_S [c d c']:
  P4 c ->
  P2 (3+c) d c' ->
  P4 (6+c*2+c').
Proof.
  unfold P4,P2.
  intros HP4 HP2.
  follow HP4.
  remember (S1 0inf) as v1.
  rewrite <-(lpow_all0 [0] (7+((2+c)*3+d))) by solve_const0_eq.
  subst v1.
  rewrite <-S1_add.
  follow Ov1b.
  follow (Incs1 (2+c) lh 1 0 2 d 0inf).
  epose proof (HP2 _ _) as HP2.
  follow HP2.
  rewrite lpow_all0 by solve_const0_eq.
  finish.
Qed.

Lemma P2'_0: P2 234 356 318.
Proof.
  apply (P2_S 14 P1_0 P2_0); lia.
Qed.

Inductive P: nat->Prop :=
| P_intro n a c d c1 d1
  (HP1:P1 (a*3) (c*3))
  (HP2:P2 (3+c*3) (2+d*3) (3+c*3))
  (HP4:P4 (c1*3))
  (HP2':P2 (3+c1*3) (2+d1*3) (3+c*3)):
  9+a<=c*3 ->
  9 + (5 + a + c * 3 + d) <= (3 + c * 3) * 3 ->
  9+a<=c1*2+c ->
  c1*2<=11+a+c*2 ->
  9 + (5 + a + c * 3 + d) <= (3 + c1 * 2 + c) * 2 + (3 + c * 3) ->
  n<=c1 ->
  P n.

Lemma P_n n: P n.
Proof.
  induction n.
  - eapply P_intro with (a:=185) (c:=105) (d:=90) (c1:=77) (d1:=118).
    1: apply (P1_S P1_0 P2_0).
    1: apply (P2_S 42 P1_0 P2_0); lia.
    1: apply (P4_0).
    1: apply (P2'_0).
    all: lia.
  - inverts IHn.
    eapply P_intro with (a:=5+a+c*3+d) (c:=3+c*3) (d:=12+a+d) (c1:=3+c1*2+c) (d1:=12+a+c*2+d-c1*2).
    1: applys_eq (P1_S HP1 HP2); lia.
    1: applys_eq (P2_S (c*3-(9+a)) HP1 HP2); lia.
    1: applys_eq (P4_S HP4 HP2'); lia.
    1: applys_eq (P2_S (c1*2+c-(9+a)) HP1 HP2); lia.
    all: lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_n n) as HP.
  inverts HP.
  unfold P4,S1 in HP4.
  eexists _,_; split.
  - apply HP4.
  - split.
    + solve_sigma_score.
    + lia.
Qed.

End TM5.


Module TM6.
Definition tm := Eval compute in (TM_from_str "1LB0RF_1LC0LB_1RD0RE_0RA0RC_1RC0LA_0LC---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 l a b c d r :=
  l <* [1]^^a <* [0] <{{C}} [1] *> [1;0]^^b *> [0] *> [1;0]^^c *> [0]^^d *> r.

Lemma Inc1 l a b c d r:
  S1 l a (1+b) c (3+d) r -->*
  S1 l (1+a) b (2+c) d r.
Proof.
  es.
Qed.

Lemma Incs1 n l a b c d r:
  S1 l a (n+b) c (n*3+d) r -->*
  S1 l (n+a) b (n*2+c) d r.
Proof.
  gen a b c d.
  ind n Inc1.
Qed.

Notation lh := (0inf<*[1]^^10<*[0;0]<*<[1;0]^^7<*[1]<*<[1;0]^^17).

Lemma Ov1b' a c d r:
  S1 lh (32+a) 0 c (3+d) r -->*
  S1 0inf 0 51 0 a ([1;0]^^(3+c)*>[0]^^d*>r).
Proof.
  unfold S1.
  do 3 (er; sr).
  stepn 2726%N.
Qed.

Lemma Ov1b c d r:
  S1 0inf 51 0 c (7+d) r -->*
  S1 lh 1 (2+c) 2 d r.
Proof.
  unfold S1.
  do 2 (er; sr).
  mid (lh <* <[1;0] {{C}}> [1;0]^^(3+c)*>[0]^^(4+d)*>r).
  1: stepn 1783%N.
  es.
Qed.

Lemma Ov1d_0 l a b c c' d' r:
  S1 l a b c 0 ([1;0]^^c'*>[0]^^d'*>r) -->*
  S1 l a b (c+c') d' r.
Proof.
  es.
Qed.

Lemma Ov1d_1 l a b c c' d' r:
  S1 l a (1+b) c 1 ([1;0]^^c'*>[0]^^(2+d')*>r) -->*
  S1 l (1+a) b (2+c+c') d' r.
Proof.
  es.
Qed.

Definition P1 a c :=
  forall r,
  S1 0inf 0 51 0 a r -->*
  S1 0inf 51 0 c 0 r.

Definition P2 a d c' :=
  forall r k,
  S1 lh a 0 k d r -->*
  S1 0inf 51 0 (c'+k) 0 r.

Lemma P1_0: P1 153 102.
Proof.
  unfold P1.
  intros.
  follow (Incs1 51).
  finish.
Qed.

Lemma P2_0: P2 105 83 105.
Proof.
  unfold P2.
  intros.
  follow Ov1b'.
  follow (Incs1 24).
  follow Ov1d_1.
  follow (Incs1 26).
  finish.
Qed.

Lemma S1_add l a b c d d0 r:
  S1 l a b c (d+d0) r = S1 l a b c d ([0]^^d0*>r).
Proof.
  unfold S1.
  st; reflexivity.
Qed.

Lemma P1_S [a0 c0 d c']:
  P1 a0 c0 ->
  P2 (3+c0) d c' ->
  P1 (a0+(7+((2+c0)*3+d))) (6+c0*2+c').
Proof.
  unfold P1,P2.
  intros HP1 HP2 r.
  rewrite S1_add.
  follow HP1.
  rewrite <-S1_add.
  follow Ov1b.
  follow (Incs1 (2+c0) lh 1 0 2 d r).
  follow (HP2 r (6+c0*2)).
  finish.
Qed.

Lemma P2_S [a0 c0 d c'] a1:
  P1 a0 c0 ->
  P2 (3+c0) d c' ->
  a1<=2+c0 ->
  P2 (32+(a0+(7+(a1*3+0)))) (3+(((2+c0-a1)*3+d))) (9+c0*2+c').
Proof.
  unfold P1,P2.
  intros HP1 HP2 Ha1 r k.
  follow Ov1b'.
  rewrite S1_add.
  follow HP1.
  rewrite <-S1_add.
  follow Ov1b.
  replace (2+c0) with (a1+((2+c0-a1+0))) by lia.
  follow Incs1.
  replace (a1+((2+c0-a1+0))) with (2+c0) by lia.
  follow Ov1d_0.
  follow Incs1.
  epose proof (HP2 _ _) as HP2.
  follow HP2.
  finish.
Qed.

Definition P4 c :=
  c0 -->* S1 0inf 51 0 c 0 0inf.

Lemma P4_0: P4 255.
Proof.
  stepn 133095%N.
Qed.

Lemma P4_S [c d c']:
  P4 c ->
  P2 (3+c) d c' ->
  P4 (6+c*2+c').
Proof.
  unfold P4,P2.
  intros HP4 HP2.
  follow HP4.
  remember (S1 0inf) as v1.
  rewrite <-(lpow_all0 [0] (7+((2+c)*3+d))) by solve_const0_eq.
  subst v1.
  rewrite <-S1_add.
  follow Ov1b.
  follow (Incs1 (2+c) lh 1 0 2 d 0inf).
  epose proof (HP2 _ _) as HP2.
  follow HP2.
  rewrite lpow_all0 by solve_const0_eq.
  finish.
Qed.

Lemma P2'_0: P2 258 332 318.
Proof.
  apply (P2_S 22 P1_0 P2_0); lia.
Qed.

Inductive P: nat->Prop :=
| P_intro n a c d c1 d1
  (HP1:P1 (a*3) (c*3))
  (HP2:P2 (3+c*3) (2+d*3) (3+c*3))
  (HP4:P4 (c1*3))
  (HP2':P2 (3+c1*3) (2+d1*3) (3+c*3)):
  9+a<=c*3 ->
  9 + (5 + a + c * 3 + d) <= (3 + c * 3) * 3 ->
  9+a<=c1*2+c ->
  c1*2<=11+a+c*2 ->
  9 + (5 + a + c * 3 + d) <= (3 + c1 * 2 + c) * 2 + (3 + c * 3) ->
  n<=c1 ->
  P n.

Lemma P_n n: P n.
Proof.
  induction n.
  - eapply P_intro with (a:=185) (c:=105) (d:=90) (c1:=85) (d1:=110).
    1: apply (P1_S P1_0 P2_0).
    1: apply (P2_S 42 P1_0 P2_0); lia.
    1: apply (P4_0).
    1: apply (P2'_0).
    all: lia.
  - inverts IHn.
    eapply P_intro with (a:=5+a+c*3+d) (c:=3+c*3) (d:=12+a+d) (c1:=3+c1*2+c) (d1:=12+a+c*2+d-c1*2).
    1: applys_eq (P1_S HP1 HP2); lia.
    1: applys_eq (P2_S (c*3-(9+a)) HP1 HP2); lia.
    1: applys_eq (P4_S HP4 HP2'); lia.
    1: applys_eq (P2_S (c1*2+c-(9+a)) HP1 HP2); lia.
    all: lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_n n) as HP.
  inverts HP.
  unfold P4,S1 in HP4.
  eexists _,_; split.
  - apply HP4.
  - split.
    + solve_sigma_score.
    + lia.
Qed.

End TM6.


