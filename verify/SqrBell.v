From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import ES_v3.
From BusyCoq Require Import DivModCases.


Ltac stepn n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; st; reflexivity.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0RB_0RC0LA_1RD0LD_0LE0RD_0RA1LF_1LC---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation w := [0;1].
Notation "l <| r" := (l <{{C}} [1;1;0] *> r) (at level 30).

Definition S1 a b c d :=
  0inf <| w^^a *> [0] *> w^^b *> [0] *> w^^c *> [1;0] *> w^^d *> 0inf.
Ltac pre := unfold_config; st.

Lemma Inc1 a b c d:
  S1 (5+a*2) (2+b*2) (4+c) d -->*
  S1 (9+a*2) (6+b*2) (c) d.
Proof.
  pre.
  es' a b c d.
Qed.

Lemma Incs1 n a b c d:
  S1 (5+a*2) (2+b*2) (n*4+c) d -->*
  S1 (5+(n*2+a)*2) (2+(n*2+b)*2) c d.
Proof.
  gen a b c.
  induction n; intros.
  1: finish.
  follow (IHn a b (4+c)).
  follow (Inc1 (n*2+a) (n*2+b) c d).
  finish.
Qed.

Definition S2 a b c d e :=
  0inf <| w^^a *> [0] *> w^^b *> [0] *> w^^c *> [0] *> w^^d *> [0] *> w^^e *> 0inf.

Lemma Inc2 a b c d e:
  S2 (5+a*2) (2+b*2) (4+c) d e -->*
  S2 (9+a*2) (6+b*2) (c) d e.
Proof.
  pre.
  es' a b c d e.
Qed.

Lemma Incs2 n a b c d e:
  S2 (5+a*2) (2+b*2) (n*4+c) d e -->*
  S2 (5+(n*2+a)*2) (2+(n*2+b)*2) c d e.
Proof.
  gen a b c.
  induction n; intros.
  1: finish.
  follow (IHn a b (4+c)).
  follow (Inc2 (n*2+a) (n*2+b) c d e).
  finish.
Qed.

Lemma Ov1 a b d:
  S1 (5+a*2) (2+b*2) 3 (1+d) -->*
  S2 9 6 (3+a*2) (5+b*2) (1+d).
Proof.
  destruct (mod2 d); subst;
  pre;
  es' a b a0.
Qed.

Lemma IncsOv1 a b c d:
  S1 (5+a*2*2) (2+b*2*2) (c*4+3) (1+d) -->*
  S2 (5+1*2*2) (2+1*2*2) ((c+a)*4+3) (1+(c+b+1)*2*2) (1+d).
Proof.
  follow Incs1.
  follow Ov1.
  finish.
Qed.

Definition S3 a b c d e f :=
  0inf <| w^^a *> [0;0;1;1;0] *> w^^b *> [0;0;1;1;0] *> w^^c *> [0] *> w^^d *> [0] *> w^^e *> [0] *> w^^f *> 0inf.

Lemma Ov2 a b d e:
  S2 (5+a*2) (2+b*2) 3 (1+d*2) (12+e) -->*
  S3 13 10 3 (7+a*2) (15+b*2+d*2) (e).
Proof.
  destruct (mod2 e); subst;
  pre;
  es' a b d a0.
Qed.

Lemma IncsOv2 a b c d e:
  S2 (5+a*2*2) (2+b*2*2) (c*4+3) (1+d*2) (12+e) -->*
  S3 (3+(1+2*2)*2) (4+(1+1*2)*2) (1+1*2) (5+(1+c*2+a*2)*2) (1+(7+c*2+b*2+d)*2) e.
Proof.
  follow Incs2.
  follow Ov2.
  finish.
Qed.

Lemma Inc3 a b c d e f:
  S3 (3+a*2) (4+b*2) (1+c*2) (5+d*2) (5+e*2) (f) -->*
  S3 (7+a*2) (4+b*2) (3+c*2) (7+d*2) (1+e*2) (f).
Proof.
  destruct (mod2 f); subst;
  pre;
  es' a b c d e a0.
Qed.

Lemma Incs3 n a b c d e f:
  S3 (3+a*2) (4+b*2) (1+c*2) (5+d*2) (1+(n*2+e)*2) f -->*
  S3 (3+(n*2+a)*2) (4+b*2) (1+(n+c)*2) (5+(n+d)*2) (1+e*2) f.
Proof.
  gen a b c d e.
  induction n; intros.
  1: finish.
  follow (IHn a b c d (2+e)).
  follow (Inc3 (n*2+a) b (n+c) (n+d) e f).
  finish.
Qed.

Definition S4 a b c d e :=
  0inf <| w^^a *> [0] *> w^^b *> [0] *> w^^c *> [0] *> w^^d *> [1;0] *> w^^e *> 0inf.

Lemma Ov3 a b c d f:
  S3 (3+a*2) (4+b*2) (1+c*2) (5+d*2) 3 (1+f) -->*
  S4 (11+a*2) (8+b*2) (5+c*2) (5+d*2) (f).
Proof.
  destruct (mod2 f); subst;
  pre;
  es' a b c d a0.
Qed.

Lemma IncsOv3 a b c d e f:
  S3 (3+(1+a*2)*2) (4+(1+b*2)*2) (1+c*2) (5+d*2) (1+(e*2+1)*2) (1+f) -->*
  S4 (5+(2+e+a)*2*2) (2+(2+b)*2*2) (5+(e+c)*2) (5+(e+d)*2) f.
Proof.
  follow Incs3.
  follow Ov3.
  finish.
Qed.

Definition S9 a b c d e :=
  0inf <| w^^a *> [0] *> w^^b *> [0] *> w^^c *> [0;0;1;1;0] *> w^^d *> [1;0] *> w^^e *> 0inf.

Lemma Ov3_1 a b c d f:
  S3 (3+a*2) (4+b*2) (1+c*2) (5+d*2) 1 (1+f) -->*
  S9 (11+a*2) (8+b*2) (5+c*2) (1+d*2) (f).
Proof.
  destruct (mod2 f); subst;
  pre;
  es' a b c d a0.
Qed.

Lemma Inc9 a b c d e:
  S9 (5+a*2) (2+b*2) (4+c) d e -->*
  S9 (9+a*2) (6+b*2) (c) d e.
Proof.
  pre.
  es' a b c d e.
Qed.

Lemma Incs9 n a b c d e:
  S9 (5+a*2) (2+b*2) (n*4+c) d e -->*
  S9 (5+(n*2+a)*2) (2+(n*2+b)*2) c d e.
Proof.
  gen a b c.
  induction n; intros.
  1: finish.
  follow (IHn a b (4+c)).
  follow (Inc9 (n*2+a) (n*2+b) c d e).
  finish.
Qed.

Lemma IncsOv3_1 a b c d e f:
  S3 (3+(1+a*2)*2) (4+(1+b*2)*2) (1+c*2) (5+d*2) (1+(e*2+0)*2) (1+f) -->*
  S9 (5+(2+e+a)*2*2) (2+(2+b)*2*2) 
    (5 + (e + c) * 2) (1 + (e + d) * 2) f.
Proof.
  follow Incs3.
  follow Ov3_1.
  finish.
Qed.

Lemma Inc4 a b c d e:
  S4 (5+a*2) (2+b*2) (4+c) d e -->*
  S4 (9+a*2) (6+b*2) (c) d e.
Proof.
  pre.
  es' a b c d e.
Qed.

Lemma Incs4 n a b c d e:
  S4 (5+a*2) (2+b*2) (n*4+c) d e -->*
  S4 (5+(n*2+a)*2) (2+(n*2+b)*2) c d e.
Proof.
  gen a b c.
  induction n; intros.
  1: finish.
  follow (IHn a b (4+c)).
  follow (Inc4 (n*2+a) (n*2+b) c d e).
  finish.
Qed.

Definition S5 a b c d :=
  0inf <| w^^a *> [0] *> w^^b *> [0] *> w^^c *> [0;0;1;1;0] *> w^^d *> 0inf.

Lemma Inc5 a b c d:
  S5 (5+a*2) (2+b*2) (4+c) d -->*
  S5 (9+a*2) (6+b*2) (c) d.
Proof.
  pre.
  es' a b c d.
Qed.

Lemma Incs5 n a b c d:
  S5 (5+a*2) (2+b*2) (n*4+c) d -->*
  S5 (5+(n*2+a)*2) (2+(n*2+b)*2) c d.
Proof.
  gen a b c.
  induction n; intros.
  1: finish.
  follow (IHn a b (4+c)).
  follow (Inc5 (n*2+a) (n*2+b) c d).
  finish.
Qed.

Lemma Ov4_3_2 a b d:
  S4 (5+a*2) (2+b*2) 3 (5+d*2) 2 -->*
  S5 9 6 (12+a*2) (4+(2+b*2)+(5+d*2)).
Proof.
  pre.
  es' a b d.
Qed.

Lemma Ov5 a b d:
  S5 (5+a*2) (2+b*2) 0 (3+d) -->+
  S1 9 (10+a*2) (11+b*2) (d).
Proof.
  destruct (mod2 d); subst;
  pre;
  es' a b a0.
Qed.

Lemma IncsOv5 a b c d:
  S5 (5+a*2*2) (2+b*2*2) (c*4+0) (3+d) -->+
  S1 (5+1*2*2) (2+(2+c+a)*2*2) ((2+c+b)*4+3) d.
Proof.
  follow Incs5.
  follow10 Ov5.
  finish.
Qed.

Lemma Ov4_1 a b d e:
  S4 (5+a*2) (2+b*2) 1 (5+d*2) (3+e) -->*
  S5 9 6 (8+a*2) (1+(2+b*2)+(5+d*2)+(3+e)).
Proof.
  destruct (mod2 e); subst;
  pre;
  es' a b d a0.
Qed.

Lemma Incs4Ov4_1 a b c d e:
  S4 (5+a*2*2) (2+b*2*2) (c*4+1) (5+d*2) (3+e) -->*
  S5 9 6 ((2+c+a)*2*2) (1+(2+c*4+b*4)+(5+d*2)+(3+e)).
Proof.
  follow Incs4.
  follow Ov4_1.
  finish.
Qed.

Lemma IncsOvs5_ex c d:
  S5 (5+1*2*2) (2+1*2*2) (c*4+0) (3+(1+(11+(1+d)))) -->+
  S4 (5 + (19 + c * 3) * 2 * 2) (2 + 3 * 2 * 2)
    (5 + (16 + c * 3) * 2)
    (5 + (26 + c * 5) * 2) d.
Proof.
  follow10 IncsOv5.
  follow IncsOv1.
  follow IncsOv2.
  replace (7 + (2 + c + 1 + 1) * 2 + 1 * 2 + (2 + c + 1 + (2 + c + 1) + 1) * 2)
  with ((15+c*3)*2+1) by lia.
  follow IncsOv3.
  finish.
Qed.

Lemma IncsOvs5_c0 c d:
  S5 9 6 ((0+c*2)*4+0) (19+d) -->+
  S5 9 6 (((30+c*9))*4+0) (19+(92+c*32+d)).
Proof.
  follow10 IncsOvs5_ex.
  replace (5 + (16 + (0 + c * 2) * 3) * 2) with
    ((9 + c * 3) * 4 + 1) by lia.
  follow Incs4Ov4_1.
  finish.
Qed.

Definition S6 a b c d e f :=
  0inf <| w^^a *> [0] *> w^^b *> [0] *> w^^c *> [0] *> w^^d *> [0] *> w^^e *> [0] *> w^^f *> 0inf.

Lemma Ov4_3 a b d e:
  S4 (5+a*2) (2+b*2) 3 (5+d*2) (9+e) -->*
  S6 9 6 (12+a*2) (6+(2+b*2)+(5+d*2)) 9 (e).
Proof.
  destruct (mod2 e); subst;
  pre;
  es' a b d a0.
Qed.

Lemma Incs4Ov4_3 a b c d e:
  S4 (5+a*2*2) (2+b*2*2) (c*4+3) (5+d*2) (9+e) -->*
  S6 (5+1*2*2) (2+1*2*2) ((3+c+a)*4+0) (1+(6+(c+b)*2+d)*2) 9 e.
Proof.
  follow Incs4.
  follow Ov4_3.
  finish.
Qed.

Lemma Inc6 a b c d e f:
  S6 (5+a*2) (2+b*2) (4+c) d e f -->*
  S6 (9+a*2) (6+b*2) (c) d e f.
Proof.
  pre.
  es' a b c d e f.
Qed.

Lemma Incs6 n a b c d e f:
  S6 (5+a*2) (2+b*2) (n*4+c) d e f -->*
  S6 (5+(n*2+a)*2) (2+(n*2+b)*2) c d e f.
Proof.
  gen a b c.
  induction n; intros.
  1: finish.
  follow (IHn a b (4+c)).
  follow (Inc6 (n*2+a) (n*2+b) c d e f).
  finish.
Qed.

Lemma Ov6_0_9 a b d f:
  S6 (5+a*2) (2+b*2) 0 (1+d*2) 9 (4+f) -->*
  S6 9 6 (3+a*2) ((2+b*2)+(1+d*2)) 13 (f).
Proof.
  destruct (mod2 f); subst;
  pre;
  es' a b d a0.
Qed.

Lemma IncsOv6_0_9 a b c d f:
  S6 (5+a*2*2) (2+b*2) (c*4+0) (1+d*2) 9 (4+f) -->*
  S6 (5+1*2*2) (2+1*2*2) ((c+a)*4+3) (1+(1+c*2+b+d)*2) 13 (f).
Proof.
  follow Incs6.
  follow Ov6_0_9.
  finish.
Qed.

Lemma Ov6_3_13 a b d f:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 13 (11+f) -->*
  S6 9 6 (31+a*2) (20+(2+b*2)+(1+d*2)) 9 (f).
Proof.
  destruct (mod2 f); subst;
  pre;
  es' a b d a0.
Qed.

Lemma IncsOv6_3_13 a b c d f:
  S6 (5+a*2*2) (2+b*2) (c*4+3) (1+d*2) 13 (11+f) -->*
  S6 9 6 ((7+c+a)*4+3) (1+(11+c*2+b+d)*2) 9 (f).
Proof.
  follow Incs6.
  follow Ov6_3_13.
  finish.
Qed.

Lemma IncsOvs5_c1 c d:
  S5 9 6 ((1+c*2)*4+0) (40+d) -->+
  S6 9 6 ((44+c*9)*4+3) (1+(221+c*52)*2) 9 d.
Proof.
  follow10 IncsOvs5_ex.
  replace (5 + (16 + (1 + c * 2) * 3) * 2) with
    ((10 + c * 3) * 4 + 3) by lia.
  follow Incs4Ov4_3.
  follow IncsOv6_0_9.
  follow IncsOv6_3_13.
  finish.
Qed.

Lemma Ov6_3_9 a b d f:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 (11+f) -->+
  S6 9 6 (27+a*2) (16+(2+b*2)+(1+d*2)) 9 (f).
Proof.
  destruct (mod2 f); subst;
  pre;
  es' a b d a0.
Qed.

Lemma IncsOv6_3_9 n d f:
  S6 9 6 (n*4+3) (1+d*2) 9 (11+f) -->+
  S6 9 6 ((7+n)*4+3) (1+(n*2+11+d)*2) 9 f.
Proof.
  follow (Incs6 n 2 2 3 (1+d*2) 9 (11+f)).
  follow10 (Ov6_3_9 (n*2+2) (n*2+2) d f).
  finish.
Qed.

Lemma Ov6_3_9_10 a b d:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 10 -->+
  S3 (3+(1+2*2)*2) (4+(1+1*2)*2) (1+1*2) (5+23*2) (121+a*2) (1+(6+(2+b*2)+(1+d*2))).
Proof.
  pre.
  es' a b d.
Qed.

Lemma Ov9_1 a b d e:
  S9 (5+a*2) (2+b*2) 1 (3+d*2) (1+e*2) -->*
  S2 9 6 (3+a*2) (4+(2+b*2)+(3+d*2)+(1+e*2)) 0.
Proof.
  pre.
  es' a b d e.
Qed.

Lemma Ov9_3 a b d e:
  S9 (5+a*2) (2+b*2) 3 (3+d*2) (1+e*2) -->*
  S5 9 6 (8+a*2) (3+(2+b*2)+(3+d*2)+(1+e*2)).
Proof.
  pre.
  es' a b d e.
Qed.

Lemma Ov2_0 a b d:
  S2 (5+a*2) (2+b*2) 3 (2+d*2) 0 -->*
  S5 9 6 (4+a*2) ((2+b*2)+(2+d*2)).
Proof.
  pre.
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_10_0 c d:
  S6 (5+1*2*2) (2+1*2*2) ((c*2)*4+3) (1+d*2) 9 10 -->+
  S5 (5+1*2*2) (2+1*2*2) ((c*3+54)*4+0) ((211+c*14+d)*2).
Proof.
  replace (c*2) with (c*2+0) by lia.
  follow Incs6.
  follow10 Ov6_3_9_10.
  replace (121 + ((c*2+0) * 2 + 1 * 2) * 2) with (1+((c*2+31)*2+0)*2) by lia.
  follow IncsOv3_1.
  replace (5 + (c * 2 + 31 + 1) * 2) with ((17+c)*4+1) by lia.
  replace (1 + (c * 2 + 31 + 23) * 2) with (3+(c*2+53)*2) by lia.
  replace (6 + (2 + ((c * 2 + 0) * 2 + 1 * 2) * 2) + (1 + d * 2)) with
    (1+(6+c*4+d)*2) by lia.
  follow Incs9.
  follow Ov9_1.
  mid (S2 (5+1*2*2) (2+1*2*2) ((c*3+52)*4+3) ((104+c*8+d)*2) 0).
  1: finish.
  follow Incs2.
  replace ((104+c*8+d)*2) with (2+(103+c*8+d)*2) by lia.
  follow Ov2_0.
  finish.
Qed.

Lemma IncsOvs6_3_9_10_1 c d:
  S6 (5+1*2*2) (2+1*2*2) ((1+c*2)*4+3) (1+d*2) 9 10 -->+
  S5 (5+1*2*2) (2+1*2*2) ((c*3+55)*4+0) (3+(105+c*8+d)*2).
Proof.
  rewrite (Nat.add_comm 1 (c*2)).
  follow Incs6.
  follow10 Ov6_3_9_10.
  replace (121 + ((c*2+1) * 2 + 1 * 2) * 2) with (1+((c*2+32)*2+0)*2) by lia.
  follow IncsOv3_1.
  replace (5 + (c * 2 + 32 + 1) * 2) with ((17+c)*4+3) by lia.
  replace (1 + (c * 2 + 32 + 23) * 2) with (3+(c*2+54)*2) by lia.
  replace (6 + (2 + ((c * 2 + 1) * 2 + 1 * 2) * 2) + (1 + d * 2)) with
    (1+(8+c*4+d)*2) by lia.
  follow Incs9.
  follow Ov9_3.
  finish.
Qed.

Lemma Ov6_3_9_9 a b d:
  S6 (5+a*2*2) (2+b*2) 3 (1+d*2) 9 9 -->+
  S2 (5+1*2*2) (2+(7+a)*2*2) (1+(12+b+d)*2) 4 0.
Proof.
  pre.
  es' a b d.
Qed.

Lemma Ov2_1_4 a b:
  S2 (5+a*2) (4+b*2) 1 4 0 -->*
  S2 37 (34+a*2) (2+b*2) 0 0.
Proof.
  pre.
  es' a b.
Qed.

Lemma Ov2_0_0 a b:
  S2 (5+a*2) (2+b*2) 0 0 0 -->*
  S2 9 (2+a*2) (2+b*2) 0 0.
Proof.
  pre.
  es' a b.
Qed.

Lemma Ov2_2_0 a b:
  S2 (5+a*2) (2+b*2) 2 0 0 -->*
  S5 9 6 (8+a*2) (b*2).
Proof.
  pre.
  es' a b.
Qed.

Lemma IncsOvs6_3_9_9_0 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+(d*2)*2) 9 9 -->+
  S5 (5+1*2*2) (2+1*2*2) ((34+c*3+d*2)*4+0) (3+(1+(53+c*5+d*3)*4)).
Proof.
  replace (d*2) with (d*2+0) by lia.
  follow Incs6.
  replace (c*2+1*2) with ((1+c)*2) by lia.
  follow10 Ov6_3_9_9.
  replace (1 + (12 + (1 + c) * 2 + (d * 2 + 0)) * 2) with
    ((7+c+d)*4+1) by lia.
  follow Incs2.
  follow Ov2_1_4.
  fold Nat.mul Nat.add.
  mid (S2 (5+8*2*2) (2+(16+c+d)*2*2) ((15+c*2+d)*4+0) 0 0).
  1: finish.
  follow Incs2.
  follow Ov2_0_0.
  mid (S2 (5+1*2*2) (2+(23+c*2+d)*2*2) ((31+c*3+d*2)*4+2) 0 0).
  1: finish.
  follow Incs2.
  follow Ov2_2_0.
  finish.
Qed.

Lemma Ov2_3_4 a b:
  S2 (5+a*2) (2+b*2) 3 4 0 -->*
  S5 9 6 (4+a*2) (6+b*2).
Proof.
  pre.
  es' a b.
Qed.

Lemma IncsOvs6_3_9_9_1 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+(1+d*2)*2) 9 9 -->+
  S5 (5+1*2*2) (2+1*2*2) ((9+c+d)*4+0) (2+(16+c*2+d)*4).
Proof.
  follow Incs6.
  replace (c*2+1*2) with ((1+c)*2) by lia.
  follow10 Ov6_3_9_9.
  replace (1 + (12 + (1 + c) * 2 + (1 + d * 2)) * 2) with
    ((7+c+d)*4+3) by lia.
  follow Incs2.
  follow Ov2_3_4.
  finish.
Qed.

Definition S7 a b c d e :=
  0inf <| w^^a *> [0] *> w^^b *> [0] *> w^^c *> [0;0;1;1;0] *> w^^d *> [0;0;1;1;0] *> w^^e *> 0inf.

Lemma Ov6_3_9_8 a b d:
  S6 (5+a*2*2) (2+b*2) 3 (1+d*2) 9 8 -->+
  S7 (5+1*2*2) (2+1*2*2) ((8+a)*4+0) ((10+b+d)*2) 0.
Proof.
  pre.
  es' a b d.
Qed.

Lemma Inc7 a b c d e:
  S7 (5+a*2) (2+b*2) (4+c) d e -->*
  S7 (9+a*2) (6+b*2) (c) d e.
Proof.
  pre.
  es' a b c d e.
Qed.

Lemma Incs7 n a b c d e:
  S7 (5+a*2) (2+b*2) (n*4+c) d e -->*
  S7 (5+(n*2+a)*2) (2+(n*2+b)*2) c d e.
Proof.
  gen a b c.
  induction n; intros.
  1: finish.
  follow (IHn a b (4+c)).
  follow (Inc7 (n*2+a) (n*2+b) c d).
  finish.
Qed.

Lemma Ov7_0_0 a b d:
  S7 (5+a*2) (2+b*2) 0 (2+d*2) 0 -->*
  S5 9 6 (8+a*2) (5+b*2+d*2).
Proof.
  pre.
  es' a b d.
Qed.

Lemma Ov7_0_5 a b d:
  S7 (5+a*2) (2+b*2) 0 (2+d*2) 5 -->*
  S5 9 6 (16+a*2) (6+(2+b*2)+(2+d*2)).
Proof.
  pre.
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_8 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+d*2) 9 8 -->+
  S5 9 6 ((12+c)*4+0) (67+c*8+d*2).
Proof.
  follow Incs6.
  replace (c*2+1*2) with ((1+c)*2) by lia.
  follow10 Ov6_3_9_8.
  follow Incs7.
  follow Ov7_0_0.
  fold Nat.add Nat.mul.
  finish.
Qed.

Lemma Ov6_3_9_7 a b d:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 7 -->+
  S5 9 6 (36+a*2) (18+(2+b*2)+(1+d*2)).
Proof.
  pre.
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_7 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+d*2) 9 7 -->+
  S5 9 6 ((10+c)*4+0) (25+c*4+d*2).
Proof.
  follow Incs6.
  follow10 Ov6_3_9_7.
  finish.
Qed.

Lemma Ov6_3_9_6 a b d:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 6 -->+
  S5 9 6 (28+a*2) (16+(2+b*2)+(1+d*2)).
Proof.
  pre.
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_6 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+d*2) 9 6 -->+
  S5 9 6 ((8+c)*4+0) (23+c*4+d*2).
Proof.
  follow Incs6.
  follow10 Ov6_3_9_6.
  finish.
Qed.

Lemma Ov6_3_9_5 a b d:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 5 -->+
  S5 9 6 (32+a*2) (16+(2+b*2)+(1+d*2)).
Proof.
  pre.
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_5 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+d*2) 9 5 -->+
  S5 9 6 ((9+c)*4+0) (23+c*4+d*2).
Proof.
  follow Incs6.
  follow10 Ov6_3_9_5.
  finish.
Qed.

Lemma Ov6_3_9_4 a b d:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 4 -->+
  S5 9 6 (28+a*2) (13+(2+b*2)+(1+d*2)).
Proof.
  pre.
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_4 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+d*2) 9 4 -->+
  S5 9 6 ((8+c)*4+0) (20+c*4+d*2).
Proof.
  follow Incs6.
  follow10 Ov6_3_9_4.
  finish.
Qed.

Definition S8 a b c d e :=
  0inf <| w^^a *> [0] *> w^^b *> [0] *> w^^c *> [0;0;1;1;0] *> w^^d *> [0] *> w^^e *> 0inf.

Lemma Inc8 a b c d e:
  S8 (5+a*2) (2+b*2) (4+c) d e -->*
  S8 (9+a*2) (6+b*2) (c) d e.
Proof.
  pre.
  es' a b c d e.
Qed.

Lemma Incs8 n a b c d e:
  S8 (5+a*2) (2+b*2) (n*4+c) d e -->*
  S8 (5+(n*2+a)*2) (2+(n*2+b)*2) c d e.
Proof.
  gen a b c.
  induction n; intros.
  1: finish.
  follow (IHn a b (4+c)).
  follow (Inc8 (n*2+a) (n*2+b) c d).
  finish.
Qed.

Lemma Ov6_3_9_3 a b d:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 3 -->+
  S8 9 6 (8+a*2) (2+(2+b*2)+(1+d*2)) 10.
Proof.
  pre.
  es' a b d.
Qed.

Lemma Ov8_0_10 a b d:
  S8 (5+a*2) (2+b*2) 0 (3+d*2) 10 -->*
  S5 9 6 (28+a*2) (13+(2+b*2)+(3+d*2)).
Proof.
  pre;
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_3 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+d*2) 9 3 -->+
  S5 9 6 ((11+c)*4+0) (40+c*8+d*2).
Proof.
  follow Incs6.
  follow10 Ov6_3_9_3.
  mid (S8 (5+1*2*2) (2+1*2*2) ((3+c)*4+0) (3+(3+c*2+d)*2) 10).
  1: finish.
  follow Incs8.
  follow Ov8_0_10.
  finish.
Qed.

Lemma Ov6_3_9_2 a b d:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 2 -->+
  S2 9 6 (7+a*2) (8+(2+b*2)+(1+d*2)) 8.
Proof.
  pre.
  es' a b d.
Qed.

Lemma Ov2_3_8 a b d:
  S2 (5+a*2) (2+b*2) 3 (1+d*2) 8 -->*
  S2 25 (30+a*2) (3+(2+b*2)+(1+d*2)) 0 0.
Proof.
  pre.
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_2_0 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+(d*2)*2) 9 2 -->+
  S5 9 6 ((21+c*3+d)*4+0) ((31+c*5+d*2)*4).
Proof.
  follow Incs6.
  follow10 Ov6_3_9_2.
  mid (S2 (5+1*2*2) (2+1*2*2) ((2+c)*4+3) (1+(7+c*2+d*2)*2) 8).
  1: finish.
  follow Incs2.
  follow Ov2_3_8.
  mid (S2 (5+5*2*2) (2+(10+c)*2*2) ((8+c*2+d)*4+0) 0 0).
  1: finish.
  follow Incs2.
  follow Ov2_0_0.
  mid (S2 (5+1*2*2) (2+(13+c*2+d)*2*2) ((18+c*3+d)*4+2) 0 0).
  1: finish.
  follow Incs2.
  follow Ov2_2_0.
  finish.
Qed.

Lemma IncsOvs6_3_9_2_1 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+(1+d*2)*2) 9 2 -->+
  S5 9 6 ((15+c*2+d)*4+0) ((18+c*3+d)*4).
Proof.
  follow Incs6.
  follow10 Ov6_3_9_2.
  mid (S2 (5+1*2*2) (2+1*2*2) ((2+c)*4+3) (1+(8+c*2+d*2)*2) 8).
  1: finish.
  follow Incs2.
  follow Ov2_3_8.
  mid (S2 (5+5*2*2) (2+(10+c)*2*2) ((8+c*2+d)*4+2) 0 0).
  1: finish.
  follow Incs2.
  follow Ov2_2_0.
  finish.
Qed.

Lemma Ov6_3_9_1 a b d:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 1 -->+
  S7 9 6 (8+a*2) (3+(2+b*2)+(1+d*2)) 5.
Proof.
  pre.
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_1 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+d*2) 9 1 -->+
  S5 9 6 ((8+c)*4+0) (34+c*8+d*2).
Proof.
  follow Incs6.
  follow10 Ov6_3_9_1.
  mid (S7 (5+1*2*2) (2+1*2*2) ((3+c)*4+0) (2+(4+c*2+d)*2) 5).
  1: finish.
  follow Incs7.
  follow Ov7_0_5.
  finish.
Qed.

Lemma Ov6_3_9_0 a b d:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 0 -->*
  S2 (5+a*2) (2+b*2) 3 (1+d*2) 9.
Proof.
  pre.
  es' a b d.
Qed.

Lemma Ov2_3_9 a b d:
  S2 (5+a*2) (2+b*2) 3 (1+d*2) 9 -->+
  S2 45 (58+a*2) (1+(2+b*2)+(1+d*2)) 0 0.
Proof.
  pre.
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_0_0 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+(d*2)*2) 9 0 -->+
  S5 9 6 ((20+c*2+d)*4+0) ((29+c*3+d*2)*4).
Proof.
  follow Incs6.
  follow Ov6_3_9_0.
  follow10 Ov2_3_9.
  mid (S2 (5+10*2*2) (2+(15+c)*2*2) ((2+c+d)*4+0) 0 0).
  1: finish.
  follow Incs2.
  follow Ov2_0_0.
  mid (S2 (5+1*2*2) (2+(12+c+d)*2*2) ((17+c*2+d)*4+2) 0 0).
  1: finish.
  follow Incs2.
  follow Ov2_2_0.
  finish.
Qed.

Lemma IncsOvs6_3_9_0_1 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+(1+d*2)*2) 9 0 -->+
  S5 9 6 ((14+c+d)*4+0) ((17+c*2+d)*4).
Proof.
  follow Incs6.
  follow Ov6_3_9_0.
  follow10 Ov2_3_9.
  mid (S2 (5+10*2*2) (2+(15+c)*2*2) ((2+c+d)*4+2) 0 0).
  1: finish.
  follow Incs2.
  follow Ov2_2_0.
  finish.
Qed.

Inductive Config :=
| cfg6 (c d f:nat)
| cfg5 (c d:nat)
.

Definition to_config x :=
match x with
| cfg6 c d f => S6 9 6 (c*4+3) (1+d*2) 9 f
| cfg5 c d => S5 9 6 (c*4+0) (20+d)
end.

Definition P x :=
match x with
| cfg6 c d f => c>=5
| cfg5 c d => d>=20
end.


Ltac eex a :=
  (eexists (a _ _) || eexists (a _ _ _));
  split; [|shelve];
  cbn[to_config].

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P.
  intros HP.
  destruct x; cbn[to_config].
  - destruct f.
    {
      destruct (mod2 d); subst.
      - eex cfg5; apply IncsOvs6_3_9_0_0.
      - eex cfg5; apply IncsOvs6_3_9_0_1.
    }
    destruct f.
    1: eex cfg5; apply IncsOvs6_3_9_1.
    destruct f.
    {
      destruct (mod2 d); subst.
      - eex cfg5; apply IncsOvs6_3_9_2_0.
      - eex cfg5; apply IncsOvs6_3_9_2_1.
    }
    destruct f.
    1: eex cfg5; apply IncsOvs6_3_9_3.
    destruct f.
    1: eex cfg5; apply IncsOvs6_3_9_4.
    destruct f.
    1: eex cfg5; apply IncsOvs6_3_9_5.
    destruct f.
    1: eex cfg5; apply IncsOvs6_3_9_6.
    destruct f.
    1: eex cfg5; apply IncsOvs6_3_9_7.
    destruct f.
    1: eex cfg5; apply IncsOvs6_3_9_8.
    destruct f.
    {
      destruct (mod2 d); subst.
      - eex cfg5; apply IncsOvs6_3_9_9_0.
      - eex cfg5; apply IncsOvs6_3_9_9_1.
    }
    destruct f.
    {
      destruct (mod2 c); subst.
      - eex cfg5; apply IncsOvs6_3_9_10_0.
      - eex cfg5; apply IncsOvs6_3_9_10_1.
    }
    eex cfg6; apply IncsOv6_3_9.
  - destruct (mod2 c); subst.
    + eex cfg5; apply IncsOvs5_c0.
    + replace d with (20+(d-20)) by lia.
      eex cfg6; apply IncsOvs5_c1.
  Unshelve.
  all: fold Nat.add Nat.mul; lia.
Qed.

Lemma init:
  c0 -->*
  to_config (cfg5 44 137).
Proof.
  stepn 1115477%N.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond.
  apply (fun i => closed i).
  unfold P; lia.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC0LC_0LD0RC_0RE1LA_1RF0RF_0RB0LE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation w := [0;1].
Notation "l <| r" := (l <{{B}} [1;1;0] *> r) (at level 30).

Definition S1 a b c d :=
  0inf <| w^^a *> [0] *> w^^b *> [0] *> w^^c *> [1;0] *> w^^d *> 0inf.
Ltac pre := unfold_config; st.

Lemma Inc1 a b c d:
  S1 (5+a*2) (2+b*2) (4+c) d -->*
  S1 (9+a*2) (6+b*2) (c) d.
Proof.
  pre.
  es' a b c d.
Qed.

Lemma Incs1 n a b c d:
  S1 (5+a*2) (2+b*2) (n*4+c) d -->*
  S1 (5+(n*2+a)*2) (2+(n*2+b)*2) c d.
Proof.
  gen a b c.
  induction n; intros.
  1: finish.
  follow (IHn a b (4+c)).
  follow (Inc1 (n*2+a) (n*2+b) c d).
  finish.
Qed.

Definition S2 a b c d e :=
  0inf <| w^^a *> [0] *> w^^b *> [0] *> w^^c *> [0] *> w^^d *> [0] *> w^^e *> 0inf.

Lemma Inc2 a b c d e:
  S2 (5+a*2) (2+b*2) (4+c) d e -->*
  S2 (9+a*2) (6+b*2) (c) d e.
Proof.
  pre.
  es' a b c d e.
Qed.

Lemma Incs2 n a b c d e:
  S2 (5+a*2) (2+b*2) (n*4+c) d e -->*
  S2 (5+(n*2+a)*2) (2+(n*2+b)*2) c d e.
Proof.
  gen a b c.
  induction n; intros.
  1: finish.
  follow (IHn a b (4+c)).
  follow (Inc2 (n*2+a) (n*2+b) c d e).
  finish.
Qed.

Lemma Ov1 a b d:
  S1 (5+a*2) (2+b*2) 3 (1+d) -->*
  S2 9 6 (3+a*2) (5+b*2) (1+d).
Proof.
  destruct (mod2 d); subst;
  pre;
  es' a b a0.
Qed.

Lemma IncsOv1 a b c d:
  S1 (5+a*2*2) (2+b*2*2) (c*4+3) (1+d) -->*
  S2 (5+1*2*2) (2+1*2*2) ((c+a)*4+3) (1+(c+b+1)*2*2) (1+d).
Proof.
  follow Incs1.
  follow Ov1.
  finish.
Qed.

Definition S3 a b c d e f :=
  0inf <| w^^a *> [0;0;1;1;0] *> w^^b *> [0;0;1;1;0] *> w^^c *> [0] *> w^^d *> [0] *> w^^e *> [0] *> w^^f *> 0inf.

Lemma Ov2 a b d e:
  S2 (5+a*2) (2+b*2) 3 (1+d*2) (12+e) -->*
  S3 13 10 3 (7+a*2) (15+b*2+d*2) (e).
Proof.
  destruct (mod2 e); subst;
  pre;
  es' a b d a0.
Qed.

Lemma IncsOv2 a b c d e:
  S2 (5+a*2*2) (2+b*2*2) (c*4+3) (1+d*2) (12+e) -->*
  S3 (3+(1+2*2)*2) (4+(1+1*2)*2) (1+1*2) (5+(1+c*2+a*2)*2) (1+(7+c*2+b*2+d)*2) e.
Proof.
  follow Incs2.
  follow Ov2.
  finish.
Qed.

Lemma Inc3 a b c d e f:
  S3 (3+a*2) (4+b*2) (1+c*2) (5+d*2) (5+e*2) (f) -->*
  S3 (7+a*2) (4+b*2) (3+c*2) (7+d*2) (1+e*2) (f).
Proof.
  destruct (mod2 f); subst;
  pre;
  es' a b c d e a0.
Qed.

Lemma Incs3 n a b c d e f:
  S3 (3+a*2) (4+b*2) (1+c*2) (5+d*2) (1+(n*2+e)*2) f -->*
  S3 (3+(n*2+a)*2) (4+b*2) (1+(n+c)*2) (5+(n+d)*2) (1+e*2) f.
Proof.
  gen a b c d e.
  induction n; intros.
  1: finish.
  follow (IHn a b c d (2+e)).
  follow (Inc3 (n*2+a) b (n+c) (n+d) e f).
  finish.
Qed.

Definition S4 a b c d e :=
  0inf <| w^^a *> [0] *> w^^b *> [0] *> w^^c *> [0] *> w^^d *> [1;0] *> w^^e *> 0inf.

Lemma Ov3 a b c d f:
  S3 (3+a*2) (4+b*2) (1+c*2) (5+d*2) 3 (1+f) -->*
  S4 (11+a*2) (8+b*2) (5+c*2) (5+d*2) (f).
Proof.
  destruct (mod2 f); subst;
  pre;
  es' a b c d a0.
Qed.

Lemma IncsOv3 a b c d e f:
  S3 (3+(1+a*2)*2) (4+(1+b*2)*2) (1+c*2) (5+d*2) (1+(e*2+1)*2) (1+f) -->*
  S4 (5+(2+e+a)*2*2) (2+(2+b)*2*2) (5+(e+c)*2) (5+(e+d)*2) f.
Proof.
  follow Incs3.
  follow Ov3.
  finish.
Qed.

Definition S9 a b c d e :=
  0inf <| w^^a *> [0] *> w^^b *> [0] *> w^^c *> [0;0;1;1;0] *> w^^d *> [1;0] *> w^^e *> 0inf.

Lemma Ov3_1 a b c d f:
  S3 (3+a*2) (4+b*2) (1+c*2) (5+d*2) 1 (1+f) -->*
  S9 (11+a*2) (8+b*2) (5+c*2) (1+d*2) (f).
Proof.
  destruct (mod2 f); subst;
  pre;
  es' a b c d a0.
Qed.

Lemma Inc9 a b c d e:
  S9 (5+a*2) (2+b*2) (4+c) d e -->*
  S9 (9+a*2) (6+b*2) (c) d e.
Proof.
  pre.
  es' a b c d e.
Qed.

Lemma Incs9 n a b c d e:
  S9 (5+a*2) (2+b*2) (n*4+c) d e -->*
  S9 (5+(n*2+a)*2) (2+(n*2+b)*2) c d e.
Proof.
  gen a b c.
  induction n; intros.
  1: finish.
  follow (IHn a b (4+c)).
  follow (Inc9 (n*2+a) (n*2+b) c d e).
  finish.
Qed.

Lemma IncsOv3_1 a b c d e f:
  S3 (3+(1+a*2)*2) (4+(1+b*2)*2) (1+c*2) (5+d*2) (1+(e*2+0)*2) (1+f) -->*
  S9 (5+(2+e+a)*2*2) (2+(2+b)*2*2) 
    (5 + (e + c) * 2) (1 + (e + d) * 2) f.
Proof.
  follow Incs3.
  follow Ov3_1.
  finish.
Qed.

Lemma Inc4 a b c d e:
  S4 (5+a*2) (2+b*2) (4+c) d e -->*
  S4 (9+a*2) (6+b*2) (c) d e.
Proof.
  pre.
  es' a b c d e.
Qed.

Lemma Incs4 n a b c d e:
  S4 (5+a*2) (2+b*2) (n*4+c) d e -->*
  S4 (5+(n*2+a)*2) (2+(n*2+b)*2) c d e.
Proof.
  gen a b c.
  induction n; intros.
  1: finish.
  follow (IHn a b (4+c)).
  follow (Inc4 (n*2+a) (n*2+b) c d e).
  finish.
Qed.

Definition S5 a b c d :=
  0inf <| w^^a *> [0] *> w^^b *> [0] *> w^^c *> [0;0;1;1;0] *> w^^d *> 0inf.

Lemma Inc5 a b c d:
  S5 (5+a*2) (2+b*2) (4+c) d -->*
  S5 (9+a*2) (6+b*2) (c) d.
Proof.
  pre.
  es' a b c d.
Qed.

Lemma Incs5 n a b c d:
  S5 (5+a*2) (2+b*2) (n*4+c) d -->*
  S5 (5+(n*2+a)*2) (2+(n*2+b)*2) c d.
Proof.
  gen a b c.
  induction n; intros.
  1: finish.
  follow (IHn a b (4+c)).
  follow (Inc5 (n*2+a) (n*2+b) c d).
  finish.
Qed.

Lemma Ov4_3_2 a b d:
  S4 (5+a*2) (2+b*2) 3 (5+d*2) 2 -->*
  S5 9 6 (12+a*2) (4+(2+b*2)+(5+d*2)).
Proof.
  pre.
  es' a b d.
Qed.

Lemma Ov5 a b d:
  S5 (5+a*2) (2+b*2) 0 (3+d) -->+
  S1 9 (10+a*2) (11+b*2) (d).
Proof.
  destruct (mod2 d); subst;
  pre;
  es' a b a0.
Qed.

Lemma IncsOv5 a b c d:
  S5 (5+a*2*2) (2+b*2*2) (c*4+0) (3+d) -->+
  S1 (5+1*2*2) (2+(2+c+a)*2*2) ((2+c+b)*4+3) d.
Proof.
  follow Incs5.
  follow10 Ov5.
  finish.
Qed.

Lemma Ov4_1 a b d e:
  S4 (5+a*2) (2+b*2) 1 (5+d*2) (3+e) -->*
  S5 9 6 (8+a*2) (1+(2+b*2)+(5+d*2)+(3+e)).
Proof.
  destruct (mod2 e); subst;
  pre;
  es' a b d a0.
Qed.

Lemma Incs4Ov4_1 a b c d e:
  S4 (5+a*2*2) (2+b*2*2) (c*4+1) (5+d*2) (3+e) -->*
  S5 9 6 ((2+c+a)*2*2) (1+(2+c*4+b*4)+(5+d*2)+(3+e)).
Proof.
  follow Incs4.
  follow Ov4_1.
  finish.
Qed.

Lemma IncsOvs5_ex c d:
  S5 (5+1*2*2) (2+1*2*2) (c*4+0) (3+(1+(11+(1+d)))) -->+
  S4 (5 + (19 + c * 3) * 2 * 2) (2 + 3 * 2 * 2)
    (5 + (16 + c * 3) * 2)
    (5 + (26 + c * 5) * 2) d.
Proof.
  follow10 IncsOv5.
  follow IncsOv1.
  follow IncsOv2.
  replace (7 + (2 + c + 1 + 1) * 2 + 1 * 2 + (2 + c + 1 + (2 + c + 1) + 1) * 2)
  with ((15+c*3)*2+1) by lia.
  follow IncsOv3.
  finish.
Qed.

Lemma IncsOvs5_c0 c d:
  S5 9 6 ((0+c*2)*4+0) (19+d) -->+
  S5 9 6 (((30+c*9))*4+0) (19+(92+c*32+d)).
Proof.
  follow10 IncsOvs5_ex.
  replace (5 + (16 + (0 + c * 2) * 3) * 2) with
    ((9 + c * 3) * 4 + 1) by lia.
  follow Incs4Ov4_1.
  finish.
Qed.

Definition S6 a b c d e f :=
  0inf <| w^^a *> [0] *> w^^b *> [0] *> w^^c *> [0] *> w^^d *> [0] *> w^^e *> [0] *> w^^f *> 0inf.

Lemma Ov4_3 a b d e:
  S4 (5+a*2) (2+b*2) 3 (5+d*2) (9+e) -->*
  S6 9 6 (12+a*2) (6+(2+b*2)+(5+d*2)) 9 (e).
Proof.
  destruct (mod2 e); subst;
  pre;
  es' a b d a0.
Qed.

Lemma Incs4Ov4_3 a b c d e:
  S4 (5+a*2*2) (2+b*2*2) (c*4+3) (5+d*2) (9+e) -->*
  S6 (5+1*2*2) (2+1*2*2) ((3+c+a)*4+0) (1+(6+(c+b)*2+d)*2) 9 e.
Proof.
  follow Incs4.
  follow Ov4_3.
  finish.
Qed.

Lemma Inc6 a b c d e f:
  S6 (5+a*2) (2+b*2) (4+c) d e f -->*
  S6 (9+a*2) (6+b*2) (c) d e f.
Proof.
  pre.
  es' a b c d e f.
Qed.

Lemma Incs6 n a b c d e f:
  S6 (5+a*2) (2+b*2) (n*4+c) d e f -->*
  S6 (5+(n*2+a)*2) (2+(n*2+b)*2) c d e f.
Proof.
  gen a b c.
  induction n; intros.
  1: finish.
  follow (IHn a b (4+c)).
  follow (Inc6 (n*2+a) (n*2+b) c d e f).
  finish.
Qed.

Lemma Ov6_0_9 a b d f:
  S6 (5+a*2) (2+b*2) 0 (1+d*2) 9 (4+f) -->*
  S6 9 6 (3+a*2) ((2+b*2)+(1+d*2)) 13 (f).
Proof.
  destruct (mod2 f); subst;
  pre;
  es' a b d a0.
Qed.

Lemma IncsOv6_0_9 a b c d f:
  S6 (5+a*2*2) (2+b*2) (c*4+0) (1+d*2) 9 (4+f) -->*
  S6 (5+1*2*2) (2+1*2*2) ((c+a)*4+3) (1+(1+c*2+b+d)*2) 13 (f).
Proof.
  follow Incs6.
  follow Ov6_0_9.
  finish.
Qed.

Lemma Ov6_3_13 a b d f:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 13 (11+f) -->*
  S6 9 6 (31+a*2) (20+(2+b*2)+(1+d*2)) 9 (f).
Proof.
  destruct (mod2 f); subst;
  pre;
  es' a b d a0.
Qed.

Lemma IncsOv6_3_13 a b c d f:
  S6 (5+a*2*2) (2+b*2) (c*4+3) (1+d*2) 13 (11+f) -->*
  S6 9 6 ((7+c+a)*4+3) (1+(11+c*2+b+d)*2) 9 (f).
Proof.
  follow Incs6.
  follow Ov6_3_13.
  finish.
Qed.

Lemma IncsOvs5_c1 c d:
  S5 9 6 ((1+c*2)*4+0) (40+d) -->+
  S6 9 6 ((44+c*9)*4+3) (1+(221+c*52)*2) 9 d.
Proof.
  follow10 IncsOvs5_ex.
  replace (5 + (16 + (1 + c * 2) * 3) * 2) with
    ((10 + c * 3) * 4 + 3) by lia.
  follow Incs4Ov4_3.
  follow IncsOv6_0_9.
  follow IncsOv6_3_13.
  finish.
Qed.

Lemma Ov6_3_9 a b d f:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 (11+f) -->+
  S6 9 6 (27+a*2) (16+(2+b*2)+(1+d*2)) 9 (f).
Proof.
  destruct (mod2 f); subst;
  pre;
  es' a b d a0.
Qed.

Lemma IncsOv6_3_9 n d f:
  S6 9 6 (n*4+3) (1+d*2) 9 (11+f) -->+
  S6 9 6 ((7+n)*4+3) (1+(n*2+11+d)*2) 9 f.
Proof.
  follow (Incs6 n 2 2 3 (1+d*2) 9 (11+f)).
  follow10 (Ov6_3_9 (n*2+2) (n*2+2) d f).
  finish.
Qed.

Lemma Ov6_3_9_10 a b d:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 10 -->+
  S3 (3+(1+2*2)*2) (4+(1+1*2)*2) (1+1*2) (5+23*2) (121+a*2) (1+(6+(2+b*2)+(1+d*2))).
Proof.
  pre.
  es' a b d.
Qed.

Lemma Ov9_1 a b d e:
  S9 (5+a*2) (2+b*2) 1 (3+d*2) (1+e*2) -->*
  S2 9 6 (3+a*2) (4+(2+b*2)+(3+d*2)+(1+e*2)) 0.
Proof.
  pre.
  es' a b d e.
Qed.

Lemma Ov9_3 a b d e:
  S9 (5+a*2) (2+b*2) 3 (3+d*2) (1+e*2) -->*
  S5 9 6 (8+a*2) (3+(2+b*2)+(3+d*2)+(1+e*2)).
Proof.
  pre.
  es' a b d e.
Qed.

Lemma Ov2_0 a b d:
  S2 (5+a*2) (2+b*2) 3 (2+d*2) 0 -->*
  S5 9 6 (4+a*2) ((2+b*2)+(2+d*2)).
Proof.
  pre.
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_10_0 c d:
  S6 (5+1*2*2) (2+1*2*2) ((c*2)*4+3) (1+d*2) 9 10 -->+
  S5 (5+1*2*2) (2+1*2*2) ((c*3+54)*4+0) ((211+c*14+d)*2).
Proof.
  replace (c*2) with (c*2+0) by lia.
  follow Incs6.
  follow10 Ov6_3_9_10.
  replace (121 + ((c*2+0) * 2 + 1 * 2) * 2) with (1+((c*2+31)*2+0)*2) by lia.
  follow IncsOv3_1.
  replace (5 + (c * 2 + 31 + 1) * 2) with ((17+c)*4+1) by lia.
  replace (1 + (c * 2 + 31 + 23) * 2) with (3+(c*2+53)*2) by lia.
  replace (6 + (2 + ((c * 2 + 0) * 2 + 1 * 2) * 2) + (1 + d * 2)) with
    (1+(6+c*4+d)*2) by lia.
  follow Incs9.
  follow Ov9_1.
  mid (S2 (5+1*2*2) (2+1*2*2) ((c*3+52)*4+3) ((104+c*8+d)*2) 0).
  1: finish.
  follow Incs2.
  replace ((104+c*8+d)*2) with (2+(103+c*8+d)*2) by lia.
  follow Ov2_0.
  finish.
Qed.

Lemma IncsOvs6_3_9_10_1 c d:
  S6 (5+1*2*2) (2+1*2*2) ((1+c*2)*4+3) (1+d*2) 9 10 -->+
  S5 (5+1*2*2) (2+1*2*2) ((c*3+55)*4+0) (3+(105+c*8+d)*2).
Proof.
  rewrite (Nat.add_comm 1 (c*2)).
  follow Incs6.
  follow10 Ov6_3_9_10.
  replace (121 + ((c*2+1) * 2 + 1 * 2) * 2) with (1+((c*2+32)*2+0)*2) by lia.
  follow IncsOv3_1.
  replace (5 + (c * 2 + 32 + 1) * 2) with ((17+c)*4+3) by lia.
  replace (1 + (c * 2 + 32 + 23) * 2) with (3+(c*2+54)*2) by lia.
  replace (6 + (2 + ((c * 2 + 1) * 2 + 1 * 2) * 2) + (1 + d * 2)) with
    (1+(8+c*4+d)*2) by lia.
  follow Incs9.
  follow Ov9_3.
  finish.
Qed.

Lemma Ov6_3_9_9 a b d:
  S6 (5+a*2*2) (2+b*2) 3 (1+d*2) 9 9 -->+
  S2 (5+1*2*2) (2+(7+a)*2*2) (1+(12+b+d)*2) 4 0.
Proof.
  pre.
  es' a b d.
Qed.

Lemma Ov2_1_4 a b:
  S2 (5+a*2) (4+b*2) 1 4 0 -->*
  S2 37 (34+a*2) (2+b*2) 0 0.
Proof.
  pre.
  es' a b.
Qed.

Lemma Ov2_0_0 a b:
  S2 (5+a*2) (2+b*2) 0 0 0 -->*
  S2 9 (2+a*2) (2+b*2) 0 0.
Proof.
  pre.
  es' a b.
Qed.

Lemma Ov2_2_0 a b:
  S2 (5+a*2) (2+b*2) 2 0 0 -->*
  S5 9 6 (8+a*2) (b*2).
Proof.
  pre.
  es' a b.
Qed.

Lemma IncsOvs6_3_9_9_0 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+(d*2)*2) 9 9 -->+
  S5 (5+1*2*2) (2+1*2*2) ((34+c*3+d*2)*4+0) (3+(1+(53+c*5+d*3)*4)).
Proof.
  replace (d*2) with (d*2+0) by lia.
  follow Incs6.
  replace (c*2+1*2) with ((1+c)*2) by lia.
  follow10 Ov6_3_9_9.
  replace (1 + (12 + (1 + c) * 2 + (d * 2 + 0)) * 2) with
    ((7+c+d)*4+1) by lia.
  follow Incs2.
  follow Ov2_1_4.
  fold Nat.mul Nat.add.
  mid (S2 (5+8*2*2) (2+(16+c+d)*2*2) ((15+c*2+d)*4+0) 0 0).
  1: finish.
  follow Incs2.
  follow Ov2_0_0.
  mid (S2 (5+1*2*2) (2+(23+c*2+d)*2*2) ((31+c*3+d*2)*4+2) 0 0).
  1: finish.
  follow Incs2.
  follow Ov2_2_0.
  finish.
Qed.

Lemma Ov2_3_4 a b:
  S2 (5+a*2) (2+b*2) 3 4 0 -->*
  S5 9 6 (4+a*2) (6+b*2).
Proof.
  pre.
  es' a b.
Qed.

Lemma IncsOvs6_3_9_9_1 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+(1+d*2)*2) 9 9 -->+
  S5 (5+1*2*2) (2+1*2*2) ((9+c+d)*4+0) (2+(16+c*2+d)*4).
Proof.
  follow Incs6.
  replace (c*2+1*2) with ((1+c)*2) by lia.
  follow10 Ov6_3_9_9.
  replace (1 + (12 + (1 + c) * 2 + (1 + d * 2)) * 2) with
    ((7+c+d)*4+3) by lia.
  follow Incs2.
  follow Ov2_3_4.
  finish.
Qed.

Definition S7 a b c d e :=
  0inf <| w^^a *> [0] *> w^^b *> [0] *> w^^c *> [0;0;1;1;0] *> w^^d *> [0;0;1;1;0] *> w^^e *> 0inf.

Lemma Ov6_3_9_8 a b d:
  S6 (5+a*2*2) (2+b*2) 3 (1+d*2) 9 8 -->+
  S7 (5+1*2*2) (2+1*2*2) ((8+a)*4+0) ((10+b+d)*2) 0.
Proof.
  pre.
  es' a b d.
Qed.

Lemma Inc7 a b c d e:
  S7 (5+a*2) (2+b*2) (4+c) d e -->*
  S7 (9+a*2) (6+b*2) (c) d e.
Proof.
  pre.
  es' a b c d e.
Qed.

Lemma Incs7 n a b c d e:
  S7 (5+a*2) (2+b*2) (n*4+c) d e -->*
  S7 (5+(n*2+a)*2) (2+(n*2+b)*2) c d e.
Proof.
  gen a b c.
  induction n; intros.
  1: finish.
  follow (IHn a b (4+c)).
  follow (Inc7 (n*2+a) (n*2+b) c d).
  finish.
Qed.

Lemma Ov7_0_0 a b d:
  S7 (5+a*2) (2+b*2) 0 (2+d*2) 0 -->*
  S5 9 6 (8+a*2) (5+b*2+d*2).
Proof.
  pre.
  es' a b d.
Qed.

Lemma Ov7_0_5 a b d:
  S7 (5+a*2) (2+b*2) 0 (2+d*2) 5 -->*
  S5 9 6 (16+a*2) (6+(2+b*2)+(2+d*2)).
Proof.
  pre.
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_8 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+d*2) 9 8 -->+
  S5 9 6 ((12+c)*4+0) (67+c*8+d*2).
Proof.
  follow Incs6.
  replace (c*2+1*2) with ((1+c)*2) by lia.
  follow10 Ov6_3_9_8.
  follow Incs7.
  follow Ov7_0_0.
  fold Nat.add Nat.mul.
  finish.
Qed.

Lemma Ov6_3_9_7 a b d:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 7 -->+
  S5 9 6 (36+a*2) (18+(2+b*2)+(1+d*2)).
Proof.
  pre.
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_7 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+d*2) 9 7 -->+
  S5 9 6 ((10+c)*4+0) (25+c*4+d*2).
Proof.
  follow Incs6.
  follow10 Ov6_3_9_7.
  finish.
Qed.

Lemma Ov6_3_9_6 a b d:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 6 -->+
  S5 9 6 (28+a*2) (16+(2+b*2)+(1+d*2)).
Proof.
  pre.
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_6 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+d*2) 9 6 -->+
  S5 9 6 ((8+c)*4+0) (23+c*4+d*2).
Proof.
  follow Incs6.
  follow10 Ov6_3_9_6.
  finish.
Qed.

Lemma Ov6_3_9_5 a b d:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 5 -->+
  S5 9 6 (32+a*2) (16+(2+b*2)+(1+d*2)).
Proof.
  pre.
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_5 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+d*2) 9 5 -->+
  S5 9 6 ((9+c)*4+0) (23+c*4+d*2).
Proof.
  follow Incs6.
  follow10 Ov6_3_9_5.
  finish.
Qed.

Lemma Ov6_3_9_4 a b d:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 4 -->+
  S5 9 6 (28+a*2) (13+(2+b*2)+(1+d*2)).
Proof.
  pre.
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_4 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+d*2) 9 4 -->+
  S5 9 6 ((8+c)*4+0) (20+c*4+d*2).
Proof.
  follow Incs6.
  follow10 Ov6_3_9_4.
  finish.
Qed.

Definition S8 a b c d e :=
  0inf <| w^^a *> [0] *> w^^b *> [0] *> w^^c *> [0;0;1;1;0] *> w^^d *> [0] *> w^^e *> 0inf.

Lemma Inc8 a b c d e:
  S8 (5+a*2) (2+b*2) (4+c) d e -->*
  S8 (9+a*2) (6+b*2) (c) d e.
Proof.
  pre.
  es' a b c d e.
Qed.

Lemma Incs8 n a b c d e:
  S8 (5+a*2) (2+b*2) (n*4+c) d e -->*
  S8 (5+(n*2+a)*2) (2+(n*2+b)*2) c d e.
Proof.
  gen a b c.
  induction n; intros.
  1: finish.
  follow (IHn a b (4+c)).
  follow (Inc8 (n*2+a) (n*2+b) c d).
  finish.
Qed.

Lemma Ov6_3_9_3 a b d:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 3 -->+
  S8 9 6 (8+a*2) (2+(2+b*2)+(1+d*2)) 10.
Proof.
  pre.
  es' a b d.
Qed.

Lemma Ov8_0_10 a b d:
  S8 (5+a*2) (2+b*2) 0 (3+d*2) 10 -->*
  S5 9 6 (28+a*2) (13+(2+b*2)+(3+d*2)).
Proof.
  pre;
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_3 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+d*2) 9 3 -->+
  S5 9 6 ((11+c)*4+0) (40+c*8+d*2).
Proof.
  follow Incs6.
  follow10 Ov6_3_9_3.
  mid (S8 (5+1*2*2) (2+1*2*2) ((3+c)*4+0) (3+(3+c*2+d)*2) 10).
  1: finish.
  follow Incs8.
  follow Ov8_0_10.
  finish.
Qed.

Lemma Ov6_3_9_2 a b d:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 2 -->+
  S2 9 6 (7+a*2) (8+(2+b*2)+(1+d*2)) 8.
Proof.
  pre.
  es' a b d.
Qed.

Lemma Ov2_3_8 a b d:
  S2 (5+a*2) (2+b*2) 3 (1+d*2) 8 -->*
  S2 25 (30+a*2) (3+(2+b*2)+(1+d*2)) 0 0.
Proof.
  pre.
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_2_0 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+(d*2)*2) 9 2 -->+
  S5 9 6 ((21+c*3+d)*4+0) ((31+c*5+d*2)*4).
Proof.
  follow Incs6.
  follow10 Ov6_3_9_2.
  mid (S2 (5+1*2*2) (2+1*2*2) ((2+c)*4+3) (1+(7+c*2+d*2)*2) 8).
  1: finish.
  follow Incs2.
  follow Ov2_3_8.
  mid (S2 (5+5*2*2) (2+(10+c)*2*2) ((8+c*2+d)*4+0) 0 0).
  1: finish.
  follow Incs2.
  follow Ov2_0_0.
  mid (S2 (5+1*2*2) (2+(13+c*2+d)*2*2) ((18+c*3+d)*4+2) 0 0).
  1: finish.
  follow Incs2.
  follow Ov2_2_0.
  finish.
Qed.

Lemma IncsOvs6_3_9_2_1 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+(1+d*2)*2) 9 2 -->+
  S5 9 6 ((15+c*2+d)*4+0) ((18+c*3+d)*4).
Proof.
  follow Incs6.
  follow10 Ov6_3_9_2.
  mid (S2 (5+1*2*2) (2+1*2*2) ((2+c)*4+3) (1+(8+c*2+d*2)*2) 8).
  1: finish.
  follow Incs2.
  follow Ov2_3_8.
  mid (S2 (5+5*2*2) (2+(10+c)*2*2) ((8+c*2+d)*4+2) 0 0).
  1: finish.
  follow Incs2.
  follow Ov2_2_0.
  finish.
Qed.

Lemma Ov6_3_9_1 a b d:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 1 -->+
  S7 9 6 (8+a*2) (3+(2+b*2)+(1+d*2)) 5.
Proof.
  pre.
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_1 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+d*2) 9 1 -->+
  S5 9 6 ((8+c)*4+0) (34+c*8+d*2).
Proof.
  follow Incs6.
  follow10 Ov6_3_9_1.
  mid (S7 (5+1*2*2) (2+1*2*2) ((3+c)*4+0) (2+(4+c*2+d)*2) 5).
  1: finish.
  follow Incs7.
  follow Ov7_0_5.
  finish.
Qed.

Lemma Ov6_3_9_0 a b d:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 0 -->*
  S2 (5+a*2) (2+b*2) 3 (1+d*2) 9.
Proof.
  pre.
  es' a b d.
Qed.

Lemma Ov2_3_9 a b d:
  S2 (5+a*2) (2+b*2) 3 (1+d*2) 9 -->+
  S2 45 (58+a*2) (1+(2+b*2)+(1+d*2)) 0 0.
Proof.
  pre.
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_0_0 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+(d*2)*2) 9 0 -->+
  S5 9 6 ((20+c*2+d)*4+0) ((29+c*3+d*2)*4).
Proof.
  follow Incs6.
  follow Ov6_3_9_0.
  follow10 Ov2_3_9.
  mid (S2 (5+10*2*2) (2+(15+c)*2*2) ((2+c+d)*4+0) 0 0).
  1: finish.
  follow Incs2.
  follow Ov2_0_0.
  mid (S2 (5+1*2*2) (2+(12+c+d)*2*2) ((17+c*2+d)*4+2) 0 0).
  1: finish.
  follow Incs2.
  follow Ov2_2_0.
  finish.
Qed.

Lemma IncsOvs6_3_9_0_1 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+(1+d*2)*2) 9 0 -->+
  S5 9 6 ((14+c+d)*4+0) ((17+c*2+d)*4).
Proof.
  follow Incs6.
  follow Ov6_3_9_0.
  follow10 Ov2_3_9.
  mid (S2 (5+10*2*2) (2+(15+c)*2*2) ((2+c+d)*4+2) 0 0).
  1: finish.
  follow Incs2.
  follow Ov2_2_0.
  finish.
Qed.

Inductive Config :=
| cfg6 (c d f:nat)
| cfg5 (c d:nat)
.

Definition to_config x :=
match x with
| cfg6 c d f => S6 9 6 (c*4+3) (1+d*2) 9 f
| cfg5 c d => S5 9 6 (c*4+0) (20+d)
end.

Definition P x :=
match x with
| cfg6 c d f => c>=5
| cfg5 c d => d>=20
end.


Ltac eex a :=
  (eexists (a _ _) || eexists (a _ _ _));
  split; [|shelve];
  cbn[to_config].

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P.
  intros HP.
  destruct x; cbn[to_config].
  - destruct f.
    {
      destruct (mod2 d); subst.
      - eex cfg5; apply IncsOvs6_3_9_0_0.
      - eex cfg5; apply IncsOvs6_3_9_0_1.
    }
    destruct f.
    1: eex cfg5; apply IncsOvs6_3_9_1.
    destruct f.
    {
      destruct (mod2 d); subst.
      - eex cfg5; apply IncsOvs6_3_9_2_0.
      - eex cfg5; apply IncsOvs6_3_9_2_1.
    }
    destruct f.
    1: eex cfg5; apply IncsOvs6_3_9_3.
    destruct f.
    1: eex cfg5; apply IncsOvs6_3_9_4.
    destruct f.
    1: eex cfg5; apply IncsOvs6_3_9_5.
    destruct f.
    1: eex cfg5; apply IncsOvs6_3_9_6.
    destruct f.
    1: eex cfg5; apply IncsOvs6_3_9_7.
    destruct f.
    1: eex cfg5; apply IncsOvs6_3_9_8.
    destruct f.
    {
      destruct (mod2 d); subst.
      - eex cfg5; apply IncsOvs6_3_9_9_0.
      - eex cfg5; apply IncsOvs6_3_9_9_1.
    }
    destruct f.
    {
      destruct (mod2 c); subst.
      - eex cfg5; apply IncsOvs6_3_9_10_0.
      - eex cfg5; apply IncsOvs6_3_9_10_1.
    }
    eex cfg6; apply IncsOv6_3_9.
  - destruct (mod2 c); subst.
    + eex cfg5; apply IncsOvs5_c0.
    + replace d with (20+(d-20)) by lia.
      eex cfg6; apply IncsOvs5_c1.
  Unshelve.
  all: fold Nat.add Nat.mul; lia.
Qed.

Lemma init:
  c0 -->*
  to_config (cfg5 66 275).
Proof.
  stepn 2722398%N.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond.
  apply (fun i => closed i).
  unfold P; lia.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB0LB_0LC0RB_0RE1LD_1LA---_1RF0RF_0RA0LE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation w := [0;1].
Notation "l <| r" := (l <{{A}} [1;1;0] *> r) (at level 30).

Definition S1 a b c d :=
  0inf <| w^^a *> [0] *> w^^b *> [0] *> w^^c *> [1;0] *> w^^d *> 0inf.
Ltac pre := unfold_config; st.

Lemma Inc1 a b c d:
  S1 (5+a*2) (2+b*2) (4+c) d -->*
  S1 (9+a*2) (6+b*2) (c) d.
Proof.
  pre.
  es' a b c d.
Qed.

Lemma Incs1 n a b c d:
  S1 (5+a*2) (2+b*2) (n*4+c) d -->*
  S1 (5+(n*2+a)*2) (2+(n*2+b)*2) c d.
Proof.
  gen a b c.
  induction n; intros.
  1: finish.
  follow (IHn a b (4+c)).
  follow (Inc1 (n*2+a) (n*2+b) c d).
  finish.
Qed.

Definition S2 a b c d e :=
  0inf <| w^^a *> [0] *> w^^b *> [0] *> w^^c *> [0] *> w^^d *> [0] *> w^^e *> 0inf.

Lemma Inc2 a b c d e:
  S2 (5+a*2) (2+b*2) (4+c) d e -->*
  S2 (9+a*2) (6+b*2) (c) d e.
Proof.
  pre.
  es' a b c d e.
Qed.

Lemma Incs2 n a b c d e:
  S2 (5+a*2) (2+b*2) (n*4+c) d e -->*
  S2 (5+(n*2+a)*2) (2+(n*2+b)*2) c d e.
Proof.
  gen a b c.
  induction n; intros.
  1: finish.
  follow (IHn a b (4+c)).
  follow (Inc2 (n*2+a) (n*2+b) c d e).
  finish.
Qed.

Lemma Ov1 a b d:
  S1 (5+a*2) (2+b*2) 3 (1+d) -->*
  S2 9 6 (3+a*2) (5+b*2) (1+d).
Proof.
  destruct (mod2 d); subst;
  pre;
  es' a b a0.
Qed.

Lemma IncsOv1 a b c d:
  S1 (5+a*2*2) (2+b*2*2) (c*4+3) (1+d) -->*
  S2 (5+1*2*2) (2+1*2*2) ((c+a)*4+3) (1+(c+b+1)*2*2) (1+d).
Proof.
  follow Incs1.
  follow Ov1.
  finish.
Qed.

Definition S3 a b c d e f :=
  0inf <| w^^a *> [0;0;1;1;0] *> w^^b *> [0;0;1;1;0] *> w^^c *> [0] *> w^^d *> [0] *> w^^e *> [0] *> w^^f *> 0inf.

Lemma Ov2 a b d e:
  S2 (5+a*2) (2+b*2) 3 (1+d*2) (12+e) -->*
  S3 13 10 3 (7+a*2) (15+b*2+d*2) (e).
Proof.
  destruct (mod2 e); subst;
  pre;
  es' a b d a0.
Qed.

Lemma IncsOv2 a b c d e:
  S2 (5+a*2*2) (2+b*2*2) (c*4+3) (1+d*2) (12+e) -->*
  S3 (3+(1+2*2)*2) (4+(1+1*2)*2) (1+1*2) (5+(1+c*2+a*2)*2) (1+(7+c*2+b*2+d)*2) e.
Proof.
  follow Incs2.
  follow Ov2.
  finish.
Qed.

Lemma Inc3 a b c d e f:
  S3 (3+a*2) (4+b*2) (1+c*2) (5+d*2) (5+e*2) (f) -->*
  S3 (7+a*2) (4+b*2) (3+c*2) (7+d*2) (1+e*2) (f).
Proof.
  destruct (mod2 f); subst;
  pre;
  es' a b c d e a0.
Qed.

Lemma Incs3 n a b c d e f:
  S3 (3+a*2) (4+b*2) (1+c*2) (5+d*2) (1+(n*2+e)*2) f -->*
  S3 (3+(n*2+a)*2) (4+b*2) (1+(n+c)*2) (5+(n+d)*2) (1+e*2) f.
Proof.
  gen a b c d e.
  induction n; intros.
  1: finish.
  follow (IHn a b c d (2+e)).
  follow (Inc3 (n*2+a) b (n+c) (n+d) e f).
  finish.
Qed.

Definition S4 a b c d e :=
  0inf <| w^^a *> [0] *> w^^b *> [0] *> w^^c *> [0] *> w^^d *> [1;0] *> w^^e *> 0inf.

Lemma Ov3 a b c d f:
  S3 (3+a*2) (4+b*2) (1+c*2) (5+d*2) 3 (1+f) -->*
  S4 (11+a*2) (8+b*2) (5+c*2) (5+d*2) (f).
Proof.
  destruct (mod2 f); subst;
  pre;
  es' a b c d a0.
Qed.

Lemma IncsOv3 a b c d e f:
  S3 (3+(1+a*2)*2) (4+(1+b*2)*2) (1+c*2) (5+d*2) (1+(e*2+1)*2) (1+f) -->*
  S4 (5+(2+e+a)*2*2) (2+(2+b)*2*2) (5+(e+c)*2) (5+(e+d)*2) f.
Proof.
  follow Incs3.
  follow Ov3.
  finish.
Qed.

Definition S9 a b c d e :=
  0inf <| w^^a *> [0] *> w^^b *> [0] *> w^^c *> [0;0;1;1;0] *> w^^d *> [1;0] *> w^^e *> 0inf.

Lemma Ov3_1 a b c d f:
  S3 (3+a*2) (4+b*2) (1+c*2) (5+d*2) 1 (1+f) -->*
  S9 (11+a*2) (8+b*2) (5+c*2) (1+d*2) (f).
Proof.
  destruct (mod2 f); subst;
  pre;
  es' a b c d a0.
Qed.

Lemma Inc9 a b c d e:
  S9 (5+a*2) (2+b*2) (4+c) d e -->*
  S9 (9+a*2) (6+b*2) (c) d e.
Proof.
  pre.
  es' a b c d e.
Qed.

Lemma Incs9 n a b c d e:
  S9 (5+a*2) (2+b*2) (n*4+c) d e -->*
  S9 (5+(n*2+a)*2) (2+(n*2+b)*2) c d e.
Proof.
  gen a b c.
  induction n; intros.
  1: finish.
  follow (IHn a b (4+c)).
  follow (Inc9 (n*2+a) (n*2+b) c d e).
  finish.
Qed.

Lemma IncsOv3_1 a b c d e f:
  S3 (3+(1+a*2)*2) (4+(1+b*2)*2) (1+c*2) (5+d*2) (1+(e*2+0)*2) (1+f) -->*
  S9 (5+(2+e+a)*2*2) (2+(2+b)*2*2) 
    (5 + (e + c) * 2) (1 + (e + d) * 2) f.
Proof.
  follow Incs3.
  follow Ov3_1.
  finish.
Qed.

Lemma Inc4 a b c d e:
  S4 (5+a*2) (2+b*2) (4+c) d e -->*
  S4 (9+a*2) (6+b*2) (c) d e.
Proof.
  pre.
  es' a b c d e.
Qed.

Lemma Incs4 n a b c d e:
  S4 (5+a*2) (2+b*2) (n*4+c) d e -->*
  S4 (5+(n*2+a)*2) (2+(n*2+b)*2) c d e.
Proof.
  gen a b c.
  induction n; intros.
  1: finish.
  follow (IHn a b (4+c)).
  follow (Inc4 (n*2+a) (n*2+b) c d e).
  finish.
Qed.

Definition S5 a b c d :=
  0inf <| w^^a *> [0] *> w^^b *> [0] *> w^^c *> [0;0;1;1;0] *> w^^d *> 0inf.

Lemma Inc5 a b c d:
  S5 (5+a*2) (2+b*2) (4+c) d -->*
  S5 (9+a*2) (6+b*2) (c) d.
Proof.
  pre.
  es' a b c d.
Qed.

Lemma Incs5 n a b c d:
  S5 (5+a*2) (2+b*2) (n*4+c) d -->*
  S5 (5+(n*2+a)*2) (2+(n*2+b)*2) c d.
Proof.
  gen a b c.
  induction n; intros.
  1: finish.
  follow (IHn a b (4+c)).
  follow (Inc5 (n*2+a) (n*2+b) c d).
  finish.
Qed.

Lemma Ov4_3_2 a b d:
  S4 (5+a*2) (2+b*2) 3 (5+d*2) 2 -->*
  S5 9 6 (12+a*2) (4+(2+b*2)+(5+d*2)).
Proof.
  pre.
  es' a b d.
Qed.

Lemma Ov5 a b d:
  S5 (5+a*2) (2+b*2) 0 (3+d) -->+
  S1 9 (10+a*2) (11+b*2) (d).
Proof.
  destruct (mod2 d); subst;
  pre;
  es' a b a0.
Qed.

Lemma IncsOv5 a b c d:
  S5 (5+a*2*2) (2+b*2*2) (c*4+0) (3+d) -->+
  S1 (5+1*2*2) (2+(2+c+a)*2*2) ((2+c+b)*4+3) d.
Proof.
  follow Incs5.
  follow10 Ov5.
  finish.
Qed.

Lemma Ov4_1 a b d e:
  S4 (5+a*2) (2+b*2) 1 (5+d*2) (3+e) -->*
  S5 9 6 (8+a*2) (1+(2+b*2)+(5+d*2)+(3+e)).
Proof.
  destruct (mod2 e); subst;
  pre;
  es' a b d a0.
Qed.

Lemma Incs4Ov4_1 a b c d e:
  S4 (5+a*2*2) (2+b*2*2) (c*4+1) (5+d*2) (3+e) -->*
  S5 9 6 ((2+c+a)*2*2) (1+(2+c*4+b*4)+(5+d*2)+(3+e)).
Proof.
  follow Incs4.
  follow Ov4_1.
  finish.
Qed.

Lemma IncsOvs5_ex c d:
  S5 (5+1*2*2) (2+1*2*2) (c*4+0) (3+(1+(11+(1+d)))) -->+
  S4 (5 + (19 + c * 3) * 2 * 2) (2 + 3 * 2 * 2)
    (5 + (16 + c * 3) * 2)
    (5 + (26 + c * 5) * 2) d.
Proof.
  follow10 IncsOv5.
  follow IncsOv1.
  follow IncsOv2.
  replace (7 + (2 + c + 1 + 1) * 2 + 1 * 2 + (2 + c + 1 + (2 + c + 1) + 1) * 2)
  with ((15+c*3)*2+1) by lia.
  follow IncsOv3.
  finish.
Qed.

Lemma IncsOvs5_c0 c d:
  S5 9 6 ((0+c*2)*4+0) (19+d) -->+
  S5 9 6 (((30+c*9))*4+0) (19+(92+c*32+d)).
Proof.
  follow10 IncsOvs5_ex.
  replace (5 + (16 + (0 + c * 2) * 3) * 2) with
    ((9 + c * 3) * 4 + 1) by lia.
  follow Incs4Ov4_1.
  finish.
Qed.

Definition S6 a b c d e f :=
  0inf <| w^^a *> [0] *> w^^b *> [0] *> w^^c *> [0] *> w^^d *> [0] *> w^^e *> [0] *> w^^f *> 0inf.

Lemma Ov4_3 a b d e:
  S4 (5+a*2) (2+b*2) 3 (5+d*2) (9+e) -->*
  S6 9 6 (12+a*2) (6+(2+b*2)+(5+d*2)) 9 (e).
Proof.
  destruct (mod2 e); subst;
  pre;
  es' a b d a0.
Qed.

Lemma Incs4Ov4_3 a b c d e:
  S4 (5+a*2*2) (2+b*2*2) (c*4+3) (5+d*2) (9+e) -->*
  S6 (5+1*2*2) (2+1*2*2) ((3+c+a)*4+0) (1+(6+(c+b)*2+d)*2) 9 e.
Proof.
  follow Incs4.
  follow Ov4_3.
  finish.
Qed.

Lemma Inc6 a b c d e f:
  S6 (5+a*2) (2+b*2) (4+c) d e f -->*
  S6 (9+a*2) (6+b*2) (c) d e f.
Proof.
  pre.
  es' a b c d e f.
Qed.

Lemma Incs6 n a b c d e f:
  S6 (5+a*2) (2+b*2) (n*4+c) d e f -->*
  S6 (5+(n*2+a)*2) (2+(n*2+b)*2) c d e f.
Proof.
  gen a b c.
  induction n; intros.
  1: finish.
  follow (IHn a b (4+c)).
  follow (Inc6 (n*2+a) (n*2+b) c d e f).
  finish.
Qed.

Lemma Ov6_0_9 a b d f:
  S6 (5+a*2) (2+b*2) 0 (1+d*2) 9 (4+f) -->*
  S6 9 6 (3+a*2) ((2+b*2)+(1+d*2)) 13 (f).
Proof.
  destruct (mod2 f); subst;
  pre;
  es' a b d a0.
Qed.

Lemma IncsOv6_0_9 a b c d f:
  S6 (5+a*2*2) (2+b*2) (c*4+0) (1+d*2) 9 (4+f) -->*
  S6 (5+1*2*2) (2+1*2*2) ((c+a)*4+3) (1+(1+c*2+b+d)*2) 13 (f).
Proof.
  follow Incs6.
  follow Ov6_0_9.
  finish.
Qed.

Lemma Ov6_3_13 a b d f:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 13 (11+f) -->*
  S6 9 6 (31+a*2) (20+(2+b*2)+(1+d*2)) 9 (f).
Proof.
  destruct (mod2 f); subst;
  pre;
  es' a b d a0.
Qed.

Lemma IncsOv6_3_13 a b c d f:
  S6 (5+a*2*2) (2+b*2) (c*4+3) (1+d*2) 13 (11+f) -->*
  S6 9 6 ((7+c+a)*4+3) (1+(11+c*2+b+d)*2) 9 (f).
Proof.
  follow Incs6.
  follow Ov6_3_13.
  finish.
Qed.

Lemma IncsOvs5_c1 c d:
  S5 9 6 ((1+c*2)*4+0) (40+d) -->+
  S6 9 6 ((44+c*9)*4+3) (1+(221+c*52)*2) 9 d.
Proof.
  follow10 IncsOvs5_ex.
  replace (5 + (16 + (1 + c * 2) * 3) * 2) with
    ((10 + c * 3) * 4 + 3) by lia.
  follow Incs4Ov4_3.
  follow IncsOv6_0_9.
  follow IncsOv6_3_13.
  finish.
Qed.

Lemma Ov6_3_9 a b d f:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 (11+f) -->+
  S6 9 6 (27+a*2) (16+(2+b*2)+(1+d*2)) 9 (f).
Proof.
  destruct (mod2 f); subst;
  pre;
  es' a b d a0.
Qed.

Lemma IncsOv6_3_9 n d f:
  S6 9 6 (n*4+3) (1+d*2) 9 (11+f) -->+
  S6 9 6 ((7+n)*4+3) (1+(n*2+11+d)*2) 9 f.
Proof.
  follow (Incs6 n 2 2 3 (1+d*2) 9 (11+f)).
  follow10 (Ov6_3_9 (n*2+2) (n*2+2) d f).
  finish.
Qed.

Lemma Ov6_3_9_10 a b d:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 10 -->+
  S3 (3+(1+2*2)*2) (4+(1+1*2)*2) (1+1*2) (5+23*2) (121+a*2) (1+(6+(2+b*2)+(1+d*2))).
Proof.
  pre.
  es' a b d.
Qed.

Lemma Ov9_1 a b d e:
  S9 (5+a*2) (2+b*2) 1 (3+d*2) (1+e*2) -->*
  S2 9 6 (3+a*2) (4+(2+b*2)+(3+d*2)+(1+e*2)) 0.
Proof.
  pre.
  es' a b d e.
Qed.

Lemma Ov9_3 a b d e:
  S9 (5+a*2) (2+b*2) 3 (3+d*2) (1+e*2) -->*
  S5 9 6 (8+a*2) (3+(2+b*2)+(3+d*2)+(1+e*2)).
Proof.
  pre.
  es' a b d e.
Qed.

Lemma Ov2_0 a b d:
  S2 (5+a*2) (2+b*2) 3 (2+d*2) 0 -->*
  S5 9 6 (4+a*2) ((2+b*2)+(2+d*2)).
Proof.
  pre.
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_10_0 c d:
  S6 (5+1*2*2) (2+1*2*2) ((c*2)*4+3) (1+d*2) 9 10 -->+
  S5 (5+1*2*2) (2+1*2*2) ((c*3+54)*4+0) ((211+c*14+d)*2).
Proof.
  replace (c*2) with (c*2+0) by lia.
  follow Incs6.
  follow10 Ov6_3_9_10.
  replace (121 + ((c*2+0) * 2 + 1 * 2) * 2) with (1+((c*2+31)*2+0)*2) by lia.
  follow IncsOv3_1.
  replace (5 + (c * 2 + 31 + 1) * 2) with ((17+c)*4+1) by lia.
  replace (1 + (c * 2 + 31 + 23) * 2) with (3+(c*2+53)*2) by lia.
  replace (6 + (2 + ((c * 2 + 0) * 2 + 1 * 2) * 2) + (1 + d * 2)) with
    (1+(6+c*4+d)*2) by lia.
  follow Incs9.
  follow Ov9_1.
  mid (S2 (5+1*2*2) (2+1*2*2) ((c*3+52)*4+3) ((104+c*8+d)*2) 0).
  1: finish.
  follow Incs2.
  replace ((104+c*8+d)*2) with (2+(103+c*8+d)*2) by lia.
  follow Ov2_0.
  finish.
Qed.

Lemma IncsOvs6_3_9_10_1 c d:
  S6 (5+1*2*2) (2+1*2*2) ((1+c*2)*4+3) (1+d*2) 9 10 -->+
  S5 (5+1*2*2) (2+1*2*2) ((c*3+55)*4+0) (3+(105+c*8+d)*2).
Proof.
  rewrite (Nat.add_comm 1 (c*2)).
  follow Incs6.
  follow10 Ov6_3_9_10.
  replace (121 + ((c*2+1) * 2 + 1 * 2) * 2) with (1+((c*2+32)*2+0)*2) by lia.
  follow IncsOv3_1.
  replace (5 + (c * 2 + 32 + 1) * 2) with ((17+c)*4+3) by lia.
  replace (1 + (c * 2 + 32 + 23) * 2) with (3+(c*2+54)*2) by lia.
  replace (6 + (2 + ((c * 2 + 1) * 2 + 1 * 2) * 2) + (1 + d * 2)) with
    (1+(8+c*4+d)*2) by lia.
  follow Incs9.
  follow Ov9_3.
  finish.
Qed.

Lemma Ov6_3_9_9 a b d:
  S6 (5+a*2*2) (2+b*2) 3 (1+d*2) 9 9 -->+
  S2 (5+1*2*2) (2+(7+a)*2*2) (1+(12+b+d)*2) 4 0.
Proof.
  pre.
  es' a b d.
Qed.

Lemma Ov2_1_4 a b:
  S2 (5+a*2) (4+b*2) 1 4 0 -->*
  S2 37 (34+a*2) (2+b*2) 0 0.
Proof.
  pre.
  es' a b.
Qed.

Lemma Ov2_0_0 a b:
  S2 (5+a*2) (2+b*2) 0 0 0 -->*
  S2 9 (2+a*2) (2+b*2) 0 0.
Proof.
  pre.
  es' a b.
Qed.

Lemma Ov2_2_0 a b:
  S2 (5+a*2) (2+b*2) 2 0 0 -->*
  S5 9 6 (8+a*2) (b*2).
Proof.
  pre.
  es' a b.
Qed.

Lemma IncsOvs6_3_9_9_0 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+(d*2)*2) 9 9 -->+
  S5 (5+1*2*2) (2+1*2*2) ((34+c*3+d*2)*4+0) (3+(1+(53+c*5+d*3)*4)).
Proof.
  replace (d*2) with (d*2+0) by lia.
  follow Incs6.
  replace (c*2+1*2) with ((1+c)*2) by lia.
  follow10 Ov6_3_9_9.
  replace (1 + (12 + (1 + c) * 2 + (d * 2 + 0)) * 2) with
    ((7+c+d)*4+1) by lia.
  follow Incs2.
  follow Ov2_1_4.
  fold Nat.mul Nat.add.
  mid (S2 (5+8*2*2) (2+(16+c+d)*2*2) ((15+c*2+d)*4+0) 0 0).
  1: finish.
  follow Incs2.
  follow Ov2_0_0.
  mid (S2 (5+1*2*2) (2+(23+c*2+d)*2*2) ((31+c*3+d*2)*4+2) 0 0).
  1: finish.
  follow Incs2.
  follow Ov2_2_0.
  finish.
Qed.

Lemma Ov2_3_4 a b:
  S2 (5+a*2) (2+b*2) 3 4 0 -->*
  S5 9 6 (4+a*2) (6+b*2).
Proof.
  pre.
  es' a b.
Qed.

Lemma IncsOvs6_3_9_9_1 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+(1+d*2)*2) 9 9 -->+
  S5 (5+1*2*2) (2+1*2*2) ((9+c+d)*4+0) (2+(16+c*2+d)*4).
Proof.
  follow Incs6.
  replace (c*2+1*2) with ((1+c)*2) by lia.
  follow10 Ov6_3_9_9.
  replace (1 + (12 + (1 + c) * 2 + (1 + d * 2)) * 2) with
    ((7+c+d)*4+3) by lia.
  follow Incs2.
  follow Ov2_3_4.
  finish.
Qed.

Definition S7 a b c d e :=
  0inf <| w^^a *> [0] *> w^^b *> [0] *> w^^c *> [0;0;1;1;0] *> w^^d *> [0;0;1;1;0] *> w^^e *> 0inf.

Lemma Ov6_3_9_8 a b d:
  S6 (5+a*2*2) (2+b*2) 3 (1+d*2) 9 8 -->+
  S7 (5+1*2*2) (2+1*2*2) ((8+a)*4+0) ((10+b+d)*2) 0.
Proof.
  pre.
  es' a b d.
Qed.

Lemma Inc7 a b c d e:
  S7 (5+a*2) (2+b*2) (4+c) d e -->*
  S7 (9+a*2) (6+b*2) (c) d e.
Proof.
  pre.
  es' a b c d e.
Qed.

Lemma Incs7 n a b c d e:
  S7 (5+a*2) (2+b*2) (n*4+c) d e -->*
  S7 (5+(n*2+a)*2) (2+(n*2+b)*2) c d e.
Proof.
  gen a b c.
  induction n; intros.
  1: finish.
  follow (IHn a b (4+c)).
  follow (Inc7 (n*2+a) (n*2+b) c d).
  finish.
Qed.

Lemma Ov7_0_0 a b d:
  S7 (5+a*2) (2+b*2) 0 (2+d*2) 0 -->*
  S5 9 6 (8+a*2) (5+b*2+d*2).
Proof.
  pre.
  es' a b d.
Qed.

Lemma Ov7_0_5 a b d:
  S7 (5+a*2) (2+b*2) 0 (2+d*2) 5 -->*
  S5 9 6 (16+a*2) (6+(2+b*2)+(2+d*2)).
Proof.
  pre.
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_8 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+d*2) 9 8 -->+
  S5 9 6 ((12+c)*4+0) (67+c*8+d*2).
Proof.
  follow Incs6.
  replace (c*2+1*2) with ((1+c)*2) by lia.
  follow10 Ov6_3_9_8.
  follow Incs7.
  follow Ov7_0_0.
  fold Nat.add Nat.mul.
  finish.
Qed.

Lemma Ov6_3_9_7 a b d:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 7 -->+
  S5 9 6 (36+a*2) (18+(2+b*2)+(1+d*2)).
Proof.
  pre.
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_7 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+d*2) 9 7 -->+
  S5 9 6 ((10+c)*4+0) (25+c*4+d*2).
Proof.
  follow Incs6.
  follow10 Ov6_3_9_7.
  finish.
Qed.

Lemma Ov6_3_9_6 a b d:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 6 -->+
  S5 9 6 (28+a*2) (16+(2+b*2)+(1+d*2)).
Proof.
  pre.
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_6 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+d*2) 9 6 -->+
  S5 9 6 ((8+c)*4+0) (23+c*4+d*2).
Proof.
  follow Incs6.
  follow10 Ov6_3_9_6.
  finish.
Qed.

Lemma Ov6_3_9_5 a b d:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 5 -->+
  S5 9 6 (32+a*2) (16+(2+b*2)+(1+d*2)).
Proof.
  pre.
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_5 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+d*2) 9 5 -->+
  S5 9 6 ((9+c)*4+0) (23+c*4+d*2).
Proof.
  follow Incs6.
  follow10 Ov6_3_9_5.
  finish.
Qed.

Lemma Ov6_3_9_4 a b d:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 4 -->+
  S5 9 6 (28+a*2) (13+(2+b*2)+(1+d*2)).
Proof.
  pre.
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_4 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+d*2) 9 4 -->+
  S5 9 6 ((8+c)*4+0) (20+c*4+d*2).
Proof.
  follow Incs6.
  follow10 Ov6_3_9_4.
  finish.
Qed.

Definition S8 a b c d e :=
  0inf <| w^^a *> [0] *> w^^b *> [0] *> w^^c *> [0;0;1;1;0] *> w^^d *> [0] *> w^^e *> 0inf.

Lemma Inc8 a b c d e:
  S8 (5+a*2) (2+b*2) (4+c) d e -->*
  S8 (9+a*2) (6+b*2) (c) d e.
Proof.
  pre.
  es' a b c d e.
Qed.

Lemma Incs8 n a b c d e:
  S8 (5+a*2) (2+b*2) (n*4+c) d e -->*
  S8 (5+(n*2+a)*2) (2+(n*2+b)*2) c d e.
Proof.
  gen a b c.
  induction n; intros.
  1: finish.
  follow (IHn a b (4+c)).
  follow (Inc8 (n*2+a) (n*2+b) c d).
  finish.
Qed.

Lemma Ov6_3_9_3 a b d:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 3 -->+
  S8 9 6 (8+a*2) (2+(2+b*2)+(1+d*2)) 10.
Proof.
  pre.
  es' a b d.
Qed.

Lemma Ov8_0_10 a b d:
  S8 (5+a*2) (2+b*2) 0 (3+d*2) 10 -->*
  S5 9 6 (28+a*2) (13+(2+b*2)+(3+d*2)).
Proof.
  pre;
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_3 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+d*2) 9 3 -->+
  S5 9 6 ((11+c)*4+0) (40+c*8+d*2).
Proof.
  follow Incs6.
  follow10 Ov6_3_9_3.
  mid (S8 (5+1*2*2) (2+1*2*2) ((3+c)*4+0) (3+(3+c*2+d)*2) 10).
  1: finish.
  follow Incs8.
  follow Ov8_0_10.
  finish.
Qed.

Lemma Ov6_3_9_2 a b d:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 2 -->+
  S2 9 6 (7+a*2) (8+(2+b*2)+(1+d*2)) 8.
Proof.
  pre.
  es' a b d.
Qed.

Lemma Ov2_3_8 a b d:
  S2 (5+a*2) (2+b*2) 3 (1+d*2) 8 -->*
  S2 25 (30+a*2) (3+(2+b*2)+(1+d*2)) 0 0.
Proof.
  pre.
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_2_0 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+(d*2)*2) 9 2 -->+
  S5 9 6 ((21+c*3+d)*4+0) ((31+c*5+d*2)*4).
Proof.
  follow Incs6.
  follow10 Ov6_3_9_2.
  mid (S2 (5+1*2*2) (2+1*2*2) ((2+c)*4+3) (1+(7+c*2+d*2)*2) 8).
  1: finish.
  follow Incs2.
  follow Ov2_3_8.
  mid (S2 (5+5*2*2) (2+(10+c)*2*2) ((8+c*2+d)*4+0) 0 0).
  1: finish.
  follow Incs2.
  follow Ov2_0_0.
  mid (S2 (5+1*2*2) (2+(13+c*2+d)*2*2) ((18+c*3+d)*4+2) 0 0).
  1: finish.
  follow Incs2.
  follow Ov2_2_0.
  finish.
Qed.

Lemma IncsOvs6_3_9_2_1 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+(1+d*2)*2) 9 2 -->+
  S5 9 6 ((15+c*2+d)*4+0) ((18+c*3+d)*4).
Proof.
  follow Incs6.
  follow10 Ov6_3_9_2.
  mid (S2 (5+1*2*2) (2+1*2*2) ((2+c)*4+3) (1+(8+c*2+d*2)*2) 8).
  1: finish.
  follow Incs2.
  follow Ov2_3_8.
  mid (S2 (5+5*2*2) (2+(10+c)*2*2) ((8+c*2+d)*4+2) 0 0).
  1: finish.
  follow Incs2.
  follow Ov2_2_0.
  finish.
Qed.

Lemma Ov6_3_9_1 a b d:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 1 -->+
  S7 9 6 (8+a*2) (3+(2+b*2)+(1+d*2)) 5.
Proof.
  pre.
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_1 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+d*2) 9 1 -->+
  S5 9 6 ((8+c)*4+0) (34+c*8+d*2).
Proof.
  follow Incs6.
  follow10 Ov6_3_9_1.
  mid (S7 (5+1*2*2) (2+1*2*2) ((3+c)*4+0) (2+(4+c*2+d)*2) 5).
  1: finish.
  follow Incs7.
  follow Ov7_0_5.
  finish.
Qed.

Lemma Ov6_3_9_0 a b d:
  S6 (5+a*2) (2+b*2) 3 (1+d*2) 9 0 -->*
  S2 (5+a*2) (2+b*2) 3 (1+d*2) 9.
Proof.
  pre.
  es' a b d.
Qed.

Lemma Ov2_3_9 a b d:
  S2 (5+a*2) (2+b*2) 3 (1+d*2) 9 -->+
  S2 45 (58+a*2) (1+(2+b*2)+(1+d*2)) 0 0.
Proof.
  pre.
  es' a b d.
Qed.

Lemma IncsOvs6_3_9_0_0 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+(d*2)*2) 9 0 -->+
  S5 9 6 ((20+c*2+d)*4+0) ((29+c*3+d*2)*4).
Proof.
  follow Incs6.
  follow Ov6_3_9_0.
  follow10 Ov2_3_9.
  mid (S2 (5+10*2*2) (2+(15+c)*2*2) ((2+c+d)*4+0) 0 0).
  1: finish.
  follow Incs2.
  follow Ov2_0_0.
  mid (S2 (5+1*2*2) (2+(12+c+d)*2*2) ((17+c*2+d)*4+2) 0 0).
  1: finish.
  follow Incs2.
  follow Ov2_2_0.
  finish.
Qed.

Lemma IncsOvs6_3_9_0_1 c d:
  S6 (5+1*2*2) (2+1*2*2) (c*4+3) (1+(1+d*2)*2) 9 0 -->+
  S5 9 6 ((14+c+d)*4+0) ((17+c*2+d)*4).
Proof.
  follow Incs6.
  follow Ov6_3_9_0.
  follow10 Ov2_3_9.
  mid (S2 (5+10*2*2) (2+(15+c)*2*2) ((2+c+d)*4+2) 0 0).
  1: finish.
  follow Incs2.
  follow Ov2_2_0.
  finish.
Qed.

Inductive Config :=
| cfg6 (c d f:nat)
| cfg5 (c d:nat)
.

Definition to_config x :=
match x with
| cfg6 c d f => S6 9 6 (c*4+3) (1+d*2) 9 f
| cfg5 c d => S5 9 6 (c*4+0) (20+d)
end.

Definition P x :=
match x with
| cfg6 c d f => c>=5
| cfg5 c d => d>=20
end.


Ltac eex a :=
  (eexists (a _ _) || eexists (a _ _ _));
  split; [|shelve];
  cbn[to_config].

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P.
  intros HP.
  destruct x; cbn[to_config].
  - destruct f.
    {
      destruct (mod2 d); subst.
      - eex cfg5; apply IncsOvs6_3_9_0_0.
      - eex cfg5; apply IncsOvs6_3_9_0_1.
    }
    destruct f.
    1: eex cfg5; apply IncsOvs6_3_9_1.
    destruct f.
    {
      destruct (mod2 d); subst.
      - eex cfg5; apply IncsOvs6_3_9_2_0.
      - eex cfg5; apply IncsOvs6_3_9_2_1.
    }
    destruct f.
    1: eex cfg5; apply IncsOvs6_3_9_3.
    destruct f.
    1: eex cfg5; apply IncsOvs6_3_9_4.
    destruct f.
    1: eex cfg5; apply IncsOvs6_3_9_5.
    destruct f.
    1: eex cfg5; apply IncsOvs6_3_9_6.
    destruct f.
    1: eex cfg5; apply IncsOvs6_3_9_7.
    destruct f.
    1: eex cfg5; apply IncsOvs6_3_9_8.
    destruct f.
    {
      destruct (mod2 d); subst.
      - eex cfg5; apply IncsOvs6_3_9_9_0.
      - eex cfg5; apply IncsOvs6_3_9_9_1.
    }
    destruct f.
    {
      destruct (mod2 c); subst.
      - eex cfg5; apply IncsOvs6_3_9_10_0.
      - eex cfg5; apply IncsOvs6_3_9_10_1.
    }
    eex cfg6; apply IncsOv6_3_9.
  - destruct (mod2 c); subst.
    + eex cfg5; apply IncsOvs5_c0.
    + replace d with (20+(d-20)) by lia.
      eex cfg6; apply IncsOvs5_c1.
  Unshelve.
  all: fold Nat.add Nat.mul; lia.
Qed.

Lemma init:
  c0 -->*
  to_config (cfg5 38 283).
Proof.
  stepn 1521986%N.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond.
  apply (fun i => closed i).
  unfold P; lia.
Qed.

End TM3.

