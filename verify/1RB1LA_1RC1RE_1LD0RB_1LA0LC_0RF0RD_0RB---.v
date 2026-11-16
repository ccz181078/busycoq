From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Ltac flia := repeat (lia||f_equal).

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* <[1]^^(1+a*2) <{{C}} [0;1]^^b *> [1]^^(c*2) *> [0;1] *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (2+c) -->*
  S1 a (3+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n*2+c) -->*
  S1 a (n*3+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma LOv1 b c:
  S1 0 b (3+c) -->*
  S1 (2+b) 2 c.
Proof.
  es.
Qed.

Definition S2 a b :=
  0inf <* <[1]^^(1+a*2) <{{C}} [0;1]^^b *> [1] *> 0inf.

Lemma Inc2 a b:
  S2 (1+a) b -->*
  S2 a (3+b).
Proof.
  es.
Qed.

Lemma Incs2 a b:
  S2 a b -->*
  S2 0 (a*3+b).
Proof.
  gen b.
  ind a Inc2.
Qed.

Definition S3 a b :=
  0inf <* <[1]^^(1+a*2) <{{C}} [0;1]^^b *> 0inf.

Lemma Ov2 b:
  S2 0 b -->*
  S3 (2+b) 1.
Proof.
  es.
Qed.

Lemma Inc3 a b:
  S3 (1+a) b -->*
  S3 a (2+b).
Proof.
  es.
Qed.

Lemma Incs3 a b:
  S3 a b -->*
  S3 0 (a*2+b).
Proof.
  gen b.
  ind a Inc3.
Qed.

Lemma Ov3 b:
  S3 0 b -->*
  S1 0 2 (2+b).
Proof.
  es.
Qed.

Lemma IncsOv3 a b:
  S3 a b -->*
  S1 0 2 (2+a*2+b).
Proof.
  follow Incs3.
  follow Ov3.
  finish.
Qed.

Lemma IncsOv2 a b:
  S2 a b -->*
  S1 0 2 (7+a*6+b*2).
Proof.
  follow Incs2.
  follow Ov2.
  follow IncsOv3.
  finish.
Qed.

Lemma ROv1_1 a b:
  S1 (2+a) b 1 -->*
  S1 0 2 (19+a*6+b*2).
Proof.
  mid (S2 a (6+b)).
  1: es.
  follow IncsOv2.
  finish.
Qed.

Lemma ROv1_1_0 b:
  halts tm (S1 0 b 1).
Proof.
  esx.
Qed.

Lemma ROv1_0 a b:
  S1 a b 0 -->*
  S1 0 2 (3+a*2+b).
Proof.
  mid (S3 a (1+b)).
  1: es.
  follow IncsOv3.
  finish.
Qed.

Definition P n1 n2 :=
  forall c,
  S1 0 2 (n1+c) -->*
  S1 n2 2 c.

Lemma P_O:
  P 0 0.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S n1 n2:
  P n1 n2 ->
  P (n1+n2*2+3) (4+n2*3).
Proof.
  unfold P; intros HP c.
  follow (HP (n2*2+(3+(c)))).
  follow (Incs1 n2 0 2 (3+(c))).
  follow LOv1.
  finish.
Qed.

Lemma pow3_ge i:
  3^i>=i+1.
Proof.
  induction i; cbn[Nat.pow]; lia.
Qed.

Lemma P_n i:
  P (3^i*2-i-2) (3^i*2-2).
Proof.
  induction i.
  1: apply P_O.
  apply P_S in IHi.
  cbn[Nat.pow].
  pose proof (pow3_ge i).
  applys_eq IHi; flia.
Qed.

Definition S' n := S1 0 2 n.

Lemma BigStep1 n1 n2 c:
  P n1 (c+(2+n2)) ->
  S' (n1+c*2+1) -->*
  S' (23+n2*6+c*6).
Proof.
  unfold S',P; intros HP.
  follow (HP (c*2+1)).
  follow Incs1.
  follow ROv1_1.
  finish.
Qed.

Lemma BigStep0 n1 n2 c:
  P n1 (c+n2) ->
  S' (n1+c*2+0) -->*
  S' (5+n2*2+c*3).
Proof.
  unfold S',P; intros HP.
  follow (HP (c*2+0)).
  follow Incs1.
  follow ROv1_0.
  finish.
Qed.

Lemma init:
  c0 -->*
  S' 18.
Proof.
  unfold S',S1.
  esx.
Qed.

Close Scope sym.

Lemma BigStep0' i n:
  3^i*2-i-2 <= n <= 3^i*6-i-6 ->
  n mod 2 = i mod 2 ->
  S' n -->*
  S' ((n+(3^i*6+i+4))/2).
Proof.
  intros.
  pose proof (pow3_ge i).
  pose proof (P_n i) as HP.
  remember ((n-(3^i*2-i-2))/2) as c.
  pose proof (BigStep0 (3^i*2-i-2) (3^i*2-2-c) c) as I1.
  follow I1.
  1: applys_eq HP; flia.
  finish.
Qed.

Lemma BigStep1' i n:
  3^i*2-i <= n <= 3^i*6-i-10 ->
  n mod 2 = (i+1) mod 2 ->
  S' n -->*
  S' (3^i*12-1).
Proof.
  intros.
  pose proof (pow3_ge i).
  pose proof (P_n i) as HP.
  remember ((n-(3^i*2-i-2))/2) as c.
  pose proof (BigStep1 (3^i*2-i-2) (3^i*2-4-c) c) as I1.
  follow I1.
  1: applys_eq HP; flia.
  finish.
Qed.

End TM1.

