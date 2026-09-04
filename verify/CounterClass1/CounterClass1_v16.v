From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import BinaryCounter_v2.
From BusyCoq Require Import Longitudinal ES_v3.

Ltac es_v3_pre ::= ut.

Module TM16.

Definition tm := Eval compute in (TM_from_str "1LB1LA_0LC0LB_0RD0RE_0RE---_1RF1RC_1RA1RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l {{F}}> r) (at level 30).


Definition L2 a b := 0inf <* <[0;1]^^a <* <[0;0] <* [1]^^b.

Lemma Inc01 a b r:
  L2 (1+a) b |> [0;1] *> r -->*
  L2 a (4+b) |> r.
Proof.
  es' a b & r.
Qed.

Lemma Inc1 a b r:
  L2 a b |> [1] *> r -->*
  L2 a (1+b) |> r.
Proof.
  es' a b & r.
Qed.

Lemma ROv a b r:
  L2 a (4+b) |> [0;0] *> r -->*
  0inf <| [0;1]^^a *> [0]^^b *> [1] *> r.
Proof.
  es' a b & r.
Qed.

Lemma LOv_1 n r:
  L2 0 (3+n*2) |> [0;1;0;1;0;1] *> r -->*
  L2 n 9 |> r.
Proof.
  es' n & r.
Qed.

Lemma LOv_2 n r:
  L2 0 (1+n*2) |> [0;1;0;0;0] *> r -->*
  L2 n 6 |> r.
Proof.
  es' n & r.
Qed.

Lemma LOv_3 n r:
  L2 0 (3+n*2) |> [0;1;0;1;0;0] *> r -->*
  L2 n 9 |> r.
Proof.
  es' n & r.
Qed.

Lemma LOv_4 n r:
  L2 0 (n*2) |> [0;1;1;0;0;0] *> r -->*
  L2 n 6 |> r.
Proof.
  es' n & r.
Qed.

Lemma LOv_5 n r:
  L2 0 (n*2) |> [0;1;0;0;0;0;0] *> r -->*
  L2 (1+n) 5 |> r.
Proof.
  es' n & r.
Qed.

Lemma LOv_6 n r:
  L2 0 (1+n*2) |> [0;1;1;0;0;0;0;0] *> r -->*
  L2 (2+n) 5 |> r.
Proof.
  es' n & r.
Qed.

Lemma Rst_01 r:
  0inf <| [0;1] *> r -->*
  L2 0 7 |> r.
Proof.
  unfold L2.
  es.
Qed.

Lemma Rst_0 r:
  0inf <| [0] *> r -->*
  L2 0 6 |> r.
Proof.
  unfold L2.
  es.
Qed.

Lemma LOv_7 n r:
  L2 0 (3+n*2) |> [0;1;0;0;1] *> r -->*
  L2 n 8 |> r.
Proof.
  es' n & r.
Qed.

Lemma LOv_8 n r:
  L2 0 (2+n*2) |> [0;1;1;0;1;0;0] *> r -->*
  L2 n 9 |> r.
Proof.
  es' n & r.
Qed.

Lemma LOv_9 n r:
  L2 0 (n*2) |> [0;1;1;0;1;1;0;0] *> r -->*
  0inf <| [0;1]^^(1+n) *> [1] *> r.
Proof.
  es' n & r.
Qed.

Lemma init:
  c0 -->*
  0inf <| [0;1]^^1 *> 0inf.
Proof.
  esx.
Qed.

Open Scope nat.

Inductive P: nat->nat->nat->nat->Prop :=
| PRst01:
  P 1 0 0 7
| PRst0:
  P 0 1 0 6
| PInc01 a c d:
  P a 0 (1+c) d ->
  P (1+a) 0 c (4+d)
| PROv a b c d c' d':
  P a b c (4+d) ->
  P c d c' d' ->
  P a (2+b) c' (1+d')
| PROv' a b c d c' d':
  P a b c (5+d) ->
  P c d (1+c') d' ->
  P a (2+b) c' (4+d')
| PLOv1 a n:
  P a 0 0 (3+n*2) ->
  P (3+a) 0 n 9
| PLOv2 a n:
  P a 0 0 (1+n*2) ->
  P (1+a) 3 n 6
| PLOv2' a b c d n:
  P a b c (5+d) ->
  P c d 0 (1+n*2) ->
  P a (5+b) n 6
| PLOv3 a n:
  P a 0 0 (3+n*2) ->
  P (2+a) 2 n 9
| PLOv3' a b c d c' d' n:
  P a b c (7+d) ->
  P c d c' (5+d') ->
  P c' d' 0 (3+n*2) ->
  P a (4+b) n 9
| PLOv5 a b c d n:
  P a b c (5+d) ->
  P c d 0 (n*2) ->
  P a (7+b) (1+n) 5
| PLOv4 a b c d c' d' n:
  P a b c (6+d) ->
  P c d c' (5+d') ->
  P c' d' 0 (n*2) ->
  P a (5+b) n 6
| PLOv6 a b c d c' d' n:
  P a b c (6+d) ->
  P c d c' (5+d') ->
  P c' d' 0 (1+n*2) ->
  P a (7+b) (2+n) 5
| PLOv7 a b c d c' d' n:
  P a b c (8+d) ->
  P c d c' (5+d') ->
  P c' d' 0 (3+n*2) ->
  P a (2+b) n 8
| PLOv8 a b c d c' d' c'' d'' n:
  P a b c (7+d) ->
  P c d c' (6+d') ->
  P c' d' c'' (5+d'') ->
  P c'' d'' 0 (2+n*2) ->
  P a (4+b) n 9
| PLOv9 a b c d c' d' c'0 d'0 c'1 d'1 n c'2 d'2:
  P a b c (6+d) ->
  P c d c' (7+d') ->
  P c' d' c'0 (6+d'0) ->
  P c'0 d'0 c'1 (5+d'1) ->
  P c'1 d'1 0 (n*2) ->
  P (1+n) 0 c'2 d'2 ->
  P a (4+b) c'2 (1+d'2)
.

Lemma P_spec a b c d:
  P a b c d ->
  (forall r,
  0inf <| [0;1]^^a *> [0]^^b *> r -->*
  L2 c d |> r)%sym.
Proof.
  intros HP.
  unfold L2.
  induction HP; intros.
  - follow Rst_01.
    finish.
  - follow Rst_0.
    finish.
  - rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP.
    follow Inc01.
    finish.
  - rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP1.
    follow ROv.
    follow IHHP2.
    follow Inc1.
    finish.
  - rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP1.
    change (5+d) with (4+(1+d)).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP2.
    follow Inc01.
    finish.
  - rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP.
    follow LOv_1.
    finish.
  - rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP.
    follow LOv_2.
    finish.
  - rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP1.
    change (5+d) with (4+(1+d)).
    rewrite <-(lpow_add' _ 2 3).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP2.
    follow LOv_2.
    finish.
  - rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP.
    follow LOv_3.
    finish.
  - rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP1.
    change (7+d) with (4+(3+d)).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    rewrite <-(lpow_add' _ 2 1).
    follow IHHP2.
    change (5+d') with (4+(1+d')).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP3.
    follow LOv_3.
    finish.
  - rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP1.
    change (5+d) with (4+(1+d)).
    rewrite <-(lpow_add' _ 2 5).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP2.
    follow LOv_5.
    finish.
  - rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP1.
    change (6+d) with (4+(2+d)).
    rewrite <-(lpow_add' _ 2 3).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP2.
    change (5+d') with (4+(1+d')).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP3.
    follow LOv_4.
    finish.
  - rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP1.
    change (6+d) with (4+(2+d)).
    rewrite <-(lpow_add' _ 2 3).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP2.
    change (5+d') with (4+(1+d')).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP3.
    follow LOv_6.
    finish.
  - rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP1.
    change (8+d) with (4+(4+d)).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP2.
    rewrite <-(lpow_add' _ 2 2).
    change (5+d') with (4+(1+d')).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP3.
    follow LOv_7.
    finish.
  - rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP1.
    change (7+d) with (4+(3+d)).
    rewrite <-(lpow_add' _ 2 2).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP2.
    rewrite <-(lpow_add' _ 2 1).
    change (6+d') with (4+(2+d')).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP3.
    change (5+d'') with (4+(1+d'')).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP4.
    follow LOv_8.
    finish.
  - rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP1.
    change (6+d) with (4+(2+d)).
    rewrite <-(lpow_add' _ 2 2).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP2.
    change (7+d') with (4+(3+d')).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP3.
    change (6+d'0) with (4+(2+d'0)).
    rewrite <-(lpow_add' _ 2 1).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP4.
    change (5+d'1) with (4+(1+d'1)).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP5.
    follow LOv_9.
    follow IHHP6.
    follow Inc1.
    finish.
Qed.

Inductive P0: nat->nat->Prop :=
| P0Init b c d:
  P 1 b c d ->
  P0 c d
.

Lemma P0_spec a b:
  P0 a b ->
  c0 -->* L2 a b |> 0inf.
Proof.
  intros HP0.
  destruct HP0 as [b0 c d HP].
  follow init.
  pose proof (P_spec _ _ _ _ HP 0inf) as Hstep.
  rewrite (lpow_all0 [S0] b0) in Hstep by solve_const0_eq.
  follow Hstep.
  finish.
Qed.

End TM16.
