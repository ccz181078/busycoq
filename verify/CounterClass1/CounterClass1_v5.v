From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import BinaryCounter_v2.
From BusyCoq Require Import Longitudinal ES_v3.

Ltac es_v3_pre ::= ut.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1LB---_0RC0LB_1RE0RD_1RA1RC_1RF0LD_1LB1LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l {{E}}> r) (at level 30).


Definition L2 a b := 0inf <* <[0;1]^^a <* <[0;1] <* [1]^^b.

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
  L2 a (3+b) |> [0;0] *> r -->*
  0inf <| [0;1]^^a *> [0]^^b *> [1] *> r.
Proof.
  es' a b & r.
Qed.

Lemma Inc00_1 a r:
  L2 (1+a) 1 |> [0;0] *> r -->*
  L2 a 5 |> r.
Proof.
  es' a & r.
Qed.

Lemma Inc00_2 a r:
  L2 (2+a) 2 |> [0;0] *> r -->*
  L2 a 8 |> r.
Proof.
  es' a & r.
Qed.

Lemma Rst_01 r:
  0inf <| [0;1] *> r -->*
  L2 0 6 |> r.
Proof.
  unfold L2.
  es.
Qed.

Lemma Rst_0 r:
  0inf <| [0] *> r -->*
  L2 0 5 |> r.
Proof.
  unfold L2.
  es.
Qed.

Lemma init:
  c0 -->*
  L2 0 1 |> 0inf.
Proof.
  esx.
Qed.

Lemma LOv_1 n r:
  L2 0 (n*2) |> [0;1;0] *> r -->*
  L2 (1+n) 1 |> r.
Proof.
  es' n & r.
Qed.

Lemma LOv_2 n r:
  L2 0 (1+n*2) |> [0;1;1;0] *> r -->*
  L2 (2+n) 1 |> r.
Proof.
  ut; es; er.
Qed.

Lemma LOv_3 n r:
  L2 0 (3+n*2) |> [0;1;0;0] *> r -->*
  L2 (3+n) 1 |> r.
Proof.
  es' n & r.
Qed.

Open Scope nat.

Inductive P: nat->nat->nat->nat->Prop :=
| PRst0:
  P 0 1 0 5
| PInc01 a c d:
  P a 0 (1+c) d ->
  P (1+a) 0 c (4+d)
| PInc1 a c d:
  P a 1 c d ->
  P (1+a) 0 c (1+d)
| PInc00_1 a b c:
  P a b (1+c) 1 ->
  P a (2+b) c 5
| PInc00_2 a b c:
  P a b (2+c) 2 ->
  P a (2+b) c 8
| PROv a b c d c' d':
  P a b c (3+d) ->
  P c d c' d' ->
  P a (2+b) c' (1+d')
| PROv' a b c d c' d':
  P a b c (4+d) ->
  P c d (1+c') d' ->
  P a (2+b) c' (4+d')
| PLOv1 a n:
  P a 0 0 (n*2) ->
  P (1+a) 1 (1+n) 1
| PLOv2 a b c d c' d' n:
  P a b c (5+d) ->
  P c d c' (4+d') ->
  P c' d' 0 (1+n*2) ->
  P a (3+b) (2+n) 1
| PLOv3 a b d n:
  P a b 0 (4+d) ->
  P 0 d 0 (3+n*2) ->
  P a (4+b) (3+n) 1
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
  - (* PRst0 *)
    follow Rst_0.
    finish.
  - (* PInc01 *)
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP.
    follow Inc01.
    finish.
  - (* PInc1 *)
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP.
    follow Inc1.
    finish.
  - (* PInc00_1 *)
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP.
    follow Inc00_1.
    finish.
  - (* PInc00_2 *)
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP.
    follow Inc00_2.
    finish.
  - (* PROv *)
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP1.
    follow ROv.
    follow IHHP2.
    follow Inc1.
    finish.
  - (* PROv' *)
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP1.
    change (4+d) with (3+(1+d)).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP2.
    follow Inc01.
    finish.
  - (* PLOv1 *)
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP.
    follow LOv_1.
    finish.
  - (* PLOv2 *)
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP1.
    change (5+d) with (3+(2+d)).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP2.
    change (4+d') with (3+(1+d')).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP3.
    follow LOv_2.
    finish.
  - (* PLOv3 *)
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP1.
    change (4+d) with (3+(1+d)).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP2.
    follow LOv_3.
    finish.
Qed.

Lemma P0_start:
  L2 0 1 |> 0inf -->*
  L2 2 1 |> 0inf.
Proof.
  es.
Qed.

Lemma P0_ROv a b:
  (L2 a (3+b) |> 0inf -->*
  0inf <| [0;1]^^a *> [0]^^b *> [1] *> 0inf)%sym.
Proof.
  es' a b.
Qed.

Lemma P0_ROv' a b:
  (L2 a (4+b) |> 0inf -->*
  0inf <| [0;1]^^a *> [0]^^b *> [0;1] *> 0inf)%sym.
Proof.
  es' a b.
Qed.

Lemma P0_ROv2 a b:
  (L2 a (5+b) |> 0inf -->*
  0inf <| [0;1]^^a *> [0]^^b *> [0;0;1] *> 0inf)%sym.
Proof.
  es' a b.
Qed.

Lemma P0_LOv3 n:
  (L2 0 (3+n*2) |> [0;1] *> 0inf -->*
  L2 (3+n) 1 |> 0inf)%sym.
Proof.
  es' n.
Qed.

Lemma P0_End1 n:
  (L2 0 (1+n*2) |> [0;1;1;1] *> 0inf -->*
  L2 (3+n) 1 |> 0inf)%sym.
Proof.
  es' n.
Qed.

Inductive P0: nat->nat->Prop :=
| P0Init:
  P0 0 1
| P0Start:
  P0 0 1 ->
  P0 2 1
| P0Inc00_1 a:
  P0 (1+a) 1 ->
  P0 a 5
| P0Ov a b c d:
  P0 a (3+b) ->
  P a b c d ->
  P0 c (1+d)
| P0Ov' a b c d:
  P0 a (4+b) ->
  P a b (1+c) d ->
  P0 c (4+d)
| P0LOv3 a b n:
  P0 a (4+b) ->
  P a b 0 (3+n*2) ->
  P0 (3+n) 1
| P0End1 a b c d c' d' n:
  P0 a (5+b) ->
  P a b c (5+d) ->
  P c d c' (4+d') ->
  P c' d' 0 (1+n*2) ->
  P0 (3+n) 1
.

Lemma P0_spec a b:
  P0 a b ->
  c0 -->* L2 a b |> 0inf.
Proof.
  intros HP0.
  induction HP0.
  - exact init.
  - follow IHHP0.
    follow P0_start.
    finish.
  - follow IHHP0.
    es' a.
  - follow IHHP0.
    follow P0_ROv.
    follow (P_spec _ _ _ _ H).
    follow Inc1.
    finish.
  - follow IHHP0.
    follow P0_ROv'.
    follow (P_spec _ _ _ _ H).
    follow Inc01.
    finish.
  - follow IHHP0.
    follow P0_ROv'.
    follow (P_spec _ _ _ _ H).
    follow P0_LOv3.
    finish.
  - follow IHHP0.
    follow P0_ROv2.
    follow (P_spec _ _ _ _ H).
    change (5+d) with (3+(2+d)).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    follow (P_spec _ _ _ _ H0).
    change (4+d') with (3+(1+d')).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    follow (P_spec _ _ _ _ H1).
    follow P0_End1.
    finish.
Qed.

End TM5.
