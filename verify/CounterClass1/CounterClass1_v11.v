From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import BinaryCounter_v2.
From BusyCoq Require Import Longitudinal ES_v3.

Ltac es_v3_pre ::= ut.


Module TM11.

Definition tm := Eval compute in (TM_from_str "1RB1RC_0RC---_1RD0RA_1RE1RD_1LF1LE_0RC0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{F}} [1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l {{D}}> r) (at level 30).


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

Lemma Inc00_0 a r:
  L2 (1+a) 0 |> [0;0] *> r -->*
  L2 a 4 |> r.
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
  0inf <| [0;1]^^1 *> 0inf.
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
  L2 0 (3+n*2) |> [0;1;0;0;0] *> r -->*
  L2 (4+n) 0 |> r.
Proof.
  es' n & r.
Qed.

Lemma LOv_4 n r:
  L2 0 (n*2) |> [0;1;1;0;0;0] *> r -->*
  L2 (3+n) 0 |> r.
Proof.
  es' n & r.
Qed.

Lemma LOv_5 n r:
  L2 0 (1+n*2) |> [0;1;1;1;0;0;0] *> r -->*
  L2 (4+n) 0 |> r.
Proof.
  ut; execute_with_shift_rule'.
  st; execute_with_shift_rule'.
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
| PInc00_0 a b c:
  P a b (1+c) 0 ->
  P a (2+b) c 4
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
| PLOv1' a b c d n:
  P a b c (4+d) ->
  P c d 0 (n*2) ->
  P a (3+b) (1+n) 1
| PLOv2 a b c d c' d' n:
  P a b c (5+d) ->
  P c d c' (4+d') ->
  P c' d' 0 (1+n*2) ->
  P a (3+b) (2+n) 1
| PLOv3 a b c d n:
  P a b c (4+d) ->
  P c d 0 (3+n*2) ->
  P a (5+b) (4+n) 0
| PLOv4 a b c d c' d' n:
  P a b c (5+d) ->
  P c d c' (4+d') ->
  P c' d' 0 (n*2) ->
  P a (5+b) (3+n) 0
| PLOv5 a b c d c' d' c'' d'' n:
  P a b c (5+d) ->
  P c d c' (5+d') ->
  P c' d' c'' (4+d'') ->
  P c'' d'' 0 (1+n*2) ->
  P a (5+b) (4+n) 0
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
  - (* PInc00_0 *)
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP.
    follow Inc00_0.
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
  - (* PLOv1' *)
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP1.
    change (4+d) with (3+(1+d)).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP2.
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
  - (* PLOv4 *)
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
    follow LOv_4.
    finish.
  - (* PLOv5 *)
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP1.
    change (5+d) with (3+(2+d)).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP2.
    change (5+d') with (3+(2+d')).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP3.
    change (4+d'') with (3+(1+d'')).
    follow ROv.
    rewrite Nat.add_comm,<-lpow_add'.
    follow IHHP4.
    follow LOv_5.
    finish.
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

Lemma P0_LOv2 n:
  (L2 0 (1+n*2) |> [0;1;1] *> 0inf -->*
  L2 (2+n) 1 |> 0inf)%sym.
Proof.
  es' n.
Qed.

Lemma P0_Inc01 a:
  (L2 (1+a) 0 |> 0inf -->*
  L2 a 4 |> 0inf)%sym.
Proof.
  es' a.
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

End TM11.
