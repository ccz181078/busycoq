From BusyCoq Require Import Individual62.
From BusyCoq Require Import BinaryCounterFull.
Require Import ZArith.
Require Import Lia.

Section BinaryCounter.
Open Scope list.

Hypothesis d0 d1:list Sym.
Hypothesis d1a:side.
Fixpoint BinaryCounter (n:positive) :=
match n with
| xH => d1a
| xI n0 => d1 *> (BinaryCounter n0)
| xO n0 => d0 *> (BinaryCounter n0)
end.

Definition BinaryCounter_0 (n:N) :=
match n with
| N0 => const 0
| Npos n0 => BinaryCounter n0
end.

Lemma not_full_Inc {n} (Hnf:not_full n):
  exists s i,
  BinaryCounter n = d1^^i *> d0 *> s /\
  BinaryCounter (Pos.succ n) = d0^^i *> d1 *> s.
Proof.
  induction Hnf.
  - exists (BinaryCounter x) O.
    auto.
  - destruct IHHnf as [s [i [H0 H1]]].
    exists s (S i).
    cbn.
    simpl_tape.
    split; congruence.
Qed.

Lemma full_Overflow {n} (Hf:full n):
  exists i,
  BinaryCounter n = d1^^i *> d1a /\
  BinaryCounter (Pos.succ n) = d0^^(S i) *> d1a /\
  (n+1)%positive = (2^Pos.of_succ_nat i)%positive.
Proof.
  induction Hf.
  - exists O.
    repeat split; auto.
    cbn. simpl_tape.
    reflexivity.
  - destruct IHHf as [i [H0 [H1 H2]]].
    exists (S i).
    cbn.
    simpl_tape.
    rewrite <-H0.
    repeat split; auto.
    + rewrite H1.
      simpl_tape.
      reflexivity.
    + rewrite Pos.pow_succ_r. lia.
Qed.

Lemma Counter_pow2 n:
  BinaryCounter (pow2 n) =
  d0^^n *> d1a.
Proof.
  induction n; cbn; auto.
  rewrite IHn,Str_app_assoc.
  reflexivity.
Qed.

Lemma Counter_pow2' n:
  BinaryCounter (pow2' n) =
  d1^^n *> d1a.
Proof.
  induction n; cbn; auto.
  rewrite IHn,Str_app_assoc.
  reflexivity.
Qed.

Lemma Counter_shr_S_ctz n:
  d1a = d1 *> const 0 ->
  BinaryCounter_0 (Npos n) =
  d0^^(ctz n) *> d1 *> BinaryCounter_0 (shr n (S (ctz n))).
Proof.
  intro H.
  induction n; cbn; auto.
  cbn in IHn.
  rewrite IHn.
  simpl_tape.
  reflexivity.
Qed.

Lemma BinaryCounter_0_d0 n:
  BinaryCounter_0 (Npos (n~0)) =
  d0 *> BinaryCounter_0 (Npos n).
Proof.
  reflexivity.
Qed.

Lemma BinaryCounter_0_d1 n:
  BinaryCounter_0 (Npos (n~1)) =
  d1 *> BinaryCounter_0 (Npos n).
Proof.
  reflexivity.
Qed.

Hypothesis tm:TM.

Hypothesis QL QR:Q.
Hypothesis qL qR:list Sym.

Local Notation "l <| r" :=
  (l <{{QL}} qL *> r) (at level 30).

Local Notation "l |> r" :=
  (l <* qR {{QR}}> r) (at level 30).

Lemma LInc:
  (forall l r n,
    l <* d0 <* d1^^n <| r -[ tm ]->+
    l <* d1 <* d0^^n |> r) ->
  forall n (Hnf:not_full n) r,
    BinaryCounter n <| r -[ tm ]->+
    BinaryCounter (Pos.succ n) |> r.
Proof.
  intros.
  destruct (not_full_Inc Hnf) as [s [i [H0 H1]]].
  rewrite H0,H1.
  simpl_tape.
  apply H.
Qed.

Lemma RInc:
  (forall l r n,
    l |> d1^^n *> d0 *> r -[ tm ]->+
    l <| d0^^n *> d1 *> r) ->
  forall n (Hnf:not_full n) l,
    l |> BinaryCounter n -[ tm ]->+
    l <| BinaryCounter (Pos.succ n).
Proof.
  intros.
  destruct (not_full_Inc Hnf) as [s [i [H0 H1]]].
  rewrite H0,H1.
  simpl_tape.
  apply H.
Qed.

Lemma RInc_0:
  (forall l r n,
    l |> d1^^n *> d0 *> r -[ tm ]->+
    l <| d0^^n *> d1 *> r) ->
  d1a = d1 *> const 0 ->
  d0 *> const 0 = const 0 ->
  forall n l,
    l |> BinaryCounter_0 n -[ tm ]->+
    l <| BinaryCounter_0 (N.succ n).
Proof.
  intros.
  destruct n as [|n].
  - cbn[BinaryCounter_0].
    rewrite <-H1.
    change (d0 *> const 0) with (d1^^0 *> d0 *> const 0).
    follow10 H.
    cbn.
    rewrite H0.
    finish.
  - destruct (is_full n) eqn:E.
    + rewrite <-is_full_spec in E.
      cbn.
      destruct (full_Overflow E) as [i [H2 [H3 H4]]].
      rewrite H2,H3.
      rewrite H0.
      rewrite lpow_shift'.
      specialize (H l (const 0) (S i)).
      cbn in H. cbn.
      gen H.
      simpl_tape.
      rewrite H1.
      tauto.
    + rewrite <-is_full_spec' in E.
      destruct (not_full_Inc E) as [s [i [H2 H3]]].
      cbn.
      rewrite H2,H3.
      apply H.
Qed.


End BinaryCounter.
