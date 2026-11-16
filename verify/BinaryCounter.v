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

Lemma Counter_mulpow2 m n:
  BinaryCounter (m*(pow2 n)) =
  d0^^n *> BinaryCounter m.
Proof.
  induction n; cbn.
  - f_equal; lia.
  - simpl_tape.
    rewrite <-IHn.
    rewrite POrderedType.Positive_as_OT.mul_xO_r.
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

Lemma LInc':
  (forall l r n,
    l <* d0 <* d1^^n <| r -[ tm ]->+
    l <* d1 <* d0^^n |> r) ->
  (forall r n,
    d1a <* d1^^n <| r -[ tm ]->+
    d1a <* d0^^(1+n) |> r) ->
  forall n r,
    BinaryCounter n <| r -[ tm ]->+
    BinaryCounter (Pos.succ n) |> r.
Proof.
  intros H H0 n r.
  destruct (is_full n) eqn:E.
  - rewrite <-is_full_spec in E.
    destruct (full_Overflow E) as [i [H1 [H2 H3]]].
    rewrite H1,H2.
    apply H0.
  - rewrite <-is_full_spec' in E.
    apply LInc; auto.
Qed.

Lemma RInc':
  (forall l r n,
    l |> d1^^n *> d0 *> r -[ tm ]->+
    l <| d0^^n *> d1 *> r) ->
  (forall l n,
    l |> d1^^n *> d1a -[ tm ]->+
    l <| d0^^(1+n) *> d1a) ->
  forall n l,
    l |> BinaryCounter n -[ tm ]->+
    l <| BinaryCounter (Pos.succ n).
Proof.
  intros H H0 n r.
  destruct (is_full n) eqn:E.
  - rewrite <-is_full_spec in E.
    destruct (full_Overflow E) as [i [H1 [H2 H3]]].
    rewrite H1,H2.
    apply H0.
  - rewrite <-is_full_spec' in E.
    apply RInc; auto.
Qed.

End BinaryCounter.

Section BinaryCounter_0.

Hypothesis d1:list Sym.
Definition d0:list Sym := List.repeat 0 (length d1).
Definition d1a := d1 *> const 0.

Definition BinaryCounter_0 (n:N) :=
match n with
| N0 => const 0
| Npos n0 => BinaryCounter d0 d1 d1a n0
end.

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

Lemma d0_all0:
  d0 *> const 0 = const 0.
Proof.
  unfold d0.
  induction (length d1); cbn.
  - reflexivity.
  - rewrite IHn.
    solve_const0_eq.
Qed.

Lemma BinaryCounter_0_d0' n:
  BinaryCounter_0 (n*2+0) =
  d0 *> BinaryCounter_0 n.
Proof.
  destruct n as [|n].
  - cbn.
    rewrite d0_all0.
    reflexivity.
  - replace ((N.pos n)*2+0)%N with (N.pos n~0) by lia.
    apply BinaryCounter_0_d0.
Qed.

Lemma BinaryCounter_0_d1' n:
  BinaryCounter_0 (n*2+1) =
  d1 *> BinaryCounter_0 n.
Proof.
  destruct n as [|n].
  - reflexivity.
  - replace ((N.pos n)*2+1)%N with (N.pos n~1) by lia.
    apply BinaryCounter_0_d1.
Qed.



Lemma Counter_shr_S_ctz n:
  BinaryCounter_0 (Npos n) =
  d0^^(ctz n) *> d1 *> BinaryCounter_0 (shr n (S (ctz n))).
Proof.
  induction n; cbn; auto.
  cbn in IHn.
  rewrite IHn.
  simpl_tape.
  reflexivity.
Qed.

Lemma Counter_shr_S_ctzS n:
  BinaryCounter_0 n =
  d1^^(ctz (N.succ_pos n)) *> d0 *> BinaryCounter_0 (shr (N.succ_pos n) (S (ctz (N.succ_pos n)))).
Proof.
  remember (N.succ_pos n) as n'.
  gen n.
  induction n'; intros.
  - cbn[ctz]. cbn[shr].
    destruct n as [|[n|n|]]; try lia.
    rewrite BinaryCounter_0_d0.
    assert (n=n') by lia.
    subst.
    reflexivity.
  - cbn[shr]. cbn[ctz].
    destruct n as [|[n|n|]]; try lia.
    + rewrite BinaryCounter_0_d1.
      cbn[lpow]. rewrite Str_app_assoc.
      rewrite <-(IHn' (N.pos n)).
      * reflexivity.
      * lia.
    + assert (n'=1%positive) by lia.
      subst.
      cbn. simpl_tape. cbn.
      rewrite d0_all0.
      reflexivity.
  - assert (n=N0) by lia.
    subst.
    cbn.
    rewrite d0_all0.
    reflexivity.
Qed.

Hypothesis tm:TM.

Hypothesis QL QR:Q.
Hypothesis qL qR:list Sym.

Local Notation "l <| r" :=
  (l <{{QL}} qL *> r) (at level 30).

Local Notation "l |> r" :=
  (l <* qR {{QR}}> r) (at level 30).
Lemma LInc_0:
  (forall l r n,
    d1^^n *> d0 *> l <| r -[ tm ]->+
    d0^^n *> d1 *> l |> r) ->
  forall n r,
    BinaryCounter_0 n <| r -[ tm ]->+
    BinaryCounter_0 (N.succ n) |> r.
Proof.
  intros.
  destruct n as [|n].
  - cbn[BinaryCounter_0].
    rewrite <-d0_all0.
    change (d0 *> const 0) with (d1^^0 *> d0 *> const 0).
    follow10 H.
    cbn.
    unfold d1a.
    finish.
  - destruct (is_full n) eqn:E.
    + rewrite <-is_full_spec in E.
      cbn.
      destruct (full_Overflow d0 d1 d1a E) as [i [H2 [H3 H4]]].
      rewrite H2,H3.
      unfold d1a.
      rewrite lpow_shift'.
      specialize (H (const 0) r (S i)).
      cbn in H. cbn.
      gen H.
      simpl_tape.
      rewrite d0_all0.
      tauto.
    + rewrite <-is_full_spec' in E.
      destruct (not_full_Inc d0 d1 d1a E) as [s [i [H2 H3]]].
      cbn.
      rewrite H2,H3.
      apply H.
Qed.

Lemma RInc_0:
  (forall l r n,
    l |> d1^^n *> d0 *> r -[ tm ]->+
    l <| d0^^n *> d1 *> r) ->
  forall n l,
    l |> BinaryCounter_0 n -[ tm ]->+
    l <| BinaryCounter_0 (N.succ n).
Proof.
  intros.
  destruct n as [|n].
  - cbn[BinaryCounter_0].
    rewrite <-d0_all0.
    change (d0 *> const 0) with (d1^^0 *> d0 *> const 0).
    follow10 H.
    cbn.
    unfold d1a.
    finish.
  - destruct (is_full n) eqn:E.
    + rewrite <-is_full_spec in E.
      cbn.
      destruct (full_Overflow d0 d1 d1a E) as [i [H2 [H3 H4]]].
      rewrite H2,H3.
      unfold d1a.
      rewrite lpow_shift'.
      specialize (H l (const 0) (S i)).
      cbn in H. cbn.
      gen H.
      simpl_tape.
      rewrite d0_all0.
      tauto.
    + rewrite <-is_full_spec' in E.
      destruct (not_full_Inc d0 d1 d1a E) as [s [i [H2 H3]]].
      cbn.
      rewrite H2,H3.
      apply H.
Qed.


End BinaryCounter_0.
