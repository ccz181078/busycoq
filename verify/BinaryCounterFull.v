Require Import Lia.
Require Import ZArith.
Set Default Goal Selector "!".




Inductive not_full: positive -> Prop :=
| not_full_O x: not_full (xO x)
| not_full_S x: not_full x -> not_full (xI x)
.

Inductive full: positive -> Prop :=
| full_O: full xH
| full_S x: full x -> full (xI x)
.

Fixpoint pow2(n:nat):positive :=
match n with
| O => xH
| S n0 => xO (pow2 n0)
end.

Fixpoint pow2'(n:nat):positive :=
match n with
| O => xH
| S n0 => xI (pow2' n0)
end.

Fixpoint log2(n:positive):nat :=
match n with
| xH => O
| xI n0 => S (log2 n0)
| xO n0 => S (log2 n0)
end.

Fixpoint ctz(n:positive):nat :=
match n with
| xO n0 => S (ctz n0)
| _ => O
end.

Fixpoint shr(n:positive)(k:nat){struct k}:N :=
match k with
| O => Npos n
| S k0 =>
  match n with
  | xH => N0
  | xO n0 => shr n0 k0
  | xI n0 => shr n0 k0
  end
end.

Lemma shr_S_le n m:
  (shr n (S m) <= shr n m)%N.
Proof.
  generalize dependent n.
  induction m; intros.
  - destruct n; cbn; lia.
  - destruct n.
    + apply (IHm n).
    + apply (IHm n).
    + cbn. lia.
Qed.

Lemma shr_S_lt n m:
  (shr n (S m) < Npos n)%N.
Proof.
  induction m.
  - destruct n; cbn; lia.
  - eapply N.le_lt_trans.
    2: apply IHm.
    apply shr_S_le.
Qed.




Open Scope positive.

Lemma full_iff_pow2' n:
  full n <->
  n = pow2' (log2 n).
Proof.
  split; intro.
  - induction n.
    + inversion H; subst.
      specialize (IHn H1).
      cbn. congruence.
    + inversion H.
    + reflexivity.
  - induction n.
    + cbn in H.
      inversion H; subst.
      specialize (IHn H1).
      constructor.
      congruence.
    + inversion H.
    + constructor.
Qed.

Lemma not_full_log2_S {n} (Hnf:not_full n):
  log2 (Pos.succ n) = log2 n.
Proof.
  induction Hnf; cbn; auto.
Qed.

Lemma pow2'_spec n:
  Pos.succ (pow2' n) = pow2 (S n).
Proof.
  induction n; cbn; auto.
  rewrite IHn.
  reflexivity.
Qed.

Definition rest(n:positive):N :=
  Npos (pow2' (log2 n)) - (Npos n).

Lemma pow2'_log2_ge n:
  (pow2' (log2 n) >= n)%positive.
Proof.
  induction n; cbn; lia.
Qed.

Lemma rest_mul2 n:
  (rest (n~0) = (rest n)*2+1)%N.
Proof.
  unfold rest.
  cbn[log2].
  cbn[pow2'].
  pose proof (pow2'_log2_ge n) as H.
  lia.
Qed.

Lemma rest_mul_pow2 n i:
  (rest (n*(pow2 i))+1 = ((rest n)+1)*(Npos (pow2 i)))%N.
Proof.
  induction i.
  - cbn[pow2].
    rewrite N.mul_1_r.
    rewrite Pos.mul_1_r.
    reflexivity.
  - cbn[pow2].
    rewrite POrderedType.Positive_as_OT.mul_xO_r.
    pose proof (rest_mul2 (n*pow2 i)) as H.
    lia.
Qed.

Lemma full_iff_rest_eq0 n:
  full n <-> rest n = N0.
Proof.
  rewrite full_iff_pow2'.
  unfold rest.
  pose proof (pow2'_log2_ge n).
  lia.
Qed.

Lemma not_full_iff_pow2' n:
  not_full n <-> (n < pow2' (log2 n))%positive.
Proof.
  induction n.
  - split; intro H.
    + inversion H; subst.
      rewrite IHn in H1. cbn. lia.
    + constructor.
      rewrite IHn.
      cbn in H. lia.
  - split; intro H.
    + cbn.
      pose proof (pow2'_log2_ge n). lia.
    + constructor.
  - cbn.
    split; intro H.
    + inversion H; subst.
    + lia.
Qed.

Lemma full_iff_rest n:
  full n <-> rest n = N0.
Proof.
  rewrite full_iff_pow2'.
  unfold rest.
  pose proof (pow2'_log2_ge n) as H.
  lia.
Qed.

Lemma not_full_iff_rest n:
  not_full n <-> rest n <> N0.
Proof.
  rewrite not_full_iff_pow2'.
  unfold rest.
  lia.
Qed.

Lemma rest_S n:
  rest n <> N0 ->
  ((rest (Pos.succ n)) + 1)%N = rest n.
Proof.
  intro H.
  unfold rest.
  rewrite <-not_full_iff_rest in H.
  rewrite (not_full_log2_S H).
  rewrite not_full_iff_pow2' in H.
  lia.
Qed.

Lemma rest_pow2_add n i x:
  (n*(pow2 i) <= x < (n+1)*(pow2 i))%positive ->
  ((rest n)*(Npos (pow2 i)) <= rest x < (rest n + 1)*(Npos (pow2 i)))%N.
Proof.
  generalize dependent x.
  unfold rest.
  induction i; intros.
  - cbn in H.
    assert (n=x) as E by lia.
    subst.
    cbn[pow2]. lia.
  - destruct x.
    + cbn[pow2].
      cbn[log2]. cbn[pow2'].
      cbn[pow2] in H.
      specialize (IHi x). lia.
    + cbn[pow2].
      cbn[log2]. cbn[pow2'].
      cbn[pow2] in H.
      specialize (IHi x). lia.
    + cbn in H. lia.
Qed.

Lemma not_empty_pow2_add n i x:
  (n*(pow2 i) <= x < (n+1)*(pow2 i))%positive ->
  pow2 (log2 n) < n ->
  pow2 (log2 x) < x.
Proof.
  generalize dependent x.
  unfold rest.
  induction i; intros.
  - cbn in H.
    assert (n=x) as E by lia.
    subst.
    cbn[pow2]. lia.
  - destruct x.
    + cbn[log2]. cbn[pow2].
      cbn[pow2'].
      cbn[pow2] in H.
      specialize (IHi x). lia.
    + cbn[log2]. cbn[pow2].
      cbn[pow2'].
      cbn[pow2] in H.
      specialize (IHi x). lia.
    + cbn in H. lia.
Qed.

Lemma le_pow2a a b c d:
  (b * N.pos (pow2 (c + (S d))) <= a)%N ->
  (b*2 <= a)%N.
Proof.
  intro H.
  rewrite Nat.add_comm in H.
  cbn in H.
  remember (N.pos (pow2 (d + c))~0) as c1.
  assert (2<=c1)%N as H0 by lia.
  pose proof (N.mul_le_mono_l _ _ b H0).
  lia.
Qed.

Lemma log2_pow2 x:
  log2 (pow2 x) = x.
Proof.
  induction x; cbn; auto.
Qed.

Lemma log2_mulpow2 n m: (log2 (n*(pow2 m)) = m + log2 n)%nat.
Proof.
  induction m.
  - cbn.
    f_equal. lia.
  - cbn.
    rewrite POrderedType.Positive_as_OT.mul_xO_r.
    rewrite <-IHm.
    reflexivity.
Qed.


Lemma rest_pow2 x:
  (rest (pow2 x) + 1 = Npos (pow2 x))%N.
Proof.
  induction x.
  - reflexivity.
  - cbn[pow2].
    rewrite rest_mul2.
    lia.
Qed.

Lemma split_bound m:
  ((rest (pow2 (ctz m)) + 1) * 2 + shr m (S (ctz m)) <= (Npos m)*2)%N.
Proof.
  rewrite rest_pow2.
  induction m.
  - cbn[ctz].
    cbn[pow2].
    cbn[shr].
    lia.
  - cbn[ctz].
    cbn[pow2].
    remember (S (ctz m)) as c1.
    cbn[shr].
    lia.
  - cbn; lia.
Qed.

Lemma split_bound' n l:
  (2 <= n*2 < pow2 l)%positive ->
  ((N.pos (pow2 (ctz n)))*4 + shr n (S (ctz n)) <= N.pos (pow2 l))%N.
Proof.
  generalize dependent n.
  induction l; intros.
  1: cbn in H; lia.
  cbn in H.
  destruct l as [|l].
  1: cbn in H; lia.
  cbn in H.
  destruct n.
  3: cbn; lia.
  1: cbn[ctz]; cbn[shr]; cbn[pow2]; lia.
  cbn[ctz]. cbn[pow2].
  remember (S (ctz n)) as c1.
  cbn[shr].
  subst c1.
  specialize (IHl n).
  cbn[pow2] in IHl.
  lia.
Qed.


Lemma rest_mul2add1 n:
  (rest (n~1) = rest n * 2)%N.
Proof.
  replace (n~1) with (Pos.succ (n~0)) by lia.
  assert (not_full (n~0))%positive as nf by constructor.
  rewrite not_full_iff_rest in nf.
  pose proof (rest_S (n~0) nf) as H3.
  pose proof (rest_mul2 n).
  lia.
Qed.

Lemma rest_le n:
  (rest n <= rest (pow2 (log2 n)))%N.
Proof.
  induction n.
  - assert (n~1 = Pos.succ (n~0))%positive as E by lia.
    rewrite E.
    assert (not_full (n~0))%positive as nf by constructor.
    rewrite not_full_log2_S; auto.
    rewrite not_full_iff_rest in nf.
    pose proof (rest_S (n~0) nf) as H3.
    assert (rest n~0 <= rest (pow2 (log2 n~0)))%N. {
      rewrite rest_mul2.
      cbn[log2].
      pose proof (rest_pow2 (log2 n)) as H.
      pose proof (rest_pow2 (S (log2 n))) as H0.
      cbn[pow2].
      cbn[pow2] in H0.
      lia.
    }
    lia.
  - rewrite rest_mul2.
    cbn[log2].
    pose proof (rest_pow2 (log2 n)) as H.
    pose proof (rest_pow2 (S (log2 n))) as H0.
    cbn[pow2].
    cbn[pow2] in H0.
    lia.
  - cbn; lia.
Qed.

Lemma neq1_pow2_log2 k:
  (k<>1 -> pow2 (log2 k) <> 1)%positive.
Proof.
  destruct k; cbn; intro H; lia.
Qed.

Lemma not_empty_rest_iff n:
  pow2 (log2 n) < n <->
  (rest n < rest (pow2 (log2 n)))%N.
Proof.
  split; intro H.
  - unfold rest.
    pose proof (pow2'_log2_ge n).
    rewrite log2_pow2.
    lia.
  - unfold rest in H.
    pose proof (pow2'_log2_ge n).
    rewrite log2_pow2 in H.
    lia.
Qed.

Lemma not_empty_rest_pow2_add n i x:
  (n*(pow2 i) <= x < (n+1)*(pow2 i))%positive ->
  (rest n < rest (pow2 (log2 n)) ->
  rest x < rest (pow2 (log2 x)))%N.
Proof.
  intros H H0.
  rewrite <-not_empty_rest_iff.
  rewrite <-not_empty_rest_iff in H0.
  eapply not_empty_pow2_add; eauto.
Qed.

Lemma rest_S_not_empty k:
  (rest k <> 0)%N ->
  (rest (Pos.succ k) < rest (pow2 (log2 (Pos.succ k))))%N.
Proof.
  intro H.
  pose proof (rest_S _ H).
  rewrite <-not_full_iff_rest in H.
  rewrite not_full_log2_S; auto.
  pose proof (rest_le k).
  lia.
Qed.


Lemma full_iff n:
  full n <->
  exists i, n+1 = 2^(Pos.of_succ_nat i).
Proof.
  split; intro H.
  - induction H.
    + exists O. reflexivity.
    + destruct IHfull as [i Hf].
      exists (S i).
      cbn.
      rewrite Pos.pow_succ_r.
      lia.
  - induction n.
    + constructor.
      apply IHn.
      destruct H as [i H].
      destruct i as [|i].
      1: lia.
      cbn in H.
      exists i.
      rewrite Pos.pow_succ_r in H.
      lia.
    + destruct H as [i H].
      destruct i as [|i].
      * lia.
      * cbn in H.
        rewrite Pos.pow_succ_r in H.
        lia.
    + constructor.
Qed.

Fixpoint is_full n :=
match n with
| xH => true
| xI x => is_full x
| xO x => false
end.

Lemma is_full_spec n:
  full n <-> is_full n = true.
Proof.
  split; intro H.
  - induction H; auto 1.
  - induction n; cbn in H.
    + constructor; tauto.
    + congruence.
    + constructor.
Qed.

Lemma is_full_spec' n:
  not_full n <-> is_full n = false.
Proof.
  split; intro H.
  - induction H; auto 1.
  - induction n; cbn in H.
    + constructor; tauto.
    + constructor.
    + congruence.
Qed.

Definition full_discriminate {n}:
  full n -> not_full n -> False.
Proof.
  rewrite is_full_spec.
  rewrite is_full_spec'.
  congruence.
Qed.

Lemma full_2n_not_full {n} (Hf:full n) {m}:
  (n < m ->
  m <= 2*n ->
  not_full m)%positive.
Proof.
  intros H0 H1.
  destruct (is_full m) eqn:E.
  2: rewrite is_full_spec'; apply E.
  rewrite <-is_full_spec in E.
  rewrite full_iff in E,Hf.
  destruct E as [i E].
  destruct Hf as [i' E'].
  assert (i<i'\/i=i'\/S i'=i\/S i'<i)%nat as H by lia.
  pose proof (f_equal Pos.to_nat E') as F'.
  pose proof (f_equal Pos.to_nat E) as F.
  rewrite Pos2Nat.inj_pow,SuccNat2Pos.id_succ in F',F.
  change (Pos.to_nat 2) with (2%nat) in F',F.
  cbn in F,F'.
  destruct H as [H|[H|[H|H]]].
  - rewrite (Nat.pow_lt_mono_r_iff 2) in H; lia.
  - subst. lia.
  - subst. cbn in F. lia.
  - rewrite (Nat.pow_lt_mono_r_iff 2) in H. 2: lia.
    cbn in H.
    lia.
Qed.

Lemma full_S__not_full n:
  full n -> not_full (n+1).
Proof.
  intro Hf.
  induction Hf; cbn; constructor.
Qed.

Lemma full_cases n:
  {full n} + {not_full n}.
Proof.
  destruct (is_full n) eqn:E.
  - rewrite <-is_full_spec in E; auto.
  - rewrite <-is_full_spec' in E; auto.
Qed.

Close Scope positive.