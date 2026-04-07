From Coq Require Import Uint63 ZArith Lia.
Require Import BigInt.NTTTree BigInt.NTTConcrete BigInt.BigIntMul BigInt.BigIntMulCanonical BigInt.BigIntMulCRTArrayExact BigInt.BigIntMulConvolutionBridge.

Local Open Scope Z_scope.

Lemma prime469_input_get_canonical :
  forall n (t : NTTTree.tree Prime469.int n) i,
    Prime469.canonical_tree n t ->
    (i < Prime469.pow2 n)%nat ->
    Prime469.canonical (Prime469.input_get n t i).
Proof.
  induction n as [|n IH]; intros t i Ht Hi.
  - exact Ht.
  - destruct t as [l r].
    simpl in Ht.
    destruct Ht as [Hl Hr].
    cbn [Prime469.input_get].
    destruct (Nat.even i) eqn:Heven.
    + apply IH.
      * exact Hl.
      * rewrite Prime469.pow2_succ in Hi.
        apply Nat.even_spec in Heven.
        destruct Heven as [q ->].
        rewrite Nat.div2_even.
        lia.
    + apply IH.
      * exact Hr.
      * rewrite Prime469.pow2_succ in Hi.
        pose proof (Nat.negb_even i) as Hodd.
        rewrite Heven in Hodd.
        simpl in Hodd.
        symmetry in Hodd.
        apply Nat.odd_spec in Hodd.
        destruct Hodd as [q ->].
        replace (2 * q + 1)%nat with (S (2 * q)) by lia.
        rewrite Nat.div2_succ_double.
        lia.
Qed.

Lemma prime181_input_get_canonical :
  forall n (t : NTTTree.tree Prime181.int n) i,
    Prime181.canonical_tree n t ->
    (i < Prime181.pow2 n)%nat ->
    Prime181.canonical (Prime181.input_get n t i).
Proof.
  induction n as [|n IH]; intros t i Ht Hi.
  - exact Ht.
  - destruct t as [l r].
    simpl in Ht.
    destruct Ht as [Hl Hr].
    cbn [Prime181.input_get].
    destruct (Nat.even i) eqn:Heven.
    + apply IH.
      * exact Hl.
      * rewrite Prime181.pow2_succ in Hi.
        apply Nat.even_spec in Heven.
        destruct Heven as [q ->].
        rewrite Nat.div2_even.
        lia.
    + apply IH.
      * exact Hr.
      * rewrite Prime181.pow2_succ in Hi.
        pose proof (Nat.negb_even i) as Hodd.
        rewrite Heven in Hodd.
        simpl in Hodd.
        symmetry in Hodd.
        apply Nat.odd_spec in Hodd.
        destruct Hodd as [q ->].
        replace (2 * q + 1)%nat with (S (2 * q)) by lia.
        rewrite Nat.div2_succ_double.
        lia.
Qed.

Lemma prime469_canonical_zip_mul :
  forall n (x y : NTTTree.tree Prime469.int n),
    Prime469.canonical_tree n x ->
    Prime469.canonical_tree n y ->
    Prime469.canonical_tree n (Prime469.zip_tree n Prime469.mul_mod x y).
Proof.
  induction n as [|n IH]; intros x y Hx Hy.
  - apply Prime469.canonical_mul_mod.
  - destruct x as [xl xr], y as [yl yr].
    simpl in *.
    destruct Hx as [Hxl Hxr], Hy as [Hyl Hyr].
    split.
    + apply IH; assumption.
    + apply IH; assumption.
Qed.

Lemma prime181_canonical_zip_mul :
  forall n (x y : NTTTree.tree Prime181.int n),
    Prime181.canonical_tree n x ->
    Prime181.canonical_tree n y ->
    Prime181.canonical_tree n (Prime181.zip_tree n Prime181.mul_mod x y).
Proof.
  induction n as [|n IH]; intros x y Hx Hy.
  - apply Prime181.canonical_mul_mod.
  - destruct x as [xl xr], y as [yl yr].
    simpl in *.
    destruct Hx as [Hxl Hxr], Hy as [Hyl Hyr].
    split.
    + apply IH; assumption.
    + apply IH; assumption.
Qed.

Lemma prime469_canonical_zip_mul_fast :
  forall n (x y : NTTTree.tree Prime469.int n),
    Prime469.canonical_tree n x ->
    Prime469.canonical_tree n y ->
    Prime469.canonical_tree n (Prime469.zip_tree n Prime469.mul_mod_fast x y).
Proof.
  induction n as [|n IH]; intros x y Hx Hy.
  - cbn [Prime469.zip_tree].
    rewrite (Prime469.mul_mod_fast_eq x y Hx Hy).
    apply Prime469.canonical_mul_mod.
  - destruct x as [xl xr], y as [yl yr].
    simpl in *.
    destruct Hx as [Hxl Hxr], Hy as [Hyl Hyr].
    split.
    + apply IH; assumption.
    + apply IH; assumption.
Qed.

Lemma prime181_canonical_zip_mul_fast :
  forall n (x y : NTTTree.tree Prime181.int n),
    Prime181.canonical_tree n x ->
    Prime181.canonical_tree n y ->
    Prime181.canonical_tree n (Prime181.zip_tree n Prime181.mul_mod_fast x y).
Proof.
  induction n as [|n IH]; intros x y Hx Hy.
  - cbn [Prime181.zip_tree].
    rewrite (Prime181.mul_mod_fast_eq x y Hx Hy).
    apply Prime181.canonical_mul_mod.
  - destruct x as [xl xr], y as [yl yr].
    simpl in *.
    destruct Hx as [Hxl Hxr], Hy as [Hyl Hyr].
    split.
    + apply IH; assumption.
    + apply IH; assumption.
Qed.

Lemma prime469_inv_pow2_canonical :
  forall n, Prime469.canonical (Prime469.inv_pow2 n).
Proof.
  intro n.
  unfold Prime469.canonical, Prime469.value, Prime469.modulus_z.
  exact (Prime469Cfg.inv_pow2_range n).
Qed.

Lemma prime181_inv_pow2_canonical :
  forall n, Prime181.canonical (Prime181.inv_pow2 n).
Proof.
  intro n.
  unfold Prime181.canonical, Prime181.value, Prime181.modulus_z.
  exact (Prime181Cfg.inv_pow2_range n).
Qed.

Lemma prime469_canonical_intt :
  forall n (t : NTTTree.tree Prime469.int n),
    Prime469.canonical_tree n t ->
    Prime469.canonical_tree n (Prime469.intt n t).
Proof.
  intros n t Ht.
  unfold Prime469.intt.
  apply Prime469.canonical_scale_tree.
  - apply prime469_inv_pow2_canonical.
  - apply Prime469.canonical_intt_raw.
    exact Ht.
Qed.

Lemma prime181_canonical_intt :
  forall n (t : NTTTree.tree Prime181.int n),
    Prime181.canonical_tree n t ->
    Prime181.canonical_tree n (Prime181.intt n t).
Proof.
  intros n t Ht.
  unfold Prime181.intt.
  apply Prime181.canonical_scale_tree.
  - apply prime181_inv_pow2_canonical.
  - apply Prime181.canonical_intt_raw.
    exact Ht.
Qed.

Lemma prime469_convolution_blocks_canonical :
  forall k (a b : NTTTree.tree Prime469.block8 k),
    Prime469.canonical_tree (S (S (S k))) (Prime469.unpack_tree8 k a) ->
    Prime469.canonical_tree (S (S (S k))) (Prime469.unpack_tree8 k b) ->
    Prime469.canonical_tree (S (S (S k)))
      (Prime469.unpack_tree8 k (Prime469Ops.convolution_blocks k a b)).
Proof.
  intros k a b Ha Hb.
  rewrite prime469_convolution_blocks_eq_scalar.
  set (freq :=
    Prime469.zip_tree (S (S (S k))) Prime469.mul_mod_fast
      (Prime469.ntt_fast (S (S (S k))) (Prime469.unpack_tree8 k a))
      (Prime469.ntt_fast (S (S (S k))) (Prime469.unpack_tree8 k b))).
  assert (Hfreq : Prime469.canonical_tree (S (S (S k))) freq).
  {
    subst freq.
    apply prime469_canonical_zip_mul_fast.
    - rewrite Prime469.ntt_fast_eq by exact Ha.
      apply Prime469.canonical_ntt.
      exact Ha.
    - rewrite Prime469.ntt_fast_eq by exact Hb.
      apply Prime469.canonical_ntt.
      exact Hb.
  }
  rewrite (Prime469.intt_fast_eq (S (S (S k))) freq Hfreq).
  apply prime469_canonical_intt.
  exact Hfreq.
Qed.

Lemma prime181_convolution_blocks_canonical :
  forall k (a b : NTTTree.tree Prime181.block8 k),
    Prime181.canonical_tree (S (S (S k))) (Prime181.unpack_tree8 k a) ->
    Prime181.canonical_tree (S (S (S k))) (Prime181.unpack_tree8 k b) ->
    Prime181.canonical_tree (S (S (S k)))
      (Prime181.unpack_tree8 k (Prime181Ops.convolution_blocks k a b)).
Proof.
  intros k a b Ha Hb.
  rewrite prime181_convolution_blocks_eq_scalar.
  set (freq :=
    Prime181.zip_tree (S (S (S k))) Prime181.mul_mod_fast
      (Prime181.ntt_fast (S (S (S k))) (Prime181.unpack_tree8 k a))
      (Prime181.ntt_fast (S (S (S k))) (Prime181.unpack_tree8 k b))).
  assert (Hfreq : Prime181.canonical_tree (S (S (S k))) freq).
  {
    subst freq.
    apply prime181_canonical_zip_mul_fast.
    - rewrite Prime181.ntt_fast_eq by exact Ha.
      apply Prime181.canonical_ntt.
      exact Ha.
    - rewrite Prime181.ntt_fast_eq by exact Hb.
      apply Prime181.canonical_ntt.
      exact Hb.
  }
  rewrite (Prime181.intt_fast_eq (S (S (S k))) freq Hfreq).
  apply prime181_canonical_intt.
  exact Hfreq.
Qed.

Lemma prime469_convolution_coeff_at_range :
  forall k (a b : NTTTree.tree Prime469.block8 k) i,
    Prime469.canonical_tree (S (S (S k))) (Prime469.unpack_tree8 k a) ->
    Prime469.canonical_tree (S (S (S k))) (Prime469.unpack_tree8 k b) ->
    (i < Prime469.pow2 (S (S (S k))))%nat ->
    (0 <= Uint63.to_Z (prime469_coeff_at k (Prime469Ops.convolution_blocks k a b) i) < prime469_z)%Z.
Proof.
  intros k a b i Ha Hb Hi.
  unfold prime469_coeff_at.
  apply prime469_input_get_canonical.
  - apply prime469_convolution_blocks_canonical; assumption.
  - exact Hi.
Qed.

Lemma prime181_convolution_coeff_at_range :
  forall k (a b : NTTTree.tree Prime181.block8 k) i,
    Prime181.canonical_tree (S (S (S k))) (Prime181.unpack_tree8 k a) ->
    Prime181.canonical_tree (S (S (S k))) (Prime181.unpack_tree8 k b) ->
    (i < Prime181.pow2 (S (S (S k))))%nat ->
    (0 <= Uint63.to_Z (prime181_coeff_at k (Prime181Ops.convolution_blocks k a b) i) < prime181_z)%Z.
Proof.
  intros k a b i Ha Hb Hi.
  unfold prime181_coeff_at.
  apply prime181_input_get_canonical.
  - apply prime181_convolution_blocks_canonical; assumption.
  - exact Hi.
Qed.
