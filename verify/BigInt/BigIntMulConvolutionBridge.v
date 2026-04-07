From Coq Require Import Uint63 Lia.
Require Import BigInt.NTTTree BigInt.NTTConcrete BigInt.BigIntMul.

Lemma prime469_unpack_tree_scale_block :
  forall k c (t : tree Prime469.block8 k),
    Prime469.unpack_tree8 k (tree_map k (Prime469Ops.scale_block c) t) =
    Prime469.scale_tree_fast (S (S (S k))) c (Prime469.unpack_tree8 k t).
Proof.
  induction k as [|k IH]; intros c t.
  - destruct t as [x0 x1 x2 x3 x4 x5 x6 x7].
    reflexivity.
  - destruct t as [l r].
    cbn [tree_map Prime469.unpack_tree8 Prime469.scale_tree_fast].
    rewrite IH.
    rewrite IH.
    reflexivity.
Qed.

Lemma prime469_unpack_tree_mul_block :
  forall k (x y : tree Prime469.block8 k),
    Prime469.unpack_tree8 k (tree_zip k Prime469Ops.mul_block x y) =
    Prime469.zip_tree (S (S (S k))) Prime469.mul_mod_fast
      (Prime469.unpack_tree8 k x) (Prime469.unpack_tree8 k y).
Proof.
  induction k as [|k IH]; intros x y.
  - destruct x as [x0 x1 x2 x3 x4 x5 x6 x7].
    destruct y as [y0 y1 y2 y3 y4 y5 y6 y7].
    reflexivity.
  - destruct x as [xl xr], y as [yl yr].
    cbn [tree_zip Prime469.unpack_tree8 Prime469.zip_tree].
    rewrite IH.
    rewrite IH.
    reflexivity.
Qed.

Lemma prime469_ntt_block_eq_scalar :
  forall k (t : tree Prime469.block8 k),
    Prime469.unpack_tree8 k (Prime469.ntt_fast_block8_ge3 k t) =
    Prime469.ntt_fast (S (S (S k))) (Prime469.unpack_tree8 k t).
Proof.
  assert (Hpack_unpack :
    forall k (u : tree Prime469.block8 k),
      Prime469.pack_tree8 k (Prime469.unpack_tree8 k u) = u).
  {
    induction k as [|k IH]; intros u.
    - destruct u.
      reflexivity.
    - destruct u as [l r].
      cbn [Prime469.pack_tree8 Prime469.unpack_tree8].
      rewrite IH.
      rewrite IH.
      reflexivity.
  }
  intros k t.
  unfold Prime469.ntt_fast.
  cbn [Prime469.ntt_fast_record8].
  rewrite Hpack_unpack.
  reflexivity.
Qed.

Lemma prime469_intt_raw_block_eq_scalar :
  forall k (t : tree Prime469.block8 k),
    Prime469.unpack_tree8 k (Prime469.intt_fast_block8_ge3_raw k t) =
    Prime469.intt_fast_record8_raw (S (S (S k))) (Prime469.unpack_tree8 k t).
Proof.
  assert (Hpack_unpack :
    forall k (u : tree Prime469.block8 k),
      Prime469.pack_tree8 k (Prime469.unpack_tree8 k u) = u).
  {
    induction k as [|k IH]; intros u.
    - destruct u.
      reflexivity.
    - destruct u as [l r].
      cbn [Prime469.pack_tree8 Prime469.unpack_tree8].
      rewrite IH.
      rewrite IH.
      reflexivity.
  }
  intros k t.
  cbn [Prime469.intt_fast_record8_raw].
  rewrite Hpack_unpack.
  reflexivity.
Qed.

Lemma prime469_convolution_blocks_eq_scalar :
  forall k (a b : tree Prime469.block8 k),
    Prime469.unpack_tree8 k (Prime469Ops.convolution_blocks k a b) =
    Prime469.intt_fast (S (S (S k)))
      (Prime469.zip_tree (S (S (S k))) Prime469.mul_mod_fast
        (Prime469.ntt_fast (S (S (S k))) (Prime469.unpack_tree8 k a))
        (Prime469.ntt_fast (S (S (S k))) (Prime469.unpack_tree8 k b))).
Proof.
  intros k a b.
  unfold Prime469Ops.convolution_blocks.
  rewrite prime469_unpack_tree_scale_block.
  rewrite prime469_intt_raw_block_eq_scalar.
  rewrite prime469_unpack_tree_mul_block.
  rewrite prime469_ntt_block_eq_scalar.
  rewrite prime469_ntt_block_eq_scalar.
  unfold Prime469.intt_fast, Prime469.intt_fast_record8.
  unfold transform_log_of_block_log.
  replace (k + 3)%nat with (S (S (S k))) by lia.
  reflexivity.
Qed.

Lemma prime181_unpack_tree_scale_block :
  forall k c (t : tree Prime181.block8 k),
    Prime181.unpack_tree8 k (tree_map k (Prime181Ops.scale_block c) t) =
    Prime181.scale_tree_fast (S (S (S k))) c (Prime181.unpack_tree8 k t).
Proof.
  induction k as [|k IH]; intros c t.
  - destruct t as [x0 x1 x2 x3 x4 x5 x6 x7].
    reflexivity.
  - destruct t as [l r].
    cbn [tree_map Prime181.unpack_tree8 Prime181.scale_tree_fast].
    rewrite IH.
    rewrite IH.
    reflexivity.
Qed.

Lemma prime181_unpack_tree_mul_block :
  forall k (x y : tree Prime181.block8 k),
    Prime181.unpack_tree8 k (tree_zip k Prime181Ops.mul_block x y) =
    Prime181.zip_tree (S (S (S k))) Prime181.mul_mod_fast
      (Prime181.unpack_tree8 k x) (Prime181.unpack_tree8 k y).
Proof.
  induction k as [|k IH]; intros x y.
  - destruct x as [x0 x1 x2 x3 x4 x5 x6 x7].
    destruct y as [y0 y1 y2 y3 y4 y5 y6 y7].
    reflexivity.
  - destruct x as [xl xr], y as [yl yr].
    cbn [tree_zip Prime181.unpack_tree8 Prime181.zip_tree].
    rewrite IH.
    rewrite IH.
    reflexivity.
Qed.

Lemma prime181_ntt_block_eq_scalar :
  forall k (t : tree Prime181.block8 k),
    Prime181.unpack_tree8 k (Prime181.ntt_fast_block8_ge3 k t) =
    Prime181.ntt_fast (S (S (S k))) (Prime181.unpack_tree8 k t).
Proof.
  assert (Hpack_unpack :
    forall k (u : tree Prime181.block8 k),
      Prime181.pack_tree8 k (Prime181.unpack_tree8 k u) = u).
  {
    induction k as [|k IH]; intros u.
    - destruct u.
      reflexivity.
    - destruct u as [l r].
      cbn [Prime181.pack_tree8 Prime181.unpack_tree8].
      rewrite IH.
      rewrite IH.
      reflexivity.
  }
  intros k t.
  unfold Prime181.ntt_fast.
  cbn [Prime181.ntt_fast_record8].
  rewrite Hpack_unpack.
  reflexivity.
Qed.

Lemma prime181_intt_raw_block_eq_scalar :
  forall k (t : tree Prime181.block8 k),
    Prime181.unpack_tree8 k (Prime181.intt_fast_block8_ge3_raw k t) =
    Prime181.intt_fast_record8_raw (S (S (S k))) (Prime181.unpack_tree8 k t).
Proof.
  assert (Hpack_unpack :
    forall k (u : tree Prime181.block8 k),
      Prime181.pack_tree8 k (Prime181.unpack_tree8 k u) = u).
  {
    induction k as [|k IH]; intros u.
    - destruct u.
      reflexivity.
    - destruct u as [l r].
      cbn [Prime181.pack_tree8 Prime181.unpack_tree8].
      rewrite IH.
      rewrite IH.
      reflexivity.
  }
  intros k t.
  cbn [Prime181.intt_fast_record8_raw].
  rewrite Hpack_unpack.
  reflexivity.
Qed.

Lemma prime181_convolution_blocks_eq_scalar :
  forall k (a b : tree Prime181.block8 k),
    Prime181.unpack_tree8 k (Prime181Ops.convolution_blocks k a b) =
    Prime181.intt_fast (S (S (S k)))
      (Prime181.zip_tree (S (S (S k))) Prime181.mul_mod_fast
        (Prime181.ntt_fast (S (S (S k))) (Prime181.unpack_tree8 k a))
        (Prime181.ntt_fast (S (S (S k))) (Prime181.unpack_tree8 k b))).
Proof.
  intros k a b.
  unfold Prime181Ops.convolution_blocks.
  rewrite prime181_unpack_tree_scale_block.
  rewrite prime181_intt_raw_block_eq_scalar.
  rewrite prime181_unpack_tree_mul_block.
  rewrite prime181_ntt_block_eq_scalar.
  rewrite prime181_ntt_block_eq_scalar.
  unfold Prime181.intt_fast, Prime181.intt_fast_record8.
  unfold transform_log_of_block_log.
  replace (k + 3)%nat with (S (S (S k))) by lia.
  reflexivity.
Qed.
