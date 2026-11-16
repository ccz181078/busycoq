From Coq Require Import Uint63 ZArith Lia Lists.List.
Require Import BigInt.NTTConcrete BigInt.NTTKernelBounded BigInt.BigIntMulScalarReduction
  BigInt.NTTConcrete181Supported BigInt.BigIntMul BigInt.BigIntMulProof
  BigInt.BigIntMulCanonical BigInt.BigIntMulCompose BigInt.BigIntMulCyclic
  BigInt.BigIntMulResidues.

Import ListNotations.
Local Open Scope Z_scope.

Module Prime181KB := BigIntMulScalarReduction.Prime181KB.

Lemma prime181_zip_tree_mul_mod_fast_eq :
  forall n (x y : NTTTree.tree Prime181.int n),
    Prime181.canonical_tree n x ->
    Prime181.canonical_tree n y ->
    Prime181.zip_tree n Prime181.mul_mod_fast x y =
    Prime181.zip_tree n Prime181.mul_mod x y.
Proof.
  induction n as [|n IH]; intros x y Hx Hy.
  - apply Prime181.mul_mod_fast_eq; assumption.
  - destruct x as [xl xr].
    destruct y as [yl yr].
    simpl in *.
    destruct Hx as [Hxl Hxr].
    destruct Hy as [Hyl Hyr].
    f_equal.
    + apply IH; assumption.
    + apply IH; assumption.
Qed.

Lemma prime181_kb_zip_tree_mul_mod_fast_eq :
  forall n (x y : NTTTree.tree Prime181.int n),
    Prime181KB.T.canonical_tree n x ->
    Prime181KB.T.canonical_tree n y ->
    Prime181KB.T.zip_tree n Prime181KB.T.mul_mod_fast x y =
    Prime181KB.T.zip_tree n Prime181KB.T.mul_mod x y.
Proof.
  induction n as [|n IH]; intros x y Hx Hy.
  - apply Prime181KB.T.mul_mod_fast_eq; assumption.
  - destruct x as [xl xr].
    destruct y as [yl yr].
    simpl in *.
    destruct Hx as [Hxl Hxr].
    destruct Hy as [Hyl Hyr].
    f_equal.
    + apply IH; assumption.
    + apply IH; assumption.
Qed.

Theorem prime181_convolution_bounded_concrete_fast :
  forall n (x y : NTTTree.tree Prime181.int n) j,
    (n < S supported_max_log)%nat ->
    Prime181.canonical_tree n x ->
    Prime181.canonical_tree n y ->
    (j < Prime181.pow2 n)%nat ->
    Prime181KB.T.value
      (Prime181KB.T.input_get n
        (Prime181KB.T.intt_fast n
          (Prime181KB.T.zip_tree n Prime181KB.T.mul_mod_fast
            (Prime181KB.T.ntt_fast n x)
            (Prime181KB.T.ntt_fast n y))) j) =
    Prime181KB.Conv.cyclic_convolution n x y j.
Proof.
  intros n x y j Hn Hx Hy Hj.
  assert (HfreqX : Prime181KB.T.canonical_tree n (Prime181KB.T.ntt_fast n x)).
  {
    rewrite Prime181KB.T.ntt_fast_eq by exact Hx.
    apply Prime181KB.T.canonical_ntt.
    exact Hx.
  }
  assert (HfreqY : Prime181KB.T.canonical_tree n (Prime181KB.T.ntt_fast n y)).
  {
    rewrite Prime181KB.T.ntt_fast_eq by exact Hy.
    apply Prime181KB.T.canonical_ntt.
    exact Hy.
  }
  pose proof
    (Prime181KB.intt_fast_pointwise_mul_ntt_fast_cyclic_convolution_bounded
      (S supported_max_log)
      Prime181SupportedFacts.root_square_upto
      Prime181SupportedFacts.root_half_neg_upto
      Prime181SupportedFacts.inv_root_square_upto
      Prime181SupportedFacts.inv_root_half_neg_upto
      Prime181SupportedFacts.inv_root_as_root_pred_upto
      Prime181SupportedFacts.inv_pow2_zero
      Prime181SupportedFacts.inv_pow2_double_upto
      n x y j Hn Hx Hy Hj) as Hconv.
  rewrite <- (prime181_kb_zip_tree_mul_mod_fast_eq n
    (Prime181KB.T.ntt_fast n x) (Prime181KB.T.ntt_fast n y) HfreqX HfreqY) in Hconv.
  exact Hconv.
Qed.

Theorem prime181_scalar_cyclic_concrete_kb :
  forall a b j,
    canonical_bigint a ->
    canonical_bigint b ->
    a <> [] ->
    b <> [] ->
    Nat.leb (mul_total_log a b) supported_max_log = true ->
    Nat.leb (mul_needed_digits a b) coeff_array_max_digits = true ->
    (j < Prime181.pow2 (S (S (S (mul_block_log a b)))))%nat ->
    Prime181KB.T.value
      (Prime181KB.T.input_get (S (S (S (mul_block_log a b))))
        (Prime181KB.T.intt_fast (S (S (S (mul_block_log a b))))
          (prime181_scalar_freq_kb (mul_block_log a b) a b)) j) =
    Prime181Conv.cyclic_convolution (S (S (S (mul_block_log a b))))
      (Prime181.unpack_tree8 (mul_block_log a b) (build_tree181 (mul_block_log a b) a))
      (Prime181.unpack_tree8 (mul_block_log a b) (build_tree181 (mul_block_log a b) b)) j.
Proof.
  intros a b j Ha Hb Hna Hnb Hlog Hdigits Hj.
  set (k := mul_block_log a b).
  set (xa := Prime181.unpack_tree8 k (build_tree181 k a)).
  set (xb := Prime181.unpack_tree8 k (build_tree181 k b)).
  pose proof (mul_block_log_le_supported a b Hlog) as Hk.
  pose proof (bigint_length_bound_max_length_left a b Hdigits) as HlenA.
  pose proof (bigint_length_bound_max_length_right a b Hdigits) as HlenB.
  assert (Hn : (S (S (S k)) < S supported_max_log)%nat).
  {
    apply Nat.leb_le in Hlog.
    cbv [mul_total_log transform_log_of_block_log supported_max_log] in Hlog |- *.
    lia.
  }
  assert (HcanonA : Prime181.canonical_tree (S (S (S k))) xa).
  {
    subst xa k.
    apply build_tree181_canonical; assumption.
  }
  assert (HcanonB : Prime181.canonical_tree (S (S (S k))) xb).
  {
    subst xb k.
    apply build_tree181_canonical; assumption.
  }
  change
    (Prime181Conv.cyclic_convolution (S (S (S k))) xa xb j)
    with (Prime181KB.Conv.cyclic_convolution (S (S (S k))) xa xb j).
  unfold prime181_scalar_freq_kb.
  change (Prime181.unpack_tree8 k (build_tree181 k a)) with xa.
  change (Prime181.unpack_tree8 k (build_tree181 k b)) with xb.
  change (j < Prime181.pow2 (S (S (S k))))%nat in Hj.
  clear Hk HlenA HlenB.
  clear Ha Hb Hna Hnb Hlog Hdigits.
  clearbody k xa xb.
  apply (prime181_convolution_bounded_concrete_fast (S (S (S k))) xa xb j).
  - exact Hn.
  - exact HcanonA.
  - exact HcanonB.
  - exact Hj.
Qed.
