From Coq Require Import Uint63 ZArith Lia Lists.List Array.PArray.
Require Import BigInt.NTTConcrete BigInt.NTTKernelBounded BigInt.BigIntMul BigInt.BigIntMulProof BigInt.BigIntMulCanonical
  BigInt.BigIntMulCompose BigInt.BigIntMulConvolutionBridge BigInt.BigIntMulConvolutionCanonical
  BigInt.BigIntMulCRTArrayExact BigInt.BigIntMulCoefficients BigInt.BigIntMulCyclic BigInt.BigIntMulResidues.

Import ListNotations.
Local Open Scope Z_scope.

Module Prime469KB := TreeNTTKernelBounded(Prime469Cfg).
Module Prime181KB := TreeNTTKernelBounded(Prime181Cfg).

Definition prime469_scalar_freq (k : nat) (a b : bigint) : NTTTree.tree Prime469.int (S (S (S k))) :=
  Prime469.zip_tree (S (S (S k))) Prime469.mul_mod_fast
    (Prime469.ntt_fast (S (S (S k))) (Prime469.unpack_tree8 k (build_tree469 k a)))
    (Prime469.ntt_fast (S (S (S k))) (Prime469.unpack_tree8 k (build_tree469 k b))).

Definition prime181_scalar_freq (k : nat) (a b : bigint) : NTTTree.tree Prime181.int (S (S (S k))) :=
  Prime181.zip_tree (S (S (S k))) Prime181.mul_mod_fast
    (Prime181.ntt_fast (S (S (S k))) (Prime181.unpack_tree8 k (build_tree181 k a)))
    (Prime181.ntt_fast (S (S (S k))) (Prime181.unpack_tree8 k (build_tree181 k b))).

Definition prime469_scalar_freq_kb (k : nat) (a b : bigint) : NTTTree.tree Prime469KB.T.int (S (S (S k))) :=
  Prime469KB.T.zip_tree (S (S (S k))) Prime469KB.T.mul_mod_fast
    (Prime469KB.T.ntt_fast (S (S (S k))) (Prime469.unpack_tree8 k (build_tree469 k a)))
    (Prime469KB.T.ntt_fast (S (S (S k))) (Prime469.unpack_tree8 k (build_tree469 k b))).

Definition prime181_scalar_freq_kb (k : nat) (a b : bigint) : NTTTree.tree Prime181KB.T.int (S (S (S k))) :=
  Prime181KB.T.zip_tree (S (S (S k))) Prime181KB.T.mul_mod_fast
    (Prime181KB.T.ntt_fast (S (S (S k))) (Prime181.unpack_tree8 k (build_tree181 k a)))
    (Prime181KB.T.ntt_fast (S (S (S k))) (Prime181.unpack_tree8 k (build_tree181 k b))).

Lemma prime469_mul_mod_fast_kb_eq :
  forall x y,
    Prime469.canonical x ->
    Prime469.canonical y ->
    Prime469.mul_mod_fast x y = Prime469KB.T.mul_mod_fast x y.
Proof.
  intros x y Hx Hy.
  rewrite Prime469.mul_mod_fast_eq by assumption.
  rewrite Prime469KB.T.mul_mod_fast_eq by assumption.
  reflexivity.
Defined.

Lemma prime181_mul_mod_fast_kb_eq :
  forall x y,
    Prime181.canonical x ->
    Prime181.canonical y ->
    Prime181.mul_mod_fast x y = Prime181KB.T.mul_mod_fast x y.
Proof.
  intros x y Hx Hy.
  rewrite Prime181.mul_mod_fast_eq by assumption.
  rewrite Prime181KB.T.mul_mod_fast_eq by assumption.
  reflexivity.
Defined.

Lemma prime469_ntt_eq_kb :
  forall n (t : NTTTree.tree Prime469.int n),
    Prime469.ntt n t = Prime469KB.T.ntt n t.
Proof.
  intros n t.
  reflexivity.
Qed.

Lemma prime181_ntt_eq_kb :
  forall n (t : NTTTree.tree Prime181.int n),
    Prime181.ntt n t = Prime181KB.T.ntt n t.
Proof.
  intros n t.
  reflexivity.
Qed.

Lemma prime469_intt_eq_kb :
  forall n (t : NTTTree.tree Prime469.int n),
    Prime469.intt n t = Prime469KB.T.intt n t.
Proof.
  intros n t.
  reflexivity.
Qed.

Lemma prime181_intt_eq_kb :
  forall n (t : NTTTree.tree Prime181.int n),
    Prime181.intt n t = Prime181KB.T.intt n t.
Proof.
  intros n t.
  reflexivity.
Qed.

Lemma prime469_intt_point_eq_kb :
  forall n (t : NTTTree.tree Prime469.int n) i,
    Prime469.value (Prime469.input_get n (Prime469.intt n t) i) =
    Prime469KB.T.value (Prime469KB.T.input_get n (Prime469KB.T.intt n t) i).
Proof.
  intros n t i.
  rewrite prime469_intt_eq_kb.
  reflexivity.
Qed.

Lemma prime181_intt_point_eq_kb :
  forall n (t : NTTTree.tree Prime181.int n) i,
    Prime181.value (Prime181.input_get n (Prime181.intt n t) i) =
    Prime181KB.T.value (Prime181KB.T.input_get n (Prime181KB.T.intt n t) i).
Proof.
  intros n t i.
  rewrite prime181_intt_eq_kb.
  reflexivity.
Qed.

Lemma prime469_ntt_fast_eq_kb :
  forall n (t : NTTTree.tree Prime469.int n),
    Prime469.canonical_tree n t ->
    Prime469.ntt_fast n t = Prime469KB.T.ntt_fast n t.
Proof.
  intros n t Ht.
  rewrite Prime469.ntt_fast_eq by exact Ht.
  rewrite Prime469KB.T.ntt_fast_eq by exact Ht.
  apply prime469_ntt_eq_kb.
Qed.

Lemma prime181_ntt_fast_eq_kb :
  forall n (t : NTTTree.tree Prime181.int n),
    Prime181.canonical_tree n t ->
    Prime181.ntt_fast n t = Prime181KB.T.ntt_fast n t.
Proof.
  intros n t Ht.
  rewrite Prime181.ntt_fast_eq by exact Ht.
  rewrite Prime181KB.T.ntt_fast_eq by exact Ht.
  apply prime181_ntt_eq_kb.
Qed.

Lemma prime469_canonical_zip_tree_mul_mod_fast :
  forall n (x y : NTTTree.tree Prime469.int n),
    Prime469.canonical_tree n x ->
    Prime469.canonical_tree n y ->
    Prime469.canonical_tree n (Prime469.zip_tree n Prime469.mul_mod_fast x y).
Proof.
  induction n as [|n IH]; intros x y Hx Hy.
  - apply Prime469.canonical_mul_mod_fast; assumption.
  - destruct x as [xl xr], y as [yl yr].
    simpl in *.
    destruct Hx as [Hxl Hxr].
    destruct Hy as [Hyl Hyr].
    split.
    + apply IH; assumption.
    + apply IH; assumption.
Qed.

Lemma prime181_canonical_zip_tree_mul_mod_fast :
  forall n (x y : NTTTree.tree Prime181.int n),
    Prime181.canonical_tree n x ->
    Prime181.canonical_tree n y ->
    Prime181.canonical_tree n (Prime181.zip_tree n Prime181.mul_mod_fast x y).
Proof.
  induction n as [|n IH]; intros x y Hx Hy.
  - apply Prime181.canonical_mul_mod_fast; assumption.
  - destruct x as [xl xr], y as [yl yr].
    simpl in *.
    destruct Hx as [Hxl Hxr].
    destruct Hy as [Hyl Hyr].
    split.
    + apply IH; assumption.
    + apply IH; assumption.
Qed.

Lemma prime469_zip_tree_mul_mod_fast_kb_eq :
  forall n (x y : NTTTree.tree Prime469.int n),
    Prime469.canonical_tree n x ->
    Prime469.canonical_tree n y ->
    Prime469.zip_tree n Prime469.mul_mod_fast x y =
    Prime469.zip_tree n Prime469KB.T.mul_mod_fast x y.
Proof.
  induction n as [|n IH]; intros x y Hx Hy.
  - apply prime469_mul_mod_fast_kb_eq; assumption.
  - destruct x as [xl xr], y as [yl yr].
    cbn [Prime469.zip_tree] in *.
    destruct Hx as [Hxl Hxr].
    destruct Hy as [Hyl Hyr].
    rewrite (IH xl yl Hxl Hyl).
    rewrite (IH xr yr Hxr Hyr).
    reflexivity.
Qed.

Lemma prime181_zip_tree_mul_mod_fast_kb_eq :
  forall n (x y : NTTTree.tree Prime181.int n),
    Prime181.canonical_tree n x ->
    Prime181.canonical_tree n y ->
    Prime181.zip_tree n Prime181.mul_mod_fast x y =
    Prime181.zip_tree n Prime181KB.T.mul_mod_fast x y.
Proof.
  induction n as [|n IH]; intros x y Hx Hy.
  - apply prime181_mul_mod_fast_kb_eq; assumption.
  - destruct x as [xl xr], y as [yl yr].
    cbn [Prime181.zip_tree] in *.
    destruct Hx as [Hxl Hxr].
    destruct Hy as [Hyl Hyr].
    rewrite (IH xl yl Hxl Hyl).
    rewrite (IH xr yr Hxr Hyr).
    reflexivity.
Qed.

Lemma prime469_scalar_freq_tree_eq_kb :
  forall n (x y : NTTTree.tree Prime469.int n),
    Prime469.canonical_tree n x ->
    Prime469.canonical_tree n y ->
    Prime469.zip_tree n Prime469.mul_mod_fast
      (Prime469.ntt_fast n x) (Prime469.ntt_fast n y) =
    Prime469KB.T.zip_tree n Prime469KB.T.mul_mod_fast
      (Prime469KB.T.ntt_fast n x) (Prime469KB.T.ntt_fast n y).
Proof.
  intros n x y Hx Hy.
  rewrite <- (prime469_ntt_fast_eq_kb n x Hx).
  rewrite <- (prime469_ntt_fast_eq_kb n y Hy).
  assert (Hfx : Prime469.canonical_tree n (Prime469.ntt_fast n x)).
  {
    rewrite Prime469.ntt_fast_eq by exact Hx.
    apply Prime469.canonical_ntt.
    exact Hx.
  }
  assert (Hfy : Prime469.canonical_tree n (Prime469.ntt_fast n y)).
  {
    rewrite Prime469.ntt_fast_eq by exact Hy.
    apply Prime469.canonical_ntt.
    exact Hy.
  }
  apply prime469_zip_tree_mul_mod_fast_kb_eq; assumption.
Qed.

Lemma prime181_scalar_freq_tree_eq_kb :
  forall n (x y : NTTTree.tree Prime181.int n),
    Prime181.canonical_tree n x ->
    Prime181.canonical_tree n y ->
    Prime181.zip_tree n Prime181.mul_mod_fast
      (Prime181.ntt_fast n x) (Prime181.ntt_fast n y) =
    Prime181KB.T.zip_tree n Prime181KB.T.mul_mod_fast
      (Prime181KB.T.ntt_fast n x) (Prime181KB.T.ntt_fast n y).
Proof.
  intros n x y Hx Hy.
  rewrite <- (prime181_ntt_fast_eq_kb n x Hx).
  rewrite <- (prime181_ntt_fast_eq_kb n y Hy).
  assert (Hfx : Prime181.canonical_tree n (Prime181.ntt_fast n x)).
  {
    rewrite Prime181.ntt_fast_eq by exact Hx.
    apply Prime181.canonical_ntt.
    exact Hx.
  }
  assert (Hfy : Prime181.canonical_tree n (Prime181.ntt_fast n y)).
  {
    rewrite Prime181.ntt_fast_eq by exact Hy.
    apply Prime181.canonical_ntt.
    exact Hy.
  }
  apply prime181_zip_tree_mul_mod_fast_kb_eq; assumption.
Qed.

Lemma prime469_scalar_freq_tree_canonical :
  forall n (x y : NTTTree.tree Prime469.int n),
    Prime469.canonical_tree n x ->
    Prime469.canonical_tree n y ->
    Prime469.canonical_tree n
      (Prime469.zip_tree n Prime469.mul_mod_fast
         (Prime469.ntt_fast n x) (Prime469.ntt_fast n y)).
Proof.
  intros n x y Hx Hy.
  rewrite Prime469.ntt_fast_eq by exact Hx.
  rewrite Prime469.ntt_fast_eq by exact Hy.
  exact
    (prime469_canonical_zip_tree_mul_mod_fast n
       (Prime469.ntt n x) (Prime469.ntt n y)
       (Prime469.canonical_ntt n x Hx)
       (Prime469.canonical_ntt n y Hy)).
Qed.

Lemma prime181_scalar_freq_tree_canonical :
  forall n (x y : NTTTree.tree Prime181.int n),
    Prime181.canonical_tree n x ->
    Prime181.canonical_tree n y ->
    Prime181.canonical_tree n
      (Prime181.zip_tree n Prime181.mul_mod_fast
         (Prime181.ntt_fast n x) (Prime181.ntt_fast n y)).
Proof.
  intros n x y Hx Hy.
  rewrite Prime181.ntt_fast_eq by exact Hx.
  rewrite Prime181.ntt_fast_eq by exact Hy.
  exact
    (prime181_canonical_zip_tree_mul_mod_fast n
       (Prime181.ntt n x) (Prime181.ntt n y)
       (Prime181.canonical_ntt n x Hx)
       (Prime181.canonical_ntt n y Hy)).
Qed.

Lemma prime469_scalar_cyclic_tree_of_kb :
  forall n (x y : NTTTree.tree Prime469.int n) i,
    Prime469.canonical_tree n x ->
    Prime469.canonical_tree n y ->
    (i < Prime469.pow2 n)%nat ->
    Prime469KB.T.value
      (Prime469KB.T.input_get n
        (Prime469KB.T.intt_fast n
          (Prime469KB.T.zip_tree n Prime469KB.T.mul_mod_fast
            (Prime469KB.T.ntt_fast n x)
            (Prime469KB.T.ntt_fast n y))) i) =
    Prime469Conv.cyclic_convolution n x y i ->
    Prime469.value
      (Prime469.input_get n
        (Prime469.intt_fast n
          (Prime469.zip_tree n Prime469.mul_mod_fast
            (Prime469.ntt_fast n x)
            (Prime469.ntt_fast n y))) i) =
    Prime469Conv.cyclic_convolution n x y i.
Proof.
  intros n x y i Hx Hy Hi Hscalar.
  pose proof (prime469_scalar_freq_tree_eq_kb n x y Hx Hy) as Hfreq_eq.
  pose proof (prime469_scalar_freq_tree_canonical n x y Hx Hy) as Hfreq_canon.
  rewrite Prime469.intt_fast_eq by exact Hfreq_canon.
  rewrite Prime469KB.T.intt_fast_eq in Hscalar.
  2:{
    rewrite <- Hfreq_eq.
    exact Hfreq_canon.
  }
  rewrite <- Hfreq_eq in Hscalar.
  change
    (Prime469KB.T.value
       (Prime469KB.T.input_get n
          (Prime469KB.T.intt n
             (Prime469.zip_tree n Prime469.mul_mod_fast
                (Prime469.ntt_fast n x)
                (Prime469.ntt_fast n y))) i) =
     Prime469Conv.cyclic_convolution n x y i)
    in Hscalar.
  eapply eq_trans.
  - apply prime469_intt_point_eq_kb.
  - exact Hscalar.
Qed.

Lemma prime181_scalar_cyclic_tree_of_kb :
  forall n (x y : NTTTree.tree Prime181.int n) i,
    Prime181.canonical_tree n x ->
    Prime181.canonical_tree n y ->
    (i < Prime181.pow2 n)%nat ->
    Prime181KB.T.value
      (Prime181KB.T.input_get n
        (Prime181KB.T.intt_fast n
          (Prime181KB.T.zip_tree n Prime181KB.T.mul_mod_fast
            (Prime181KB.T.ntt_fast n x)
            (Prime181KB.T.ntt_fast n y))) i) =
    Prime181Conv.cyclic_convolution n x y i ->
    Prime181.value
      (Prime181.input_get n
        (Prime181.intt_fast n
          (Prime181.zip_tree n Prime181.mul_mod_fast
            (Prime181.ntt_fast n x)
            (Prime181.ntt_fast n y))) i) =
    Prime181Conv.cyclic_convolution n x y i.
Proof.
  intros n x y i Hx Hy Hi Hscalar.
  pose proof (prime181_scalar_freq_tree_eq_kb n x y Hx Hy) as Hfreq_eq.
  pose proof (prime181_scalar_freq_tree_canonical n x y Hx Hy) as Hfreq_canon.
  rewrite Prime181.intt_fast_eq by exact Hfreq_canon.
  rewrite Prime181KB.T.intt_fast_eq in Hscalar.
  2:{
    rewrite <- Hfreq_eq.
    exact Hfreq_canon.
  }
  rewrite <- Hfreq_eq in Hscalar.
  change
    (Prime181KB.T.value
       (Prime181KB.T.input_get n
          (Prime181KB.T.intt n
             (Prime181.zip_tree n Prime181.mul_mod_fast
                (Prime181.ntt_fast n x)
                (Prime181.ntt_fast n y))) i) =
     Prime181Conv.cyclic_convolution n x y i)
    in Hscalar.
  eapply eq_trans.
  - apply prime181_intt_point_eq_kb.
  - exact Hscalar.
Qed.

Lemma prime469_residue_of_scalar_cyclic :
  forall a b i,
    canonical_bigint a ->
    canonical_bigint b ->
    a <> [] ->
    b <> [] ->
    Nat.leb (mul_total_log a b) supported_max_log = true ->
    (Z.of_nat (List.length a) <= Uint63.to_Z PArray.max_length)%Z ->
    (Z.of_nat (List.length b) <= Uint63.to_Z PArray.max_length)%Z ->
    (i < mul_needed_digits a b)%nat ->
    (forall j,
      (j < Prime469.pow2 (S (S (S (mul_block_log a b)))))%nat ->
      Prime469.value
        (Prime469.input_get (S (S (S (mul_block_log a b))))
          (Prime469.intt_fast (S (S (S (mul_block_log a b))))
            (prime469_scalar_freq (mul_block_log a b) a b)) j) =
      Prime469Conv.cyclic_convolution (S (S (S (mul_block_log a b))))
        (Prime469.unpack_tree8 (mul_block_log a b) (build_tree469 (mul_block_log a b) a))
        (Prime469.unpack_tree8 (mul_block_log a b) (build_tree469 (mul_block_log a b) b)) j) ->
    Uint63.to_Z
      (prime469_coeff_at (mul_block_log a b)
        (Prime469Ops.convolution_blocks (mul_block_log a b)
          (build_tree469 (mul_block_log a b) a)
          (build_tree469 (mul_block_log a b) b)) i) =
    Prime469.zcanon (convolution_coeff (bigint_digits_z a) (bigint_digits_z b) i).
Proof.
  intros a b i Ha Hb Hna Hnb Hlog HlenA HlenB Hi Hscalar.
  unfold prime469_coeff_at.
  rewrite prime469_convolution_blocks_eq_scalar.
  rewrite Hscalar.
  2:{
    replace (Prime469.pow2 (S (S (S (mul_block_log a b)))))
      with (Prime469.pow2 (mul_total_log a b)).
    2:{
      unfold mul_total_log, transform_log_of_block_log.
      f_equal.
      lia.
    }
    eapply Nat.lt_le_trans; [exact Hi|].
    apply mul_needed_digits_le_transform_size; assumption.
  }
  apply prime469_cyclic_convolution_bigint_digits; try assumption.
  - apply mul_block_log_le_supported.
    exact Hlog.
  - rewrite !bigint_digits_z_length.
    unfold mul_needed_digits, mul_needed_blocks.
    replace (8 * Datatypes.length a + 8 * Datatypes.length b)%nat
      with (8 * (Datatypes.length a + Datatypes.length b))%nat by lia.
    replace (Prime469.pow2 (S (S (S (mul_block_log a b)))))
      with (Prime469.pow2 (mul_total_log a b)).
    2:{
      unfold mul_total_log, transform_log_of_block_log.
      f_equal.
      lia.
    }
    apply mul_needed_digits_le_transform_size; assumption.
  - eapply Nat.lt_le_trans; [exact Hi|].
    replace (Prime469.pow2 (S (S (S (mul_block_log a b)))))
      with (Prime469.pow2 (mul_total_log a b)).
    2:{
      unfold mul_total_log, transform_log_of_block_log.
      f_equal.
      lia.
    }
    apply mul_needed_digits_le_transform_size; assumption.
Qed.

Lemma prime181_residue_of_scalar_cyclic :
  forall a b i,
    canonical_bigint a ->
    canonical_bigint b ->
    a <> [] ->
    b <> [] ->
    Nat.leb (mul_total_log a b) supported_max_log = true ->
    (Z.of_nat (List.length a) <= Uint63.to_Z PArray.max_length)%Z ->
    (Z.of_nat (List.length b) <= Uint63.to_Z PArray.max_length)%Z ->
    (i < mul_needed_digits a b)%nat ->
    (forall j,
      (j < Prime181.pow2 (S (S (S (mul_block_log a b)))))%nat ->
      Prime181.value
        (Prime181.input_get (S (S (S (mul_block_log a b))))
          (Prime181.intt_fast (S (S (S (mul_block_log a b))))
            (prime181_scalar_freq (mul_block_log a b) a b)) j) =
      Prime181Conv.cyclic_convolution (S (S (S (mul_block_log a b))))
        (Prime181.unpack_tree8 (mul_block_log a b) (build_tree181 (mul_block_log a b) a))
        (Prime181.unpack_tree8 (mul_block_log a b) (build_tree181 (mul_block_log a b) b)) j) ->
    Uint63.to_Z
      (prime181_coeff_at (mul_block_log a b)
        (Prime181Ops.convolution_blocks (mul_block_log a b)
          (build_tree181 (mul_block_log a b) a)
          (build_tree181 (mul_block_log a b) b)) i) =
    Prime181.zcanon (convolution_coeff (bigint_digits_z a) (bigint_digits_z b) i).
Proof.
  intros a b i Ha Hb Hna Hnb Hlog HlenA HlenB Hi Hscalar.
  unfold prime181_coeff_at.
  rewrite prime181_convolution_blocks_eq_scalar.
  rewrite Hscalar.
  2:{
    replace (Prime181.pow2 (S (S (S (mul_block_log a b)))))
      with (Prime181.pow2 (mul_total_log a b)).
    2:{
      unfold mul_total_log, transform_log_of_block_log.
      f_equal.
      lia.
    }
    eapply Nat.lt_le_trans; [exact Hi|].
    apply mul_needed_digits_le_transform_size; assumption.
  }
  apply prime181_cyclic_convolution_bigint_digits; try assumption.
  - apply mul_block_log_le_supported.
    exact Hlog.
  - rewrite !bigint_digits_z_length.
    unfold mul_needed_digits, mul_needed_blocks.
    replace (8 * Datatypes.length a + 8 * Datatypes.length b)%nat
      with (8 * (Datatypes.length a + Datatypes.length b))%nat by lia.
    replace (Prime181.pow2 (S (S (S (mul_block_log a b)))))
      with (Prime181.pow2 (mul_total_log a b)).
    2:{
      unfold mul_total_log, transform_log_of_block_log.
      f_equal.
      lia.
    }
    apply mul_needed_digits_le_transform_size; assumption.
  - eapply Nat.lt_le_trans; [exact Hi|].
    replace (Prime181.pow2 (S (S (S (mul_block_log a b)))))
      with (Prime181.pow2 (mul_total_log a b)).
    2:{
      unfold mul_total_log, transform_log_of_block_log.
      f_equal.
      lia.
    }
    apply mul_needed_digits_le_transform_size; assumption.
Qed.

Theorem mul_bigint_correct_of_scalar_cyclic :
  forall a b,
    canonical_bigint a ->
    canonical_bigint b ->
    a <> [] ->
    b <> [] ->
    Nat.leb (mul_total_log a b) supported_max_log = true ->
    Nat.leb (mul_needed_digits a b) coeff_array_max_digits = true ->
    (forall j,
      (j < Prime469.pow2 (S (S (S (mul_block_log a b)))))%nat ->
      Prime469.value
        (Prime469.input_get (S (S (S (mul_block_log a b))))
          (Prime469.intt_fast (S (S (S (mul_block_log a b))))
            (prime469_scalar_freq (mul_block_log a b) a b)) j) =
      Prime469Conv.cyclic_convolution (S (S (S (mul_block_log a b))))
        (Prime469.unpack_tree8 (mul_block_log a b) (build_tree469 (mul_block_log a b) a))
        (Prime469.unpack_tree8 (mul_block_log a b) (build_tree469 (mul_block_log a b) b)) j) ->
    (forall j,
      (j < Prime181.pow2 (S (S (S (mul_block_log a b)))))%nat ->
      Prime181.value
        (Prime181.input_get (S (S (S (mul_block_log a b))))
          (Prime181.intt_fast (S (S (S (mul_block_log a b))))
            (prime181_scalar_freq (mul_block_log a b) a b)) j) =
      Prime181Conv.cyclic_convolution (S (S (S (mul_block_log a b))))
        (Prime181.unpack_tree8 (mul_block_log a b) (build_tree181 (mul_block_log a b) a))
        (Prime181.unpack_tree8 (mul_block_log a b) (build_tree181 (mul_block_log a b) b)) j) ->
    mul_bigint a b = Some (mul_bigint_result a b) /\
    bigint_value (mul_bigint_result a b) = bigint_value a * bigint_value b.
Proof.
  intros a b Ha Hb Hna Hnb Hlog Hdigits H469 H181.
  apply mul_bigint_correct_of_prime_zcanon_residues; try assumption.
  - intros i Hi.
    apply prime469_residue_of_scalar_cyclic; try assumption.
    + apply bigint_length_bound_max_length_left with (b := b).
      exact Hdigits.
    + apply bigint_length_bound_max_length_right with (a := a).
      exact Hdigits.
  - intros i Hi.
    apply prime181_residue_of_scalar_cyclic; try assumption.
    + apply bigint_length_bound_max_length_left with (b := b).
      exact Hdigits.
    + apply bigint_length_bound_max_length_right with (a := a).
      exact Hdigits.
Qed.

Theorem mul_bigint_correct_of_scalar_cyclic_kb :
  forall a b,
    canonical_bigint a ->
    canonical_bigint b ->
    a <> [] ->
    b <> [] ->
    Nat.leb (mul_total_log a b) supported_max_log = true ->
    Nat.leb (mul_needed_digits a b) coeff_array_max_digits = true ->
    (forall j,
      (j < Prime469.pow2 (S (S (S (mul_block_log a b)))))%nat ->
      Prime469KB.T.value
        (Prime469KB.T.input_get (S (S (S (mul_block_log a b))))
          (Prime469KB.T.intt_fast (S (S (S (mul_block_log a b))))
            (prime469_scalar_freq_kb (mul_block_log a b) a b)) j) =
      Prime469Conv.cyclic_convolution (S (S (S (mul_block_log a b))))
        (Prime469.unpack_tree8 (mul_block_log a b) (build_tree469 (mul_block_log a b) a))
        (Prime469.unpack_tree8 (mul_block_log a b) (build_tree469 (mul_block_log a b) b)) j) ->
    (forall j,
      (j < Prime181.pow2 (S (S (S (mul_block_log a b)))))%nat ->
      Prime181KB.T.value
        (Prime181KB.T.input_get (S (S (S (mul_block_log a b))))
          (Prime181KB.T.intt_fast (S (S (S (mul_block_log a b))))
            (prime181_scalar_freq_kb (mul_block_log a b) a b)) j) =
      Prime181Conv.cyclic_convolution (S (S (S (mul_block_log a b))))
        (Prime181.unpack_tree8 (mul_block_log a b) (build_tree181 (mul_block_log a b) a))
        (Prime181.unpack_tree8 (mul_block_log a b) (build_tree181 (mul_block_log a b) b)) j) ->
    mul_bigint a b = Some (mul_bigint_result a b) /\
    bigint_value (mul_bigint_result a b) = bigint_value a * bigint_value b.
Proof.
  intros a b Ha Hb Hna Hnb Hlog Hdigits H469 H181.
  assert (H469' :
    forall j,
      (j < Prime469.pow2 (S (S (S (mul_block_log a b)))))%nat ->
      Prime469.value
        (Prime469.input_get (S (S (S (mul_block_log a b))))
          (Prime469.intt_fast (S (S (S (mul_block_log a b))))
            (prime469_scalar_freq (mul_block_log a b) a b)) j) =
      Prime469Conv.cyclic_convolution (S (S (S (mul_block_log a b))))
        (Prime469.unpack_tree8 (mul_block_log a b) (build_tree469 (mul_block_log a b) a))
        (Prime469.unpack_tree8 (mul_block_log a b) (build_tree469 (mul_block_log a b) b)) j).
  {
    intros j Hj.
    pose proof (bigint_length_bound_max_length_left a b Hdigits) as HlenA.
    pose proof (bigint_length_bound_max_length_right a b Hdigits) as HlenB.
    pose proof (mul_block_log_le_supported a b Hlog) as Hk.
    set (x := Prime469.unpack_tree8 (mul_block_log a b) (build_tree469 (mul_block_log a b) a)).
    set (y := Prime469.unpack_tree8 (mul_block_log a b) (build_tree469 (mul_block_log a b) b)).
    change
      (Prime469.value
         (Prime469.input_get (S (S (S (mul_block_log a b))))
            (Prime469.intt_fast (S (S (S (mul_block_log a b))))
               (Prime469.zip_tree (S (S (S (mul_block_log a b)))) Prime469.mul_mod_fast
                  (Prime469.ntt_fast (S (S (S (mul_block_log a b)))) x)
                  (Prime469.ntt_fast (S (S (S (mul_block_log a b)))) y))) j) =
       Prime469Conv.cyclic_convolution (S (S (S (mul_block_log a b)))) x y j).
    eapply prime469_scalar_cyclic_tree_of_kb.
    - apply build_tree469_canonical; assumption.
    - apply build_tree469_canonical; assumption.
    - exact Hj.
    - change
        (Prime469KB.T.value
           (Prime469KB.T.input_get (S (S (S (mul_block_log a b))))
              (Prime469KB.T.intt_fast (S (S (S (mul_block_log a b))))
                 (Prime469KB.T.zip_tree (S (S (S (mul_block_log a b)))) Prime469KB.T.mul_mod_fast
                    (Prime469KB.T.ntt_fast (S (S (S (mul_block_log a b)))) x)
                    (Prime469KB.T.ntt_fast (S (S (S (mul_block_log a b)))) y))) j) =
         Prime469Conv.cyclic_convolution (S (S (S (mul_block_log a b)))) x y j).
      exact (H469 j Hj).
  }
  assert (H181' :
    forall j,
      (j < Prime181.pow2 (S (S (S (mul_block_log a b)))))%nat ->
      Prime181.value
        (Prime181.input_get (S (S (S (mul_block_log a b))))
          (Prime181.intt_fast (S (S (S (mul_block_log a b))))
            (prime181_scalar_freq (mul_block_log a b) a b)) j) =
      Prime181Conv.cyclic_convolution (S (S (S (mul_block_log a b))))
        (Prime181.unpack_tree8 (mul_block_log a b) (build_tree181 (mul_block_log a b) a))
        (Prime181.unpack_tree8 (mul_block_log a b) (build_tree181 (mul_block_log a b) b)) j).
  {
    intros j Hj.
    pose proof (bigint_length_bound_max_length_left a b Hdigits) as HlenA.
    pose proof (bigint_length_bound_max_length_right a b Hdigits) as HlenB.
    pose proof (mul_block_log_le_supported a b Hlog) as Hk.
    set (x := Prime181.unpack_tree8 (mul_block_log a b) (build_tree181 (mul_block_log a b) a)).
    set (y := Prime181.unpack_tree8 (mul_block_log a b) (build_tree181 (mul_block_log a b) b)).
    change
      (Prime181.value
         (Prime181.input_get (S (S (S (mul_block_log a b))))
            (Prime181.intt_fast (S (S (S (mul_block_log a b))))
               (Prime181.zip_tree (S (S (S (mul_block_log a b)))) Prime181.mul_mod_fast
                  (Prime181.ntt_fast (S (S (S (mul_block_log a b)))) x)
                  (Prime181.ntt_fast (S (S (S (mul_block_log a b)))) y))) j) =
       Prime181Conv.cyclic_convolution (S (S (S (mul_block_log a b)))) x y j).
    eapply prime181_scalar_cyclic_tree_of_kb.
    - apply build_tree181_canonical; assumption.
    - apply build_tree181_canonical; assumption.
    - exact Hj.
    - change
        (Prime181KB.T.value
           (Prime181KB.T.input_get (S (S (S (mul_block_log a b))))
              (Prime181KB.T.intt_fast (S (S (S (mul_block_log a b))))
                 (Prime181KB.T.zip_tree (S (S (S (mul_block_log a b)))) Prime181KB.T.mul_mod_fast
                    (Prime181KB.T.ntt_fast (S (S (S (mul_block_log a b)))) x)
                    (Prime181KB.T.ntt_fast (S (S (S (mul_block_log a b)))) y))) j) =
         Prime181Conv.cyclic_convolution (S (S (S (mul_block_log a b)))) x y j).
      exact (H181 j Hj).
  }
  eapply mul_bigint_correct_of_scalar_cyclic; eauto.
Qed.
