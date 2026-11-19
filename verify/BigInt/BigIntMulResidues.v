From Coq Require Import Uint63 ZArith Lia Lists.List Array.PArray.
Require Import BigInt.NTTConcrete BigInt.BigIntMul BigInt.BigIntMulProof BigInt.BigIntMulCanonical BigInt.BigIntMulCompose
  BigInt.BigIntMulCRTArrayExact BigInt.BigIntMulCRTPrefix BigInt.BigIntMulCRTExact
  BigInt.BigIntMulConvolutionCanonical BigInt.BigIntMulNormalizeArithmetic
  BigInt.BigIntMulCoefficients BigInt.BigIntMulCoeffExact BigInt.BigIntMulCoeffExactFinal.

Import ListNotations.
Local Open Scope Z_scope.

Lemma mul_block_log_le_supported :
  forall a b,
    Nat.leb (mul_total_log a b) supported_max_log = true ->
    (mul_block_log a b <= supported_max_block_log)%nat.
Proof.
  intros a b Hlog.
  apply Nat.leb_le in Hlog.
  unfold mul_total_log, transform_log_of_block_log, supported_max_log,
    mul_block_log, supported_max_block_log in *.
  lia.
Qed.

Lemma bigint_length_bound_max_length_left :
  forall a b,
    Nat.leb (mul_needed_digits a b) coeff_array_max_digits = true ->
    (Z.of_nat (List.length a) <= Uint63.to_Z PArray.max_length)%Z.
Proof.
  intros a b Hdigits.
  assert (Hlen : (List.length a <= mul_needed_digits a b)%nat).
  {
    unfold mul_needed_digits, mul_needed_blocks.
    lia.
  }
  eapply Z.le_trans.
  - apply Nat2Z.inj_le.
    exact Hlen.
  - apply mul_needed_digits_bound_max_length.
    exact Hdigits.
Qed.

Lemma bigint_length_bound_max_length_right :
  forall a b,
    Nat.leb (mul_needed_digits a b) coeff_array_max_digits = true ->
    (Z.of_nat (List.length b) <= Uint63.to_Z PArray.max_length)%Z.
Proof.
  intros a b Hdigits.
  assert (Hlen : (List.length b <= mul_needed_digits a b)%nat).
  {
    unfold mul_needed_digits, mul_needed_blocks.
    lia.
  }
  eapply Z.le_trans.
  - apply Nat2Z.inj_le.
    exact Hlen.
  - apply mul_needed_digits_bound_max_length.
    exact Hdigits.
Qed.

Lemma mul_needed_digits_le_transform_size :
  forall a b,
    a <> [] ->
    b <> [] ->
    (mul_needed_digits a b <= Prime469.pow2 (mul_total_log a b))%nat.
Proof.
  intros a b Hna Hnb.
  pose proof (block_log_bound (mul_needed_blocks a b)) as Hbound.
  assert (Hpos : (1 <= mul_needed_blocks a b)%nat).
  {
    unfold mul_needed_blocks.
    destruct a as [|a0 a']; [contradiction|].
    destruct b as [|b0 b']; [contradiction|].
    simpl.
    lia.
  }
  assert (Hblocks : (mul_needed_blocks a b <= Nat.pow 2 (mul_block_log a b))%nat).
  {
    unfold mul_block_log in Hbound.
    replace (Nat.max 1 (mul_needed_blocks a b)) with (mul_needed_blocks a b) in Hbound by lia.
    exact Hbound.
  }
  change (Nat.pow 2 (mul_block_log a b)) with (Prime469.pow2 (mul_block_log a b)) in Hblocks.
  unfold mul_needed_digits, mul_total_log, transform_log_of_block_log.
  replace (mul_block_log a b + 3)%nat with (S (S (S (mul_block_log a b)))) by lia.
  repeat rewrite Prime469.pow2_succ.
  lia.
Qed.

Lemma coeff_array_at_mul_coeff_array_get :
  forall a b i,
    Nat.leb (mul_total_log a b) supported_max_log = true ->
    Nat.leb (mul_needed_digits a b) coeff_array_max_digits = true ->
    (i < mul_needed_digits a b)%nat ->
    coeff_array_at (mul_coeff_array a b) (u63_of_nat i) =
    PArray.get (mul_coeff_array a b) (u63_of_nat i).
Proof.
  intros a b i Hlog Hdigits Hlt.
  unfold coeff_array_at.
  rewrite (mul_coeff_array_length a b Hdigits).
  assert (HiB : (Z.of_nat i < Uint63.wB)%Z).
  {
    eapply Z.lt_trans.
    - apply Nat2Z.inj_lt.
      exact Hlt.
    - apply mul_needed_digits_lt_wB.
      exact Hlog.
  }
  assert (HlenB : (Z.of_nat (mul_needed_digits a b) < Uint63.wB)%Z).
  {
    apply mul_needed_digits_lt_wB.
    exact Hlog.
  }
  assert (Hltb :
    Uint63.ltb (u63_of_nat i) (u63_of_nat (mul_needed_digits a b)) = true).
  {
    apply Uint63.ltb_spec.
    rewrite !u63_of_nat_small by assumption.
    lia.
  }
  rewrite Hltb.
  reflexivity.
Qed.

Lemma prime469_zcanon_modulo :
  forall z,
    Prime469.zcanon z = Z.modulo z prime469_z.
Proof.
  intro z.
  unfold Prime469.zcanon, prime469_z, Prime469.modulus_z.
  reflexivity.
Qed.

Lemma prime181_zcanon_modulo :
  forall z,
    Prime181.zcanon z = Z.modulo z prime181_z.
Proof.
  intro z.
  unfold Prime181.zcanon, prime181_z, Prime181.modulus_z.
  reflexivity.
Qed.

Theorem mul_bigint_correct_of_prime_residues :
  forall a b,
    canonical_bigint a ->
    canonical_bigint b ->
    a <> [] ->
    b <> [] ->
    Nat.leb (mul_total_log a b) supported_max_log = true ->
    Nat.leb (mul_needed_digits a b) coeff_array_max_digits = true ->
    (forall i,
      (i < mul_needed_digits a b)%nat ->
      Z.modulo (convolution_coeff (bigint_digits_z a) (bigint_digits_z b) i) prime469_z =
      Uint63.to_Z
        (prime469_coeff_at (mul_block_log a b)
          (Prime469Ops.convolution_blocks (mul_block_log a b)
            (build_tree469 (mul_block_log a b) a)
            (build_tree469 (mul_block_log a b) b)) i)) ->
    (forall i,
      (i < mul_needed_digits a b)%nat ->
      Z.modulo (convolution_coeff (bigint_digits_z a) (bigint_digits_z b) i) prime181_z =
      Uint63.to_Z
        (prime181_coeff_at (mul_block_log a b)
          (Prime181Ops.convolution_blocks (mul_block_log a b)
            (build_tree181 (mul_block_log a b) a)
            (build_tree181 (mul_block_log a b) b)) i)) ->
    mul_bigint a b = Some (mul_bigint_result a b) /\
    bigint_value (mul_bigint_result a b) = bigint_value a * bigint_value b.
Proof.
  intros a b Ha Hb Hna Hnb Hlog Hdigits H469 H181.
  apply mul_bigint_correct_of_coeff_exact; try assumption.
  intros i Hlt.
  rewrite coeff_array_at_mul_coeff_array_get by assumption.
  unfold mul_coeff_array.
  set (k := mul_block_log a b).
  set (z := convolution_coeff (bigint_digits_z a) (bigint_digits_z b) i).
  pose proof
    (coeff_array_from_packed_trees_make_get_prefix
      k (mul_needed_digits a b)
      (Prime469Ops.convolution_blocks k (build_tree469 k a) (build_tree469 k b))
      (Prime181Ops.convolution_blocks k (build_tree181 k a) (build_tree181 k b))
      i)
    as Hprefix.
  rewrite Hprefix.
  2:{
    subst k.
    apply mul_block_log_le_supported.
    exact Hlog.
  }
  2:{
    apply mul_needed_digits_bound_max_length.
    exact Hdigits.
  }
  2:{
    apply mul_needed_digits_lt_wB.
    exact Hlog.
  }
  2: exact Hlt.
  2:{
    replace (Prime469.pow2 (S (S (S k)))) with (Prime469.pow2 (mul_total_log a b)).
    2:{
      subst k.
      unfold mul_total_log, transform_log_of_block_log.
      f_equal.
      lia.
    }
    eapply Nat.lt_le_trans; [exact Hlt|].
    apply mul_needed_digits_le_transform_size; assumption.
  }
  subst z.
  apply crt_combine_u63_exact.
  - apply prime469_convolution_coeff_at_range.
    + apply build_tree469_canonical.
      * subst k.
        apply mul_block_log_le_supported.
        exact Hlog.
      * exact Ha.
      * apply bigint_length_bound_max_length_left with (b := b).
        exact Hdigits.
    + apply build_tree469_canonical.
      * subst k.
        apply mul_block_log_le_supported.
        exact Hlog.
      * exact Hb.
      * apply bigint_length_bound_max_length_right with (a := a).
        exact Hdigits.
    + replace (Prime469.pow2 (S (S (S k)))) with (Prime469.pow2 (mul_total_log a b)).
      2:{
        subst k.
        unfold mul_total_log, transform_log_of_block_log.
        f_equal.
        lia.
      }
      eapply Nat.lt_le_trans; [exact Hlt|].
      apply mul_needed_digits_le_transform_size; assumption.
  - apply prime181_convolution_coeff_at_range.
    + apply build_tree181_canonical.
      * subst k.
        apply mul_block_log_le_supported.
        exact Hlog.
      * exact Ha.
      * apply bigint_length_bound_max_length_left with (b := b).
        exact Hdigits.
    + apply build_tree181_canonical.
      * subst k.
        apply mul_block_log_le_supported.
        exact Hlog.
      * exact Hb.
      * apply bigint_length_bound_max_length_right with (a := a).
        exact Hdigits.
    + replace (Prime181.pow2 (S (S (S k)))) with (Prime181.pow2 (mul_total_log a b)).
      2:{
        subst k.
        unfold mul_total_log, transform_log_of_block_log.
        f_equal.
        lia.
      }
      eapply Nat.lt_le_trans; [exact Hlt|].
      apply mul_needed_digits_le_transform_size; assumption.
  - apply convolution_coeff_crt_range; assumption.
  - apply H469.
    exact Hlt.
  - apply H181.
    exact Hlt.
Qed.

Theorem mul_bigint_correct_of_prime_zcanon_residues :
  forall a b,
    canonical_bigint a ->
    canonical_bigint b ->
    a <> [] ->
    b <> [] ->
    Nat.leb (mul_total_log a b) supported_max_log = true ->
    Nat.leb (mul_needed_digits a b) coeff_array_max_digits = true ->
    (forall i,
      (i < mul_needed_digits a b)%nat ->
      Uint63.to_Z
        (prime469_coeff_at (mul_block_log a b)
          (Prime469Ops.convolution_blocks (mul_block_log a b)
            (build_tree469 (mul_block_log a b) a)
            (build_tree469 (mul_block_log a b) b)) i) =
      Prime469.zcanon (convolution_coeff (bigint_digits_z a) (bigint_digits_z b) i)) ->
    (forall i,
      (i < mul_needed_digits a b)%nat ->
      Uint63.to_Z
        (prime181_coeff_at (mul_block_log a b)
          (Prime181Ops.convolution_blocks (mul_block_log a b)
            (build_tree181 (mul_block_log a b) a)
            (build_tree181 (mul_block_log a b) b)) i) =
      Prime181.zcanon (convolution_coeff (bigint_digits_z a) (bigint_digits_z b) i)) ->
    mul_bigint a b = Some (mul_bigint_result a b) /\
    bigint_value (mul_bigint_result a b) = bigint_value a * bigint_value b.
Proof.
  intros a b Ha Hb Hna Hnb Hlog Hdigits H469 H181.
  apply mul_bigint_correct_of_prime_residues; try assumption.
  - intros i Hi.
    rewrite <- prime469_zcanon_modulo.
    symmetry.
    apply H469.
    exact Hi.
  - intros i Hi.
    rewrite <- prime181_zcanon_modulo.
    symmetry.
    apply H181.
    exact Hi.
Qed.
