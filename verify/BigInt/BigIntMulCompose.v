From Coq Require Import Uint63 ZArith Lia Lists.List.
Require Import BigInt.NTTConcrete BigInt.BigIntMul BigInt.BigIntMulProof BigInt.BigIntMulCoefficients
  BigInt.BigIntMulNormalize BigInt.BigIntMulNormalizeArray BigInt.BigIntMulNormalizeValue
  BigInt.BigIntMulNormalizeInvariant.

Import ListNotations.
Local Open Scope Z_scope.

Definition mul_needed_blocks (a b : bigint) : nat :=
  (List.length a + List.length b)%nat.

Definition mul_block_log (a b : bigint) : nat :=
  block_log (mul_needed_blocks a b).

Definition mul_total_log (a b : bigint) : nat :=
  transform_log_of_block_log (mul_block_log a b).

Definition mul_needed_digits (a b : bigint) : nat :=
  (8 * mul_needed_blocks a b)%nat.

Definition mul_coeff_array (a b : bigint) : PArray.array Uint63.int :=
  let k := mul_block_log a b in
  coeff_array_from_packed_trees k (coeff_array_make (mul_needed_digits a b))
    zero_digit u63_one
    (Prime469Ops.convolution_blocks k (build_tree469 k a) (build_tree469 k b))
    (Prime181Ops.convolution_blocks k (build_tree181 k a) (build_tree181 k b)).

Definition mul_bigint_result (a b : bigint) : bigint :=
  normalize_coeff_array_to_bigint (S (mul_needed_blocks a b)) (mul_coeff_array a b).

Lemma limb8_value_nonneg :
  forall x,
    (0 <= limb8_value x)%Z.
Proof.
  intros [x0 x1 x2 x3 x4 x5 x6 x7].
  unfold limb8_value.
  cbn [limb8_digits_z limb8_digits_u63 map digits_value].
  pose proof (Uint63.to_Z_bounded x0) as [Hx0 _].
  pose proof (Uint63.to_Z_bounded x1) as [Hx1 _].
  pose proof (Uint63.to_Z_bounded x2) as [Hx2 _].
  pose proof (Uint63.to_Z_bounded x3) as [Hx3 _].
  pose proof (Uint63.to_Z_bounded x4) as [Hx4 _].
  pose proof (Uint63.to_Z_bounded x5) as [Hx5 _].
  pose proof (Uint63.to_Z_bounded x6) as [Hx6 _].
  pose proof (Uint63.to_Z_bounded x7) as [Hx7 _].
  cbv [digit_base_z].
  lia.
Qed.

Lemma bigint_value_nonneg :
  forall x,
    (0 <= bigint_value x)%Z.
Proof.
  induction x as [|b bs IH].
  - reflexivity.
  - rewrite bigint_value_cons.
    pose proof (limb8_value_nonneg b) as Hb.
    cbv [digit_base8_z digit_base_z].
    lia.
Qed.

Lemma canonical_bigint_value_bound :
  forall x,
    canonical_bigint x ->
    (0 <= bigint_value x < digit_base_z ^ Z.of_nat (8 * List.length x))%Z.
Proof.
  intros x Hx.
  unfold bigint_value.
  rewrite digits_value_eq_base.
  replace (digit_base_z ^ Z.of_nat (8 * List.length x))%Z
    with (digit_base_z ^ Z.of_nat (List.length (bigint_digits_z x)))%Z.
  2:{
    rewrite bigint_digits_z_length.
    reflexivity.
  }
  apply digits_value_base_range.
  - cbv [digit_base_z].
    lia.
  - apply canonical_bigint_digits_z_range.
    exact Hx.
Qed.

Lemma canonical_bigint_product_bound_fuel :
  forall a b fuel,
    canonical_bigint a ->
    canonical_bigint b ->
    (mul_needed_blocks a b <= fuel)%nat ->
    (0 <= bigint_value a * bigint_value b <
      digit_base_z ^ Z.of_nat (8 * fuel))%Z.
Proof.
  intros a b fuel Ha Hb Hfuel.
  pose proof (canonical_bigint_value_bound a Ha) as Ha_bound.
  pose proof (canonical_bigint_value_bound b Hb) as Hb_bound.
  destruct Ha_bound as [Ha0 Ha1].
  destruct Hb_bound as [Hb0 Hb1].
  split.
  - nia.
  - assert (Hprod :
      (bigint_value a * bigint_value b <
       digit_base_z ^ Z.of_nat (8 * List.length a) *
       digit_base_z ^ Z.of_nat (8 * List.length b))%Z).
    {
      nia.
    }
    assert (Hpow_eq :
      (digit_base_z ^ Z.of_nat (8 * List.length a) *
       digit_base_z ^ Z.of_nat (8 * List.length b) =
       digit_base_z ^ Z.of_nat (8 * mul_needed_blocks a b))%Z).
    {
      unfold mul_needed_blocks.
      replace (8 * (List.length a + List.length b))%nat
        with ((8 * List.length a + 8 * List.length b)%nat) by lia.
      rewrite Nat2Z.inj_add.
      rewrite Z.pow_add_r by (cbv [digit_base_z]; lia).
      reflexivity.
    }
    rewrite Hpow_eq in Hprod.
    eapply Z.lt_le_trans; [exact Hprod|].
    apply Z.pow_le_mono_r.
    + cbv [digit_base_z].
      lia.
    + apply Nat2Z.inj_le.
      lia.
Qed.

Theorem normalize_coeff_array_to_bigint_correct_of_value :
  forall fuel arr a b,
    canonical_bigint a ->
    canonical_bigint b ->
    (mul_needed_blocks a b <= fuel)%nat ->
    Forall (fun z => (0 <= z < crt_modulus_z)%Z)
      (coeff_digits_z (8 * fuel) zero_digit arr) ->
    digits_value (coeff_digits_z (8 * fuel) zero_digit arr) =
      bigint_value a * bigint_value b ->
    bigint_value (normalize_coeff_array_to_bigint fuel arr) =
      bigint_value a * bigint_value b.
Proof.
  intros fuel arr a b Ha Hb Hfuel Hcoeffs Hvalue.
  assert (HzeroCarry : (0 <= Uint63.to_Z zero_digit < carry_limit_z)%Z).
  {
    rewrite zero_digit_to_Z.
    unfold carry_limit_z.
    lia.
  }
  destruct (normalize_coeff_block_state fuel zero_digit zero_digit arr)
    as [digits carry'] eqn:Hstate.
  pose proof (normalize_coeff_array_to_bigint_value fuel arr) as Hnorm.
  rewrite <- normalize_coeff_block_state_fst
    with (fuel := fuel) (idx := zero_digit) (carry := zero_digit) (arr := arr) in Hnorm.
  rewrite Hstate in Hnorm.
  simpl in Hnorm.
  pose proof
    (normalize_coeff_block_state_value fuel zero_digit zero_digit arr Hcoeffs HzeroCarry)
    as Hstate_value.
  rewrite Hstate in Hstate_value.
  simpl in Hstate_value.
  destruct Hstate_value as [Hcarry_range Hdigits].
  rewrite <- Hnorm in Hdigits.
  change (Uint63.to_Z zero_digit) with 0%Z in Hdigits.
  simpl in Hdigits.
  pose proof
    (canonical_bigint_product_bound_fuel a b fuel Ha Hb Hfuel)
    as Hproduct_bound.
  pose proof (bigint_value_nonneg (normalize_coeff_array_to_bigint fuel arr))
    as Hresult_nonneg.
  destruct Hcarry_range as [Hcarry0 Hcarry1].
  destruct Hproduct_bound as [Hproduct0 Hproduct1].
  assert (Hdigits_prod :
    bigint_value (normalize_coeff_array_to_bigint fuel arr) +
      digit_base_z ^ Z.of_nat (8 * fuel) * Uint63.to_Z carry' =
    bigint_value a * bigint_value b).
  {
    etransitivity.
    - exact Hdigits.
    - exact Hvalue.
  }
  assert (Hcarry_zero : (Uint63.to_Z carry' = 0)%Z).
  {
    destruct (Z.eq_dec (Uint63.to_Z carry') 0) as [Hz|Hnz].
    - exact Hz.
    - assert (1 <= Uint63.to_Z carry')%Z.
      {
        lia.
      }
      assert (Hpow_pos : (0 < digit_base_z ^ Z.of_nat (8 * fuel))%Z).
      {
        apply Z.pow_pos_nonneg; cbv [digit_base_z]; lia.
      }
      assert (Hcarry_term :
        (digit_base_z ^ Z.of_nat (8 * fuel) <=
         digit_base_z ^ Z.of_nat (8 * fuel) * Uint63.to_Z carry')%Z).
      {
        nia.
      }
      lia.
  }
  rewrite Hcarry_zero in Hdigits_prod.
  lia.
Qed.

Theorem mul_bigint_correct_of_coeff_digits_value :
  forall a b,
    canonical_bigint a ->
    canonical_bigint b ->
    a <> [] ->
    b <> [] ->
    Nat.leb (mul_total_log a b) supported_max_log = true ->
    Nat.leb (mul_needed_digits a b) coeff_array_max_digits = true ->
    Forall (fun z => (0 <= z < crt_modulus_z)%Z)
      (coeff_digits_z (8 * S (mul_needed_blocks a b)) zero_digit (mul_coeff_array a b)) ->
    digits_value
      (coeff_digits_z (8 * S (mul_needed_blocks a b)) zero_digit (mul_coeff_array a b)) =
      bigint_value a * bigint_value b ->
    mul_bigint a b = Some (mul_bigint_result a b) /\
    bigint_value (mul_bigint_result a b) = bigint_value a * bigint_value b.
Proof.
  intros a b Ha Hb Hna Hnb Hlog Hdigits Hcoeffs Hvalue.
  unfold mul_bigint.
  destruct a as [|a0 a']; [contradiction|].
  destruct b as [|b0 b']; [contradiction|].
  cbn [mul_needed_blocks mul_block_log mul_total_log mul_coeff_array mul_bigint_result]
    in Hlog, Hdigits, Hcoeffs, Hvalue |- *.
  destruct
    (Nat.leb
      (transform_log_of_block_log (block_log (S (List.length a') + S (List.length b'))))
      supported_max_log) eqn:Hcheck_log;
  destruct
    (Nat.leb (8 * (S (List.length a') + S (List.length b'))) coeff_array_max_digits)
      eqn:Hcheck_digits.
  - split.
    + replace
        (transform_log_of_block_log
           (block_log (length (a0 :: a') + length (b0 :: b'))))
        with
        (transform_log_of_block_log
           (block_log (S (List.length a') + S (List.length b')))) by reflexivity.
      replace (8 * (length (a0 :: a') + length (b0 :: b')))%nat
        with (8 * (S (List.length a') + S (List.length b')))%nat by reflexivity.
      rewrite Hcheck_log, Hcheck_digits.
      reflexivity.
    + apply normalize_coeff_array_to_bigint_correct_of_value.
      * exact Ha.
      * exact Hb.
      * lia.
      * exact Hcoeffs.
      * exact Hvalue.
  - apply Nat.leb_le in Hlog.
    apply Nat.leb_le in Hdigits.
    apply Nat.leb_gt in Hcheck_digits.
    change ((8 * (S (List.length a') + S (List.length b')) <= coeff_array_max_digits)%nat)
      in Hdigits.
    lia.
  - apply Nat.leb_le in Hlog.
    apply Nat.leb_gt in Hcheck_log.
    change
      ((transform_log_of_block_log
          (block_log (S (List.length a') + S (List.length b'))) <= supported_max_log)%nat)
      in Hlog.
    lia.
  - apply Nat.leb_le in Hlog.
    apply Nat.leb_gt in Hcheck_log.
    change
      ((transform_log_of_block_log
          (block_log (S (List.length a') + S (List.length b'))) <= supported_max_log)%nat)
      in Hlog.
    lia.
Qed.
