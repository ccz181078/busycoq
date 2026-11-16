From Coq Require Import Uint63 ZArith Lia Lists.List.
Require Import BigInt.BigIntMul BigInt.BigIntMulProof BigInt.BigIntMulCoefficients
  BigInt.BigIntMulAlgebra BigInt.BigIntMulNormalize BigInt.BigIntMulNormalizeArithmetic BigInt.BigIntMulNormalizeValue
  BigInt.BigIntMulCoeffExact BigInt.BigIntMulCompose.

Import ListNotations.
Local Open Scope Z_scope.

Lemma coeff_digits_z_mul_coeff_array_eq_convolution :
  forall a b,
    canonical_bigint a ->
    canonical_bigint b ->
    a <> [] ->
    b <> [] ->
    Nat.leb (mul_total_log a b) supported_max_log = true ->
    Nat.leb (mul_needed_digits a b) coeff_array_max_digits = true ->
    (forall i,
      (i < mul_needed_digits a b)%nat ->
      Uint63.to_Z (coeff_array_at (mul_coeff_array a b) (u63_of_nat i)) =
      convolution_coeff (bigint_digits_z a) (bigint_digits_z b) i) ->
    coeff_digits_z (8 * S (mul_needed_blocks a b)) zero_digit (mul_coeff_array a b) =
    convolution_digits (bigint_digits_z a) (bigint_digits_z b) ++ repeat 0 9.
Proof.
  intros a b Ha Hb Hna Hnb Hlog Hdigits Hpoint.
  apply list_eq_nth_default_Z.
  - rewrite coeff_digits_z_length.
    rewrite app_length.
    rewrite convolution_digits_length_nonempty.
    2:{
      apply bigint_digits_z_nonempty.
      exact Hna.
    }
    2:{
      apply bigint_digits_z_nonempty.
      exact Hnb.
    }
    rewrite !bigint_digits_z_length.
    destruct a as [|a0 a']; [contradiction|].
    destruct b as [|b0 b']; [contradiction|].
    simpl.
    lia.
  - intros i Hi.
    rewrite nth_coeff_digits_z_zero.
    2:{
      rewrite coeff_digits_z_length in Hi.
      exact Hi.
    }
    2:{
      apply mul_coeff_fuel_lt_wB.
      exact Hlog.
    }
    rewrite nth_convolution_digits_pad_zero_nonempty.
    2:{
      apply bigint_digits_z_nonempty.
      exact Hna.
    }
    2:{
      apply bigint_digits_z_nonempty.
      exact Hnb.
    }
    2:{
      rewrite coeff_digits_z_length in Hi.
      unfold mul_needed_digits, mul_needed_blocks in Hi |- *.
      rewrite !bigint_digits_z_length.
      destruct a as [|a0 a']; [contradiction|].
      destruct b as [|b0 b']; [contradiction|].
      cbn [List.length] in *.
      lia.
    }
    destruct (lt_dec i (mul_needed_digits a b)) as [Hlt|Hge].
    + apply Hpoint.
      exact Hlt.
    + pose proof
        (coeff_array_at_u63_of_nat_oob
          (mul_coeff_array a b) (mul_needed_digits a b) i)
        as Hoob.
      assert (HiB : (Z.of_nat i < Uint63.wB)%Z).
      {
        eapply Z.lt_trans.
        - apply Nat2Z.inj_lt.
          rewrite coeff_digits_z_length in Hi.
          exact Hi.
        - apply mul_coeff_fuel_lt_wB.
          exact Hlog.
      }
      apply Nat.nlt_ge in Hge.
      rewrite (Hoob
        (mul_coeff_array_length a b Hdigits)
        (mul_needed_digits_lt_wB a b Hlog)
        HiB
        Hge).
      * rewrite zero_digit_to_Z.
        symmetry.
        apply convolution_coeff_zero_tail.
        rewrite !bigint_digits_z_length.
        unfold mul_needed_digits, mul_needed_blocks in Hge |- *.
        replace (8 * length a + 8 * length b)%nat with (8 * (length a + length b))%nat by lia.
        eapply Nat.le_trans; [exact Hge|].
        apply Nat.le_succ_diag_r.
Qed.

Theorem mul_bigint_correct_of_coeff_exact :
  forall a b,
    canonical_bigint a ->
    canonical_bigint b ->
    a <> [] ->
    b <> [] ->
    Nat.leb (mul_total_log a b) supported_max_log = true ->
    Nat.leb (mul_needed_digits a b) coeff_array_max_digits = true ->
    (forall i,
      (i < mul_needed_digits a b)%nat ->
      Uint63.to_Z (coeff_array_at (mul_coeff_array a b) (u63_of_nat i)) =
      convolution_coeff (bigint_digits_z a) (bigint_digits_z b) i) ->
    mul_bigint a b = Some (mul_bigint_result a b) /\
    bigint_value (mul_bigint_result a b) = bigint_value a * bigint_value b.
Proof.
  intros a b Ha Hb Hna Hnb Hlog Hdigits Hpoint.
  pose proof
    (coeff_digits_z_mul_coeff_array_eq_convolution a b Ha Hb Hna Hnb Hlog Hdigits Hpoint)
    as Heq.
  apply mul_bigint_correct_of_coeff_digits_value; try assumption.
  - rewrite Heq.
    apply Forall_app.
    split.
    + apply convolution_digits_crt_range; assumption.
    + apply repeat_zero_crt_range.
  - rewrite Heq.
    rewrite digits_value_app.
    rewrite digits_value_repeat_zero.
    rewrite bigint_value_digits_convolution.
    ring.
Qed.
