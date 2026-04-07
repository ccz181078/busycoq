From Coq Require Import ZArith Lists.List.
Require Import BigInt.BigIntMul BigInt.BigIntMulProof BigInt.BigIntMulCompose
  BigInt.BigIntMulScalarReduction BigInt.BigIntMulPrime469Concrete
  BigInt.BigIntMulPrime181Concrete.

Import ListNotations.
Local Open Scope Z_scope.

Theorem mul_bigint_result_correct :
  forall a b,
    canonical_bigint a ->
    canonical_bigint b ->
    a <> [] ->
    b <> [] ->
    Nat.leb (mul_total_log a b) supported_max_log = true ->
    Nat.leb (mul_needed_digits a b) coeff_array_max_digits = true ->
    mul_bigint a b = Some (mul_bigint_result a b) /\
    bigint_value (mul_bigint_result a b) = bigint_value a * bigint_value b.
Proof.
  intros a b Ha Hb Hna Hnb Hlog Hdigits.
  apply mul_bigint_correct_of_scalar_cyclic_kb; try assumption.
  - intros j Hj.
    apply prime469_scalar_cyclic_concrete_kb; assumption.
  - intros j Hj.
    apply prime181_scalar_cyclic_concrete_kb; assumption.
Qed.

Theorem mul_bigint_correct :
  forall a b c,
    canonical_bigint a ->
    canonical_bigint b ->
    mul_bigint a b = Some c ->
    bigint_value c = bigint_value a * bigint_value b.
Proof.
  intros a b c Ha Hb Hmul.
  destruct a as [|a0 a']; destruct b as [|b0 b'].
  - simpl in Hmul. inversion Hmul; subst; reflexivity.
  - simpl in Hmul. inversion Hmul; subst; reflexivity.
  - simpl in Hmul. inversion Hmul; subst; simpl. rewrite Z.mul_0_r. reflexivity.
  - destruct (andb (Nat.leb (mul_total_log (a0 :: a') (b0 :: b')) supported_max_log)
      (Nat.leb (mul_needed_digits (a0 :: a') (b0 :: b')) coeff_array_max_digits))
      eqn:Hguard.
    +
      apply andb_prop in Hguard.
      destruct Hguard as [Hlog Hdigits].
      destruct
        (mul_bigint_result_correct (a0 :: a') (b0 :: b') Ha Hb
           (fun H => match H with end)
           (fun H => match H with end)
           Hlog Hdigits)
        as [Hres Hvalue].
      rewrite Hres in Hmul.
      inversion Hmul; subst; clear Hmul.
      exact Hvalue.
    + cbv [mul_bigint mul_total_log mul_block_log mul_needed_digits mul_needed_blocks] in Hmul.
      cbv [mul_total_log mul_block_log mul_needed_digits mul_needed_blocks] in Hguard.
      rewrite Hguard in Hmul.
      simpl in Hmul.
      discriminate Hmul.
Qed.

Theorem mul_bigint_supported_correct :
  forall a b,
    canonical_bigint a ->
    canonical_bigint b ->
    Nat.leb (mul_total_log a b) supported_max_log = true ->
    Nat.leb (mul_needed_digits a b) coeff_array_max_digits = true ->
    exists c,
      mul_bigint a b = Some c /\
      bigint_value c = bigint_value a * bigint_value b.
Proof.
  intros a b Ha Hb Hlog Hdigits.
  destruct a as [|a0 a']; destruct b as [|b0 b'].
  - exists [].
    split; simpl; reflexivity.
  - exists [].
    split; simpl; reflexivity.
  - exists [].
    split; simpl.
    + reflexivity.
    + rewrite Z.mul_0_r.
      reflexivity.
  - destruct
      (mul_bigint_result_correct (a0 :: a') (b0 :: b') Ha Hb
         (fun H => match H with end)
         (fun H => match H with end)
         Hlog Hdigits)
      as [Hres Hvalue].
    exists (mul_bigint_result (a0 :: a') (b0 :: b')).
    split; assumption.
Qed.
