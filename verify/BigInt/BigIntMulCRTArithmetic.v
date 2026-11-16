From Coq Require Import Uint63 ZArith Lia.
Require Import BigInt.NTTConcrete BigInt.BigIntMul BigInt.BigIntMulCanonical.

Local Open Scope Z_scope.

Lemma crt_inv_prime469_mod_prime181_value :
  Uint63.to_Z crt_inv_prime469_mod_prime181 = 1540148431.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma crt_inv_prime469_mod_prime181_correct :
  Z.modulo (prime469_z * Uint63.to_Z crt_inv_prime469_mod_prime181) prime181_z = 1.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma prime469_z_value :
  prime469_z = 469762049.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma prime181_z_value :
  prime181_z = 1811939329.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma prime469_lt_prime181 :
  (prime469_z < prime181_z)%Z.
Proof.
  change (469762049 < 1811939329)%Z.
  lia.
Qed.

Lemma prime181_lt_wB :
  (prime181_z < Uint63.wB)%Z.
Proof.
  unfold prime181_z.
  pose proof (Uint63.to_Z_bounded Prime181Cfg.modulus) as [_ H].
  exact H.
Qed.

Lemma crt_delta_mul_lt_wB :
  (1811939328 * 1540148431 < Uint63.wB)%Z.
Proof.
  change (2790655513086394368 < 9223372036854775808)%Z.
  lia.
Qed.

Lemma crt_combine_lt_wB :
  (469762048 + 469762049 * 1811939328 < Uint63.wB)%Z.
Proof.
  change (851180331854725120 < 9223372036854775808)%Z.
  lia.
Qed.

Lemma crt_prod469_lt_wB :
  (469762049 * 1811939328 < Uint63.wB)%Z.
Proof.
  change (851180331384963072 < 9223372036854775808)%Z.
  lia.
Qed.

Lemma crt_delta_u63_value :
  forall x469 x181,
    (0 <= Uint63.to_Z x469 < prime469_z)%Z ->
    (0 <= Uint63.to_Z x181 < prime181_z)%Z ->
    Uint63.to_Z (crt_delta_u63 x469 x181) =
    Z.modulo (Uint63.to_Z x181 - Uint63.to_Z x469) prime181_z.
Proof.
  intros x469 x181 H469 H181.
  unfold crt_delta_u63.
  destruct H469 as [H4690 H4691].
  destruct H181 as [H1810 H1811].
  rewrite prime469_z_value in H4691.
  rewrite prime181_z_value in H1811.
  destruct (Uint63.ltb x181 x469) eqn:Hlt.
  - apply Uint63.ltb_spec in Hlt.
    rewrite Uint63.sub_spec.
    assert (Hsum : (0 <= Uint63.to_Z x181 + 1811939329 < Uint63.wB)%Z).
    {
      split.
      - lia.
      - change Uint63.wB with 9223372036854775808%Z.
        lia.
    }
    assert (Hadd :
      Uint63.to_Z (Uint63.add x181 prime181_u63) =
      Uint63.to_Z x181 + 1811939329).
    {
      unfold prime181_u63.
      rewrite Uint63.add_spec.
      change (Uint63.to_Z Prime181Cfg.modulus) with 1811939329.
      apply Z.mod_small.
      exact Hsum.
    }
    rewrite Hadd.
    assert (Hdiff : (0 <= Uint63.to_Z x181 + 1811939329 - Uint63.to_Z x469 < Uint63.wB)%Z).
    {
      split.
      - lia.
      - change Uint63.wB with 9223372036854775808%Z.
        lia.
    }
    rewrite Z.mod_small by exact Hdiff.
    apply Z.mod_unique with (q := -1).
    + left.
      split.
      * exact (proj1 Hdiff).
      * rewrite prime181_z_value.
        lia.
    + rewrite prime181_z_value.
      lia.
  - assert (Hge : (Uint63.to_Z x469 <= Uint63.to_Z x181)%Z).
    {
      apply Z.le_ngt.
      intro Hcontra.
      assert (Hlt_true : (x181 <? x469)%uint63 = true).
      {
        apply Uint63.ltb_spec.
        exact Hcontra.
      }
      rewrite Hlt_true in Hlt.
      discriminate.
    }
    rewrite Uint63.sub_spec.
    assert (Hdiff : (0 <= Uint63.to_Z x181 - Uint63.to_Z x469 < Uint63.wB)%Z).
    {
      split.
      - lia.
      - change Uint63.wB with 9223372036854775808%Z.
        lia.
    }
    rewrite Z.mod_small by exact Hdiff.
    symmetry.
    apply Z.mod_small.
    split.
    + lia.
    + rewrite prime181_z_value.
      lia.
Qed.

Lemma crt_combine_u63_value :
  forall x469 x181,
    (0 <= Uint63.to_Z x469 < prime469_z)%Z ->
    (0 <= Uint63.to_Z x181 < prime181_z)%Z ->
    Uint63.to_Z (crt_combine_u63 x469 x181) = crt_combine x469 x181.
Proof.
  intros x469 x181 H469 H181.
  unfold crt_combine_u63, crt_combine.
  pose proof (crt_delta_u63_value x469 x181 H469 H181) as Hdelta.
  assert (Hmul :
    Uint63.to_Z (Uint63.mul (crt_delta_u63 x469 x181) crt_inv_prime469_mod_prime181) =
    Z.modulo (Uint63.to_Z x181 - Uint63.to_Z x469) prime181_z * 1540148431).
  {
    rewrite Uint63.mul_spec.
    rewrite Hdelta.
    rewrite crt_inv_prime469_mod_prime181_value.
    assert (Hprod :
      (0 <=
         Z.modulo (Uint63.to_Z x181 - Uint63.to_Z x469) prime181_z * 1540148431
       < Uint63.wB)%Z).
    {
      assert (Hmod :
        (0 <= Z.modulo (Uint63.to_Z x181 - Uint63.to_Z x469) prime181_z < prime181_z)%Z).
      {
        apply Z.mod_pos_bound.
        rewrite prime181_z_value.
        lia.
      }
      destruct Hmod as [Hmod0 Hmod1].
      split.
      - nia.
      - rewrite prime181_z_value in Hmod1.
        eapply Z.le_lt_trans.
        + assert
            ((Z.modulo (Uint63.to_Z x181 - Uint63.to_Z x469) 1811939329 * 1540148431
              <= 1811939328 * 1540148431)%Z) by nia.
          exact H.
        + exact crt_delta_mul_lt_wB.
    }
    apply Z.mod_small.
    exact Hprod.
  }
  assert (Htval :
    Uint63.to_Z
      (Uint63.mod
         (Uint63.mul (crt_delta_u63 x469 x181) crt_inv_prime469_mod_prime181)
         prime181_u63) =
    Z.modulo
      (Z.modulo (Uint63.to_Z x181 - Uint63.to_Z x469) prime181_z * 1540148431)
      prime181_z).
  {
    rewrite Uint63.mod_spec.
    rewrite Hmul.
    unfold prime181_u63.
    change (Uint63.to_Z Prime181Cfg.modulus) with 1811939329.
    reflexivity.
  }
  assert
    (Ht :
      (0 <=
         Z.modulo
           (Z.modulo (Uint63.to_Z x181 - Uint63.to_Z x469) prime181_z * 1540148431)
           prime181_z
       < prime181_z)%Z).
  {
    apply Z.mod_pos_bound.
    rewrite prime181_z_value.
    lia.
  }
  destruct H469 as [H4690 H4691].
  rewrite prime469_z_value in H4691.
  rewrite Uint63.add_spec.
  rewrite Uint63.mul_spec.
  rewrite Htval.
  unfold prime469_u63.
  change (Uint63.to_Z Prime469Cfg.modulus) with 469762049.
  assert (Hprod469 :
    (0 <=
       469762049 *
       Z.modulo
         (Z.modulo (Uint63.to_Z x181 - Uint63.to_Z x469) prime181_z * 1540148431)
         prime181_z
     < Uint63.wB)%Z).
  {
    destruct Ht as [Ht0 Ht1].
    rewrite prime181_z_value in Ht1.
    split.
    - apply Z.mul_nonneg_nonneg.
      + lia.
      + exact Ht0.
    - eapply Z.le_lt_trans.
      + assert
          ((469762049 *
            Z.modulo
              (Z.modulo (Uint63.to_Z x181 - Uint63.to_Z x469) prime181_z * 1540148431)
              prime181_z
            <= 469762049 * 1811939328)%Z).
        {
          apply Z.mul_le_mono_nonneg_l.
          - lia.
          - change 1811939329 with (Z.succ 1811939328) in Ht1.
            apply Zlt_succ_le.
            exact Ht1.
        }
        exact H.
      + exact crt_prod469_lt_wB.
  }
  rewrite
    (Z.mod_small
       (469762049 *
        Z.modulo
          (Z.modulo (Uint63.to_Z x181 - Uint63.to_Z x469) prime181_z * 1540148431)
          prime181_z)
       Uint63.wB) by exact Hprod469.
  assert (Hsum :
    (0 <=
       Uint63.to_Z x469 +
       469762049 *
       Z.modulo
         (Z.modulo (Uint63.to_Z x181 - Uint63.to_Z x469) prime181_z * 1540148431)
         prime181_z
     < Uint63.wB)%Z).
  {
    destruct Ht as [Ht0 Ht1].
    rewrite prime181_z_value in Ht1.
      split.
      - apply Z.add_nonneg_nonneg.
        + exact H4690.
        + apply Z.mul_nonneg_nonneg.
          * lia.
          * exact Ht0.
      - eapply Z.le_lt_trans.
        + assert (H4691' : (Uint63.to_Z x469 <= 469762048)%Z).
          {
            change 469762049 with (Z.succ 469762048) in H4691.
            apply Zlt_succ_le.
            exact H4691.
          }
          assert (Ht1' :
              (Z.modulo
                 (Z.modulo (Uint63.to_Z x181 - Uint63.to_Z x469) prime181_z * 1540148431)
                 prime181_z <= 1811939328)%Z).
          {
            change 1811939329 with (Z.succ 1811939328) in Ht1.
            apply Zlt_succ_le.
            exact Ht1.
          }
          assert
            ((Uint63.to_Z x469 +
              469762049 *
              Z.modulo
                (Z.modulo (Uint63.to_Z x181 - Uint63.to_Z x469) prime181_z * 1540148431)
                prime181_z
              <= 851180331854725120)%Z) by nia.
          exact H.
        + change (851180331854725120 < Uint63.wB)%Z.
          exact crt_combine_lt_wB.
  }
  rewrite Z.mod_small by exact Hsum.
  reflexivity.
Qed.
