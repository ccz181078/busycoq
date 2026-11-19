From Coq Require Import Uint63 ZArith Lia Znumtheory Array.PArray.
Require Import BigInt.NTTConcrete BigInt.BigIntMul BigInt.BigIntMulCRT BigInt.BigIntMulCRTArithmetic.

Local Open Scope Z_scope.

Lemma prime_moduli_rel_prime :
  rel_prime prime469_z prime181_z.
Proof.
  rewrite prime469_z_value, prime181_z_value.
  change (Zis_gcd 469762049 1811939329 1).
  assert (Hgcd : Z.gcd 469762049 1811939329 = 1) by (vm_compute; reflexivity).
  rewrite <- Hgcd.
  apply Zgcd_is_gcd.
Qed.

Lemma crt_combine_range :
  forall x469 x181,
    (0 <= Uint63.to_Z x469 < prime469_z)%Z ->
    (0 <= Uint63.to_Z x181 < prime181_z)%Z ->
    (0 <= crt_combine x469 x181 < crt_modulus_z)%Z.
Proof.
  intros x469 x181 H469 H181.
  unfold crt_combine, crt_modulus_z.
  destruct H469 as [H4690 H4691].
  destruct H181 as [_ H1811].
  assert
    (Ht :
      (0 <=
         Z.modulo
           (Z.modulo (Uint63.to_Z x181 - Uint63.to_Z x469) prime181_z *
            Uint63.to_Z crt_inv_prime469_mod_prime181)
           prime181_z
       < prime181_z)%Z).
  {
    apply Z.mod_pos_bound.
    rewrite prime181_z_value.
    lia.
  }
  destruct Ht as [Ht0 Ht1].
  split.
  - apply Z.add_nonneg_nonneg.
    + exact H4690.
    + apply Z.mul_nonneg_nonneg; lia.
  - rewrite prime469_z_value in H4691.
    rewrite prime181_z_value in Ht1.
    assert (H4691' : Uint63.to_Z x469 <= 469762048).
    {
      change 469762049 with (Z.succ 469762048) in H4691.
      apply Zlt_succ_le.
      exact H4691.
    }
    assert
      (Ht1' :
        Z.modulo
          (Z.modulo (Uint63.to_Z x181 - Uint63.to_Z x469) prime181_z *
           Uint63.to_Z crt_inv_prime469_mod_prime181)
          prime181_z <= 1811939328).
    {
      change 1811939329 with (Z.succ 1811939328) in Ht1.
      apply Zlt_succ_le.
      exact Ht1.
    }
    unfold crt_modulus_z.
    rewrite prime469_z_value.
    rewrite prime181_z_value.
    eapply Z.le_lt_trans.
    + assert
        ((Uint63.to_Z x469 +
          469762049 *
            Z.modulo
              (Z.modulo (Uint63.to_Z x181 - Uint63.to_Z x469) prime181_z *
               Uint63.to_Z crt_inv_prime469_mod_prime181)
              prime181_z
          <= 469762048 + 469762049 * 1811939328)%Z) by nia.
      exact H.
    + change (469762048 + 469762049 * 1811939328 < 469762049 * 1811939329)%Z.
      nia.
Qed.

Lemma crt_combine_mod_prime469 :
  forall x469 x181,
    (0 <= Uint63.to_Z x469 < prime469_z)%Z ->
    (0 <= Uint63.to_Z x181 < prime181_z)%Z ->
    Z.modulo (crt_combine x469 x181) prime469_z = Uint63.to_Z x469.
Proof.
  intros x469 x181 H469 H181.
  unfold crt_combine.
  rewrite Z.mul_comm.
  rewrite Z.mod_add by (rewrite prime469_z_value; lia).
  apply Z.mod_small.
  exact H469.
Qed.

Lemma crt_combine_mod_prime181 :
  forall x469 x181,
    (0 <= Uint63.to_Z x469 < prime469_z)%Z ->
    (0 <= Uint63.to_Z x181 < prime181_z)%Z ->
    Z.modulo (crt_combine x469 x181) prime181_z = Uint63.to_Z x181.
Proof.
  intros x469 x181 H469 H181.
  destruct H181 as [H1810 H1811].
  set (a := Uint63.to_Z x469).
  set (b := Uint63.to_Z x181).
  set (delta := Z.modulo (b - a) prime181_z).
  set (inv := Uint63.to_Z crt_inv_prime469_mod_prime181).
  set (expr := delta * inv).
  set (t := Z.modulo expr prime181_z).
  assert (Hmod_delta : (prime181_z | (b - a) - delta)).
  {
    subst delta.
    apply Zmod_divide_minus.
    - rewrite prime181_z_value.
      lia.
    - reflexivity.
  }
  assert (Hmod_t : (prime181_z | expr - t)).
  {
    subst t.
    apply Zmod_divide_minus.
    - rewrite prime181_z_value.
      lia.
    - reflexivity.
  }
  assert (Hmod_inv : (prime181_z | prime469_z * inv - 1)).
  {
    apply Zmod_divide_minus with (c := 1).
    - rewrite prime181_z_value.
      lia.
    - subst inv.
      rewrite crt_inv_prime469_mod_prime181_correct.
      reflexivity.
  }
  assert (Hdiv :
    (prime181_z | crt_combine x469 x181 - b)).
  {
    unfold crt_combine.
    subst a b delta expr t inv.
    replace
      (Uint63.to_Z x469 +
       prime469_z *
         Z.modulo
           (Z.modulo
              (Uint63.to_Z x181 - Uint63.to_Z x469)
           prime181_z *
            Uint63.to_Z crt_inv_prime469_mod_prime181)
           prime181_z -
       Uint63.to_Z x181)%Z
    with
      (prime469_z *
         (Z.modulo
            (Z.modulo
               (Uint63.to_Z x181 - Uint63.to_Z x469)
               prime181_z *
             Uint63.to_Z crt_inv_prime469_mod_prime181)
            prime181_z -
          (Z.modulo
             (Uint63.to_Z x181 - Uint63.to_Z x469)
             prime181_z *
           Uint63.to_Z crt_inv_prime469_mod_prime181)) +
       Z.modulo
         (Uint63.to_Z x181 - Uint63.to_Z x469)
         prime181_z *
         (prime469_z *
            Uint63.to_Z crt_inv_prime469_mod_prime181 - 1) +
       (Z.modulo
          (Uint63.to_Z x181 - Uint63.to_Z x469)
          prime181_z -
        (Uint63.to_Z x181 - Uint63.to_Z x469)))%Z
      by ring.
    apply Z.divide_add_r.
    - apply Z.divide_add_r.
      + rewrite Z.mul_comm.
        apply Z.divide_mul_l.
        replace
          (Z.modulo
             (Z.modulo
                (Uint63.to_Z x181 - Uint63.to_Z x469)
                prime181_z *
              Uint63.to_Z crt_inv_prime469_mod_prime181)
             prime181_z -
           Z.modulo
             (Uint63.to_Z x181 - Uint63.to_Z x469)
             prime181_z *
             Uint63.to_Z crt_inv_prime469_mod_prime181)%Z
        with
          (- (Z.modulo
                (Uint63.to_Z x181 - Uint63.to_Z x469)
                prime181_z *
               Uint63.to_Z crt_inv_prime469_mod_prime181 -
              Z.modulo
                (Z.modulo
                   (Uint63.to_Z x181 - Uint63.to_Z x469)
                   prime181_z *
                 Uint63.to_Z crt_inv_prime469_mod_prime181)
                prime181_z))%Z
          by ring.
        apply Z.divide_opp_r.
        exact Hmod_t.
      + apply Z.divide_mul_r.
        exact Hmod_inv.
    - replace
        (Z.modulo
           (Uint63.to_Z x181 - Uint63.to_Z x469)
           prime181_z -
         (Uint63.to_Z x181 - Uint63.to_Z x469))%Z
      with
        (- ((Uint63.to_Z x181 - Uint63.to_Z x469) -
            Z.modulo
              (Uint63.to_Z x181 - Uint63.to_Z x469)
              prime181_z))%Z
        by ring.
      apply Z.divide_opp_r.
      exact Hmod_delta.
  }
  apply Zdivide_mod_minus.
  - split; assumption.
  - exact Hdiv.
Qed.

Lemma crt_combine_exact :
  forall x469 x181 z,
    (0 <= Uint63.to_Z x469 < prime469_z)%Z ->
    (0 <= Uint63.to_Z x181 < prime181_z)%Z ->
    (0 <= z < crt_modulus_z)%Z ->
    Z.modulo z prime469_z = Uint63.to_Z x469 ->
    Z.modulo z prime181_z = Uint63.to_Z x181 ->
    crt_combine x469 x181 = z.
Proof.
  intros x469 x181 z H469 H181 Hz Hz469 Hz181.
  pose proof (crt_combine_range x469 x181 H469 H181) as Hrange.
  assert (H469div : (prime469_z | crt_combine x469 x181 - z)).
  {
    assert (Hcombine :
      (prime469_z | crt_combine x469 x181 - Uint63.to_Z x469)).
    {
      apply Zmod_divide_minus.
      - rewrite prime469_z_value.
        lia.
      - apply crt_combine_mod_prime469; assumption.
    }
    assert (Hzdiv :
      (prime469_z | z - Uint63.to_Z x469)).
    {
      apply Zmod_divide_minus.
      - rewrite prime469_z_value.
        lia.
      - exact Hz469.
    }
    replace (crt_combine x469 x181 - z)%Z with
      ((crt_combine x469 x181 - Uint63.to_Z x469) - (z - Uint63.to_Z x469))%Z
      by ring.
    eapply Z.divide_sub_r; eauto.
  }
  assert (H181div : (prime181_z | crt_combine x469 x181 - z)).
  {
    assert (Hcombine :
      (prime181_z | crt_combine x469 x181 - Uint63.to_Z x181)).
    {
      apply Zmod_divide_minus.
      - rewrite prime181_z_value.
        lia.
      - apply crt_combine_mod_prime181; assumption.
    }
    assert (Hzdiv :
      (prime181_z | z - Uint63.to_Z x181)).
    {
      apply Zmod_divide_minus.
      - rewrite prime181_z_value.
        lia.
      - exact Hz181.
    }
    replace (crt_combine x469 x181 - z)%Z with
      ((crt_combine x469 x181 - Uint63.to_Z x181) - (z - Uint63.to_Z x181))%Z
      by ring.
    eapply Z.divide_sub_r; eauto.
  }
  assert (Hproddiv : (crt_modulus_z | crt_combine x469 x181 - z)).
  {
    unfold crt_modulus_z.
    destruct H469div as [q Hq].
    assert (Hqdiv : (prime181_z | q)).
    {
      apply (Gauss prime181_z prime469_z q).
      - rewrite Z.mul_comm.
        rewrite <- Hq.
        exact H181div.
      - apply rel_prime_sym.
        exact prime_moduli_rel_prime.
    }
    destruct Hqdiv as [r Hr].
    exists r.
    rewrite Hq, Hr.
    unfold prime469_z, prime181_z.
    ring.
  }
  destruct Hrange as [Hrange0 Hrange1].
  destruct Hz as [Hz0 Hz1].
  destruct Hproddiv as [q Hq].
  assert
    (Hdiff :
      (- crt_modulus_z < crt_combine x469 x181 - z < crt_modulus_z)%Z).
  {
    unfold crt_modulus_z in *.
    lia.
  }
  rewrite Hq in Hdiff.
  assert (q = 0)%Z by nia.
  subst q.
  lia.
Qed.

Lemma crt_combine_u63_exact :
  forall x469 x181 z,
    (0 <= Uint63.to_Z x469 < prime469_z)%Z ->
    (0 <= Uint63.to_Z x181 < prime181_z)%Z ->
    (0 <= z < crt_modulus_z)%Z ->
    Z.modulo z prime469_z = Uint63.to_Z x469 ->
    Z.modulo z prime181_z = Uint63.to_Z x181 ->
    Uint63.to_Z (crt_combine_u63 x469 x181) = z.
Proof.
  intros x469 x181 z H469 H181 Hz Hz469 Hz181.
  rewrite crt_combine_u63_value by assumption.
  apply crt_combine_exact; assumption.
Qed.
