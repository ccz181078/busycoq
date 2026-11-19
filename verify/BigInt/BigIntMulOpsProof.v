From Coq Require Import Uint63 ZArith NArith Lia Psatz Bool Lists.List.
Require Import BigInt.BigIntMul BigInt.BigIntMulProof BigInt.BigIntMulCanonical
  BigInt.BigIntMulNormalize.

Import ListNotations.
Local Open Scope Z_scope.

Lemma wB_pos :
  (0 < wB)%Z.
Proof.
  change (0 < 9223372036854775808)%Z.
  nia.
Qed.

Lemma shift_right_limb8_small_low :
  forall bits carry x hi lo,
    (0 < bits < digit_shift_nat)%nat ->
    shift_right_limb8_small
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      carry x = (hi, lo) ->
    lo =
      Uint63.land (d0 x)
        (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one).
Proof.
  intros bits carry [x0 x1 x2 x3 x4 x5 x6 x7] hi lo Hbits Hshift.
  unfold shift_right_limb8_small in Hshift.
  destruct (shift_right_digit_small
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      carry x7) as [y7 c7] eqn:H7.
  destruct (shift_right_digit_small
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      c7 x6) as [y6 c6] eqn:H6.
  destruct (shift_right_digit_small
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      c6 x5) as [y5 c5] eqn:H5.
  destruct (shift_right_digit_small
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      c5 x4) as [y4 c4] eqn:H4.
  destruct (shift_right_digit_small
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      c4 x3) as [y3 c3] eqn:H3.
  destruct (shift_right_digit_small
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      c3 x2) as [y2 c2] eqn:H2.
  destruct (shift_right_digit_small
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      c2 x1) as [y1 c1] eqn:H1.
  destruct (shift_right_digit_small
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      c1 x0) as [y0 c0] eqn:H0.
  cbn in Hshift.
  inversion Hshift; subst; clear Hshift.
  unfold shift_right_digit_small in H0.
  cbn in H0.
  inversion H0.
  reflexivity.
Qed.

Lemma digit_base_lt_wB :
  (digit_base_z < wB)%Z.
Proof.
  change (262144 < 9223372036854775808)%Z.
  lia.
Qed.

Lemma digit_mask_to_Z :
  Uint63.to_Z digit_mask = (digit_base_z - 1)%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma digit_shift_to_Z :
  Uint63.to_Z digit_shift = Z.of_nat digit_shift_nat.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma digit_base_N_to_Z :
  Z.of_N digit_base_N = digit_base_z.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma digit_base_N_eq_pow2 :
  digit_base_N = (2 ^ N.of_nat digit_shift_nat)%N.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma digit_mask_N_eq_ones :
  digit_mask_N = N.ones (N.of_nat digit_shift_nat).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma u63_of_Z_exact :
  forall z,
    (0 <= z < wB)%Z ->
    Uint63.to_Z (Uint63.of_Z z) = z.
Proof.
  intros z Hz.
  symmetry.
  apply Uint63.is_int.
  exact Hz.
Qed.

Lemma digit_base_z_pow2 :
  digit_base_z = (2 ^ Z.of_nat digit_shift_nat)%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma shift_u63_value :
  forall bits,
    (bits < digit_shift_nat)%nat ->
    Uint63.to_Z (Uint63.of_Z (Z.of_nat bits)) = Z.of_nat bits.
Proof.
  intros bits Hbits.
  change (Uint63.of_Z (Z.of_nat bits)) with (u63_of_nat bits).
  apply u63_of_nat_small.
  change (Z.of_nat bits < Uint63.wB)%Z.
  cbv [digit_shift_nat] in Hbits.
  apply (Z.lt_trans _ 18%Z).
  - lia.
  - change (18 < 9223372036854775808)%Z.
    easy.
Qed.

Lemma shift_left_u63_value :
  forall bits,
    (bits < digit_shift_nat)%nat ->
    Uint63.to_Z
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits))) =
    Z.of_nat (digit_shift_nat - bits).
Proof.
  intros bits Hbits.
  rewrite Uint63.sub_spec.
  rewrite digit_shift_to_Z.
  rewrite shift_u63_value by exact Hbits.
  rewrite Nat2Z.inj_sub by lia.
  apply Z.mod_small.
  split.
  - lia.
  - apply (Z.le_lt_trans _ 18%Z).
    + cbv [digit_shift_nat] in Hbits |- *.
      change (18 - Z.of_nat bits <= 18)%Z.
      lia.
    + change (18 < 9223372036854775808)%Z.
      lia.
Qed.

Lemma pow_bits_lt_wB :
  forall bits,
    (bits < digit_shift_nat)%nat ->
    (2 ^ Z.of_nat bits < wB)%Z.
Proof.
  intros bits Hbits.
  apply (Z.lt_trans _ digit_base_z).
  - rewrite digit_base_z_pow2.
    apply Z.pow_lt_mono_r.
    + lia.
    + lia.
    + apply (proj1 (Nat2Z.inj_lt bits digit_shift_nat)).
      exact Hbits.
  - apply digit_base_lt_wB.
Qed.

Lemma shift_low_mask_value :
  forall bits,
    (0 < bits < digit_shift_nat)%nat ->
    Uint63.to_Z
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one) =
    (2 ^ Z.of_nat bits - 1)%Z.
Proof.
  intros bits [Hbits0 Hbits].
  cbv [digit_shift_nat] in Hbits, Hbits0.
  rewrite Uint63.sub_spec.
  rewrite Uint63.lsl_spec.
  rewrite shift_u63_value by exact Hbits.
  change (Uint63.to_Z u63_one) with 1%Z.
  rewrite Z.mul_1_l.
  replace (2 ^ Z.of_nat bits mod wB)%Z with (2 ^ Z.of_nat bits).
  2:{
    symmetry.
    apply Z.mod_small.
    split.
    - apply Z.pow_nonneg; lia.
    - apply pow_bits_lt_wB.
      exact Hbits.
  }
  apply Z.mod_small.
  split.
  - assert (1 <= 2 ^ Z.of_nat bits)%Z.
    { change (2 ^ 0 <= 2 ^ Z.of_nat bits)%Z.
      apply Z.pow_le_mono_r; lia. }
    lia.
  - apply (Z.lt_trans _ (2 ^ Z.of_nat bits)).
    + lia.
    + apply pow_bits_lt_wB.
      exact Hbits.
Qed.

Lemma land_small_shiftl_zero :
  forall a b n,
    (0 <= a < 2 ^ n)%Z ->
    (0 <= n)%Z ->
    Z.land a (Z.shiftl b n) = 0%Z.
Proof.
  intros a b n Ha Hn.
  apply Z.bits_inj'.
  intros m Hm.
  rewrite Z.land_spec.
  destruct (Z_lt_ge_dec m n) as [Hm_lt | Hm_ge].
  - rewrite Z.shiftl_spec_low by lia.
    rewrite Bool.andb_false_r.
    symmetry.
    apply Z.bits_0.
  - rewrite <- (Z.mod_small a (2 ^ n)) by exact Ha.
    rewrite Z.testbit_mod_pow2 by lia.
    replace (m <? n)%Z with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite Bool.andb_false_l.
    symmetry.
    apply Z.bits_0.
Qed.

Lemma digit_base_z_split_pow :
  forall bits,
    (bits <= digit_shift_nat)%nat ->
    (2 ^ Z.of_nat bits * 2 ^ Z.of_nat (digit_shift_nat - bits) = digit_base_z)%Z.
Proof.
  intros bits Hbits.
  rewrite digit_base_z_pow2.
  rewrite <- Z.pow_add_r by lia.
  f_equal.
  rewrite Nat2Z.inj_sub by lia.
  lia.
Qed.

Lemma limb8_single_digit_value :
  forall d,
    limb8_value (limb8_single_digit d) = Uint63.to_Z d.
Proof.
  intros d.
  cbv [limb8_single_digit limb8_value limb8_digits_z limb8_digits_u63 digits_value].
  cbn [map].
  repeat rewrite zero_digit_to_Z.
  ring_simplify.
  reflexivity.
Qed.

Lemma limb8_value_high_zero :
  forall d,
    limb8_value
      (Limb8 d zero_digit zero_digit zero_digit zero_digit zero_digit zero_digit zero_digit) =
      Uint63.to_Z d.
Proof.
  intro d.
  change (limb8_value (limb8_single_digit d) = Uint63.to_Z d).
  apply limb8_single_digit_value.
Qed.

Lemma canonical_limb8_single_digit :
  forall d,
    canonical_digit d ->
    canonical_limb8 (limb8_single_digit d).
Proof.
  intros d [Hd0 Hd1].
  unfold canonical_limb8, limb8_single_digit.
  simpl.
  repeat split; try exact Hd0; try exact Hd1; apply canonical_zero_digit.
Qed.

Lemma canonical_limb8_digits_u63 :
  forall x,
    canonical_limb8 x ->
    Forall canonical_digit (limb8_digits_u63 x).
Proof.
  intros [x0 x1 x2 x3 x4 x5 x6 x7] Hx.
  destruct Hx as [Hx0 [Hx1 [Hx2 [Hx3 [Hx4 [Hx5 [Hx6 Hx7]]]]]]].
  change (Forall canonical_digit [x0; x1; x2; x3; x4; x5; x6; x7]).
  constructor; [exact Hx0|].
  constructor; [exact Hx1|].
  constructor; [exact Hx2|].
  constructor; [exact Hx3|].
  constructor; [exact Hx4|].
  constructor; [exact Hx5|].
  constructor; [exact Hx6|].
  constructor; [exact Hx7|].
  constructor.
Qed.

Lemma canonical_bigint_digits_u63 :
  forall x,
    canonical_bigint x ->
    Forall canonical_digit (bigint_digits_u63 x).
Proof.
  intros x Hx.
  rewrite bigint_digits_u63_eq_flat.
  induction Hx as [|b bs Hb Hbs IH].
  - constructor.
  - simpl.
    apply Forall_app.
    split.
    + apply canonical_limb8_digits_u63.
      exact Hb.
    + exact IH.
Qed.

Lemma digits_to_N_value :
  forall xs,
    Forall canonical_digit xs ->
    Z.of_N (digits_to_N xs) = digits_value (map Uint63.to_Z xs).
Proof.
  intros xs Hxs.
  induction Hxs as [|x xs Hx Hxs IH].
  - reflexivity.
  - cbn [digits_to_N].
    rewrite N2Z.inj_add.
    rewrite Z2N.id by (destruct Hx; lia).
    replace (Z.of_N (digit_base_N * digits_to_N xs))
      with (digit_base_z * digits_value (map Uint63.to_Z xs)).
    2:{
      rewrite N2Z.inj_mul.
      rewrite digit_base_N_to_Z.
      rewrite IH.
      reflexivity.
    }
    reflexivity.
Qed.

Lemma bigint_to_N_value :
  forall x,
    canonical_bigint x ->
    Z.of_N (bigint_to_N x) = bigint_value x.
Proof.
  intros x Hx.
  unfold bigint_to_N, bigint_value.
  apply eq_sym.
  rewrite bigint_digits_u63_eq_flat.
  rewrite bigint_digits_z_eq_flat.
  symmetry.
  apply digits_to_N_value.
  rewrite <- bigint_digits_u63_eq_flat.
  apply canonical_bigint_digits_u63.
  exact Hx.
Qed.

Lemma drop_zero_prefix_canonical :
  forall x,
    canonical_bigint x ->
    canonical_bigint (drop_zero_prefix x).
Proof.
  intros x Hx.
  induction Hx as [|b bs Hb Hbs IH].
  - constructor.
  - simpl.
    destruct (limb8_eqb b zero_limb8); auto.
    constructor; assumption.
Qed.

Lemma trim_bigint_canonical :
  forall x,
    canonical_bigint x ->
    canonical_bigint (trim_bigint x).
Proof.
  intros x Hx.
  unfold trim_bigint.
  apply Forall_rev.
  apply drop_zero_prefix_canonical.
  apply Forall_rev.
  exact Hx.
Qed.

Lemma split_digits8_canonical :
  forall xs block rest,
    Forall canonical_digit xs ->
    split_digits8 xs = (block, rest) ->
    canonical_limb8 block /\ Forall canonical_digit rest.
Proof.
  intros xs block rest Hxs Hsplit.
  destruct xs as
      [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 xs]]]]]]]];
    simpl in Hsplit;
    inversion Hsplit; subst; clear Hsplit;
    repeat match goal with
    | H : Forall canonical_digit (_ :: _) |- _ =>
        inversion H; subst; clear H
    end;
    repeat match goal with
    | H : canonical_digit _ |- _ => destruct H
    end;
    unfold canonical_limb8 in *;
    cbn in *;
    repeat split; try assumption; try constructor; try apply canonical_zero_digit; try lia.
Qed.

Fixpoint digits_to_bigint_blocks_canonical (fuel : nat) :
    forall xs,
      Forall canonical_digit xs ->
      canonical_bigint (digits_to_bigint_blocks fuel xs).
Proof.
  destruct fuel as [|fuel']; intros xs Hxs.
  - constructor.
  - destruct xs as [|x xs].
    + constructor.
    + cbn [digits_to_bigint_blocks].
      remember (split_digits8 (x :: xs)) as split eqn:Hsplit.
      destruct split as [block rest].
      simpl.
      constructor.
      * apply (proj1 (split_digits8_canonical _ _ _ Hxs (eq_sym Hsplit))).
      * apply digits_to_bigint_blocks_canonical.
        exact (proj2 (split_digits8_canonical _ _ _ Hxs (eq_sym Hsplit))).
Qed.

Lemma digits_to_bigint_canonical :
  forall xs,
    Forall canonical_digit xs ->
    canonical_bigint (digits_to_bigint xs).
Proof.
  intros xs Hxs.
  unfold digits_to_bigint.
  apply trim_bigint_canonical.
  replace (rev (digits_to_bigint_rev_aux (List.length xs) xs []))
    with (digits_to_bigint_blocks (List.length xs) xs).
  apply digits_to_bigint_blocks_canonical.
  exact Hxs.
  symmetry.
  rewrite digits_to_bigint_rev_aux_rev.
  simpl.
  reflexivity.
Qed.

Lemma digits_of_N_aux_canonical :
  forall fuel x,
    Forall canonical_digit (digits_of_N_aux fuel x).
Proof.
  induction fuel as [|fuel IH]; intros x.
  - constructor.
  - simpl.
    destruct (N.eqb x 0%N) eqn:Hx.
    + constructor.
    + constructor.
      * unfold canonical_digit.
        rewrite u63_of_Z_exact.
        2:{
          split.
          - apply N2Z.is_nonneg.
          - rewrite digit_mask_N_eq_ones.
            rewrite N.land_ones.
            assert (Hlt :
              (x mod 2 ^ N.of_nat digit_shift_nat < digit_base_N)%N).
            {
              rewrite digit_base_N_eq_pow2.
              apply N.mod_lt.
              discriminate.
            }
            apply N2Z.inj_lt in Hlt.
            rewrite digit_base_N_to_Z in Hlt.
            pose proof digit_base_lt_wB as Hbase.
            exact (Z.lt_trans _ _ _ Hlt Hbase).
        }
        split.
        -- apply N2Z.is_nonneg.
        -- rewrite digit_mask_N_eq_ones.
           rewrite N.land_ones.
           assert (Hlt :
             (x mod 2 ^ N.of_nat digit_shift_nat < digit_base_N)%N).
           {
             rewrite digit_base_N_eq_pow2.
             apply N.mod_lt.
             discriminate.
           }
           apply N2Z.inj_lt in Hlt.
           rewrite digit_base_N_to_Z in Hlt.
           exact Hlt.
      * apply IH.
Qed.

Lemma digits_to_N_bigint_digits_u63_flat :
  forall x,
    digits_to_N (bigint_digits_u63_flat x) = bigint_to_N x.
Proof.
  intros x.
  unfold bigint_to_N.
  rewrite bigint_digits_u63_eq_flat.
  reflexivity.
Qed.

Lemma bigint_to_N_digits_to_bigint :
  forall xs,
    Forall canonical_digit xs ->
    bigint_to_N (digits_to_bigint xs) = digits_to_N xs.
Proof.
  intros xs Hxs.
  apply N2Z.inj.
  rewrite bigint_to_N_value.
  - rewrite digits_to_bigint_value.
    rewrite <- digits_to_N_value.
    + reflexivity.
    + exact Hxs.
  - apply digits_to_bigint_canonical.
    exact Hxs.
Qed.

Lemma digits_of_N_aux_value :
  forall fuel x,
    digits_to_N (digits_of_N_aux fuel x) =
      (x mod (digit_base_N ^ N.of_nat fuel))%N.
Proof.
  induction fuel as [|fuel IH]; intros x.
  - simpl.
    rewrite N.mod_1_r.
    reflexivity.
  - cbn [digits_to_N digits_of_N_aux].
    destruct (N.eqb_spec x 0%N) as [->|Hx].
    + cbn [digits_to_N digits_of_N_aux].
      rewrite N.mod_0_l by discriminate.
      reflexivity.
    + cbn [digits_to_N].
      rewrite IH.
      rewrite digit_mask_N_eq_ones.
      rewrite N.land_ones.
      rewrite digit_base_N_eq_pow2.
      assert (Hlow :
        (Z.to_N (Uint63.to_Z (Uint63.of_Z (Z.of_N (x mod 2 ^ N.of_nat digit_shift_nat)))) =
         (x mod 2 ^ N.of_nat digit_shift_nat))%N).
      {
        apply N2Z.inj.
        rewrite Z2N.id.
        2:{
          pose proof Uint63.to_Z_bounded
            (Uint63.of_Z (Z.of_N (x mod 2 ^ N.of_nat digit_shift_nat))) as Hbound.
          lia.
        }
        rewrite u63_of_Z_exact.
        - reflexivity.
        - split.
          + apply N2Z.is_nonneg.
          + rewrite N2Z.inj_mod.
            assert (Z.of_N (2 ^ N.of_nat digit_shift_nat) = digit_base_z).
            {
              rewrite <- digit_base_N_eq_pow2.
              apply digit_base_N_to_Z.
            }
            rewrite H.
            assert ((Z.of_N x mod digit_base_z < digit_base_z)%Z).
            {
              apply Z.mod_pos_bound.
              change (0 < 262144)%Z.
              lia.
            }
            pose proof digit_base_lt_wB as Hbase.
            lia.
      }
      rewrite Hlow.
      rewrite N.shiftr_div_pow2.
      rewrite Nat2N.inj_succ.
      rewrite N.pow_succ_r'.
      replace (2 ^ N.of_nat digit_shift_nat)%N with digit_base_N by
        (symmetry; apply digit_base_N_eq_pow2).
      rewrite N.Div0.mod_mul_r.
      reflexivity.
Qed.

Lemma bigint_to_N_bigint_of_N :
  forall x,
    bigint_to_N (bigint_of_N x) = x.
Proof.
  intros x.
  unfold bigint_of_N.
  rewrite bigint_to_N_digits_to_bigint.
  - rewrite digits_of_N_aux_value.
    apply N.mod_small.
    rewrite Nat2N.inj_succ.
    rewrite digit_base_N_eq_pow2.
    rewrite <- N.pow_mul_r.
    rewrite N2Nat.id.
    eapply N.lt_le_trans.
    + apply N.size_gt.
    + apply N.pow_le_mono_r.
      * discriminate.
      * eapply N.le_trans.
        -- apply N.le_succ_diag_r.
        -- assert (Hshift : (1 <= N.of_nat digit_shift_nat)%N).
           { cbv [digit_shift_nat]. compute. discriminate. }
           apply (N.mul_le_mono_r 1 (N.of_nat digit_shift_nat) (N.succ (N.size x)))
             in Hshift.
           rewrite N.mul_1_l in Hshift.
           exact Hshift.
  - apply digits_of_N_aux_canonical.
Qed.

Lemma bigint_of_N_canonical :
  forall x,
    canonical_bigint (bigint_of_N x).
Proof.
  intros x.
  unfold bigint_of_N.
  apply digits_to_bigint_canonical.
  apply digits_of_N_aux_canonical.
Qed.

Lemma u63_add_small :
  forall x y,
    (0 <= Uint63.to_Z x + Uint63.to_Z y < wB)%Z ->
    Uint63.to_Z (Uint63.add x y) = Uint63.to_Z x + Uint63.to_Z y.
Proof.
  intros x y Hxy.
  rewrite Uint63.add_spec.
  apply Z.mod_small.
  exact Hxy.
Qed.

Lemma u63_mul_small :
  forall x y,
    (0 <= Uint63.to_Z x * Uint63.to_Z y < wB)%Z ->
    Uint63.to_Z (Uint63.mul x y) = Uint63.to_Z x * Uint63.to_Z y.
Proof.
  intros x y Hxy.
  rewrite Uint63.mul_spec.
  apply Z.mod_small.
  exact Hxy.
Qed.

Lemma carry_chain8_add_value :
  forall z0 z1 z2 z3 z4 z5 z6 z7
         c0 c1 c2 c3 c4 c5 c6 c7
         x0 x1 x2 x3 x4 x5 x6 x7
         y0 y1 y2 y3 y4 y5 y6 y7
         carry,
    z0 + digit_base_z * c0 = x0 + y0 + carry ->
    z1 + digit_base_z * c1 = x1 + y1 + c0 ->
    z2 + digit_base_z * c2 = x2 + y2 + c1 ->
    z3 + digit_base_z * c3 = x3 + y3 + c2 ->
    z4 + digit_base_z * c4 = x4 + y4 + c3 ->
    z5 + digit_base_z * c5 = x5 + y5 + c4 ->
    z6 + digit_base_z * c6 = x6 + y6 + c5 ->
    z7 + digit_base_z * c7 = x7 + y7 + c6 ->
    digits_value [z0; z1; z2; z3; z4; z5; z6; z7] + digit_base8_z * c7 =
      digits_value [x0; x1; x2; x3; x4; x5; x6; x7] +
      digits_value [y0; y1; y2; y3; y4; y5; y6; y7] + carry.
Proof.
  cbv [digits_value digit_base8_z digit_base_z].
  nia.
Qed.

Lemma carry_chain8_mul_value :
  forall z0 z1 z2 z3 z4 z5 z6 z7
         c0 c1 c2 c3 c4 c5 c6 c7
         m x0 x1 x2 x3 x4 x5 x6 x7
         carry,
    z0 + digit_base_z * c0 = m * x0 + carry ->
    z1 + digit_base_z * c1 = m * x1 + c0 ->
    z2 + digit_base_z * c2 = m * x2 + c1 ->
    z3 + digit_base_z * c3 = m * x3 + c2 ->
    z4 + digit_base_z * c4 = m * x4 + c3 ->
    z5 + digit_base_z * c5 = m * x5 + c4 ->
    z6 + digit_base_z * c6 = m * x6 + c5 ->
    z7 + digit_base_z * c7 = m * x7 + c6 ->
    digits_value [z0; z1; z2; z3; z4; z5; z6; z7] + digit_base8_z * c7 =
      m * digits_value [x0; x1; x2; x3; x4; x5; x6; x7] + carry.
Proof.
  cbv [digits_value digit_base8_z digit_base_z].
  nia.
Qed.

Lemma add_digit_with_carry_correct :
  forall x y carry digit carry',
    canonical_digit x ->
    canonical_digit y ->
    canonical_digit carry ->
    add_digit_with_carry x y carry = (digit, carry') ->
    canonical_digit digit /\
    canonical_digit carry' /\
    Uint63.to_Z digit + digit_base_z * Uint63.to_Z carry' =
      Uint63.to_Z x + Uint63.to_Z y + Uint63.to_Z carry.
Proof.
  intros x y carry digit carry' Hx Hy Hcarry Hadd.
  unfold add_digit_with_carry in Hadd.
  inversion Hadd; subst; clear Hadd.
  destruct Hx as [Hx0 Hx1].
  destruct Hy as [Hy0 Hy1].
  destruct Hcarry as [Hc0 Hc1].
  set (sum := Uint63.to_Z x + Uint63.to_Z y + Uint63.to_Z carry).
  assert (Hsum : (0 <= sum < wB)%Z).
  {
    unfold sum.
    split.
    - lia.
    - change
        (Uint63.to_Z x + Uint63.to_Z y + Uint63.to_Z carry <
         9223372036854775808)%Z.
      cbv [digit_base_z] in Hx1, Hy1, Hc1.
      lia.
  }
  assert (Htotal :
    Uint63.to_Z (Uint63.add (Uint63.add x y) carry) = sum).
  {
    unfold sum.
    rewrite Uint63.add_spec.
    rewrite u63_add_small.
    - apply Z.mod_small.
      split; [lia|].
      change
        (Uint63.to_Z x + Uint63.to_Z y + Uint63.to_Z carry <
         9223372036854775808)%Z.
      cbv [digit_base_z] in Hx1, Hy1, Hc1.
      lia.
    - split; lia.
  }
  unfold canonical_digit.
  rewrite Uint63.land_spec', Uint63.lsr_spec.
  rewrite Htotal.
  rewrite digit_shift_to_Z.
  replace (Uint63.to_Z digit_mask) with (Z.ones (Z.of_nat digit_shift_nat)).
  2:{ vm_compute. reflexivity. }
  rewrite Z.land_ones by lia.
  split.
  - apply Z.mod_pos_bound.
    change (0 < 262144)%Z.
    lia.
  - split.
    + split.
      * apply Z.div_pos; cbv [digit_base_z]; lia.
      * assert (sum < digit_base_z * digit_base_z)%Z.
        {
          cbv [digit_base_z] in Hx1, Hy1, Hc1 |- *.
          lia.
        }
        apply Z.div_lt_upper_bound.
        -- cbv [digit_base_z]. lia.
        -- replace (digit_base_z * digit_base_z) with (digit_base_z * digit_base_z)%Z by ring.
           exact H.
    + rewrite <- digit_base_N_to_Z.
      rewrite digit_base_N_eq_pow2.
      rewrite N2Z.inj_pow.
      rewrite nat_N_Z.
      replace
        (sum mod 2 ^ Z.of_nat digit_shift_nat +
         sum / 2 ^ Z.of_nat digit_shift_nat * Z.of_N 2 ^ Z.of_nat digit_shift_nat)%Z
        with
        (Z.of_N 2 ^ Z.of_nat digit_shift_nat * (sum / 2 ^ Z.of_nat digit_shift_nat) +
         sum mod 2 ^ Z.of_nat digit_shift_nat)%Z by ring.
      symmetry.
      rewrite Z.add_comm.
      apply Z_div_mod_eq_full.
Qed.

Lemma add_limb8_with_carry_correct :
  forall x y carry block carry',
    canonical_limb8 x ->
    canonical_limb8 y ->
    canonical_digit carry ->
    add_limb8_with_carry x y carry = (block, carry') ->
    canonical_limb8 block /\
    canonical_digit carry' /\
    limb8_value block + digit_base8_z * Uint63.to_Z carry' =
      limb8_value x + limb8_value y + Uint63.to_Z carry.
Proof.
  intros [x0 x1 x2 x3 x4 x5 x6 x7] [y0 y1 y2 y3 y4 y5 y6 y7]
      carry block carry' Hx Hy Hcarry Hadd.
  destruct Hx as [Hx0 [Hx1 [Hx2 [Hx3 [Hx4 [Hx5 [Hx6 Hx7]]]]]]].
  destruct Hy as [Hy0 [Hy1 [Hy2 [Hy3 [Hy4 [Hy5 [Hy6 Hy7]]]]]]].
  destruct (add_digit_with_carry x0 y0 carry) as [z0 c0] eqn:H0.
  destruct (add_digit_with_carry x1 y1 c0) as [z1 c1] eqn:H1.
  destruct (add_digit_with_carry x2 y2 c1) as [z2 c2] eqn:H2.
  destruct (add_digit_with_carry x3 y3 c2) as [z3 c3] eqn:H3.
  destruct (add_digit_with_carry x4 y4 c3) as [z4 c4] eqn:H4.
  destruct (add_digit_with_carry x5 y5 c4) as [z5 c5] eqn:H5.
  destruct (add_digit_with_carry x6 y6 c5) as [z6 c6] eqn:H6.
  destruct (add_digit_with_carry x7 y7 c6) as [z7 c7] eqn:H7.
  unfold add_limb8_with_carry in Hadd.
  cbn in Hadd.
  injection Hadd as Hblock Hcarry'.
  destruct (add_digit_with_carry_correct _ _ _ _ _ Hx0 Hy0 Hcarry H0)
    as [Hz0 [Hc0 Hval0]].
  destruct (add_digit_with_carry_correct _ _ _ _ _ Hx1 Hy1 Hc0 H1)
    as [Hz1 [Hc1 Hval1]].
  destruct (add_digit_with_carry_correct _ _ _ _ _ Hx2 Hy2 Hc1 H2)
    as [Hz2 [Hc2 Hval2]].
  destruct (add_digit_with_carry_correct _ _ _ _ _ Hx3 Hy3 Hc2 H3)
    as [Hz3 [Hc3 Hval3]].
  destruct (add_digit_with_carry_correct _ _ _ _ _ Hx4 Hy4 Hc3 H4)
    as [Hz4 [Hc4 Hval4]].
  destruct (add_digit_with_carry_correct _ _ _ _ _ Hx5 Hy5 Hc4 H5)
    as [Hz5 [Hc5 Hval5]].
  destruct (add_digit_with_carry_correct _ _ _ _ _ Hx6 Hy6 Hc5 H6)
    as [Hz6 [Hc6 Hval6]].
  destruct (add_digit_with_carry_correct _ _ _ _ _ Hx7 Hy7 Hc6 H7)
    as [Hz7 [Hc7 Hval7]].
  destruct Hz0 as [Hz0lo Hz0hi].
  destruct Hz1 as [Hz1lo Hz1hi].
  destruct Hz2 as [Hz2lo Hz2hi].
  destruct Hz3 as [Hz3lo Hz3hi].
  destruct Hz4 as [Hz4lo Hz4hi].
  destruct Hz5 as [Hz5lo Hz5hi].
  destruct Hz6 as [Hz6lo Hz6hi].
  destruct Hz7 as [Hz7lo Hz7hi].
  unfold add_digit_with_carry in H0, H1, H2, H3, H4, H5, H6, H7.
  cbn in H0, H1, H2, H3, H4, H5, H6, H7.
  inversion H0; inversion H1; inversion H2; inversion H3;
    inversion H4; inversion H5; inversion H6; inversion H7; subst.
  cbn [d0 d1 d2 d3 d4 d5 d6 d7] in
    Hval0, Hval1, Hval2, Hval3, Hval4, Hval5, Hval6, Hval7.
  split.
  - unfold canonical_limb8.
    cbn [d0 d1 d2 d3 d4 d5 d6 d7].
    repeat split.
    + exact Hz0lo.
    + exact Hz0hi.
    + exact Hz1lo.
    + exact Hz1hi.
    + exact Hz2lo.
    + exact Hz2hi.
    + exact Hz3lo.
    + exact Hz3hi.
    + exact Hz4lo.
    + exact Hz4hi.
    + exact Hz5lo.
    + exact Hz5hi.
    + exact Hz6lo.
    + exact Hz6hi.
    + exact Hz7lo.
    + exact Hz7hi.
  - split.
    + exact Hc7.
    + cbv [limb8_value limb8_digits_z digits_value digit_base8_z].
      cbn [map].
      eapply carry_chain8_add_value;
        eexact Hval0 || eexact Hval1 || eexact Hval2 || eexact Hval3 ||
        eexact Hval4 || eexact Hval5 || eexact Hval6 || eexact Hval7.
Qed.

Lemma cons_block_if_needed_correct :
  forall x xs,
    canonical_limb8 x ->
    canonical_bigint xs ->
    canonical_bigint (cons_block_if_needed x xs) /\
    bigint_value (cons_block_if_needed x xs) = bigint_value (x :: xs).
Proof.
  intros x xs Hx Hxs.
  unfold cons_block_if_needed.
  destruct xs as [|b bs].
  - destruct (limb8_eqb x zero_limb8) eqn:Hxz.
    + apply limb8_eqb_eq in Hxz.
      subst x.
      split.
      * constructor.
      * simpl.
        reflexivity.
    + split.
      * constructor; [exact Hx|constructor].
      * reflexivity.
  - split.
    + constructor; assumption.
    + reflexivity.
Qed.

Lemma add_bigint_aux_correct :
  forall fuel carry xs ys,
    canonical_bigint xs ->
    canonical_bigint ys ->
    canonical_digit carry ->
    (List.length xs <= fuel)%nat ->
    (List.length ys <= fuel)%nat ->
    canonical_bigint (add_bigint_aux (S fuel) carry xs ys) /\
    bigint_value (add_bigint_aux (S fuel) carry xs ys) =
      bigint_value xs + bigint_value ys + Uint63.to_Z carry.
Proof.
  induction fuel as [|fuel IH]; intros carry xs ys Hx Hy Hcarry Hlx Hly.
  - destruct xs as [|x xs]; destruct ys as [|y ys]; simpl in Hlx, Hly; try lia.
    + destruct (Uint63.eqb carry zero_digit) eqn:Hcz.
      * simpl. rewrite Hcz.
        split.
        -- constructor.
        -- apply Uint63.eqb_spec in Hcz.
           subst carry.
           rewrite zero_digit_to_Z.
           reflexivity.
      * simpl. rewrite Hcz.
        split.
        -- constructor.
           ++ apply canonical_limb8_single_digit. exact Hcarry.
           ++ constructor.
        -- change (bigint_value [limb8_single_digit carry] =
                     bigint_value [] + bigint_value [] + Uint63.to_Z carry).
           cbv [bigint_value limb8_single_digit limb8_value limb8_digits_z
                limb8_digits_u63 bigint_digits_z bigint_digits_u63 digits_value].
           cbn [map app].
           repeat rewrite zero_digit_to_Z.
           ring_simplify.
           reflexivity.
  - destruct xs as [|x xs']; destruct ys as [|y ys'].
    + simpl.
      destruct (Uint63.eqb carry zero_digit) eqn:Hcz.
      * split.
        -- constructor.
        -- apply Uint63.eqb_spec in Hcz.
           subst carry.
           rewrite zero_digit_to_Z.
           reflexivity.
      * split.
        -- constructor.
           ++ apply canonical_limb8_single_digit. exact Hcarry.
           ++ constructor.
        -- change (bigint_value [limb8_single_digit carry] =
                     bigint_value [] + bigint_value [] + Uint63.to_Z carry).
           cbv [bigint_value limb8_single_digit limb8_value limb8_digits_z
                limb8_digits_u63 bigint_digits_z bigint_digits_u63 digits_value].
           cbn [map app].
           repeat rewrite zero_digit_to_Z.
           ring_simplify.
           reflexivity.
    + inversion Hy as [|y0 ys0 Hy0 Hyrest]; subst.
      change
        (canonical_bigint
           (let '(block, carry') := add_limb8_with_carry zero_limb8 y carry in
            cons_block_if_needed block (add_bigint_aux (S fuel) carry' [] ys')) /\
         bigint_value
           (let '(block, carry') := add_limb8_with_carry zero_limb8 y carry in
            cons_block_if_needed block (add_bigint_aux (S fuel) carry' [] ys')) =
           bigint_value [] + bigint_value (y :: ys') + Uint63.to_Z carry).
      destruct (add_limb8_with_carry zero_limb8 y carry) as [block carry'] eqn:Hblock.
      destruct
        (add_limb8_with_carry_correct zero_limb8 y carry block carry'
           canonical_zero_limb8 Hy0 Hcarry Hblock)
        as [Hblock_can [Hcarry' Hblock_val]].
      destruct (IH carry' [] ys' (Forall_nil _) Hyrest Hcarry' (Nat.le_0_l _) (le_S_n _ _ Hly))
        as [Hrec_can Hrec_val].
      destruct (cons_block_if_needed_correct block (add_bigint_aux (S fuel) carry' [] ys')
          Hblock_can Hrec_can) as [Hcan Hval].
      split.
      * exact Hcan.
      * rewrite Hval.
        rewrite bigint_value_cons.
        rewrite Hrec_val.
        rewrite bigint_value_cons.
        change
          (limb8_value block +
           digit_base8_z * (bigint_value [] + bigint_value ys' + Uint63.to_Z carry') =
           bigint_value [] +
           (limb8_value y + digit_base8_z * bigint_value ys') +
           Uint63.to_Z carry).
        replace
          (limb8_value block +
           digit_base8_z * (bigint_value ys' + Uint63.to_Z carry'))
          with
          ((limb8_value block + digit_base8_z * Uint63.to_Z carry') +
           digit_base8_z * bigint_value ys') by ring.
        replace
          ((limb8_value block + digit_base8_z * Uint63.to_Z carry') +
           digit_base8_z * bigint_value ys')
          with
          ((limb8_value zero_limb8 + limb8_value y + Uint63.to_Z carry) +
           digit_base8_z * bigint_value ys')
          by (pose proof Hblock_val as Hb; lia).
        replace (bigint_value []) with 0 by reflexivity.
        pose proof limb8_value_zero_limb8 as Hz0.
        lia.
    + inversion Hx as [|x0 xs0 Hx0 Hxrest]; subst.
      change
        (canonical_bigint
           (let '(block, carry') := add_limb8_with_carry x zero_limb8 carry in
            cons_block_if_needed block (add_bigint_aux (S fuel) carry' xs' [])) /\
         bigint_value
           (let '(block, carry') := add_limb8_with_carry x zero_limb8 carry in
            cons_block_if_needed block (add_bigint_aux (S fuel) carry' xs' [])) =
           bigint_value (x :: xs') + bigint_value [] + Uint63.to_Z carry).
      destruct (add_limb8_with_carry x zero_limb8 carry) as [block carry'] eqn:Hblock.
      destruct
        (add_limb8_with_carry_correct x zero_limb8 carry block carry'
           Hx0 canonical_zero_limb8 Hcarry Hblock)
        as [Hblock_can [Hcarry' Hblock_val]].
      destruct (IH carry' xs' [] Hxrest (Forall_nil _) Hcarry' (le_S_n _ _ Hlx) (Nat.le_0_l _))
        as [Hrec_can Hrec_val].
      destruct (cons_block_if_needed_correct block (add_bigint_aux (S fuel) carry' xs' [])
          Hblock_can Hrec_can) as [Hcan Hval].
      split.
      * exact Hcan.
      * rewrite Hval.
        rewrite bigint_value_cons.
        rewrite Hrec_val.
        rewrite bigint_value_cons.
        change
          (limb8_value block +
           digit_base8_z * (bigint_value xs' + bigint_value [] + Uint63.to_Z carry') =
           (limb8_value x + digit_base8_z * bigint_value xs') +
           bigint_value [] +
           Uint63.to_Z carry).
        replace
          (limb8_value block +
           digit_base8_z * (bigint_value xs' + Uint63.to_Z carry'))
          with
          ((limb8_value block + digit_base8_z * Uint63.to_Z carry') +
           digit_base8_z * bigint_value xs') by ring.
        replace
          ((limb8_value block + digit_base8_z * Uint63.to_Z carry') +
           digit_base8_z * bigint_value xs')
          with
          ((limb8_value x + limb8_value zero_limb8 + Uint63.to_Z carry) +
           digit_base8_z * bigint_value xs')
          by (pose proof Hblock_val as Hb; lia).
        replace (bigint_value []) with 0 by reflexivity.
        pose proof limb8_value_zero_limb8 as Hz0.
        lia.
    + inversion Hx as [|x0 xs0 Hx0 Hxrest]; subst.
      inversion Hy as [|y0 ys0 Hy0 Hyrest]; subst.
      change
        (canonical_bigint
           (let '(block, carry') := add_limb8_with_carry x y carry in
            cons_block_if_needed block (add_bigint_aux (S fuel) carry' xs' ys')) /\
         bigint_value
           (let '(block, carry') := add_limb8_with_carry x y carry in
            cons_block_if_needed block (add_bigint_aux (S fuel) carry' xs' ys')) =
           bigint_value (x :: xs') + bigint_value (y :: ys') + Uint63.to_Z carry).
      destruct (add_limb8_with_carry x y carry) as [block carry'] eqn:Hblock.
      destruct (add_limb8_with_carry_correct x y carry block carry')
        as [Hblock_can [Hcarry' Hblock_val]];
        try assumption.
      destruct (IH carry' xs' ys' Hxrest Hyrest Hcarry' (le_S_n _ _ Hlx) (le_S_n _ _ Hly))
        as [Hrec_can Hrec_val].
      destruct (cons_block_if_needed_correct block (add_bigint_aux (S fuel) carry' xs' ys')
          Hblock_can Hrec_can) as [Hcan Hval].
      split.
      * exact Hcan.
      * rewrite Hval.
        rewrite bigint_value_cons.
        rewrite Hrec_val.
        rewrite bigint_value_cons.
        rewrite bigint_value_cons.
        replace
          (limb8_value block +
           digit_base8_z * (bigint_value xs' + bigint_value ys' + Uint63.to_Z carry'))
          with
          ((limb8_value block + digit_base8_z * Uint63.to_Z carry') +
           digit_base8_z * bigint_value xs' +
           digit_base8_z * bigint_value ys') by ring.
        rewrite Hblock_val.
        ring.
Qed.

Theorem bigint_add_correct :
  forall x y,
    canonical_bigint x ->
    canonical_bigint y ->
    canonical_bigint (bigint_add x y) /\
    bigint_value (bigint_add x y) = bigint_value x + bigint_value y.
Proof.
  intros x y Hx Hy.
  unfold bigint_add.
  destruct (add_bigint_aux_correct (Nat.max (List.length x) (List.length y))
      zero_digit x y Hx Hy canonical_zero_digit (Nat.le_max_l _ _) (Nat.le_max_r _ _))
    as [Hcan Hval].
  split; [exact Hcan|].
  rewrite zero_digit_to_Z in Hval.
  ring_simplify in Hval.
  exact Hval.
Qed.

Theorem bigint_add_to_N :
  forall x y,
    canonical_bigint x ->
    canonical_bigint y ->
    bigint_to_N (bigint_add x y) = (bigint_to_N x + bigint_to_N y)%N.
Proof.
  intros x y Hx Hy.
  apply N2Z.inj.
  destruct (bigint_add_correct x y Hx Hy) as [Hcan Hval].
  rewrite N2Z.inj_add.
  rewrite bigint_to_N_value by exact Hcan.
  rewrite bigint_to_N_value by exact Hx.
  rewrite bigint_to_N_value by exact Hy.
  rewrite Hval.
  reflexivity.
Qed.

Lemma mul_digit_with_carry_correct :
  forall m x carry digit carry',
    canonical_digit m ->
    canonical_digit x ->
    canonical_digit carry ->
    mul_digit_with_carry m x carry = (digit, carry') ->
    canonical_digit digit /\
    canonical_digit carry' /\
    Uint63.to_Z digit + digit_base_z * Uint63.to_Z carry' =
      Uint63.to_Z m * Uint63.to_Z x + Uint63.to_Z carry.
Proof.
  intros m x carry digit carry' Hm Hx Hcarry Hmul.
  unfold mul_digit_with_carry in Hmul.
  inversion Hmul; subst; clear Hmul.
  destruct Hm as [Hm0 Hm1].
  destruct Hx as [Hx0 Hx1].
  destruct Hcarry as [Hc0 Hc1].
  set (sum := Uint63.to_Z m * Uint63.to_Z x + Uint63.to_Z carry).
  assert (Hsum : (0 <= sum < wB)%Z).
  {
    unfold sum.
    split.
    - lia.
    - change
        (Uint63.to_Z m * Uint63.to_Z x + Uint63.to_Z carry <
         9223372036854775808)%Z.
      cbv [digit_base_z] in Hm1, Hx1, Hc1.
      nia.
  }
  assert (Htotal :
    Uint63.to_Z (Uint63.add (Uint63.mul m x) carry) = sum).
  {
    unfold sum.
    rewrite Uint63.add_spec.
    rewrite u63_mul_small.
    - apply Z.mod_small.
      split; [lia|].
      change
        (Uint63.to_Z m * Uint63.to_Z x + Uint63.to_Z carry <
         9223372036854775808)%Z.
      cbv [digit_base_z] in Hm1, Hx1, Hc1.
      nia.
    - split; lia.
  }
  unfold canonical_digit.
  rewrite Uint63.land_spec', Uint63.lsr_spec.
  rewrite Htotal.
  rewrite digit_shift_to_Z.
  replace (Uint63.to_Z digit_mask) with (Z.ones (Z.of_nat digit_shift_nat)).
  2:{ vm_compute. reflexivity. }
  rewrite Z.land_ones by lia.
  split.
  - apply Z.mod_pos_bound.
    change (0 < 262144)%Z.
    lia.
  - split.
    + split.
      * apply Z.div_pos; cbv [digit_base_z]; lia.
      * assert (sum < digit_base_z * digit_base_z)%Z.
        {
          cbv [digit_base_z] in Hm1, Hx1, Hc1 |- *.
          nia.
        }
        apply Z.div_lt_upper_bound.
        -- cbv [digit_base_z]. lia.
        -- replace (digit_base_z * digit_base_z) with (digit_base_z * digit_base_z)%Z by ring.
           exact H.
    + rewrite <- digit_base_N_to_Z.
      rewrite digit_base_N_eq_pow2.
      rewrite N2Z.inj_pow.
      rewrite nat_N_Z.
      replace
        (sum mod 2 ^ Z.of_nat digit_shift_nat +
         sum / 2 ^ Z.of_nat digit_shift_nat * Z.of_N 2 ^ Z.of_nat digit_shift_nat)%Z
        with
        (Z.of_N 2 ^ Z.of_nat digit_shift_nat * (sum / 2 ^ Z.of_nat digit_shift_nat) +
         sum mod 2 ^ Z.of_nat digit_shift_nat)%Z by ring.
      symmetry.
      rewrite Z.add_comm.
      apply Z_div_mod_eq_full.
Qed.

Lemma mul_limb8_digit_with_carry_correct :
  forall m x carry block carry',
    canonical_digit m ->
    canonical_limb8 x ->
    canonical_digit carry ->
    mul_limb8_digit_with_carry m x carry = (block, carry') ->
    canonical_limb8 block /\
    canonical_digit carry' /\
    limb8_value block + digit_base8_z * Uint63.to_Z carry' =
      Uint63.to_Z m * limb8_value x + Uint63.to_Z carry.
Proof.
  intros m [x0 x1 x2 x3 x4 x5 x6 x7] carry block carry' Hm Hx Hcarry Hmul.
  destruct Hx as [Hx0 [Hx1 [Hx2 [Hx3 [Hx4 [Hx5 [Hx6 Hx7]]]]]]].
  unfold mul_limb8_digit_with_carry in Hmul.
  destruct (mul_digit_with_carry m x0 carry) as [z0 c0] eqn:H0.
  destruct (mul_digit_with_carry m x1 c0) as [z1 c1] eqn:H1.
  destruct (mul_digit_with_carry m x2 c1) as [z2 c2] eqn:H2.
  destruct (mul_digit_with_carry m x3 c2) as [z3 c3] eqn:H3.
  destruct (mul_digit_with_carry m x4 c3) as [z4 c4] eqn:H4.
  destruct (mul_digit_with_carry m x5 c4) as [z5 c5] eqn:H5.
  destruct (mul_digit_with_carry m x6 c5) as [z6 c6] eqn:H6.
  destruct (mul_digit_with_carry m x7 c6) as [z7 c7] eqn:H7.
  inversion Hmul; subst; clear Hmul.
  destruct (mul_digit_with_carry_correct _ _ _ _ _ Hm Hx0 Hcarry H0)
    as [Hz0 [Hc0 Hval0]].
  destruct (mul_digit_with_carry_correct _ _ _ _ _ Hm Hx1 Hc0 H1)
    as [Hz1 [Hc1 Hval1]].
  destruct (mul_digit_with_carry_correct _ _ _ _ _ Hm Hx2 Hc1 H2)
    as [Hz2 [Hc2 Hval2]].
  destruct (mul_digit_with_carry_correct _ _ _ _ _ Hm Hx3 Hc2 H3)
    as [Hz3 [Hc3 Hval3]].
  destruct (mul_digit_with_carry_correct _ _ _ _ _ Hm Hx4 Hc3 H4)
    as [Hz4 [Hc4 Hval4]].
  destruct (mul_digit_with_carry_correct _ _ _ _ _ Hm Hx5 Hc4 H5)
    as [Hz5 [Hc5 Hval5]].
  destruct (mul_digit_with_carry_correct _ _ _ _ _ Hm Hx6 Hc5 H6)
    as [Hz6 [Hc6 Hval6]].
  destruct (mul_digit_with_carry_correct _ _ _ _ _ Hm Hx7 Hc6 H7)
    as [Hz7 [Hc7 Hval7]].
  destruct Hz0 as [Hz0lo Hz0hi].
  destruct Hz1 as [Hz1lo Hz1hi].
  destruct Hz2 as [Hz2lo Hz2hi].
  destruct Hz3 as [Hz3lo Hz3hi].
  destruct Hz4 as [Hz4lo Hz4hi].
  destruct Hz5 as [Hz5lo Hz5hi].
  destruct Hz6 as [Hz6lo Hz6hi].
  destruct Hz7 as [Hz7lo Hz7hi].
  unfold mul_digit_with_carry in H0, H1, H2, H3, H4, H5, H6, H7.
  cbn in H0, H1, H2, H3, H4, H5, H6, H7.
  inversion H0; inversion H1; inversion H2; inversion H3;
    inversion H4; inversion H5; inversion H6; inversion H7; subst.
  split.
  - unfold canonical_limb8.
    cbn [d0 d1 d2 d3 d4 d5 d6 d7].
    repeat match goal with
    | |- _ /\ _ => split
    end.
    + split; [exact Hz0lo|exact Hz0hi].
    + split; [exact Hz1lo|exact Hz1hi].
    + split; [exact Hz2lo|exact Hz2hi].
    + split; [exact Hz3lo|exact Hz3hi].
    + split; [exact Hz4lo|exact Hz4hi].
    + split; [exact Hz5lo|exact Hz5hi].
    + split; [exact Hz6lo|exact Hz6hi].
    + split; [exact Hz7lo|exact Hz7hi].
  - split.
    + exact Hc7.
    + unfold limb8_value.
      cbn [limb8_digits_z limb8_digits_u63 digits_value].
      exact (carry_chain8_mul_value
        (Uint63.to_Z ((m * x0 + carry) land digit_mask))
        (Uint63.to_Z ((m * x1 + (m * x0 + carry) >> digit_shift) land digit_mask))
        (Uint63.to_Z ((m * x2 + (m * x1 + (m * x0 + carry) >> digit_shift) >> digit_shift) land digit_mask))
        (Uint63.to_Z ((m * x3 + (m * x2 + (m * x1 + (m * x0 + carry) >> digit_shift) >> digit_shift) >> digit_shift) land digit_mask))
        (Uint63.to_Z ((m * x4 + (m * x3 + (m * x2 + (m * x1 + (m * x0 + carry) >> digit_shift) >> digit_shift) >> digit_shift) >> digit_shift) land digit_mask))
        (Uint63.to_Z ((m * x5 + (m * x4 + (m * x3 + (m * x2 + (m * x1 + (m * x0 + carry) >> digit_shift) >> digit_shift) >> digit_shift) >> digit_shift) >> digit_shift) land digit_mask))
        (Uint63.to_Z ((m * x6 + (m * x5 + (m * x4 + (m * x3 + (m * x2 + (m * x1 + (m * x0 + carry) >> digit_shift) >> digit_shift) >> digit_shift) >> digit_shift) >> digit_shift) >> digit_shift) land digit_mask))
        (Uint63.to_Z ((m * x7 + (m * x6 + (m * x5 + (m * x4 + (m * x3 + (m * x2 + (m * x1 + (m * x0 + carry) >> digit_shift) >> digit_shift) >> digit_shift) >> digit_shift) >> digit_shift) >> digit_shift) >> digit_shift) land digit_mask))
        (Uint63.to_Z ((m * x0 + carry) >> digit_shift))
        (Uint63.to_Z ((m * x1 + (m * x0 + carry) >> digit_shift) >> digit_shift))
        (Uint63.to_Z ((m * x2 + (m * x1 + (m * x0 + carry) >> digit_shift) >> digit_shift) >> digit_shift))
        (Uint63.to_Z ((m * x3 + (m * x2 + (m * x1 + (m * x0 + carry) >> digit_shift) >> digit_shift) >> digit_shift) >> digit_shift))
        (Uint63.to_Z ((m * x4 + (m * x3 + (m * x2 + (m * x1 + (m * x0 + carry) >> digit_shift) >> digit_shift) >> digit_shift) >> digit_shift) >> digit_shift))
        (Uint63.to_Z ((m * x5 + (m * x4 + (m * x3 + (m * x2 + (m * x1 + (m * x0 + carry) >> digit_shift) >> digit_shift) >> digit_shift) >> digit_shift) >> digit_shift) >> digit_shift))
        (Uint63.to_Z ((m * x6 + (m * x5 + (m * x4 + (m * x3 + (m * x2 + (m * x1 + (m * x0 + carry) >> digit_shift) >> digit_shift) >> digit_shift) >> digit_shift) >> digit_shift) >> digit_shift) >> digit_shift))
        (Uint63.to_Z ((m * x7 + (m * x6 + (m * x5 + (m * x4 + (m * x3 + (m * x2 + (m * x1 + (m * x0 + carry) >> digit_shift) >> digit_shift) >> digit_shift) >> digit_shift) >> digit_shift) >> digit_shift) >> digit_shift) >> digit_shift))
        (Uint63.to_Z m)
        (Uint63.to_Z x0) (Uint63.to_Z x1) (Uint63.to_Z x2) (Uint63.to_Z x3)
        (Uint63.to_Z x4) (Uint63.to_Z x5) (Uint63.to_Z x6) (Uint63.to_Z x7)
        (Uint63.to_Z carry) Hval0 Hval1 Hval2 Hval3 Hval4 Hval5 Hval6 Hval7).
Qed.

Lemma bigint_mul_digit_aux_correct :
  forall fuel m carry xs,
    canonical_digit m ->
    canonical_bigint xs ->
    canonical_digit carry ->
    (List.length xs <= fuel)%nat ->
    canonical_bigint (bigint_mul_digit_aux (S fuel) m carry xs) /\
    bigint_value (bigint_mul_digit_aux (S fuel) m carry xs) =
      Uint63.to_Z m * bigint_value xs + Uint63.to_Z carry.
Proof.
  induction fuel as [|fuel IH]; intros m carry xs Hm Hx Hcarry Hlx.
  - destruct xs as [|x xs]; simpl in Hlx; try lia.
    simpl.
    destruct (Uint63.eqb carry zero_digit) eqn:Hcz.
    + split.
      * constructor.
      * apply Uint63.eqb_spec in Hcz.
        subst carry.
        rewrite zero_digit_to_Z.
        replace (bigint_value []) with 0 by reflexivity.
        lia.
    + split.
      * constructor.
        -- apply canonical_limb8_single_digit. exact Hcarry.
        -- constructor.
      * change (bigint_value [limb8_single_digit carry] =
                  Uint63.to_Z m * bigint_value [] + Uint63.to_Z carry).
        cbv [bigint_value limb8_single_digit limb8_value limb8_digits_z
             limb8_digits_u63 bigint_digits_z bigint_digits_u63 digits_value].
        cbn [map app].
        repeat rewrite zero_digit_to_Z.
        ring_simplify.
        reflexivity.
  - destruct xs as [|x xs'].
    + simpl.
      destruct (Uint63.eqb carry zero_digit) eqn:Hcz.
      * split.
        -- constructor.
        -- apply Uint63.eqb_spec in Hcz.
           subst carry.
           rewrite zero_digit_to_Z.
           replace (bigint_value []) with 0 by reflexivity.
           lia.
      * split.
        -- constructor.
           ++ apply canonical_limb8_single_digit. exact Hcarry.
           ++ constructor.
        -- change (bigint_value [limb8_single_digit carry] =
                    Uint63.to_Z m * bigint_value [] + Uint63.to_Z carry).
           cbv [bigint_value limb8_single_digit limb8_value limb8_digits_z
                limb8_digits_u63 bigint_digits_z bigint_digits_u63 digits_value].
           cbn [map app].
           repeat rewrite zero_digit_to_Z.
           ring_simplify.
           reflexivity.
    + inversion Hx as [|x0 xs0 Hx0 Hxrest]; subst.
      change
        (canonical_bigint
           (let '(block, carry') := mul_limb8_digit_with_carry m x carry in
            cons_block_if_needed block (bigint_mul_digit_aux (S fuel) m carry' xs')) /\
         bigint_value
           (let '(block, carry') := mul_limb8_digit_with_carry m x carry in
            cons_block_if_needed block (bigint_mul_digit_aux (S fuel) m carry' xs')) =
           Uint63.to_Z m * bigint_value (x :: xs') + Uint63.to_Z carry).
      destruct (mul_limb8_digit_with_carry m x carry) as [block carry'] eqn:Hblock.
      destruct (mul_limb8_digit_with_carry_correct m x carry block carry')
        as [Hblock_can [Hcarry' Hblock_val]];
        try assumption.
      destruct (IH m carry' xs' Hm Hxrest Hcarry' (le_S_n _ _ Hlx))
        as [Hrec_can Hrec_val].
      destruct (cons_block_if_needed_correct block (bigint_mul_digit_aux (S fuel) m carry' xs')
          Hblock_can Hrec_can) as [Hcan Hval].
      split.
      * exact Hcan.
      * rewrite Hval.
        rewrite bigint_value_cons.
        rewrite Hrec_val.
        rewrite bigint_value_cons.
        change
          (limb8_value block +
           digit_base8_z * (Uint63.to_Z m * bigint_value xs' + Uint63.to_Z carry') =
           Uint63.to_Z m * (limb8_value x + digit_base8_z * bigint_value xs') +
           Uint63.to_Z carry).
        replace
          (limb8_value block +
           digit_base8_z * (Uint63.to_Z m * bigint_value xs' + Uint63.to_Z carry'))
          with
          ((limb8_value block + digit_base8_z * Uint63.to_Z carry') +
           Uint63.to_Z m * (digit_base8_z * bigint_value xs')) by ring.
        rewrite Hblock_val.
        ring.
Qed.

Theorem bigint_mul_digit_correct :
  forall m x,
    canonical_digit m ->
    canonical_bigint x ->
    canonical_bigint (bigint_mul_digit m x) /\
    bigint_value (bigint_mul_digit m x) = Uint63.to_Z m * bigint_value x.
Proof.
  intros m x Hm Hx.
  unfold bigint_mul_digit.
  destruct (Uint63.eqb m zero_digit) eqn:Hm0.
  - split.
    + constructor.
    + apply Uint63.eqb_spec in Hm0.
      subst m.
      rewrite zero_digit_to_Z.
      change (0 = 0 * bigint_value x).
      ring.
  - destruct (Uint63.eqb m u63_one) eqn:Hm1.
    + split.
      * exact Hx.
      * apply Uint63.eqb_spec in Hm1.
        subst m.
        change (bigint_value x = 1 * bigint_value x).
        ring.
    + destruct (bigint_mul_digit_aux_correct (List.length x) m zero_digit x Hm Hx canonical_zero_digit (Nat.le_refl _))
        as [Hcan Hval].
      split; [exact Hcan|].
      rewrite zero_digit_to_Z in Hval.
      rewrite Z.add_0_r in Hval.
      exact Hval.
Qed.

Theorem bigint_mul_digit_to_N :
  forall m x,
    canonical_digit m ->
    canonical_bigint x ->
    bigint_to_N (bigint_mul_digit m x) =
      (Z.to_N (Uint63.to_Z m) * bigint_to_N x)%N.
Proof.
  intros m x Hm Hx.
  apply N2Z.inj.
  destruct (bigint_mul_digit_correct m x Hm Hx) as [Hcan Hval].
  rewrite bigint_to_N_value by exact Hcan.
  rewrite N2Z.inj_mul.
  rewrite bigint_to_N_value by exact Hx.
  rewrite Z2N.id by (destruct Hm; lia).
  exact Hval.
Qed.

(* A direct correctness theorem for `bigint_as_digit` is useful for the
   optimized `F_bigint` path, but the core arithmetic proofs above do not
   depend on it. Keeping it out of the checked file for now avoids spending
   time on a proof-shape issue that is orthogonal to the bigint operations
   themselves. *)

Theorem bigint_as_digit_correct :
  forall x m,
    canonical_bigint x ->
    bigint_as_digit x = Some m ->
    bigint_value x = Uint63.to_Z m.
Proof.
  intros x m Hcan Hx.
  destruct x as [|b bs].
  - simpl in Hx.
    inversion Hx; subst; clear Hx.
    rewrite zero_digit_to_Z.
    reflexivity.
  - destruct bs as [|b' bs'].
    + destruct b as [x0 x1 x2 x3 x4 x5 x6 x7].
      simpl in Hx.
      destruct (limb8_high_zero (Limb8 x0 x1 x2 x3 x4 x5 x6 x7)) eqn:Hhigh.
      * inversion Hx; subst; clear Hx.
        unfold limb8_high_zero in Hhigh.
        apply andb_prop in Hhigh.
        destruct Hhigh as [H123456 H7].
        apply andb_prop in H123456.
        destruct H123456 as [H12345 H6].
        apply andb_prop in H12345.
        destruct H12345 as [H1234 H5].
        apply andb_prop in H1234.
        destruct H1234 as [H123 H4].
        apply andb_prop in H123.
        destruct H123 as [H12 H3].
        apply andb_prop in H12.
        destruct H12 as [H1 H2].
        apply Uint63.eqb_spec in H1.
        apply Uint63.eqb_spec in H2.
        apply Uint63.eqb_spec in H3.
        apply Uint63.eqb_spec in H4.
        apply Uint63.eqb_spec in H5.
        apply Uint63.eqb_spec in H6.
        apply Uint63.eqb_spec in H7.
        simpl in H1, H2, H3, H4, H5, H6, H7.
        subst.
        replace
          ({|
             d0 := m;
             d1 := zero_digit;
             d2 := zero_digit;
             d3 := zero_digit;
             d4 := zero_digit;
             d5 := zero_digit;
             d6 := zero_digit;
             d7 := zero_digit
           |})
          with (limb8_single_digit m) by reflexivity.
        rewrite bigint_value_cons.
        replace (bigint_value []) with 0 by reflexivity.
        rewrite limb8_single_digit_value.
        ring.
      * discriminate Hx.
    + simpl in Hx.
      discriminate Hx.
Qed.

Lemma canonical_bigint_firstn :
  forall n x,
    canonical_bigint x ->
    canonical_bigint (firstn n x).
Proof.
  intros n x Hx.
  revert n.
  induction Hx as [|b bs Hb Hbs IH]; intros n.
  - destruct n; constructor.
  - destruct n as [|n].
    + constructor.
    + simpl.
      constructor; [exact Hb|].
      apply IH.
Qed.

Lemma canonical_bigint_skipn :
  forall n x,
    canonical_bigint x ->
    canonical_bigint (skipn n x).
Proof.
  intros n x Hx.
  revert n.
  induction Hx as [|b bs Hb Hbs IH]; intros n.
  - destruct n; constructor.
  - destruct n as [|n].
    + constructor; assumption.
    + simpl.
      apply IH.
Qed.

Lemma bigint_value_firstn_skipn :
  forall n x,
    bigint_value x =
      bigint_value (firstn n x) +
      (digit_base8_z ^ Z.of_nat (List.length (firstn n x))) *
      bigint_value (skipn n x).
Proof.
  intros n x.
  rewrite <- firstn_skipn with (n := n) (l := x) at 1.
  apply bigint_value_app_blocks.
Qed.

Lemma snoc_nonzero_block_canonical :
  forall xs x,
    canonical_bigint xs ->
    canonical_limb8 x ->
    canonical_bigint (snoc_nonzero_block xs x).
Proof.
  intros xs x Hxs Hx.
  unfold snoc_nonzero_block.
  destruct (limb8_eqb x zero_limb8) eqn:Hx0.
  - exact Hxs.
  - apply Forall_app.
    split.
    + exact Hxs.
    + constructor; [exact Hx|constructor].
Qed.

Lemma snoc_nonzero_block_value :
  forall xs x,
    bigint_value (snoc_nonzero_block xs x) = bigint_value (xs ++ [x]).
Proof.
  intros xs x.
  unfold snoc_nonzero_block.
  destruct (limb8_eqb x zero_limb8) eqn:Hx0.
  - apply limb8_eqb_eq in Hx0.
    subst x.
    symmetry.
    apply bigint_value_snoc_zero.
  - reflexivity.
Qed.

Lemma limb8_take_digits_canonical :
  forall k x,
    canonical_limb8 x ->
    canonical_limb8 (limb8_take_digits k x).
Proof.
  intros k [x0 x1 x2 x3 x4 x5 x6 x7] Hx.
  destruct Hx as [Hx0 [Hx1 [Hx2 [Hx3 [Hx4 [Hx5 [Hx6 Hx7]]]]]]].
  destruct Hx0 as [Hx0lo Hx0hi].
  destruct Hx1 as [Hx1lo Hx1hi].
  destruct Hx2 as [Hx2lo Hx2hi].
  destruct Hx3 as [Hx3lo Hx3hi].
  destruct Hx4 as [Hx4lo Hx4hi].
  destruct Hx5 as [Hx5lo Hx5hi].
  destruct Hx6 as [Hx6lo Hx6hi].
  destruct Hx7 as [Hx7lo Hx7hi].
  destruct k as [|[|[|[|[|[|[|[|k]]]]]]]];
    unfold limb8_take_digits, canonical_limb8, canonical_digit, zero_limb8;
    cbn [d0 d1 d2 d3 d4 d5 d6 d7] in *;
    repeat rewrite zero_digit_to_Z;
    repeat split;
    lia.
Qed.

Lemma limb8_take_digits_value :
  forall k x,
    limb8_value (limb8_take_digits k x) =
      digits_value (firstn k (limb8_digits_z x)).
Proof.
  intros k [x0 x1 x2 x3 x4 x5 x6 x7].
  destruct k as [|[|[|[|[|[|[|[|k]]]]]]]];
    unfold limb8_take_digits, limb8_value, limb8_digits_z, limb8_digits_u63;
    cbn [firstn digits_value List.map];
    repeat rewrite zero_digit_to_Z;
    try reflexivity.
  rewrite firstn_all2.
  2:{ cbn. lia. }
  reflexivity.
Qed.

Lemma limb8_take_digits_idem :
  forall k x,
    limb8_take_digits k (limb8_take_digits k x) = limb8_take_digits k x.
Proof.
  intros k [x0 x1 x2 x3 x4 x5 x6 x7].
  destruct k as [|[|[|[|[|[|[|[|k]]]]]]]];
    reflexivity.
Qed.

Lemma shift_right_limb8_digits_small_low_carry_canonical :
  forall k carry x hi lo,
    (k < 8)%nat ->
    canonical_limb8 carry ->
    canonical_limb8 x ->
    carry = limb8_take_digits k carry ->
    shift_right_limb8_digits_small k carry x = (hi, lo) ->
    canonical_limb8 hi /\ canonical_limb8 lo.
Proof.
  intros k [c0 c1 c2 c3 c4 c5 c6 c7] [x0 x1 x2 x3 x4 x5 x6 x7] hi lo Hk Hcarry Hx Hcarryk Hshift.
  destruct Hcarry as [Hc0 [Hc1 [Hc2 [Hc3 [Hc4 [Hc5 [Hc6 Hc7]]]]]]].
  destruct Hx as [Hx0 [Hx1 [Hx2 [Hx3 [Hx4 [Hx5 [Hx6 Hx7]]]]]]].
  destruct Hc0 as [Hc0lo Hc0hi].
  destruct Hc1 as [Hc1lo Hc1hi].
  destruct Hc2 as [Hc2lo Hc2hi].
  destruct Hc3 as [Hc3lo Hc3hi].
  destruct Hc4 as [Hc4lo Hc4hi].
  destruct Hc5 as [Hc5lo Hc5hi].
  destruct Hc6 as [Hc6lo Hc6hi].
  destruct Hc7 as [Hc7lo Hc7hi].
  destruct Hx0 as [Hx0lo Hx0hi].
  destruct Hx1 as [Hx1lo Hx1hi].
  destruct Hx2 as [Hx2lo Hx2hi].
  destruct Hx3 as [Hx3lo Hx3hi].
  destruct Hx4 as [Hx4lo Hx4hi].
  destruct Hx5 as [Hx5lo Hx5hi].
  destruct Hx6 as [Hx6lo Hx6hi].
  destruct Hx7 as [Hx7lo Hx7hi].
  destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; try lia;
    cbn [limb8_take_digits] in Hcarryk;
    inversion Hcarryk; subst; clear Hcarryk;
    unfold shift_right_limb8_digits_small in Hshift;
    cbn [limb8_take_digits] in Hshift;
    inversion Hshift; subst; clear Hshift;
    split;
    unfold canonical_limb8, canonical_digit, zero_limb8;
    cbn [d0 d1 d2 d3 d4 d5 d6 d7] in *;
    repeat rewrite zero_digit_to_Z;
    repeat split;
    lia.
Qed.

Lemma shift_right_limb8_digits_small_low_carry_digits :
  forall k carry x hi lo,
    (k < 8)%nat ->
    carry = limb8_take_digits k carry ->
    shift_right_limb8_digits_small k carry x = (hi, lo) ->
    limb8_digits_z hi =
      skipn k (limb8_digits_z x) ++ firstn k (limb8_digits_z carry).
Proof.
  intros k [c0 c1 c2 c3 c4 c5 c6 c7] [x0 x1 x2 x3 x4 x5 x6 x7] hi lo Hk Hcarryk Hshift.
  destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; try lia;
    cbn [limb8_take_digits] in Hcarryk;
    inversion Hcarryk; subst; clear Hcarryk;
    unfold shift_right_limb8_digits_small in Hshift;
    cbn [limb8_take_digits] in Hshift;
    inversion Hshift; subst; clear Hshift;
    unfold limb8_digits_z, limb8_digits_u63;
    cbn [skipn firstn List.map app];
    repeat rewrite zero_digit_to_Z;
    reflexivity.
Qed.

Lemma shift_right_limb8_digits_small_low :
  forall k carry x hi lo,
    (k < 8)%nat ->
    shift_right_limb8_digits_small k carry x = (hi, lo) ->
    lo = limb8_take_digits k x.
Proof.
  intros k [c0 c1 c2 c3 c4 c5 c6 c7] [x0 x1 x2 x3 x4 x5 x6 x7] hi lo Hk Hshift.
  destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; try lia;
    unfold shift_right_limb8_digits_small in Hshift;
    cbn [limb8_take_digits] in Hshift;
    inversion Hshift; subst; clear Hshift;
    cbn [limb8_take_digits];
    reflexivity.
Qed.

Lemma shift_right_limb8_digits_small_low_carry_value :
  forall k carry x hi lo,
    (k < 8)%nat ->
    carry = limb8_take_digits k carry ->
    shift_right_limb8_digits_small k carry x = (hi, lo) ->
    limb8_value lo + (digit_base_z ^ Z.of_nat k) * limb8_value hi =
      limb8_value x + digit_base8_z * limb8_value carry.
Proof.
  intros k carry x hi lo Hk Hcarryk Hshift.
  pose proof (shift_right_limb8_digits_small_low _ _ _ _ _ Hk Hshift) as Hlo.
  pose proof
    (shift_right_limb8_digits_small_low_carry_digits _ _ _ _ _ Hk Hcarryk Hshift)
    as Hhi.
  subst lo.
  rewrite limb8_take_digits_value.
  change (limb8_value hi) with (digits_value (limb8_digits_z hi)).
  rewrite Hhi.
  rewrite digits_value_app.
  change (limb8_value x) with (digits_value (limb8_digits_z x)).
  assert (Hxsplit :
    digits_value (limb8_digits_z x) =
      digits_value (firstn k (limb8_digits_z x) ++ skipn k (limb8_digits_z x))).
  {
    rewrite firstn_skipn.
    reflexivity.
  }
  rewrite Hxsplit.
  rewrite digits_value_app.
  assert (Hlen_first : (List.length (firstn k (limb8_digits_z x)) = k)%nat).
  {
    rewrite length_firstn, limb8_digits_z_length.
    lia.
  }
  rewrite Hlen_first.
  rewrite Hcarryk.
  rewrite limb8_take_digits_value.
  assert (Hlen_skip :
    (List.length (skipn k (limb8_digits_z x)) = (8 - k))%nat).
  {
    rewrite length_skipn, limb8_digits_z_length.
    lia.
  }
  rewrite Hlen_skip.
  rewrite Z.mul_add_distr_l.
  assert (Hpow :
    (digit_base_z ^ Z.of_nat k) * digit_base_z ^ Z.of_nat (8 - k) =
      digit_base8_z).
  {
    unfold digit_base8_z.
    rewrite <- Z.pow_add_r by lia.
    replace (Z.of_nat k + Z.of_nat (8 - k)) with 8 by lia.
    reflexivity.
  }
  rewrite Z.mul_assoc.
  rewrite Hpow.
  assert (Hcarry_firstn :
    firstn k (limb8_digits_z (limb8_take_digits k carry)) =
      firstn k (limb8_digits_z carry)).
  {
    rewrite Hcarryk.
    rewrite limb8_take_digits_idem.
    reflexivity.
  }
  rewrite Hcarry_firstn.
  ring.
Qed.

Lemma shift_right_bigint_digits_small_aux_length :
  forall k carry rev_blocks acc,
    List.length (shift_right_bigint_digits_small_aux k carry rev_blocks acc) =
      (List.length rev_blocks + List.length acc)%nat.
Proof.
  intros k carry rev_blocks acc.
  revert carry acc.
  induction rev_blocks as [|b bs IH]; intros carry acc.
  - reflexivity.
  - simpl.
    destruct (shift_right_limb8_digits_small k carry b) as [b' carry'].
    rewrite IH.
    simpl.
    lia.
Qed.

Lemma shift_right_bigint_digits_small_aux_app :
  forall k carry rev_blocks acc,
    shift_right_bigint_digits_small_aux k carry rev_blocks acc =
      shift_right_bigint_digits_small_aux k carry rev_blocks nil ++ acc.
Proof.
  intros k carry rev_blocks acc.
  revert carry acc.
  induction rev_blocks as [|b bs IH]; intros carry acc.
  - reflexivity.
  - simpl.
    destruct (shift_right_limb8_digits_small k carry b) as [b' carry'].
    rewrite (IH carry' (b' :: acc)).
    rewrite (IH carry' (b' :: nil)).
    simpl.
    rewrite <- app_assoc.
    reflexivity.
Qed.

Lemma bigint_split_whole_digits_aligned_value :
  forall whole_blocks x,
    (whole_blocks <= List.length x)%nat ->
    let '(high, low) := bigint_split_whole_digits (8 * whole_blocks) x in
    bigint_value x =
      bigint_value low +
      (digit_base_z ^ Z.of_nat (8 * whole_blocks)) * bigint_value high.
Proof.
  intros whole_blocks x Hle.
  unfold bigint_split_whole_digits.
  replace ((8 * whole_blocks / 8)%nat) with whole_blocks.
  2:{
    symmetry.
    rewrite Nat.mul_comm.
    apply Nat.div_mul.
    lia.
  }
  replace ((8 * whole_blocks mod 8)%nat) with 0%nat.
  2:{
    symmetry.
    rewrite Nat.mul_comm.
    apply Nat.mod_mul.
    lia.
  }
  cbn.
  rewrite !trim_bigint_value.
  assert (Hpow :
    digit_base8_z ^ Z.of_nat whole_blocks =
      digit_base_z ^ Z.of_nat (8 * whole_blocks)).
  {
    unfold digit_base8_z.
    rewrite Nat2Z.inj_mul.
    change (Z.of_nat 8) with 8%Z.
    rewrite Z.pow_mul_r by lia.
    reflexivity.
  }
  rewrite (bigint_value_firstn_skipn whole_blocks x).
  rewrite firstn_length_le by exact Hle.
  rewrite Hpow.
  reflexivity.
Qed.

Fixpoint shift_right_bigint_digits_small_carry
    (k : nat) (carry : limb8) (rev_blocks : bigint) : limb8 :=
  match rev_blocks with
  | [] => carry
  | b :: bs =>
      let '(_, carry') := shift_right_limb8_digits_small k carry b in
      shift_right_bigint_digits_small_carry k carry' bs
  end.

Lemma shift_right_bigint_digits_small_carry_last :
  forall k carry rev_blocks b,
    (k < 8)%nat ->
    shift_right_bigint_digits_small_carry k carry (rev_blocks ++ [b]) =
      limb8_take_digits k b.
Proof.
  intros k carry rev_blocks.
  revert carry.
  induction rev_blocks as [|a rev_blocks IH]; intros carry b Hk.
  - simpl.
    destruct (shift_right_limb8_digits_small k carry b) as [hi lo] eqn:Hshift.
    apply (shift_right_limb8_digits_small_low _ _ _ _ _ Hk Hshift).
  - simpl.
    destruct (shift_right_limb8_digits_small k carry a) as [hi lo] eqn:Hshift.
    apply (IH lo).
    exact Hk.
Qed.

Lemma limb8_take_digits_zero_limb8 :
  forall k,
    limb8_take_digits k zero_limb8 = zero_limb8.
Proof.
  intros k.
  destruct k as [|[|[|[|[|[|[|[|k]]]]]]]];
    reflexivity.
Qed.

Lemma shift_right_bigint_digits_small_carry_rev :
  forall k carry b bs,
    (k < 8)%nat ->
    shift_right_bigint_digits_small_carry k carry (rev (b :: bs)) =
      limb8_take_digits k b.
Proof.
  intros k carry b bs Hk.
  change (rev (b :: bs)) with (rev bs ++ [b]).
  apply shift_right_bigint_digits_small_carry_last.
  exact Hk.
Qed.

Lemma shift_right_limb8_digits_small_low_carry_value_scaled :
  forall scale k carry x hi lo,
    (k < 8)%nat ->
    carry = limb8_take_digits k carry ->
    shift_right_limb8_digits_small k carry x = (hi, lo) ->
    scale * limb8_value lo + scale * (digit_base_z ^ Z.of_nat k) * limb8_value hi =
      scale * limb8_value x + scale * digit_base8_z * limb8_value carry.
Proof.
  intros scale k carry x hi lo Hk Hcarry Hshift.
  pose proof
    (shift_right_limb8_digits_small_low_carry_value k carry x hi lo Hk Hcarry Hshift)
    as Hvalue.
  replace
    (scale * limb8_value lo + scale * (digit_base_z ^ Z.of_nat k) * limb8_value hi)
    with (scale * (limb8_value lo + (digit_base_z ^ Z.of_nat k) * limb8_value hi))
    by ring.
  replace
    (scale * limb8_value x + scale * digit_base8_z * limb8_value carry)
    with (scale * (limb8_value x + digit_base8_z * limb8_value carry))
    by ring.
  rewrite Hvalue.
  ring.
Qed.

Lemma shift_right_bigint_digits_small_step_value :
  forall k carry b bs hi lo,
    (k < 8)%nat ->
    carry = limb8_take_digits k carry ->
    shift_right_limb8_digits_small k carry b = (hi, lo) ->
    let A := digit_base8_z ^ Z.of_nat (List.length bs) in
    let B := digit_base_z ^ Z.of_nat k in
    bigint_value (rev (b :: bs)) + A * digit_base8_z * limb8_value carry =
      bigint_value (rev bs) + A * limb8_value lo + A * B * limb8_value hi.
Proof.
  intros k carry b bs hi lo Hk Hcarry Hshift A B.
  change (rev (b :: bs)) with (rev bs ++ [b]).
  rewrite bigint_value_app_blocks.
  rewrite length_rev.
  simpl.
  change (digit_base8_z ^ Z.of_nat (S (List.length bs)))
    with (digit_base8_z ^ Z.of_nat (List.length bs) * digit_base8_z).
  rewrite bigint_value_cons.
  change (bigint_value []) with 0%Z.
  ring_simplify.
  change (digit_base_z ^ Z.of_nat k) with B.
  change (digit_base8_z ^ Z.of_nat (List.length bs)) with A.
  pose proof
    (shift_right_limb8_digits_small_low_carry_value_scaled
      A k carry b hi lo Hk Hcarry Hshift) as Hstep.
  change (digit_base_z ^ Z.of_nat k) with B in Hstep.
  assert (Hstep' :
    bigint_value (rev bs) + (A * limb8_value lo + A * B * limb8_value hi) =
    bigint_value (rev bs) + (A * limb8_value b + A * digit_base8_z * limb8_value carry)).
  {
    rewrite Hstep.
    reflexivity.
  }
  ring_simplify in Hstep'.
  transitivity (bigint_value (rev bs) + A * limb8_value b + A * digit_base8_z * limb8_value carry).
  - ring.
  - symmetry.
    exact Hstep'.
Qed.

Lemma shift_right_bigint_digits_small_aux_value :
  forall k carry rev_blocks,
    (k < 8)%nat ->
    carry = limb8_take_digits k carry ->
    bigint_value (rev rev_blocks) +
      (digit_base8_z ^ Z.of_nat (List.length rev_blocks)) * limb8_value carry =
    limb8_value (shift_right_bigint_digits_small_carry k carry rev_blocks) +
      (digit_base_z ^ Z.of_nat k) *
        bigint_value (shift_right_bigint_digits_small_aux k carry rev_blocks []).
Proof.
  intros k carry rev_blocks Hk Hcarry.
  revert carry Hcarry.
  induction rev_blocks as [|b bs IH]; intros carry Hcarry.
  - simpl.
    change (bigint_value []) with 0%Z.
    rewrite Z.mul_0_r.
    destruct (limb8_value carry); reflexivity.
  - simpl.
    destruct (shift_right_limb8_digits_small k carry b) as [hi lo] eqn:Hshift.
    assert (Hlo : lo = limb8_take_digits k lo).
    {
      rewrite (shift_right_limb8_digits_small_low _ _ _ _ _ Hk Hshift).
      symmetry.
      apply limb8_take_digits_idem.
    }
    pose proof (shift_right_bigint_digits_small_step_value k carry b bs hi lo Hk Hcarry Hshift)
      as Hstep.
    pose proof (IH lo Hlo) as IHlo.
    rewrite (shift_right_bigint_digits_small_aux_app k lo bs [hi]).
    rewrite (bigint_value_app_blocks (shift_right_bigint_digits_small_aux k lo bs []) [hi]).
    replace
      (Z.of_nat (List.length (shift_right_bigint_digits_small_aux k lo bs [])))
      with (Z.of_nat (List.length bs)).
    2:{
      rewrite (shift_right_bigint_digits_small_aux_length k lo bs nil).
      simpl.
      rewrite Nat.add_0_r.
      reflexivity.
    }
    simpl.
    rewrite bigint_value_cons.
    change (bigint_value []) with 0%Z.
    ring_simplify.
    set (A := digit_base8_z ^ Z.of_nat (List.length bs)).
    set (B := digit_base_z ^ Z.of_nat k).
    change (digit_base8_z ^ Z.of_nat (List.length bs)) with A in Hstep, IHlo |- *.
    change (digit_base_z ^ Z.of_nat k) with B in Hstep, IHlo |- *.
    change (bigint_value (rev (b :: bs))) with (bigint_value (rev bs ++ [b])) in Hstep.
    change (digit_base8_z ^ Z.of_nat (S (List.length bs))) with (A * digit_base8_z) in Hstep.
    assert (HpowA :
      Z.pow_pos digit_base8_z (Pos.of_succ_nat (List.length bs)) = A * digit_base8_z).
    {
      subst A.
      change (digit_base8_z ^ Z.of_nat (S (List.length bs)) =
        digit_base8_z ^ Z.of_nat (List.length bs) * digit_base8_z).
      rewrite Nat2Z.inj_succ.
      replace (Z.succ (Z.of_nat (List.length bs))) with
        (Z.of_nat (List.length bs) + 1) by lia.
      rewrite Z.pow_add_r by lia.
      rewrite Z.pow_1_r.
      ring.
    }
    assert (Hsnoc :
      bigint_value (rev bs ++ [b]) = bigint_value (rev bs) + A * limb8_value b).
    {
      subst A.
      rewrite bigint_value_app_blocks.
      rewrite length_rev.
      simpl.
      rewrite bigint_value_cons.
      change (bigint_value []) with 0%Z.
      ring.
    }
    transitivity (bigint_value (rev bs ++ [b]) + A * digit_base8_z * limb8_value carry).
    + change (bigint_value (rev (b :: bs))) with (bigint_value (rev bs ++ [b])).
      rewrite HpowA.
      ring.
    + transitivity (bigint_value (rev bs) + A * limb8_value lo + A * B * limb8_value hi).
      * exact Hstep.
      * rewrite IHlo.
        replace (B * A * limb8_value hi) with (A * B * limb8_value hi) by ring.
        ring_simplify.
        reflexivity.
Qed.

Lemma shift_right_bigint_digits_small_value :
  forall k b bs,
    (0 < k < 8)%nat ->
    bigint_value (b :: bs) =
      limb8_value (limb8_take_digits k b) +
      (digit_base_z ^ Z.of_nat k) *
        bigint_value (shift_right_bigint_digits_small k (b :: bs)).
Proof.
  intros k b bs [Hk0 Hk].
  unfold shift_right_bigint_digits_small.
  rewrite trim_bigint_value.
  pose proof
    (shift_right_bigint_digits_small_aux_value k zero_limb8 (rev (b :: bs)) Hk
      (eq_sym (limb8_take_digits_zero_limb8 k))) as Hvalue.
  rewrite shift_right_bigint_digits_small_carry_rev in Hvalue by exact Hk.
  rewrite rev_involutive in Hvalue.
  rewrite rev_length in Hvalue.
  rewrite limb8_value_zero_limb8 in Hvalue.
  rewrite Z.mul_0_r in Hvalue.
  rewrite Z.add_0_r in Hvalue.
  exact Hvalue.
Qed.

Lemma bigint_split_whole_digits_unaligned_value :
  forall whole_blocks rem_digits x,
    (0 < rem_digits < 8)%nat ->
    (whole_blocks < List.length x)%nat ->
    let '(high, low) := bigint_split_whole_digits (8 * whole_blocks + rem_digits) x in
    bigint_value x =
      bigint_value low +
      (digit_base_z ^ Z.of_nat (8 * whole_blocks + rem_digits)) * bigint_value high.
Proof.
  intros whole_blocks rem_digits x Hrem Hlt.
  destruct Hrem as [Hrem_pos Hrem_lt].
  destruct rem_digits as [|rem_digits].
  { lia. }
  unfold bigint_split_whole_digits.
  replace (((8 * whole_blocks + S rem_digits) / 8)%nat) with whole_blocks.
  2:{
    replace (8 * whole_blocks + S rem_digits)%nat with
      (whole_blocks * 8 + S rem_digits)%nat by lia.
    rewrite Nat.div_add_l; try lia.
    rewrite Nat.div_small; lia.
  }
  replace (((8 * whole_blocks + S rem_digits) mod 8)%nat) with (S rem_digits).
  2:{
    replace (8 * whole_blocks + S rem_digits)%nat with
      (whole_blocks * 8 + S rem_digits)%nat by lia.
    rewrite Nat.add_mod by lia.
    rewrite Nat.mod_mul by lia.
    rewrite Nat.add_0_l.
    rewrite Nat.mod_small.
    2:{ apply Nat.mod_upper_bound. lia. }
    rewrite Nat.mod_small by exact Hrem_lt.
    reflexivity.
  }
  set (low_blocks := firstn whole_blocks x).
  set (high_blocks := skipn whole_blocks x).
  assert (Hlen_low : List.length low_blocks = whole_blocks).
  {
    subst low_blocks.
    rewrite firstn_length.
    lia.
  }
  assert (Hhigh_nonempty : high_blocks <> []).
  {
    subst high_blocks.
    intro Hnil.
    apply (f_equal (@List.length _)) in Hnil.
    rewrite length_skipn in Hnil.
    simpl in Hnil.
    lia.
  }
  subst high_blocks.
  destruct (skipn whole_blocks x) as [|b bs] eqn:Hhigh_blocks.
  { exfalso. apply Hhigh_nonempty. reflexivity. }
  cbn.
  rewrite !trim_bigint_value.
  rewrite snoc_nonzero_block_value.
  rewrite bigint_value_app_blocks.
  rewrite Hlen_low.
  rewrite (bigint_value_firstn_skipn whole_blocks x).
  subst low_blocks.
  rewrite Hhigh_blocks.
  rewrite (shift_right_bigint_digits_small_value (S rem_digits) b bs
    (conj (Nat.lt_0_succ rem_digits) Hrem_lt)).
  repeat rewrite Hlen_low.
  rewrite bigint_value_cons.
  change (bigint_value []) with 0%Z.
  ring_simplify.
  change
    (digits_value
       (bigint_digits_z
          (rev
             (drop_zero_prefix
                (rev
                   (shift_right_bigint_digits_small_aux
                      (S rem_digits) zero_limb8 (rev bs ++ [b]) []))))))
    with (bigint_value (shift_right_bigint_digits_small (S rem_digits) (b :: bs))).
  assert (Hpow :
    digit_base8_z ^ Z.of_nat whole_blocks *
      (digit_base_z ^ Z.of_nat (S rem_digits)) =
    digit_base_z ^ Z.of_nat (8 * whole_blocks + S rem_digits)).
  {
    unfold digit_base8_z.
    rewrite <- Z.pow_mul_r by lia.
    rewrite <- Z.pow_add_r by lia.
    f_equal.
    rewrite Nat2Z.inj_add.
    rewrite Nat2Z.inj_mul.
    change (Z.of_nat 8) with 8%Z.
    lia.
  }
  replace
    (Z.of_nat
       ((whole_blocks +
         (whole_blocks +
          (whole_blocks +
           (whole_blocks +
            (whole_blocks +
             (whole_blocks + (whole_blocks + (whole_blocks + 0))))))) +
         (S rem_digits))%nat))
    with (Z.of_nat (8 * whole_blocks + S rem_digits))
    by (f_equal; lia).
  set (V := bigint_value
    (shift_right_bigint_digits_small (S rem_digits) (b :: bs))).
  ring_simplify.
  replace
    (digit_base8_z ^ Z.of_nat whole_blocks *
       digit_base_z ^ Z.of_nat (S rem_digits) * V)
    with
    (digit_base_z ^ Z.of_nat (8 * whole_blocks + S rem_digits) * V).
  2:{
    rewrite Hpow.
    ring.
  }
  rewrite (Z.mul_comm V (digit_base_z ^ Z.of_nat (8 * whole_blocks + S rem_digits))).
  reflexivity.
Qed.

Lemma digit_base_pow_block_split :
  forall blocks slot,
    digit_base_z ^ Z.of_nat (8 * blocks + slot) =
      digit_base8_z ^ Z.of_nat blocks * digit_base_z ^ Z.of_nat slot.
Proof.
  intros blocks slot.
  replace (Z.of_nat (8 * blocks + slot))
    with (Z.of_nat (8 * blocks) + Z.of_nat slot) by lia.
  rewrite Nat2Z.inj_mul.
  rewrite Z.pow_add_r by (cbv [digit_base_z]; lia).
  unfold digit_base8_z.
  rewrite Z.pow_mul_r by (cbv [digit_base_z]; lia).
  reflexivity.
Qed.

Lemma digit_base_pow_block_succ :
  forall blocks slot,
    digit_base8_z * digit_base_z ^ Z.of_nat (8 * blocks + slot) =
      digit_base_z ^ Z.of_nat (8 * S blocks + slot).
Proof.
  intros blocks slot.
  rewrite digit_base_pow_block_split.
  rewrite digit_base_pow_block_split with (blocks := S blocks) (slot := slot).
  replace (Z.of_nat (S blocks)) with (Z.of_nat blocks + 1) by lia.
  rewrite Z.pow_add_r by (unfold digit_base8_z; cbv [digit_base_z]; lia).
  rewrite Z.pow_1_r.
  ring.
Qed.

Lemma bigint_value_range :
  forall x,
    canonical_bigint x ->
    (0 <= bigint_value x < digit_base8_z ^ Z.of_nat (List.length x))%Z.
Proof.
  intros x Hx.
  induction Hx as [|b bs Hb Hbs IH].
  - simpl.
    unfold bigint_value.
    simpl.
    change (digit_base8_z ^ 0) with 1%Z.
    split; lia.
  - rewrite bigint_value_cons.
    destruct (limb8_value_range _ Hb) as [Hb0 Hb1].
    destruct IH as [IH0 IH1].
    split.
    + nia.
    + replace (digit_base8_z ^ Z.of_nat (S (List.length bs)))
        with (digit_base8_z * digit_base8_z ^ Z.of_nat (List.length bs)).
      2:{
        replace (Z.of_nat (S (List.length bs)))
          with (Z.of_nat (List.length bs) + 1) by lia.
        rewrite Z.pow_add_r by (unfold digit_base8_z; cbv [digit_base_z]; lia).
        rewrite Z.pow_1_r.
        ring.
      }
      assert (1 < digit_base8_z)%Z.
      {
        unfold digit_base8_z.
        change (8%Z) with (7 + 1)%Z.
        rewrite Z.pow_add_r by (cbv [digit_base_z]; lia).
        rewrite Z.pow_1_r.
        cbv [digit_base_z].
        lia.
      }
      assert (Htail_le :
        (bigint_value bs <= digit_base8_z ^ Z.of_nat (List.length bs) - 1)%Z).
      { lia. }
      assert (Hmul_le :
        (digit_base8_z * bigint_value bs <=
         digit_base8_z * (digit_base8_z ^ Z.of_nat (List.length bs) - 1))%Z).
      {
        apply Z.mul_le_mono_nonneg_l; lia.
      }
      assert (Hlt' :
        (limb8_value b + digit_base8_z * bigint_value bs <
         digit_base8_z + digit_base8_z * (digit_base8_z ^ Z.of_nat (List.length bs) - 1))%Z).
      { nia. }
      eapply Z.lt_le_trans.
      * exact Hlt'.
      * replace (digit_base8_z ^ Z.of_nat (List.length (b :: bs)))
          with (digit_base8_z * digit_base8_z ^ Z.of_nat (List.length bs)).
        2:{
          replace (List.length (b :: bs)) with (S (List.length bs)) by reflexivity.
          replace (Z.of_nat (S (List.length bs)))
            with (1 + Z.of_nat (List.length bs))%Z by lia.
          rewrite Z.pow_add_r by (unfold digit_base8_z; cbv [digit_base_z]; lia).
          rewrite Z.pow_1_r.
          ring.
        }
        replace
          (digit_base8_z + digit_base8_z * (digit_base8_z ^ Z.of_nat (List.length bs) - 1))
          with
          (digit_base8_z * digit_base8_z ^ Z.of_nat (List.length bs)) by ring.
        apply Z.le_refl.
Qed.

Lemma limb8_set_digit_canonical :
  forall slot d x,
    (slot < 8)%nat ->
    canonical_digit d ->
    canonical_limb8 x ->
    canonical_limb8 (limb8_set_digit slot d x).
Proof.
  intros slot d [x0 x1 x2 x3 x4 x5 x6 x7] Hslot Hd Hx.
  destruct Hd as [Hd0 Hd1].
  destruct Hx as [Hx0 [Hx1 [Hx2 [Hx3 [Hx4 [Hx5 [Hx6 Hx7]]]]]]].
  destruct Hx0 as [Hx0lo Hx0hi].
  destruct Hx1 as [Hx1lo Hx1hi].
  destruct Hx2 as [Hx2lo Hx2hi].
  destruct Hx3 as [Hx3lo Hx3hi].
  destruct Hx4 as [Hx4lo Hx4hi].
  destruct Hx5 as [Hx5lo Hx5hi].
  destruct Hx6 as [Hx6lo Hx6hi].
  destruct Hx7 as [Hx7lo Hx7hi].
  destruct slot as [|[|[|[|[|[|[|[|slot]]]]]]]]; try lia;
    unfold limb8_set_digit, canonical_limb8;
    cbn [d0 d1 d2 d3 d4 d5 d6 d7];
    repeat split; assumption.
Qed.

Lemma Forall_firstn {A : Type} (P : A -> Prop) :
  forall n xs,
    Forall P xs ->
    Forall P (firstn n xs).
Proof.
  intros n xs Hxs.
  revert xs Hxs.
  induction n as [|n IH]; intros xs Hxs.
  - destruct xs; constructor.
  - destruct xs as [|x xs].
    + constructor.
    + inversion Hxs as [|x' xs' Hx Hrest]; subst.
      simpl.
      constructor.
      * exact Hx.
      * apply IH.
        exact Hrest.
Qed.

Lemma Forall_skipn {A : Type} (P : A -> Prop) :
  forall n xs,
    Forall P xs ->
    Forall P (skipn n xs).
Proof.
  intros n xs Hxs.
  revert xs Hxs.
  induction n as [|n IH]; intros xs Hxs.
  - exact Hxs.
  - destruct xs as [|x xs].
    + constructor.
    + inversion Hxs as [|x' xs' Hx Hrest]; subst.
      simpl.
      apply IH.
      exact Hrest.
Qed.

Lemma digits_value_nonneg :
  forall xs,
    Forall (fun z => (0 <= z < digit_base_z)%Z) xs ->
    (0 <= digits_value xs)%Z.
Proof.
  intros xs Hxs.
  induction Hxs as [|x xs Hx Hxs IH].
  - reflexivity.
  - simpl.
    destruct Hx as [Hx0 Hx1].
    apply Z.add_nonneg_nonneg.
    + exact Hx0.
    + destruct (digits_value xs) eqn:Hval; simpl; lia.
Qed.

Lemma digits_value_all_zero_zero :
  forall xs,
    Forall (fun z => z = 0)%Z xs ->
    digits_value xs = 0.
Proof.
  intros xs Hxs.
  induction Hxs as [|x xs Hx Hxs IH].
  - reflexivity.
  - simpl.
    subst x.
    rewrite IH.
    ring.
Qed.

Lemma digits_value_zero_all_zero :
  forall xs,
    Forall (fun z => (0 <= z < digit_base_z)%Z) xs ->
    digits_value xs = 0 ->
    Forall (fun z => z = 0)%Z xs.
Proof.
  intros xs Hxs.
  induction Hxs as [|x xs Hx Hxs IH]; intro Hvalue.
  - constructor.
  - simpl in Hvalue.
    destruct Hx as [Hx0 Hx1].
    destruct (digits_value xs) eqn:Hxs_value.
    + simpl in Hvalue.
      assert (Hx_zero : x = 0%Z) by lia.
      constructor.
      * exact Hx_zero.
      * apply IH.
        exact eq_refl.
    + simpl in Hvalue.
      exfalso.
      nia.
    + exfalso.
      pose proof (digits_value_nonneg _ Hxs) as Hxs_nonneg.
      lia.
Qed.

Lemma limb8_digits_z_canonical :
  forall x,
    canonical_limb8 x ->
    Forall (fun z => (0 <= z < digit_base_z)%Z) (limb8_digits_z x).
Proof.
  intros [x0 x1 x2 x3 x4 x5 x6 x7] Hx.
  destruct Hx as [Hx0 [Hx1 [Hx2 [Hx3 [Hx4 [Hx5 [Hx6 Hx7]]]]]]].
  destruct Hx0 as [Hx0lo Hx0hi].
  destruct Hx1 as [Hx1lo Hx1hi].
  destruct Hx2 as [Hx2lo Hx2hi].
  destruct Hx3 as [Hx3lo Hx3hi].
  destruct Hx4 as [Hx4lo Hx4hi].
  destruct Hx5 as [Hx5lo Hx5hi].
  destruct Hx6 as [Hx6lo Hx6hi].
  destruct Hx7 as [Hx7lo Hx7hi].
  change (Forall (fun z : Z => (0 <= z < digit_base_z)%Z)
            [Uint63.to_Z x0; Uint63.to_Z x1; Uint63.to_Z x2; Uint63.to_Z x3;
             Uint63.to_Z x4; Uint63.to_Z x5; Uint63.to_Z x6; Uint63.to_Z x7]).
  repeat constructor; assumption.
Qed.

Lemma limb8_set_digit_digits_z :
  forall slot d x,
    (slot < 8)%nat ->
    limb8_digits_z (limb8_set_digit slot d x) =
      firstn slot (limb8_digits_z x) ++ Uint63.to_Z d :: skipn (S slot) (limb8_digits_z x).
Proof.
  intros slot d [x0 x1 x2 x3 x4 x5 x6 x7] Hslot.
  destruct slot as [|[|[|[|[|[|[|[|slot]]]]]]]]; try lia;
    reflexivity.
Qed.

Lemma limb8_set_digit_append_value :
  forall slot x d,
    (slot < 8)%nat ->
    canonical_limb8 x ->
    canonical_digit d ->
    (limb8_value x < digit_base_z ^ Z.of_nat slot)%Z ->
    limb8_value (limb8_set_digit slot d x) =
      limb8_value x + digit_base_z ^ Z.of_nat slot * Uint63.to_Z d.
Proof.
  intros slot [x0 x1 x2 x3 x4 x5 x6 x7] d Hslot Hx Hd Hlt.
  unfold canonical_limb8 in Hx.
  cbn [d0 d1 d2 d3 d4 d5 d6 d7] in Hx.
  unfold canonical_digit in Hx, Hd.
  destruct Hx as [Hx0 [Hx1 [Hx2 [Hx3 [Hx4 [Hx5 [Hx6 Hx7]]]]]]].
  destruct Hd as [Hd0 Hd1].
  destruct slot as [|[|[|[|[|[|[|[|slot]]]]]]]]; try lia.
  - cbv [limb8_value limb8_digits_z limb8_digits_u63 digits_value limb8_set_digit List.map] in Hlt |- *.
    unfold digit_base_z in *.
    cbn [Z.of_nat Z.pow] in Hlt |- *.
    nia.
  - cbv [limb8_value limb8_digits_z limb8_digits_u63 digits_value limb8_set_digit List.map] in Hlt |- *.
    unfold digit_base_z in *.
    cbn [Z.of_nat Z.pow] in Hlt |- *.
    nia.
  - cbv [limb8_value limb8_digits_z limb8_digits_u63 digits_value limb8_set_digit List.map] in Hlt |- *.
    unfold digit_base_z in *.
    cbn [Z.of_nat Z.pow] in Hlt |- *.
    nia.
  - cbv [limb8_value limb8_digits_z limb8_digits_u63 digits_value limb8_set_digit List.map] in Hlt |- *.
    unfold digit_base_z in *.
    cbn [Z.of_nat Z.pow] in Hlt |- *.
    nia.
  - cbv [limb8_value limb8_digits_z limb8_digits_u63 digits_value limb8_set_digit List.map] in Hlt |- *.
    unfold digit_base_z in *.
    cbn [Z.of_nat Z.pow] in Hlt |- *.
    nia.
  - cbv [limb8_value limb8_digits_z limb8_digits_u63 digits_value limb8_set_digit List.map] in Hlt |- *.
    unfold digit_base_z in *.
    cbn [Z.of_nat Z.pow] in Hlt |- *.
    nia.
  - cbv [limb8_value limb8_digits_z limb8_digits_u63 digits_value limb8_set_digit List.map] in Hlt |- *.
    unfold digit_base_z in *.
    cbn [Z.of_nat Z.pow] in Hlt |- *.
    nia.
  - cbv [limb8_value limb8_digits_z limb8_digits_u63 digits_value limb8_set_digit List.map] in Hlt |- *.
    unfold digit_base_z in *.
    cbn [Z.of_nat Z.pow] in Hlt |- *.
    nia.
Qed.

Lemma bigint_set_digit_at_canonical :
  forall block_index slot xs d,
    (slot < 8)%nat ->
    canonical_bigint xs ->
    canonical_digit d ->
    canonical_bigint (bigint_set_digit_at block_index slot xs d).
Proof.
  intros block_index.
  induction block_index as [|block_index IH]; intros slot xs d Hslot Hxs Hd.
  - destruct xs as [|x xs].
    + cbn [bigint_set_digit_at].
      constructor.
      * change (canonical_limb8 (limb8_set_digit slot d zero_limb8)).
        apply limb8_set_digit_canonical; try assumption.
        apply canonical_zero_limb8.
      * constructor.
    + cbn [bigint_set_digit_at].
      inversion Hxs as [|x0 xs0 Hx0 Hxs0]; subst.
      constructor.
      * change (canonical_limb8 (limb8_set_digit slot d x)).
        apply limb8_set_digit_canonical; assumption.
      * exact Hxs0.
  - destruct xs as [|x xs].
    + simpl.
      constructor.
      * exact canonical_zero_limb8.
      * apply IH; assumption || constructor.
    + simpl.
      inversion Hxs as [|x0 xs0 Hx0 Hxs0]; subst.
      constructor.
      * exact Hx0.
      * apply IH; assumption.
Qed.

Lemma bigint_set_digit_at_append_value :
  forall block_index slot xs d,
    (slot < 8)%nat ->
    canonical_bigint xs ->
    canonical_digit d ->
    (bigint_value xs < digit_base_z ^ Z.of_nat (8 * block_index + slot))%Z ->
    bigint_value (bigint_set_digit_at block_index slot xs d) =
      bigint_value xs + digit_base_z ^ Z.of_nat (8 * block_index + slot) * Uint63.to_Z d.
Proof.
  intros block_index.
  induction block_index as [|block_index IH]; intros slot xs d Hslot Hxs Hd Hbound.
  - destruct xs as [|x xs].
    + cbn [bigint_set_digit_at].
      rewrite bigint_value_cons.
      simpl.
      pose proof
        (limb8_set_digit_append_value slot zero_limb8 d Hslot canonical_zero_limb8 Hd) as Hset.
      assert (Hzero_bound : (limb8_value zero_limb8 < digit_base_z ^ Z.of_nat slot)%Z).
      {
        rewrite limb8_value_zero_limb8.
        assert (Hpow_pos : (0 < digit_base_z ^ Z.of_nat slot)%Z).
        {
          apply Z.pow_pos_nonneg; cbv [digit_base_z]; lia.
        }
        lia.
      }
      specialize (Hset Hzero_bound).
      rewrite limb8_value_zero_limb8 in Hset.
      replace (0 + digit_base_z ^ Z.of_nat slot * Uint63.to_Z d)%Z
        with (digit_base_z ^ Z.of_nat slot * Uint63.to_Z d)%Z in Hset by lia.
      change
        ((limb8_value (limb8_set_digit slot d zero_limb8) + 0)%Z =
           digit_base_z ^ Z.of_nat slot * Uint63.to_Z d)%Z.
      rewrite Hset.
      lia.
    + inversion Hxs as [|x0 xs0 Hx0 Hxs0]; subst.
      rewrite bigint_value_cons in Hbound.
      destruct (limb8_value_range _ Hx0) as [Hxv0 Hxv1].
      destruct (bigint_value_range _ Hxs0) as [Htail0 Htail1].
      assert (Hslot_lt_block : (digit_base_z ^ Z.of_nat slot < digit_base8_z)%Z).
      {
        destruct slot as [|[|[|[|[|[|[|[|slot]]]]]]]]; try lia;
          unfold digit_base8_z, digit_base_z;
          cbn [Z.of_nat Z.pow];
          lia.
      }
      assert (Htail_zero : (bigint_value xs = 0)%Z).
      {
        destruct (bigint_value xs) eqn:Htailv.
        - reflexivity.
        - exfalso.
          assert (Htail_ge : (digit_base8_z <= digit_base8_z * Z.pos p)%Z).
          {
            replace digit_base8_z with (digit_base8_z * 1)%Z by ring.
            apply Z.mul_le_mono_nonneg_l; lia.
          }
          assert (Hlhs_ge :
            (digit_base8_z <= limb8_value x + digit_base8_z * Z.pos p)%Z).
          { nia. }
          apply (Z.lt_irrefl digit_base8_z).
          eapply Z.le_lt_trans; [exact Hlhs_ge|].
          eapply Z.lt_trans; [exact Hbound| exact Hslot_lt_block].
        - lia.
      }
      assert (Hblock_bound : (limb8_value x < digit_base_z ^ Z.of_nat slot)%Z).
      {
        rewrite Htail_zero in Hbound.
        rewrite Z.mul_0_r in Hbound.
        replace (8 * 0 + slot)%nat with slot in Hbound by lia.
        lia.
      }
      simpl.
      rewrite bigint_value_cons.
      rewrite Htail_zero.
      rewrite Z.mul_0_r.
      rewrite limb8_set_digit_append_value.
      * rewrite bigint_value_cons.
        rewrite Htail_zero.
        rewrite Z.mul_0_r.
        ring.
      * exact Hslot.
      * exact Hx0.
      * exact Hd.
      * exact Hblock_bound.
  - destruct xs as [|x xs].
	    + simpl.
	      rewrite bigint_value_cons.
	      rewrite limb8_value_zero_limb8.
	      rewrite Z.add_0_l.
	      rewrite IH.
	      * simpl.
	        change
	          (digit_base8_z *
	             (digit_base_z ^ Z.of_nat (8 * block_index + slot) * Uint63.to_Z d) =
	           digit_base_z ^ Z.of_nat (8 * S block_index + slot) * Uint63.to_Z d)%Z.
	        replace
	          (digit_base8_z *
	             (digit_base_z ^ Z.of_nat (8 * block_index + slot) * Uint63.to_Z d))%Z
	          with
	          ((digit_base8_z * digit_base_z ^ Z.of_nat (8 * block_index + slot)) *
	             Uint63.to_Z d)%Z by ring.
	        replace
	          ((digit_base8_z * digit_base_z ^ Z.of_nat (8 * block_index + slot)) *
	             Uint63.to_Z d)%Z
	          with
	          (digit_base_z ^ Z.of_nat (8 * S block_index + slot) * Uint63.to_Z d)%Z
	          by (rewrite digit_base_pow_block_succ; reflexivity).
	        ring.
	      * exact Hslot.
	      * constructor.
	      * exact Hd.
	      * change (0 < digit_base_z ^ Z.of_nat (8 * block_index + slot))%Z.
	        apply Z.pow_pos_nonneg; cbv [digit_base_z]; lia.
    + inversion Hxs as [|x0 xs0 Hx0 Hxs0]; subst.
      rewrite bigint_value_cons in Hbound.
      destruct (limb8_value_range _ Hx0) as [Hxv0 Hxv1].
      destruct (bigint_value_range _ Hxs0) as [Htail0 Htail1].
	      assert (Htail_bound :
	        (bigint_value xs < digit_base_z ^ Z.of_nat (8 * block_index + slot))%Z).
      {
        rewrite <- digit_base_pow_block_succ in Hbound.
        nia.
      }
	      simpl.
	      rewrite bigint_value_cons.
	      rewrite IH.
	      * rewrite bigint_value_cons.
	        change
	          (limb8_value x + digit_base8_z * (bigint_value xs +
	             digit_base_z ^ Z.of_nat (8 * block_index + slot) * Uint63.to_Z d) =
	           limb8_value x + digit_base8_z * bigint_value xs +
	             digit_base_z ^ Z.of_nat (8 * S block_index + slot) * Uint63.to_Z d)%Z.
	        rewrite Z.mul_add_distr_l.
	        repeat rewrite Z.add_assoc.
	        replace
	          (digit_base8_z *
	             (digit_base_z ^ Z.of_nat (8 * block_index + slot) * Uint63.to_Z d))%Z
	          with
	          ((digit_base8_z * digit_base_z ^ Z.of_nat (8 * block_index + slot)) *
	             Uint63.to_Z d)%Z by ring.
	        replace
	          ((digit_base8_z * digit_base_z ^ Z.of_nat (8 * block_index + slot)) *
	             Uint63.to_Z d)%Z
	          with
	          (digit_base_z ^ Z.of_nat (8 * S block_index + slot) * Uint63.to_Z d)%Z
	          by (rewrite digit_base_pow_block_succ; reflexivity).
	        reflexivity.
      * exact Hslot.
      * exact Hxs0.
      * exact Hd.
      * exact Htail_bound.
Qed.

Lemma bigint_append_digit_canonical :
  forall digit_count xs d,
    canonical_bigint xs ->
    canonical_digit d ->
    canonical_bigint (bigint_append_digit digit_count xs d).
Proof.
  intros digit_count xs d Hxs Hd.
  unfold bigint_append_digit.
  destruct (Uint63.eqb d zero_digit) eqn:Hd0.
  - exact Hxs.
  - apply bigint_set_digit_at_canonical.
    + apply Nat.mod_upper_bound. lia.
    + exact Hxs.
    + exact Hd.
Qed.

Lemma bigint_append_digit_value :
  forall digit_count xs d,
    canonical_bigint xs ->
    canonical_digit d ->
    (bigint_value xs < digit_base_z ^ Z.of_nat digit_count)%Z ->
    bigint_value (trim_bigint (bigint_append_digit digit_count xs d)) =
      bigint_value xs + digit_base_z ^ Z.of_nat digit_count * Uint63.to_Z d.
Proof.
  intros digit_count xs d Hxs Hd Hbound.
  rewrite trim_bigint_value.
  unfold bigint_append_digit.
  destruct (Uint63.eqb d zero_digit) eqn:Hd0.
  - apply Uint63.eqb_spec in Hd0.
    subst d.
    rewrite zero_digit_to_Z.
    ring.
  - set (q := Nat.div digit_count 8).
    set (r := Nat.modulo digit_count 8).
    change
      (bigint_value
         (bigint_set_digit_at q r xs d) =
       bigint_value xs + digit_base_z ^ Z.of_nat digit_count * Uint63.to_Z d)%Z.
    replace digit_count with (8 * q + r)%nat in Hbound |- *.
    2:{
      subst q r.
      symmetry.
      apply Nat.div_mod.
      lia.
    }
    apply bigint_set_digit_at_append_value.
    + subst r.
      apply Nat.mod_upper_bound.
      lia.
    + exact Hxs.
    + exact Hd.
    + exact Hbound.
Qed.

Lemma shift_right_digit_small_correct :
  forall bits carry d digit carry',
    (0 < bits < digit_shift_nat)%nat ->
    canonical_digit d ->
    (0 <= Uint63.to_Z carry < 2 ^ Z.of_nat bits)%Z ->
    shift_right_digit_small
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      carry d = (digit, carry') ->
    canonical_digit digit /\
    canonical_digit carry' /\
    (Uint63.to_Z carry' < 2 ^ Z.of_nat bits)%Z /\
    Uint63.to_Z carry' + 2 ^ Z.of_nat bits * Uint63.to_Z digit =
      Uint63.to_Z d + digit_base_z * Uint63.to_Z carry.
Proof.
  intros bits carry d digit carry' Hbits Hd Hcarry Hshift.
  destruct Hbits as [Hbits0 Hbits].
  destruct Hd as [Hd0 Hd1].
  unfold shift_right_digit_small in Hshift.
  inversion Hshift; subst; clear Hshift.
  assert (Hcarry' :
    Uint63.to_Z (Uint63.land d
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)) =
      Uint63.to_Z d mod 2 ^ Z.of_nat bits).
  {
    rewrite Uint63.land_spec'.
    assert (Hmask :
      Uint63.to_Z
        (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one) =
      Z.ones (Z.of_nat bits)).
    {
      rewrite shift_low_mask_value by exact (conj Hbits0 Hbits).
      rewrite Z.ones_equiv.
      lia.
    }
    rewrite Hmask.
    rewrite Z.land_ones by lia.
    reflexivity.
  }
  assert (Hlsl :
    Uint63.to_Z
      (Uint63.lsl carry (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))) =
    Uint63.to_Z carry * 2 ^ Z.of_nat (digit_shift_nat - bits)).
  {
    rewrite Uint63.lsl_spec.
    rewrite shift_left_u63_value by exact Hbits.
    replace
      ((Uint63.to_Z carry * 2 ^ Z.of_nat (digit_shift_nat - bits)) mod wB)%Z
      with (Uint63.to_Z carry * 2 ^ Z.of_nat (digit_shift_nat - bits))%Z.
    2:{
      symmetry.
      apply Z.mod_small.
      split.
      - apply Z.mul_nonneg_nonneg; [lia|apply Z.pow_nonneg; lia].
      - eapply Z.lt_trans.
        + apply (Z.mul_lt_mono_pos_r
                   (2 ^ Z.of_nat (digit_shift_nat - bits))
                   (Uint63.to_Z carry)
                   (2 ^ Z.of_nat bits)).
          * apply Z.pow_pos_nonneg; lia.
          * lia.
        + rewrite digit_base_z_split_pow by lia.
          apply digit_base_lt_wB.
    }
    reflexivity.
  }
  assert (Hlsr_range :
    (0 <= Uint63.to_Z (Uint63.lsr d (Uint63.of_Z (Z.of_nat bits))) <
     2 ^ Z.of_nat (digit_shift_nat - bits))%Z).
  {
    rewrite Uint63.lsr_spec.
    rewrite shift_u63_value by exact Hbits.
    split.
    - apply Z.div_pos; [lia|apply Z.pow_pos_nonneg; lia].
    - apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
      rewrite digit_base_z_split_pow by lia.
      exact Hd1.
  }
  assert (Hland0 :
    Z.land (Uint63.to_Z (Uint63.lsr d (Uint63.of_Z (Z.of_nat bits))))
      (Uint63.to_Z
         (Uint63.lsl carry (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits))))) =
    0%Z).
  {
    rewrite Hlsl.
    rewrite <- Z.shiftl_mul_pow2 by lia.
    apply land_small_shiftl_zero.
    - exact Hlsr_range.
    - lia.
  }
  assert (Hdigit :
    Uint63.to_Z
      (Uint63.lor (Uint63.lsr d (Uint63.of_Z (Z.of_nat bits)))
         (Uint63.lsl carry (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits))))) =
    (Uint63.to_Z d / 2 ^ Z.of_nat bits +
      Uint63.to_Z carry * 2 ^ Z.of_nat (digit_shift_nat - bits))%Z).
  {
    rewrite Uint63.lor_spec'.
    pose proof
      (Z.add_lor_land
         (Uint63.to_Z (Uint63.lsr d (Uint63.of_Z (Z.of_nat bits))))
         (Uint63.to_Z
            (Uint63.lsl carry (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits))))))
      as Hlor.
    rewrite Hland0 in Hlor.
    rewrite Uint63.lsr_spec in Hlor.
    rewrite shift_u63_value in Hlor by exact Hbits.
    rewrite Hlsl in Hlor.
    rewrite Uint63.lsr_spec.
    rewrite shift_u63_value by exact Hbits.
    rewrite Hlsl.
    rewrite Z.add_0_r in Hlor.
    exact Hlor.
  }
  assert (Hcarry'_range :
    (0 <=
       Uint63.to_Z
         (Uint63.land d
            (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)) <
     2 ^ Z.of_nat bits)%Z).
  {
    rewrite Hcarry'.
    assert (Hpow_pos : (0 < 2 ^ Z.of_nat bits)%Z).
    {
      apply Z.pow_pos_nonneg; lia.
    }
    exact (Z.mod_pos_bound (Uint63.to_Z d) (2 ^ Z.of_nat bits) Hpow_pos).
  }
  assert (Hdigit_range :
    (0 <=
       Uint63.to_Z
         (Uint63.lor (Uint63.lsr d (Uint63.of_Z (Z.of_nat bits)))
            (Uint63.lsl carry (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits))))) <
     digit_base_z)%Z).
  {
    rewrite Hdigit.
    split.
    - apply Z.add_nonneg_nonneg.
      + apply Z.div_pos; [lia|apply Z.pow_pos_nonneg; lia].
      + apply Z.mul_nonneg_nonneg; [lia|apply Z.pow_nonneg; lia].
    - assert (Hcarry_le : (Uint63.to_Z carry <= 2 ^ Z.of_nat bits - 1)%Z) by lia.
      assert (Hcarry_scaled_le :
        (Uint63.to_Z carry * 2 ^ Z.of_nat (digit_shift_nat - bits) <=
         (2 ^ Z.of_nat bits - 1) * 2 ^ Z.of_nat (digit_shift_nat - bits))%Z).
      {
        apply Z.mul_le_mono_nonneg_r.
        - apply Z.pow_nonneg; lia.
        - exact Hcarry_le.
      }
      destruct Hlsr_range as [_ Hlsr_lt].
      rewrite Uint63.lsr_spec in Hlsr_lt.
      rewrite shift_u63_value in Hlsr_lt by exact Hbits.
      eapply Z.lt_le_trans.
      * apply Z.add_lt_le_mono.
        -- exact Hlsr_lt.
        -- exact Hcarry_scaled_le.
      * rewrite <- (digit_base_z_split_pow bits) by lia.
        ring_simplify.
        lia.
  }
  split.
  - exact Hdigit_range.
  - split.
    + destruct Hcarry'_range as [Hc0 Hc1].
      split.
      * exact Hc0.
      * eapply Z.lt_trans; [exact Hc1|].
        rewrite digit_base_z_pow2.
        apply Z.pow_lt_mono_r; lia.
    + split.
      * exact (proj2 Hcarry'_range).
      * rewrite Hcarry'.
        rewrite Hdigit.
        rewrite <- (digit_base_z_split_pow bits) by lia.
        rewrite Z.mul_add_distr_l.
        rewrite Z.mul_assoc.
        replace
          (2 ^ Z.of_nat bits * Uint63.to_Z carry)%Z
          with (Uint63.to_Z carry * 2 ^ Z.of_nat bits)%Z
          by ring.
        rewrite <- Z.mul_assoc.
        replace
          (Uint63.to_Z d mod 2 ^ Z.of_nat bits +
           2 ^ Z.of_nat bits * (Uint63.to_Z d / 2 ^ Z.of_nat bits))%Z
          with
          (2 ^ Z.of_nat bits * (Uint63.to_Z d / 2 ^ Z.of_nat bits) +
           Uint63.to_Z d mod 2 ^ Z.of_nat bits)%Z
          by ring.
        assert (Hdiv :
          (Uint63.to_Z d =
           2 ^ Z.of_nat bits * (Uint63.to_Z d / 2 ^ Z.of_nat bits) +
           Uint63.to_Z d mod 2 ^ Z.of_nat bits)%Z).
        {
          apply Z_div_mod_eq_full.
        }
        nia.
Qed.

Lemma shift_right_limb8_digits_value :
  forall q
      x0 x1 x2 x3 x4 x5 x6 x7
      y0 y1 y2 y3 y4 y5 y6 y7
      c0 c1 c2 c3 c4 c5 c6 c7 carry,
    c0 + q * y0 = x0 + digit_base_z * c1 ->
    c1 + q * y1 = x1 + digit_base_z * c2 ->
    c2 + q * y2 = x2 + digit_base_z * c3 ->
    c3 + q * y3 = x3 + digit_base_z * c4 ->
    c4 + q * y4 = x4 + digit_base_z * c5 ->
    c5 + q * y5 = x5 + digit_base_z * c6 ->
    c6 + q * y6 = x6 + digit_base_z * c7 ->
    c7 + q * y7 = x7 + digit_base_z * carry ->
    c0 + q * digits_value [y0; y1; y2; y3; y4; y5; y6; y7] =
      digits_value [x0; x1; x2; x3; x4; x5; x6; x7] + digit_base8_z * carry.
Proof.
  cbv [digits_value digit_base8_z digit_base_z].
  nia.
Qed.

Lemma shift_right_limb8_small_correct :
  forall bits carry x block carry',
    (0 < bits < digit_shift_nat)%nat ->
    canonical_limb8 x ->
    (0 <= Uint63.to_Z carry < 2 ^ Z.of_nat bits)%Z ->
    shift_right_limb8_small
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      carry x = (block, carry') ->
    canonical_limb8 block /\
    canonical_digit carry' /\
    (Uint63.to_Z carry' < 2 ^ Z.of_nat bits)%Z /\
    Uint63.to_Z carry' + 2 ^ Z.of_nat bits * limb8_value block =
      limb8_value x + digit_base8_z * Uint63.to_Z carry.
Proof.
  intros bits carry
      [x0 x1 x2 x3 x4 x5 x6 x7] block carry' Hbits Hx Hcarry Hshift.
  destruct Hx as [Hx0 [Hx1 [Hx2 [Hx3 [Hx4 [Hx5 [Hx6 Hx7]]]]]]].
  unfold shift_right_limb8_small in Hshift.
  destruct (shift_right_digit_small
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      carry x7) as [y7 c7] eqn:H7.
  destruct (shift_right_digit_small
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      c7 x6) as [y6 c6] eqn:H6.
  destruct (shift_right_digit_small
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      c6 x5) as [y5 c5] eqn:H5.
  destruct (shift_right_digit_small
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      c5 x4) as [y4 c4] eqn:H4.
  destruct (shift_right_digit_small
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      c4 x3) as [y3 c3] eqn:H3.
  destruct (shift_right_digit_small
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      c3 x2) as [y2 c2] eqn:H2.
  destruct (shift_right_digit_small
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      c2 x1) as [y1 c1] eqn:H1.
  destruct (shift_right_digit_small
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      c1 x0) as [y0 c0] eqn:H0.
  cbn in Hshift.
  injection Hshift as Hblock Hcarry'; subst.
  destruct (shift_right_digit_small_correct _ _ _ _ _ Hbits Hx7 Hcarry H7)
    as [Hy7 [Hc7 [Hc7lt Hval7]]].
  destruct (shift_right_digit_small_correct _ _ _ _ _ Hbits Hx6
      (conj (proj1 Hc7) Hc7lt) H6)
    as [Hy6 [Hc6 [Hc6lt Hval6]]].
  destruct (shift_right_digit_small_correct _ _ _ _ _ Hbits Hx5
      (conj (proj1 Hc6) Hc6lt) H5)
    as [Hy5 [Hc5 [Hc5lt Hval5]]].
  destruct (shift_right_digit_small_correct _ _ _ _ _ Hbits Hx4
      (conj (proj1 Hc5) Hc5lt) H4)
    as [Hy4 [Hc4 [Hc4lt Hval4]]].
  destruct (shift_right_digit_small_correct _ _ _ _ _ Hbits Hx3
      (conj (proj1 Hc4) Hc4lt) H3)
    as [Hy3 [Hc3 [Hc3lt Hval3]]].
  destruct (shift_right_digit_small_correct _ _ _ _ _ Hbits Hx2
      (conj (proj1 Hc3) Hc3lt) H2)
    as [Hy2 [Hc2 [Hc2lt Hval2]]].
  destruct (shift_right_digit_small_correct _ _ _ _ _ Hbits Hx1
      (conj (proj1 Hc2) Hc2lt) H1)
    as [Hy1 [Hc1 [Hc1lt Hval1]]].
  destruct (shift_right_digit_small_correct _ _ _ _ _ Hbits Hx0
      (conj (proj1 Hc1) Hc1lt) H0)
    as [Hy0 [Hc0 [Hc0lt Hval0]]].
  split.
  - exact (conj Hy0
      (conj Hy1
      (conj Hy2
      (conj Hy3
      (conj Hy4
      (conj Hy5
      (conj Hy6 Hy7))))))).
  - split.
    + exact Hc0.
    + split.
      * exact Hc0lt.
      * change (limb8_value (Limb8 y0 y1 y2 y3 y4 y5 y6 y7)) with
          (digits_value
             [Uint63.to_Z y0; Uint63.to_Z y1; Uint63.to_Z y2; Uint63.to_Z y3;
              Uint63.to_Z y4; Uint63.to_Z y5; Uint63.to_Z y6; Uint63.to_Z y7]).
        change (limb8_value (Limb8 x0 x1 x2 x3 x4 x5 x6 x7)) with
          (digits_value
             [Uint63.to_Z x0; Uint63.to_Z x1; Uint63.to_Z x2; Uint63.to_Z x3;
              Uint63.to_Z x4; Uint63.to_Z x5; Uint63.to_Z x6; Uint63.to_Z x7]).
        eapply shift_right_limb8_digits_value;
          exact Hval0 || exact Hval1 || exact Hval2 || exact Hval3 ||
          exact Hval4 || exact Hval5 || exact Hval6 || exact Hval7.
Qed.

Fixpoint shift_right_bigint_small_carry (bits : nat) (carry : Uint63.int)
    (rev_blocks : bigint) : Uint63.int :=
  match rev_blocks with
  | [] => carry
  | b :: bs =>
      let '(_, carry') :=
        shift_right_limb8_small
          (Uint63.of_Z (Z.of_nat bits))
          (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
          (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
          carry b in
      shift_right_bigint_small_carry bits carry' bs
  end.

Lemma shift_right_bigint_small_aux_length :
  forall bits carry rev_blocks acc,
    List.length
      (shift_right_bigint_small_aux
         (Uint63.of_Z (Z.of_nat bits))
         (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
         (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
         carry rev_blocks acc) =
      (List.length rev_blocks + List.length acc)%nat.
Proof.
  intros bits carry rev_blocks acc.
  revert carry acc.
  induction rev_blocks as [|b bs IH]; intros carry acc.
  - reflexivity.
  - simpl.
    destruct (shift_right_limb8_small
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      carry b) as [b' carry'].
    rewrite IH.
    simpl.
    lia.
Qed.

Lemma shift_right_bigint_small_aux_app :
  forall bits carry rev_blocks acc,
    shift_right_bigint_small_aux
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      carry rev_blocks acc =
    shift_right_bigint_small_aux
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      carry rev_blocks [] ++ acc.
Proof.
  intros bits carry rev_blocks acc.
  revert carry acc.
  induction rev_blocks as [|b bs IH]; intros carry acc.
  - reflexivity.
  - simpl.
    destruct (shift_right_limb8_small
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      carry b) as [b' carry'].
    rewrite (IH carry' (b' :: acc)).
    rewrite (IH carry' [b']).
    simpl.
    rewrite <- app_assoc.
    reflexivity.
Qed.

Lemma shift_right_bigint_small_carry_last :
  forall bits carry rev_blocks b,
    (0 < bits < digit_shift_nat)%nat ->
    shift_right_bigint_small_carry bits carry (rev_blocks ++ [b]) =
      Uint63.land (d0 b)
        (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one).
Proof.
  intros bits carry rev_blocks.
  revert carry.
  induction rev_blocks as [|a rev_blocks IH]; intros carry b Hbits.
  - simpl.
    destruct (shift_right_limb8_small
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      carry b) as [hi lo] eqn:Hshift.
    exact (shift_right_limb8_small_low bits carry b hi lo Hbits Hshift).
  - simpl.
    destruct (shift_right_limb8_small
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      carry a) as [hi lo] eqn:Hshift.
    apply IH.
    exact Hbits.
Qed.

Lemma shift_right_bigint_small_carry_rev :
  forall bits carry b bs,
    (0 < bits < digit_shift_nat)%nat ->
    shift_right_bigint_small_carry bits carry (rev (b :: bs)) =
      Uint63.land (d0 b)
        (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one).
Proof.
  intros bits carry b bs Hbits.
  change (rev (b :: bs)) with (rev bs ++ [b]).
  apply shift_right_bigint_small_carry_last.
  exact Hbits.
Qed.

Lemma shift_right_limb8_small_value_scaled :
  forall scale bits carry x hi lo,
    (0 < bits < digit_shift_nat)%nat ->
    canonical_limb8 x ->
    (0 <= Uint63.to_Z carry < 2 ^ Z.of_nat bits)%Z ->
    shift_right_limb8_small
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      carry x = (hi, lo) ->
    scale * Uint63.to_Z lo + scale * (2 ^ Z.of_nat bits) * limb8_value hi =
      scale * limb8_value x + scale * digit_base8_z * Uint63.to_Z carry.
Proof.
  intros scale bits carry x hi lo Hbits Hx Hcarry Hshift.
  pose proof (shift_right_limb8_small_correct bits carry x hi lo Hbits Hx Hcarry Hshift)
    as [_ [_ [_ Hvalue]]].
  replace
    (scale * Uint63.to_Z lo + scale * 2 ^ Z.of_nat bits * limb8_value hi)
    with (scale * (Uint63.to_Z lo + 2 ^ Z.of_nat bits * limb8_value hi))
    by ring.
  replace
    (scale * limb8_value x + scale * digit_base8_z * Uint63.to_Z carry)
    with (scale * (limb8_value x + digit_base8_z * Uint63.to_Z carry))
    by ring.
  rewrite Hvalue.
  ring.
Qed.

Lemma shift_right_bigint_small_step_value :
  forall bits carry b bs hi lo,
    (0 < bits < digit_shift_nat)%nat ->
    canonical_limb8 b ->
    (0 <= Uint63.to_Z carry < 2 ^ Z.of_nat bits)%Z ->
    shift_right_limb8_small
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      carry b = (hi, lo) ->
    let A := digit_base8_z ^ Z.of_nat (List.length bs) in
    let B := 2 ^ Z.of_nat bits in
    bigint_value (rev (b :: bs)) + A * digit_base8_z * Uint63.to_Z carry =
      bigint_value (rev bs) + A * Uint63.to_Z lo + A * B * limb8_value hi.
Proof.
  intros bits carry b bs hi lo Hbits Hb Hcarry Hshift A B.
  change (rev (b :: bs)) with (rev bs ++ [b]).
  rewrite bigint_value_app_blocks.
  rewrite length_rev.
  simpl.
  change (digit_base8_z ^ Z.of_nat (S (List.length bs)))
    with (digit_base8_z ^ Z.of_nat (List.length bs) * digit_base8_z).
  rewrite bigint_value_cons.
  change (bigint_value []) with 0%Z.
  ring_simplify.
  change (digit_base8_z ^ Z.of_nat (List.length bs)) with A.
  change (2 ^ Z.of_nat bits) with B.
  pose proof
    (shift_right_limb8_small_value_scaled A bits carry b hi lo Hbits Hb
      Hcarry Hshift) as Hstep.
  change (2 ^ Z.of_nat bits) with B in Hstep.
  assert (Hstep' :
    bigint_value (rev bs) + (A * Uint63.to_Z lo + A * B * limb8_value hi) =
    bigint_value (rev bs) + (A * limb8_value b + A * digit_base8_z * Uint63.to_Z carry)).
  {
    rewrite Hstep.
    reflexivity.
  }
  ring_simplify in Hstep'.
  transitivity
    (bigint_value (rev bs) + A * limb8_value b + A * digit_base8_z * Uint63.to_Z carry).
  - ring.
  - symmetry.
    exact Hstep'.
Qed.

Lemma shift_right_bigint_small_aux_value :
  forall bits carry rev_blocks,
    (0 < bits < digit_shift_nat)%nat ->
    canonical_bigint rev_blocks ->
    (0 <= Uint63.to_Z carry < 2 ^ Z.of_nat bits)%Z ->
    bigint_value (rev rev_blocks) +
      (digit_base8_z ^ Z.of_nat (List.length rev_blocks)) * Uint63.to_Z carry =
    Uint63.to_Z (shift_right_bigint_small_carry bits carry rev_blocks) +
      (2 ^ Z.of_nat bits) *
        bigint_value
          (shift_right_bigint_small_aux
             (Uint63.of_Z (Z.of_nat bits))
             (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
             (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
             carry rev_blocks []).
Proof.
  intros bits carry rev_blocks Hbits Hrev Hcarry.
  revert carry Hcarry.
  induction Hrev as [|b bs Hb Hbs IH]; intros carry Hcarry.
  - simpl.
    change (bigint_value []) with 0%Z.
    rewrite Z.mul_0_r.
    destruct (Uint63.to_Z carry); reflexivity.
  - simpl.
    destruct (shift_right_limb8_small
      (Uint63.of_Z (Z.of_nat bits))
      (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
      (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
      carry b) as [hi lo] eqn:Hshift.
    pose proof (shift_right_limb8_small_correct bits carry b hi lo Hbits Hb Hcarry Hshift)
      as [Hhi [Hlo [Hlo_lt Hstep_limb]]].
    pose proof (IH lo (conj (proj1 Hlo) Hlo_lt)) as IHlo.
    rewrite (shift_right_bigint_small_aux_app bits lo bs [hi]).
    rewrite (bigint_value_app_blocks
      (shift_right_bigint_small_aux
         (Uint63.of_Z (Z.of_nat bits))
         (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
         (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
         lo bs []) [hi]).
    replace
      (Z.of_nat
         (List.length
            (shift_right_bigint_small_aux
               (Uint63.of_Z (Z.of_nat bits))
               (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
               (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
               lo bs [])))
      with (Z.of_nat (List.length bs)).
    2:{
      rewrite (shift_right_bigint_small_aux_length bits lo bs []).
      simpl.
      rewrite Nat.add_0_r.
      reflexivity.
    }
    simpl.
    rewrite bigint_value_cons.
    change (bigint_value []) with 0%Z.
    ring_simplify.
    set (A := digit_base8_z ^ Z.of_nat (List.length bs)).
    set (B := 2 ^ Z.of_nat bits).
    change (digit_base8_z ^ Z.of_nat (List.length bs)) with A in IHlo |- *.
    change (2 ^ Z.of_nat bits) with B in IHlo |- *.
    pose proof (shift_right_bigint_small_step_value bits carry b bs hi lo Hbits Hb Hcarry Hshift)
      as Hstep.
    change (digit_base8_z ^ Z.of_nat (List.length bs)) with A in Hstep.
    change (2 ^ Z.of_nat bits) with B in Hstep.
    change (bigint_value (rev (b :: bs))) with (bigint_value (rev bs ++ [b])) in Hstep.
    transitivity (bigint_value (rev bs ++ [b]) + A * digit_base8_z * Uint63.to_Z carry).
    + change (bigint_value (rev (b :: bs))) with (bigint_value (rev bs ++ [b])).
      replace (Z.pow_pos digit_base8_z (Pos.of_succ_nat (List.length bs)))
        with (A * digit_base8_z).
      * reflexivity.
      * subst A.
        change (Z.pow_pos digit_base8_z (Pos.of_succ_nat (List.length bs)))
          with (digit_base8_z ^ Z.of_nat (S (List.length bs))).
        replace (Z.of_nat (S (List.length bs))) with (Z.of_nat (List.length bs) + 1) by lia.
        rewrite Z.pow_add_r by (unfold digit_base8_z; cbv [digit_base_z]; lia).
        rewrite Z.pow_1_r.
        ring.
    + transitivity (bigint_value (rev bs) + A * Uint63.to_Z lo + A * B * limb8_value hi).
      * exact Hstep.
      * rewrite IHlo.
        replace (B * A * limb8_value hi) with (A * B * limb8_value hi) by ring.
        ring_simplify.
        reflexivity.
Qed.

Lemma shift_right_bigint_small_value :
  forall bits b bs,
    (0 < bits < digit_shift_nat)%nat ->
    canonical_bigint (b :: bs) ->
    bigint_value (b :: bs) =
      Uint63.to_Z
        (Uint63.land (d0 b)
           (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)) +
      (2 ^ Z.of_nat bits) * bigint_value (shift_right_bigint_small bits (b :: bs)).
Proof.
  intros bits b bs Hbits Hx.
  unfold shift_right_bigint_small.
  rewrite trim_bigint_value.
  assert (Hrev : canonical_bigint (rev (b :: bs))).
  {
    apply Forall_rev.
    exact Hx.
  }
  assert (Hzero : (0 <= Uint63.to_Z zero_digit < 2 ^ Z.of_nat bits)%Z).
  {
    rewrite zero_digit_to_Z.
    split.
    - lia.
    - apply Z.pow_pos_nonneg; lia.
  }
  pose proof
    (shift_right_bigint_small_aux_value bits zero_digit (rev (b :: bs)) Hbits
      Hrev Hzero) as Hvalue.
  rewrite shift_right_bigint_small_carry_rev in Hvalue by exact Hbits.
  rewrite rev_involutive in Hvalue.
  rewrite rev_length in Hvalue.
  rewrite zero_digit_to_Z in Hvalue.
  rewrite Z.mul_0_r in Hvalue.
  rewrite Z.add_0_r in Hvalue.
  exact Hvalue.
Qed.

Lemma digits_value_range :
  forall xs,
    Forall (fun z => (0 <= z < digit_base_z)%Z) xs ->
    (0 <= digits_value xs < digit_base_z ^ Z.of_nat (List.length xs))%Z.
Proof.
  intros xs Hxs.
  induction Hxs as [|x xs Hx Hxs IH].
  - simpl.
    change (digit_base_z ^ 0) with 1%Z.
    split; lia.
  - simpl.
    destruct Hx as [Hx0 Hx1].
    destruct IH as [IH0 IH1].
    split.
    + apply Z.add_nonneg_nonneg.
      * exact Hx0.
      * destruct (digits_value xs); simpl in *; lia.
    + assert (Htail_le :
        (digits_value xs <= digit_base_z ^ Z.of_nat (List.length xs) - 1)%Z).
      { lia. }
      assert (Hmul_le :
        (digit_base_z * digits_value xs <=
         digit_base_z * (digit_base_z ^ Z.of_nat (List.length xs) - 1))%Z).
      {
        apply Z.mul_le_mono_nonneg_l.
        - cbv [digit_base_z].
          lia.
        - exact Htail_le.
      }
      assert (Hlt' :
        (x + digit_base_z * digits_value xs <
         digit_base_z + digit_base_z * (digit_base_z ^ Z.of_nat (List.length xs) - 1))%Z).
      { nia. }
      eapply Z.lt_le_trans.
      * exact Hlt'.
      * replace (Z.pow_pos digit_base_z (Pos.of_succ_nat (List.length xs)))
          with (digit_base_z * digit_base_z ^ Z.of_nat (List.length xs)).
        2:{
          change (Z.pow_pos digit_base_z (Pos.of_succ_nat (List.length xs)))
            with (digit_base_z ^ Z.of_nat (S (List.length xs))).
          rewrite Nat2Z.inj_succ.
          replace (Z.succ (Z.of_nat (List.length xs)))
            with (Z.of_nat (List.length xs) + 1)%Z by lia.
          rewrite Z.pow_add_r by (cbv [digit_base_z]; lia).
          rewrite Z.pow_1_r.
          ring.
        }
        replace
          (digit_base_z + digit_base_z * (digit_base_z ^ Z.of_nat (List.length xs) - 1))
          with
          (digit_base_z * digit_base_z ^ Z.of_nat (List.length xs))
          by ring.
        apply Z.le_refl.
Qed.

Lemma limb8_take_digits_bound :
  forall k x,
    canonical_limb8 x ->
    (0 <= limb8_value (limb8_take_digits k x) < digit_base_z ^ Z.of_nat k)%Z.
Proof.
  intros k x Hx.
  rewrite limb8_take_digits_value.
  pose proof (Forall_firstn (fun z => (0 <= z < digit_base_z)%Z) k
    (limb8_digits_z x) (limb8_digits_z_canonical x Hx)) as Hdigits.
  pose proof (digits_value_range (firstn k (limb8_digits_z x)) Hdigits) as [H0 Hlt].
  split.
  - exact H0.
  - eapply Z.lt_le_trans.
    + exact Hlt.
    + apply Z.pow_le_mono_r.
      * cbv [digit_base_z].
        lia.
      * rewrite length_firstn, limb8_digits_z_length.
        lia.
Qed.

Lemma shift_right_bigint_digits_small_aux_canonical :
  forall k carry rev_blocks acc,
    (k < 8)%nat ->
    canonical_limb8 carry ->
    carry = limb8_take_digits k carry ->
    canonical_bigint rev_blocks ->
    canonical_bigint acc ->
    canonical_bigint (shift_right_bigint_digits_small_aux k carry rev_blocks acc).
Proof.
  intros k carry rev_blocks acc Hk Hcarry Hcarryk Hrev.
  revert carry acc Hcarry Hcarryk.
  induction Hrev as [|b bs Hb Hbs IH]; intros carry acc Hcarry Hcarryk Hacc.
  - exact Hacc.
  - simpl.
    destruct (shift_right_limb8_digits_small k carry b) as [hi lo] eqn:Hshift.
    pose proof
      (shift_right_limb8_digits_small_low_carry_canonical k carry b hi lo
        Hk Hcarry Hb Hcarryk Hshift) as [Hhi Hlo].
    apply IH.
    + exact Hlo.
    + rewrite (shift_right_limb8_digits_small_low k carry b hi lo Hk Hshift).
      symmetry.
      apply limb8_take_digits_idem.
    + constructor.
      * exact Hhi.
      * exact Hacc.
Qed.

Lemma shift_right_bigint_digits_small_canonical :
  forall k x,
    (k < 8)%nat ->
    canonical_bigint x ->
    canonical_bigint (shift_right_bigint_digits_small k x).
Proof.
  intros k x Hk Hx.
  unfold shift_right_bigint_digits_small.
  apply trim_bigint_canonical.
  apply shift_right_bigint_digits_small_aux_canonical.
  - exact Hk.
  - exact canonical_zero_limb8.
  - symmetry.
    apply limb8_take_digits_zero_limb8.
  - apply Forall_rev.
    exact Hx.
  - constructor.
Qed.

Lemma digit_base8_pow_eq_digit_base_pow :
  forall blocks,
    digit_base8_z ^ Z.of_nat blocks = digit_base_z ^ Z.of_nat (8 * blocks).
Proof.
  intros blocks.
  unfold digit_base8_z.
  rewrite Nat2Z.inj_mul.
  change (Z.of_nat 8) with 8%Z.
  rewrite Z.pow_mul_r by (cbv [digit_base_z]; lia).
  reflexivity.
Qed.

Lemma digit_base_pow_eq_pow2 :
  forall digits,
    digit_base_z ^ Z.of_nat digits = 2 ^ Z.of_nat (digit_shift_nat * digits).
Proof.
  intros digits.
  rewrite digit_base_z_pow2.
  replace (Z.of_nat (digit_shift_nat * digits))
    with (Z.of_nat digit_shift_nat * Z.of_nat digits) by lia.
  rewrite <- Z.pow_mul_r by lia.
  reflexivity.
Qed.

Lemma pow2_divmod_digit_shift :
  forall n,
    digit_base_z ^ Z.of_nat (Nat.div n digit_shift_nat) *
      2 ^ Z.of_nat (Nat.modulo n digit_shift_nat) =
    2 ^ Z.of_nat n.
Proof.
  intros n.
  rewrite digit_base_pow_eq_pow2.
  replace (Z.of_nat n)
    with (Z.of_nat (digit_shift_nat * Nat.div n digit_shift_nat + Nat.modulo n digit_shift_nat))
    by (
      pose proof (Nat.div_mod n digit_shift_nat ltac:(cbv [digit_shift_nat]; discriminate)) as Hdiv;
      apply f_equal;
      symmetry;
      exact Hdiv).
  rewrite Nat2Z.inj_add.
  rewrite Z.pow_add_r by lia.
  ring.
Qed.

Lemma bigint_split_whole_digits_canonical :
  forall whole_digits x,
    canonical_bigint x ->
    canonical_bigint (fst (bigint_split_whole_digits whole_digits x)) /\
    canonical_bigint (snd (bigint_split_whole_digits whole_digits x)).
Proof.
  intros whole_digits x Hx.
  unfold bigint_split_whole_digits.
  set (whole_blocks := Nat.div whole_digits 8).
  set (rem_digits := Nat.modulo whole_digits 8).
  set (low_blocks := firstn whole_blocks x).
  set (high_blocks := skipn whole_blocks x).
  assert (Hrem_lt8 : (rem_digits < 8)%nat).
  {
    subst rem_digits.
    apply Nat.mod_upper_bound.
    lia.
  }
  assert (Hlow_blocks : canonical_bigint low_blocks).
  {
    subst low_blocks.
    apply canonical_bigint_firstn.
    exact Hx.
  }
  assert (Hhigh_blocks : canonical_bigint high_blocks).
  {
    subst high_blocks.
    apply canonical_bigint_skipn.
    exact Hx.
  }
  destruct rem_digits as [|rem_digits].
  - simpl.
    split; apply trim_bigint_canonical; assumption.
  - simpl.
    split.
    + apply (shift_right_bigint_digits_small_canonical (S rem_digits) high_blocks).
      * lia.
      * exact Hhigh_blocks.
    + apply trim_bigint_canonical.
      apply snoc_nonzero_block_canonical.
      * exact Hlow_blocks.
      * destruct high_blocks as [|b bs].
        -- apply canonical_zero_limb8.
        -- inversion Hhigh_blocks as [|b' bs' Hb Hrest]; subst.
           apply limb8_take_digits_canonical.
           exact Hb.
Qed.

Lemma bigint_split_whole_digits_value :
  forall whole_digits x,
    canonical_bigint x ->
    bigint_value x =
      bigint_value (snd (bigint_split_whole_digits whole_digits x)) +
      digit_base_z ^ Z.of_nat whole_digits *
        bigint_value (fst (bigint_split_whole_digits whole_digits x)).
Proof.
  intros whole_digits x Hx.
  unfold bigint_split_whole_digits.
  set (whole_blocks := Nat.div whole_digits 8).
  set (rem_digits := Nat.modulo whole_digits 8).
  assert (Hrem_lt8 : (rem_digits < 8)%nat).
  {
    subst rem_digits.
    apply Nat.mod_upper_bound.
    lia.
  }
  assert (Hwhole : (whole_digits = 8 * whole_blocks + rem_digits)%nat).
  {
    subst whole_blocks rem_digits.
    exact (Nat.div_mod whole_digits 8 ltac:(lia)).
  }
  destruct rem_digits as [|rem_digits].
  - simpl in Hwhole.
    destruct (le_lt_dec whole_blocks (List.length x)).
    + replace whole_digits with (8 * whole_blocks)%nat by lia.
      simpl.
      rewrite !trim_bigint_value.
      rewrite (bigint_value_firstn_skipn whole_blocks x).
      rewrite firstn_length_le by exact l.
      rewrite digit_base8_pow_eq_digit_base_pow.
      reflexivity.
    + rewrite skipn_all2 by lia.
      rewrite firstn_all2 by lia.
      simpl.
      rewrite !trim_bigint_value.
      rewrite Z.mul_0_r.
      rewrite Z.add_0_r.
      reflexivity.
  - simpl in Hwhole.
    destruct (lt_dec whole_blocks (List.length x)).
    + replace whole_digits with (8 * whole_blocks + S rem_digits)%nat by lia.
      assert (Hlen_low : List.length (firstn whole_blocks x) = whole_blocks).
      {
        rewrite length_firstn.
        lia.
      }
      assert (Hhigh_nonempty : skipn whole_blocks x <> []).
      {
        intro Hnil.
        apply (f_equal (@List.length _)) in Hnil.
        rewrite length_skipn in Hnil.
        simpl in Hnil.
        lia.
      }
      destruct (skipn whole_blocks x) as [|b bs] eqn:Hhigh_blocks.
      { exfalso. apply Hhigh_nonempty. reflexivity. }
      simpl.
      rewrite !trim_bigint_value.
      rewrite snoc_nonzero_block_value.
      rewrite bigint_value_app_blocks.
      rewrite Hlen_low.
      rewrite (bigint_value_firstn_skipn whole_blocks x).
      rewrite Hhigh_blocks.
      rewrite (shift_right_bigint_digits_small_value (S rem_digits) b bs
        (conj (Nat.lt_0_succ rem_digits) Hrem_lt8)).
      repeat rewrite Hlen_low.
      rewrite bigint_value_cons.
      change (bigint_value []) with 0%Z.
      ring_simplify.
      assert (Hpow :
        digit_base8_z ^ Z.of_nat whole_blocks *
          digit_base_z ^ Z.of_nat (S rem_digits) =
        digit_base_z ^ Z.of_nat (8 * whole_blocks + S rem_digits)).
      {
        rewrite digit_base_pow_block_split.
        reflexivity.
      }
      set (V := bigint_value (shift_right_bigint_digits_small (S rem_digits) (b :: bs))).
      ring_simplify.
      replace
        (digit_base8_z ^ Z.of_nat whole_blocks *
           digit_base_z ^ Z.of_nat (S rem_digits) * V)
        with
        (digit_base_z ^ Z.of_nat (8 * whole_blocks + S rem_digits) * V).
      2:{
        rewrite Hpow.
        ring.
      }
      replace
        (V *
         digit_base_z
           ^ Z.of_nat
               (whole_blocks +
                (whole_blocks +
                 (whole_blocks +
                  (whole_blocks +
                   (whole_blocks +
                    (whole_blocks + (whole_blocks + (whole_blocks + 0))))))) +
                S rem_digits))
        with
        (digit_base_z
           ^ Z.of_nat
               (whole_blocks +
                (whole_blocks +
                 (whole_blocks +
                  (whole_blocks +
                   (whole_blocks +
                    (whole_blocks + (whole_blocks + (whole_blocks + 0))))))) +
                S rem_digits) * V)
        by ring.
      reflexivity.
    + rewrite skipn_all2 by lia.
      rewrite firstn_all2 by lia.
      simpl.
      rewrite trim_bigint_value.
      rewrite snoc_nonzero_block_value.
      rewrite bigint_value_snoc_zero.
      rewrite Z.mul_0_r.
      rewrite Z.add_0_r.
      reflexivity.
Qed.

Lemma bigint_split_whole_digits_low_bound :
  forall whole_digits x,
    canonical_bigint x ->
    (0 <= bigint_value (snd (bigint_split_whole_digits whole_digits x)) <
     digit_base_z ^ Z.of_nat whole_digits)%Z.
Proof.
  intros whole_digits x Hx.
  unfold bigint_split_whole_digits.
  set (whole_blocks := Nat.div whole_digits 8).
  set (rem_digits := Nat.modulo whole_digits 8).
  set (low_blocks := firstn whole_blocks x).
  assert (Hwhole : (whole_digits = 8 * whole_blocks + rem_digits)%nat).
  {
    subst whole_blocks rem_digits.
    exact (Nat.div_mod whole_digits 8 ltac:(lia)).
  }
  assert (Hlow_blocks : canonical_bigint low_blocks).
  {
    subst low_blocks.
    apply canonical_bigint_firstn.
    exact Hx.
  }
	  destruct rem_digits as [|rem_digits].
	  - simpl in Hwhole.
	    destruct (le_lt_dec whole_blocks (List.length x)) as [Hwhole_le|Hwhole_gt].
	    + simpl.
	      rewrite trim_bigint_value.
	      destruct (bigint_value_range low_blocks Hlow_blocks) as [H0 Hlt].
      split.
      * exact H0.
      * eapply Z.lt_le_trans.
        -- exact Hlt.
        -- eapply Z.le_trans.
	           ++ apply Z.pow_le_mono_r.
	              ** cbv [digit_base8_z digit_base_z].
	                 lia.
	              ** subst low_blocks.
	                 rewrite firstn_length_le by exact Hwhole_le.
	                 apply Z.le_refl.
	           ++ rewrite digit_base8_pow_eq_digit_base_pow.
	              replace whole_digits with (8 * whole_blocks)%nat by lia.
	              apply Z.le_refl.
	    + subst low_blocks.
	      rewrite firstn_all2 by exact (Nat.lt_le_incl _ _ Hwhole_gt).
	      simpl.
	      rewrite trim_bigint_value.
	      destruct (bigint_value_range x Hx) as [H0 Hlt].
      split.
      * exact H0.
      * eapply Z.lt_le_trans.
        -- exact Hlt.
	        -- eapply Z.le_trans.
	           ++ apply Z.pow_le_mono_r.
	              ** cbv [digit_base8_z digit_base_z].
	                 lia.
	              ** apply Nat2Z.inj_le.
	                 exact (Nat.lt_le_incl _ _ Hwhole_gt).
	           ++ rewrite digit_base8_pow_eq_digit_base_pow.
	              replace whole_digits with (8 * whole_blocks)%nat by lia.
	              apply Z.le_refl.
	  - simpl in Hwhole.
	    destruct (lt_dec whole_blocks (List.length x)) as [Hwhole_lt|Hwhole_ge].
	    + assert (Hlen_low : List.length low_blocks = whole_blocks).
	      {
	        subst low_blocks.
	        rewrite length_firstn.
	        rewrite Nat.min_l by exact (Nat.lt_le_incl _ _ Hwhole_lt).
	        reflexivity.
	      }
      assert (Hhigh_blocks : canonical_bigint (skipn whole_blocks x)).
      {
        apply canonical_bigint_skipn.
        exact Hx.
	      }
	      destruct (skipn whole_blocks x) as [|b bs] eqn:Hhigh_blocks_eq.
	      {
	        exfalso.
	        pose proof (length_skipn whole_blocks x) as Hlen_skip.
	        rewrite Hhigh_blocks_eq in Hlen_skip.
	        simpl in Hlen_skip.
	        lia.
	      }
	      simpl.
      rewrite trim_bigint_value.
      rewrite snoc_nonzero_block_value.
      rewrite bigint_value_app_blocks.
	      rewrite Hlen_low.
	      rewrite bigint_value_cons.
	      change (bigint_value []) with 0%Z.
	      rewrite Z.mul_0_r.
	      rewrite Z.add_0_r.
	      inversion Hhigh_blocks as [|b' bs' Hb Hrest]; subst b' bs'; clear Hhigh_blocks.
	      destruct (bigint_value_range low_blocks Hlow_blocks) as [Hlow0 Hlow_lt].
	      pose proof (limb8_take_digits_bound (S rem_digits) b Hb) as [Hextra0 Hextra_lt].
	      split.
	      * apply Z.add_nonneg_nonneg.
	        -- exact Hlow0.
	        -- apply Z.mul_nonneg_nonneg.
	           ++ apply Z.pow_nonneg.
	              cbv [digit_base8_z digit_base_z].
	              lia.
	           ++ exact Hextra0.
	      * assert (Hlow_le :
	          (bigint_value low_blocks <= digit_base8_z ^ Z.of_nat whole_blocks - 1)%Z).
	        {
	          rewrite Hlen_low in Hlow_lt.
	          lia.
	        }
	        assert (Hextra_le :
	          (limb8_value (limb8_take_digits (S rem_digits) b) <=
	           digit_base_z ^ Z.of_nat (S rem_digits) - 1)%Z).
	        { lia. }
        assert (Hlt' :
          (bigint_value low_blocks +
           digit_base8_z ^ Z.of_nat whole_blocks *
             limb8_value (limb8_take_digits (S rem_digits) b) <
           digit_base8_z ^ Z.of_nat whole_blocks +
           digit_base8_z ^ Z.of_nat whole_blocks *
             (digit_base_z ^ Z.of_nat (S rem_digits) - 1))%Z).
        { nia. }
        eapply Z.lt_le_trans.
        -- exact Hlt'.
        -- replace (digit_base_z ^ Z.of_nat whole_digits)
             with (digit_base8_z ^ Z.of_nat whole_blocks *
                   digit_base_z ^ Z.of_nat (S rem_digits)).
           2:{
             replace whole_digits with (8 * whole_blocks + S rem_digits)%nat by lia.
             rewrite digit_base_pow_block_split.
             reflexivity.
           }
           replace
             (digit_base8_z ^ Z.of_nat whole_blocks +
              digit_base8_z ^ Z.of_nat whole_blocks *
                (digit_base_z ^ Z.of_nat (S rem_digits) - 1))
             with
             (digit_base8_z ^ Z.of_nat whole_blocks *
              digit_base_z ^ Z.of_nat (S rem_digits))
             by ring.
           apply Z.le_refl.
	    + subst low_blocks.
	      rewrite firstn_all2 by exact (proj1 (Nat.nlt_ge _ _) Hwhole_ge).
	      rewrite skipn_all2 by exact (proj1 (Nat.nlt_ge _ _) Hwhole_ge).
	      simpl.
      rewrite trim_bigint_value.
      rewrite snoc_nonzero_block_value.
      rewrite bigint_value_snoc_zero.
      destruct (bigint_value_range x Hx) as [H0 Hlt].
      split.
      * exact H0.
      * eapply Z.lt_le_trans.
        -- exact Hlt.
	        -- eapply Z.le_trans.
	           ++ apply Z.pow_le_mono_r.
	              ** cbv [digit_base8_z digit_base_z].
	                 lia.
	              ** apply Nat2Z.inj_le.
	                 exact (proj1 (Nat.nlt_ge _ _) Hwhole_ge).
	           ++ rewrite digit_base8_pow_eq_digit_base_pow.
	              replace whole_digits with (8 * whole_blocks + S rem_digits)%nat by lia.
	              apply Z.pow_le_mono_r.
	              ** cbv [digit_base_z].
	                 lia.
	              ** apply Nat2Z.inj_le.
	                 lia.
Qed.

Lemma bigint_divmod_pow2_value :
  forall n x,
    canonical_bigint x ->
    bigint_value x =
      bigint_value (snd (bigint_divmod_pow2 n x)) +
      (2 ^ Z.of_nat n) * bigint_value (fst (bigint_divmod_pow2 n x)).
Proof.
  intros n x Hx.
  unfold bigint_divmod_pow2.
  set (whole_digits := Nat.div n digit_shift_nat).
  set (rem_bits := Nat.modulo n digit_shift_nat).
  assert (Hpow2 :
    digit_base_z ^ Z.of_nat whole_digits * 2 ^ Z.of_nat rem_bits =
    2 ^ Z.of_nat n).
  {
    subst whole_digits rem_bits.
    apply pow2_divmod_digit_shift.
  }
	  assert (Hrem_lt : (rem_bits < digit_shift_nat)%nat).
	  {
	    subst rem_bits.
	    apply Nat.mod_upper_bound.
	    cbv [digit_shift_nat].
	    discriminate.
	  }
  destruct (Nat.leb (8 * List.length x)%nat whole_digits) eqn:Hsmall.
  - apply Nat.leb_le in Hsmall.
    simpl.
    rewrite Z.mul_0_r.
    rewrite Z.add_0_r.
    reflexivity.
  - destruct (bigint_split_whole_digits whole_digits x) as [high_digits low_digits] eqn:Hsplit.
    pose proof (bigint_split_whole_digits_value whole_digits x Hx) as Hsplit_value.
    rewrite Hsplit in Hsplit_value.
    simpl in Hsplit_value.
    pose proof (bigint_split_whole_digits_canonical whole_digits x Hx) as Hsplit_can.
    rewrite Hsplit in Hsplit_can.
    simpl in Hsplit_can.
    destruct Hsplit_can as [Hhigh_can Hlow_can].
    pose proof (bigint_split_whole_digits_low_bound whole_digits x Hx) as Hlow_bound.
    rewrite Hsplit in Hlow_bound.
    simpl in Hlow_bound.
    destruct Hlow_bound as [Hlow0 Hlow1].
    destruct rem_bits as [|rem_bits].
	    + simpl in Hpow2.
	      rewrite Hsplit_value.
	      rewrite <- Hpow2.
	      change (2 ^ 0) with 1%Z.
	      repeat rewrite Z.mul_1_l.
	      repeat rewrite Z.mul_1_r.
	      reflexivity.
    + destruct high_digits as [|b bs].
	      * simpl in Hsplit_value |- *.
	        unfold bigint_append_digit.
	        rewrite Uint63.eqb_refl.
	        rewrite trim_bigint_value.
	        rewrite Z.mul_0_r in Hsplit_value |- *.
	        rewrite Z.add_0_r in Hsplit_value |- *.
	        exact Hsplit_value.
      * assert (Hb0 : canonical_digit (d0 b)).
        {
          inversion Hhigh_can as [|b' bs' Hb Hrest]; subst.
          destruct Hb as [Hb0 Hrestb].
          exact Hb0.
        }
        assert (Hzero : (0 <= Uint63.to_Z zero_digit < 2 ^ Z.of_nat (S rem_bits))%Z).
        {
          rewrite zero_digit_to_Z.
          split.
          - lia.
          - apply Z.pow_pos_nonneg; lia.
        }
        set (extra_low :=
          Uint63.land (d0 b)
            (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat (S rem_bits)))) u63_one)).
        assert (Hextra_can : canonical_digit extra_low).
        {
          unfold extra_low.
          pose proof
            (shift_right_digit_small_correct
              (S rem_bits) zero_digit (d0 b)
              (Uint63.lor
                 (Uint63.lsr (d0 b) (Uint63.of_Z (Z.of_nat (S rem_bits))))
                 (Uint63.lsl zero_digit
                    (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat (S rem_bits))))))
              (Uint63.land (d0 b)
                 (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat (S rem_bits)))) u63_one))
              (conj (Nat.lt_0_succ rem_bits) Hrem_lt)
              Hb0 Hzero eq_refl) as [_ [Hcan [_ _]]].
          exact Hcan.
        }
        pose proof
          (bigint_append_digit_value whole_digits low_digits extra_low
             Hlow_can Hextra_can Hlow1) as Hrem_value.
	        pose proof
	          (shift_right_bigint_small_value (S rem_bits) b bs
	             (conj (Nat.lt_0_succ rem_bits) Hrem_lt) Hhigh_can) as Hhigh_value.
	        simpl.
	        unfold extra_low in Hrem_value |- *.
	        rewrite Hrem_value.
	        rewrite Hsplit_value.
	        rewrite Hhigh_value.
	        rewrite Z.mul_add_distr_l.
	        rewrite <- Hpow2.
	        rewrite Z.mul_assoc.
	        rewrite <- Z.add_assoc.
	        reflexivity.
Qed.
