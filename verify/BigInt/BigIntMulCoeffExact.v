From Coq Require Import Uint63 ZArith Lia Lists.List Arith.PeanoNat Array.PArray.
Require Import BigInt.NTTConcrete BigInt.BigIntMul BigInt.BigIntMulProof BigInt.BigIntMulCanonical
  BigInt.BigIntMulCRT BigInt.BigIntMulNormalize BigInt.BigIntMulNormalizeArithmetic
  BigInt.BigIntMulNormalizeValue BigInt.BigIntMulAlgebra BigInt.BigIntMulCoefficients
  BigInt.BigIntMulCompose.

Import ListNotations.
Local Open Scope Z_scope.

Lemma pow2_nat_ge_linear :
  forall n,
    (n <= Nat.pow 2 n)%nat.
Proof.
  induction n as [|n IH].
  - simpl.
    lia.
  - simpl.
    pose proof (Nat.pow_nonzero 2 n ltac:(lia)) as Hpow.
    lia.
Qed.

Lemma block_log_aux_bound :
  forall fuel need len k,
    len = Nat.pow 2 k ->
    (need <= len * Nat.pow 2 fuel)%nat ->
    (need <= Nat.pow 2 (block_log_aux fuel need len k))%nat.
Proof.
  induction fuel as [|fuel IH]; intros need len k Hlen Hbound.
  - simpl.
    destruct (Nat.leb need len) eqn:Hle.
    + apply Nat.leb_le in Hle.
      rewrite <- Hlen.
      exact Hle.
    + apply Nat.leb_gt in Hle.
      simpl in Hbound.
      lia.
  - simpl.
    destruct (Nat.leb need len) eqn:Hle.
    + apply Nat.leb_le in Hle.
      rewrite <- Hlen.
      exact Hle.
    + apply IH with (len := (len * 2)%nat) (k := S k).
      * rewrite Hlen.
        simpl.
        lia.
      * simpl in Hbound.
        nia.
Qed.

Lemma block_log_bound :
  forall need,
    (Nat.max 1 need <= Nat.pow 2 (block_log need))%nat.
Proof.
  intro need.
  unfold block_log.
  eapply block_log_aux_bound with (need := Nat.max 1 need) (len := 1%nat) (k := 0%nat).
  - reflexivity.
  - simpl.
    assert (Hmax : (Nat.max 1 need <= S need)%nat) by lia.
    eapply Nat.le_trans; [exact Hmax|].
    replace (2 ^ need + (2 ^ need + 0) + 0)%nat with (Nat.pow 2 (S need))%nat.
    + apply (pow2_nat_ge_linear (S need)).
    + simpl.
      lia.
Qed.

Lemma mul_needed_blocks_le_pow20 :
  forall a b,
    Nat.leb (mul_total_log a b) supported_max_log = true ->
    (mul_needed_blocks a b <= Nat.pow 2 supported_max_block_log)%nat.
Proof.
  intros a b Hlog.
  apply Nat.leb_le in Hlog.
  unfold mul_total_log, transform_log_of_block_log, supported_max_log,
    supported_max_block_log in *.
  cbn [mul_block_log] in *.
  eapply Nat.le_trans.
  - eapply Nat.le_trans.
    + apply Nat.le_max_r.
    + apply block_log_bound.
  - assert (Hk : (block_log (mul_needed_blocks a b) <= 20)%nat).
    {
      unfold mul_block_log in Hlog.
      lia.
    }
    replace (Nat.pow 2 supported_max_block_log) with (Nat.pow 2 20) by reflexivity.
    apply Nat.pow_le_mono_r.
    + lia.
    + exact Hk.
Qed.

Lemma mul_needed_digits_le_pow23 :
  forall a b,
    Nat.leb (mul_total_log a b) supported_max_log = true ->
    (mul_needed_digits a b <= Nat.pow 2 23)%nat.
Proof.
  intros a b Hlog.
  unfold mul_needed_digits.
  pose proof (mul_needed_blocks_le_pow20 a b Hlog) as Hblocks.
  replace (Nat.pow 2 23) with (8 * Nat.pow 2 supported_max_block_log)%nat.
  2:{
    unfold supported_max_block_log.
    replace 23%nat with (20 + 3)%nat by reflexivity.
    rewrite Nat.pow_add_r by lia.
    change (Nat.pow 2 3) with 8%nat.
    lia.
  }
  apply Nat.mul_le_mono_l.
  exact Hblocks.
Qed.

Lemma mul_needed_digits_bound_max_length :
  forall a b,
    Nat.leb (mul_needed_digits a b) coeff_array_max_digits = true ->
    (Z.of_nat (mul_needed_digits a b) <= Uint63.to_Z PArray.max_length)%Z.
Proof.
  intros a b Hdigits.
  apply Nat.leb_le in Hdigits.
  assert (Hmax :
    Z.of_nat coeff_array_max_digits = Uint63.to_Z PArray.max_length).
  {
    vm_compute.
    reflexivity.
  }
  rewrite <- Hmax.
  apply Nat2Z.inj_le.
  exact Hdigits.
Qed.

Lemma mul_needed_digits_lt_wB :
  forall a b,
    Nat.leb (mul_total_log a b) supported_max_log = true ->
    (Z.of_nat (mul_needed_digits a b) < Uint63.wB)%Z.
Proof.
  intros a b Hlog.
  eapply Z.lt_trans with (m := Z.of_nat (S (Nat.pow 2 23))).
  - apply Nat2Z.inj_lt.
    apply Nat.lt_succ_r.
    apply mul_needed_digits_le_pow23.
    exact Hlog.
  - vm_compute.
    reflexivity.
Qed.

Lemma mul_coeff_fuel_lt_wB :
  forall a b,
    Nat.leb (mul_total_log a b) supported_max_log = true ->
    (Z.of_nat (8 * S (mul_needed_blocks a b)) < Uint63.wB)%Z.
Proof.
  intros a b Hlog.
  unfold mul_needed_digits.
  eapply Z.lt_trans with (m := Z.of_nat (S (Nat.pow 2 23) + 8)).
  - apply Nat2Z.inj_lt.
    pose proof (mul_needed_digits_le_pow23 a b Hlog) as Hdigits.
    rewrite Nat.mul_succ_r.
    eapply Nat.le_lt_trans.
    + apply Nat.add_le_mono_r.
      exact Hdigits.
    + lia.
  - vm_compute.
    reflexivity.
Qed.

Lemma add_digits_length :
  forall xs ys,
    List.length (add_digits xs ys) = Nat.max (List.length xs) (List.length ys).
Proof.
  induction xs as [|x xs IH]; intros ys.
  - reflexivity.
  - destruct ys as [|y ys].
    + reflexivity.
    + simpl.
      rewrite IH.
      reflexivity.
Qed.

Lemma scale_digits_length :
  forall c xs,
    List.length (scale_digits c xs) = List.length xs.
Proof.
  intros c xs.
  unfold scale_digits.
  rewrite map_length.
  reflexivity.
Qed.

Lemma convolution_digits_length_cons :
  forall x xs ys,
    ys <> [] ->
    List.length (convolution_digits (x :: xs) ys) = (List.length xs + List.length ys)%nat.
Proof.
  intros x xs.
  revert x.
  induction xs as [|x' xs' IH]; intros x ys Hys.
  - destruct ys as [|y ys].
    + contradiction.
    + simpl.
      rewrite add_digits_length.
      rewrite scale_digits_length.
      simpl.
      lia.
  - simpl.
    change
      (add_digits (scale_digits x' ys) (0 :: convolution_digits xs' ys))
      with (convolution_digits (x' :: xs') ys).
    rewrite add_digits_length.
    rewrite scale_digits_length.
    replace
      (List.length (0 :: convolution_digits (x' :: xs') ys))
      with (S (List.length (convolution_digits (x' :: xs') ys)))
      by reflexivity.
    rewrite IH by exact Hys.
    destruct ys as [|y ys'].
    + contradiction.
    + simpl.
      lia.
Qed.

Lemma convolution_digits_length_nonempty :
  forall xs ys,
    xs <> [] ->
    ys <> [] ->
    List.length (convolution_digits xs ys) = Nat.pred (List.length xs + List.length ys).
Proof.
  intros [|x xs] ys Hxs Hys.
  - contradiction.
  - rewrite convolution_digits_length_cons by exact Hys.
    destruct ys as [|y ys'].
    + contradiction.
    + simpl.
      lia.
Qed.

Lemma digits_value_repeat_zero :
  forall n,
    digits_value (repeat 0 n) = 0.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    ring.
Qed.

Lemma coeff_digits_z_length :
  forall fuel idx arr,
    List.length (coeff_digits_z fuel idx arr) = fuel.
Proof.
  induction fuel as [|fuel IH]; intros idx arr.
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Lemma list_eq_nth_default_Z :
  forall xs ys,
    List.length xs = List.length ys ->
    (forall i, (i < List.length xs)%nat -> nth i xs 0 = nth i ys 0) ->
    xs = ys.
Proof.
  induction xs as [|x xs IH]; intros ys Hlen Hnth.
  - destruct ys as [|y ys]; simpl in *; [reflexivity|lia].
  - destruct ys as [|y ys]; simpl in *; [lia|].
    assert (Hx : x = y).
    {
      specialize (Hnth 0%nat ltac:(lia)).
      simpl in Hnth.
      exact Hnth.
    }
    assert (Hrest : xs = ys).
    {
      apply IH.
      - lia.
      - intros i Hi.
        specialize (Hnth (S i) ltac:(lia)).
        simpl in Hnth.
        exact Hnth.
    }
    subst.
    reflexivity.
Qed.

Lemma nth_coeff_digits_z :
  forall fuel idx arr i,
    (i < fuel)%nat ->
    nth i (coeff_digits_z fuel idx arr) 0 =
    Uint63.to_Z (coeff_array_at arr (advance_idx i idx)).
Proof.
  induction fuel as [|fuel IH]; intros idx arr i Hi.
  - lia.
  - destruct i as [|i].
    + simpl.
      reflexivity.
    + simpl.
      apply IH.
      lia.
Qed.

Lemma nth_coeff_digits_z_zero :
  forall fuel arr i,
    (i < fuel)%nat ->
    (Z.of_nat fuel < Uint63.wB)%Z ->
    nth i (coeff_digits_z fuel zero_digit arr) 0 =
    Uint63.to_Z (coeff_array_at arr (u63_of_nat i)).
Proof.
  intros fuel arr i Hi Hfuel.
  rewrite nth_coeff_digits_z by exact Hi.
  rewrite advance_idx_correct.
  - rewrite Uint63.add_comm.
    rewrite u63_add_zero_r.
    reflexivity.
  - eapply Z.lt_trans.
    + apply Nat2Z.inj_lt.
      exact Hi.
    + exact Hfuel.
Qed.

Lemma bigint_digits_z_nonempty :
  forall x,
    x <> [] ->
    bigint_digits_z x <> [].
Proof.
  intros [|b bs] Hx.
  - contradiction.
  - destruct b.
    simpl.
    discriminate.
Qed.

Lemma nth_convolution_digits_pad_zero_nonempty :
  forall xs ys extra i,
    xs <> [] ->
    ys <> [] ->
    (i < Nat.pred (List.length xs + List.length ys) + extra)%nat ->
    nth i (convolution_digits xs ys ++ repeat 0 extra) 0 =
    convolution_coeff xs ys i.
Proof.
  intros xs ys extra i Hxs Hys Hi.
  pose proof (convolution_digits_length_nonempty xs ys Hxs Hys) as Hlen.
  destruct (lt_dec i (List.length (convolution_digits xs ys))) as [Hlt|Hge].
  - rewrite app_nth1 by exact Hlt.
    apply nth_convolution_digits.
  - rewrite app_nth2 by lia.
    rewrite nth_repeat.
    symmetry.
    apply convolution_coeff_zero_tail.
    rewrite Hlen in Hge.
    assert (Hsum_pos : (0 < List.length xs + List.length ys)%nat).
    {
      destruct xs as [|x xs']; [contradiction|].
      destruct ys as [|y ys']; [contradiction|].
      simpl.
      lia.
    }
    lia.
Qed.

Lemma coeff_array_at_u63_of_nat_oob :
  forall arr len i,
    PArray.length arr = u63_of_nat len ->
    (Z.of_nat len < Uint63.wB)%Z ->
    (Z.of_nat i < Uint63.wB)%Z ->
    (len <= i)%nat ->
    coeff_array_at arr (u63_of_nat i) = zero_digit.
Proof.
  intros arr len i Hlen HlenB HiB Hle.
  unfold coeff_array_at.
  rewrite Hlen.
  destruct (Uint63.ltb (u63_of_nat i) (u63_of_nat len)) eqn:Hlt.
  - apply Uint63.ltb_spec in Hlt.
    rewrite !u63_of_nat_small in Hlt by assumption.
    lia.
  - reflexivity.
Qed.

Lemma mul_coeff_array_length :
  forall a b,
    Nat.leb (mul_needed_digits a b) coeff_array_max_digits = true ->
    PArray.length (mul_coeff_array a b) = u63_of_nat (mul_needed_digits a b).
Proof.
  intros a b Hdigits.
  unfold mul_coeff_array.
  rewrite coeff_array_from_packed_trees_length.
  apply coeff_array_make_length.
  apply mul_needed_digits_bound_max_length.
  exact Hdigits.
Qed.

Lemma convolution_coeff_range :
  forall xs ys i,
    xs <> [] ->
    Forall (fun z => (0 <= z < digit_base_z)%Z) xs ->
    Forall (fun z => (0 <= z < digit_base_z)%Z) ys ->
    (0 <= convolution_coeff xs ys i <=
      Z.of_nat (List.length xs) * (digit_base_z - 1) * (digit_base_z - 1))%Z.
Proof.
  induction xs as [|x xs IH]; intros ys i Hxs_ne Hxs Hys.
  - contradiction.
  - inversion Hxs as [|x' xs' Hx Hxs']; subst.
    simpl.
    pose proof (nth_range ys i digit_base_z) as Hnth.
    specialize (Hnth).
    assert (Hbase : (0 < digit_base_z)%Z) by (cbv [digit_base_z]; lia).
    specialize (Hnth Hbase Hys).
    destruct Hnth as [Hnth0 Hnth1].
    destruct i as [|i].
    + simpl.
      split.
      * nia.
      * assert (Hx1 : (x <= digit_base_z - 1)%Z) by lia.
        assert (Hnth1' : (nth 0 ys 0 <= digit_base_z - 1)%Z) by lia.
        assert (Hprod :
          (x * nth 0 ys 0 <= (digit_base_z - 1) * (digit_base_z - 1))%Z).
        {
          nia.
        }
        assert (Hlen1 : (1 <= Z.of_nat (List.length (x :: xs)))%Z).
        {
          simpl.
          lia.
        }
        ring_simplify.
        eapply Z.le_trans.
        -- exact Hprod.
        -- simpl.
           nia.
    + destruct xs as [|x'' xs''].
      * simpl.
        split.
        -- nia.
        -- assert (Hx1 : (x <= digit_base_z - 1)%Z) by lia.
           assert (Hprod :
             (x * nth (S i) ys 0 <= (digit_base_z - 1) * (digit_base_z - 1))%Z).
           {
             nia.
           }
           ring_simplify.
           eapply Z.le_trans.
           ++ exact Hprod.
           ++ simpl.
              nia.
      * specialize (IH ys i ltac:(discriminate) Hxs' Hys).
        destruct IH as [IH0 IH1].
        assert (Hx1 : (x <= digit_base_z - 1)%Z) by lia.
        assert (Hnth1' : (nth (S i) ys 0 <= digit_base_z - 1)%Z) by lia.
        assert (Hprod :
          (x * nth (S i) ys 0 <= (digit_base_z - 1) * (digit_base_z - 1))%Z).
        {
          nia.
        }
        split.
        -- nia.
        -- cbn [convolution_coeff].
           assert (Htail :
             (convolution_coeff (x'' :: xs'') ys i <=
              Z.of_nat (List.length (x'' :: xs'')) *
              (digit_base_z - 1) * (digit_base_z - 1))%Z).
           {
             exact IH1.
           }
           assert (Hsum :
             (x * nth (S i) ys 0 + convolution_coeff (x'' :: xs'') ys i <=
              (digit_base_z - 1) * (digit_base_z - 1) +
              Z.of_nat (List.length (x'' :: xs'')) *
              ((digit_base_z - 1) * (digit_base_z - 1)))%Z).
           {
             nia.
           }
           eapply Z.le_trans; [exact Hsum|].
           change
             ((digit_base_z - 1) * (digit_base_z - 1) +
              Z.of_nat (List.length (x'' :: xs'')) *
              ((digit_base_z - 1) * (digit_base_z - 1)) <=
              Z.of_nat (S (List.length (x'' :: xs''))) *
              (digit_base_z - 1) * (digit_base_z - 1))%Z.
           replace
             (Z.of_nat (S (List.length (x'' :: xs''))))
             with (1 + Z.of_nat (List.length (x'' :: xs'')))%Z by lia.
           replace
             ((1 + Z.of_nat (List.length (x'' :: xs''))) *
              (digit_base_z - 1) * (digit_base_z - 1))
             with
             ((1 + Z.of_nat (List.length (x'' :: xs''))) *
              ((digit_base_z - 1) * (digit_base_z - 1)))%Z by ring.
           replace
             ((1 + Z.of_nat (List.length (x'' :: xs''))) *
              ((digit_base_z - 1) * (digit_base_z - 1)))
             with
             (((digit_base_z - 1) * (digit_base_z - 1)) +
              Z.of_nat (List.length (x'' :: xs'')) *
              ((digit_base_z - 1) * (digit_base_z - 1)))%Z by ring.
           apply Z.le_refl.
Qed.

Lemma coeff_bound_lt_crt_modulus :
  (Z.of_nat (Nat.pow 2 23) * (digit_base_z - 1) * (digit_base_z - 1) < crt_modulus_z)%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma bigint_digits_coeff_bound_le_pow23 :
  forall a b,
    Nat.leb (mul_total_log a b) supported_max_log = true ->
    (Z.of_nat (List.length (bigint_digits_z a)) * (digit_base_z - 1) * (digit_base_z - 1) <=
     Z.of_nat (Nat.pow 2 23) * (digit_base_z - 1) * (digit_base_z - 1))%Z.
Proof.
  intros a b Hlog.
  assert (Hfac_nonneg :
    (0 <= (digit_base_z - 1) * (digit_base_z - 1))%Z).
  {
    apply Z.mul_nonneg_nonneg; cbv [digit_base_z]; lia.
  }
  assert (Hlen_le :
    (Z.of_nat (List.length (bigint_digits_z a)) <= Z.of_nat (Nat.pow 2 23))%Z).
  {
    apply Nat2Z.inj_le.
    rewrite bigint_digits_z_length.
    unfold mul_needed_digits.
    pose proof (mul_needed_digits_le_pow23 a b Hlog) as Hdigits.
    assert (Hmul : (8 * List.length a <= 8 * (List.length a + List.length b))%nat).
    {
      nia.
    }
    eapply Nat.le_trans; [exact Hmul|exact Hdigits].
  }
  rewrite <- !Z.mul_assoc.
  apply Z.mul_le_mono_nonneg_r; [exact Hfac_nonneg|exact Hlen_le].
Qed.

Lemma convolution_coeff_crt_range :
  forall a b i,
    canonical_bigint a ->
    canonical_bigint b ->
    a <> [] ->
    Nat.leb (mul_total_log a b) supported_max_log = true ->
    (0 <= convolution_coeff (bigint_digits_z a) (bigint_digits_z b) i < crt_modulus_z)%Z.
Proof.
  intros a b i Ha Hb Hna Hlog.
  pose proof (convolution_coeff_range
    (bigint_digits_z a) (bigint_digits_z b) i
    (bigint_digits_z_nonempty a Hna)
    (canonical_bigint_digits_z_range a Ha)
    (canonical_bigint_digits_z_range b Hb)) as Hrange.
  destruct Hrange as [H0 H1].
  split.
  - exact H0.
  - eapply Z.le_lt_trans; [exact H1|].
    eapply Z.le_lt_trans.
    + apply (bigint_digits_coeff_bound_le_pow23 a b).
      exact Hlog.
    + exact coeff_bound_lt_crt_modulus.
Qed.

Lemma convolution_digits_crt_range :
  forall a b,
    canonical_bigint a ->
    canonical_bigint b ->
    a <> [] ->
    Nat.leb (mul_total_log a b) supported_max_log = true ->
    Forall (fun z => (0 <= z < crt_modulus_z)%Z)
      (convolution_digits (bigint_digits_z a) (bigint_digits_z b)).
Proof.
  intros a b Ha Hb Hna Hlog.
  apply Forall_forall.
  intros z Hz.
  apply In_nth with (d := 0%Z) in Hz.
  destruct Hz as [i [Hi Hnth]].
  rewrite <- Hnth.
  rewrite nth_convolution_digits.
  apply convolution_coeff_crt_range; assumption.
Qed.

Lemma repeat_zero_crt_range :
  forall n,
    Forall (fun z => (0 <= z < crt_modulus_z)%Z) (repeat 0 n).
Proof.
  induction n as [|n IH].
  - constructor.
  - constructor.
    + assert (Hpos : (0 < crt_modulus_z)%Z).
      {
        vm_compute.
        reflexivity.
      }
      lia.
    + exact IH.
Qed.
