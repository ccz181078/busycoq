From Coq Require Import Uint63 ZArith NArith Lia Psatz Bool Lists.List.
Require Import BigInt.BigIntMul BigInt.BigIntMulProof BigInt.BigIntMulTests
  BigInt.BigIntMulCanonical BigInt.BigIntMulCompose BigInt.BigIntMulCorrect
  BigInt.BigIntMulOpsProof BigInt.BigIntMulNormalize.

Import ListNotations.
Local Open Scope Z_scope.

Lemma canonical_digit_low_mask :
  forall bits d,
    (0 < bits < digit_shift_nat)%nat ->
    canonical_digit d ->
    canonical_digit
      (Uint63.land d
         (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)).
Proof.
  intros bits d Hbits Hd.
  assert (Hzero : (0 <= Uint63.to_Z zero_digit < 2 ^ Z.of_nat bits)%Z).
  {
    rewrite zero_digit_to_Z.
    split.
    - lia.
    - apply Z.pow_pos_nonneg; lia.
  }
  pose proof
    (shift_right_digit_small_correct bits zero_digit d
      (Uint63.lor
         (Uint63.lsr d (Uint63.of_Z (Z.of_nat bits)))
         (Uint63.lsl zero_digit
            (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))))
      (Uint63.land d
         (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one))
      Hbits Hd Hzero eq_refl) as [_ [Hcan [_ _]]].
  exact Hcan.
Defined.

Lemma low_mask_bound :
  forall bits d,
    (0 < bits < digit_shift_nat)%nat ->
    canonical_digit d ->
    (0 <=
      Uint63.to_Z
        (Uint63.land d
           (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)) <
     2 ^ Z.of_nat bits)%Z.
Proof.
  intros bits d Hbits Hd.
  assert (Hzero : (0 <= Uint63.to_Z zero_digit < 2 ^ Z.of_nat bits)%Z).
  {
    rewrite zero_digit_to_Z.
    split.
    - lia.
    - apply Z.pow_pos_nonneg; lia.
  }
  pose proof
    (shift_right_digit_small_correct bits zero_digit d
      (Uint63.lor
         (Uint63.lsr d (Uint63.of_Z (Z.of_nat bits)))
         (Uint63.lsl zero_digit
            (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))))
      (Uint63.land d
         (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one))
      Hbits Hd Hzero eq_refl) as [_ [_ [Hlt _]]].
  split.
  - destruct (canonical_digit_low_mask bits d Hbits Hd); lia.
  - exact Hlt.
Qed.

Lemma normalize_coeff_step_digit_canonical :
  forall idx carry arr digit carry',
    normalize_coeff_step idx carry arr = (digit, carry') ->
    canonical_digit digit.
Proof.
  intros idx carry arr digit carry' Hstep.
  unfold normalize_coeff_step in Hstep.
  inversion Hstep; subst; clear Hstep.
  unfold canonical_digit.
  rewrite Uint63.land_spec'.
  rewrite digit_mask_to_Z.
  rewrite digit_base_z_pow2.
  replace (2 ^ Z.of_nat digit_shift_nat - 1)%Z with (Z.ones (Z.of_nat digit_shift_nat)).
  2:{
    rewrite Z.ones_equiv.
    reflexivity.
  }
  rewrite Z.land_ones by lia.
  split.
  - apply Z.mod_pos_bound.
    apply Z.pow_pos_nonneg; lia.
  - apply Z.mod_pos_bound.
    apply Z.pow_pos_nonneg; lia.
Qed.

Lemma normalize_coeff_block_canonical :
  forall idx carry arr block carry',
    normalize_coeff_block idx carry arr = (block, carry') ->
    canonical_limb8 block.
Proof.
  intros idx carry arr block carry' Hblock.
  unfold normalize_coeff_block in Hblock.
  destruct (normalize_coeff_step idx carry arr) as [d0 carry0] eqn:H0.
  destruct (normalize_coeff_step (Uint63.add idx u63_one) carry0 arr) as [d1 carry1] eqn:H1.
  destruct (normalize_coeff_step (Uint63.add idx (Uint63.of_Z 2)) carry1 arr) as [d2 carry2] eqn:H2.
  destruct (normalize_coeff_step (Uint63.add idx u63_three) carry2 arr) as [d3 carry3] eqn:H3.
  destruct (normalize_coeff_step (Uint63.add idx (Uint63.of_Z 4)) carry3 arr) as [d4 carry4] eqn:H4.
  destruct (normalize_coeff_step (Uint63.add idx (Uint63.of_Z 5)) carry4 arr) as [d5 carry5] eqn:H5.
  destruct (normalize_coeff_step (Uint63.add idx (Uint63.of_Z 6)) carry5 arr) as [d6 carry6] eqn:H6.
  destruct (normalize_coeff_step (Uint63.add idx u63_seven) carry6 arr) as [d7 carry7] eqn:H7.
  inversion Hblock; subst; clear Hblock.
  unfold canonical_limb8.
  repeat split;
    eapply normalize_coeff_step_digit_canonical;
    eauto.
Qed.

Lemma normalize_coeff_array_to_bigint_aux_canonical :
  forall fuel idx carry arr,
    canonical_bigint (normalize_coeff_array_to_bigint_aux fuel idx carry arr).
Proof.
  induction fuel as [|fuel IH]; intros idx carry arr.
  - simpl. constructor.
  - unfold normalize_coeff_array_to_bigint_aux at 1.
    fold normalize_coeff_array_to_bigint_aux.
    destruct (normalize_coeff_block idx carry arr) as [block carry'] eqn:Hblock.
    destruct (normalize_coeff_array_to_bigint_aux fuel (Uint63.add idx u63_eight) carry' arr)
      as [|r rs] eqn:Hrest.
    + destruct (limb8_eqb block zero_limb8) eqn:Hzero.
      * constructor.
      * constructor.
        -- eapply normalize_coeff_block_canonical.
           exact Hblock.
        -- constructor.
    + constructor.
      * eapply normalize_coeff_block_canonical.
        exact Hblock.
      * rewrite <- Hrest.
        apply IH.
Qed.

Lemma normalize_coeff_array_to_bigint_canonical :
  forall fuel arr,
    canonical_bigint (normalize_coeff_array_to_bigint fuel arr).
Proof.
  intros fuel arr.
  unfold normalize_coeff_array_to_bigint.
  apply normalize_coeff_array_to_bigint_aux_canonical.
Qed.

Lemma mul_bigint_some_canonical :
  forall a b c,
    canonical_bigint a ->
    canonical_bigint b ->
    mul_bigint a b = Some c ->
    canonical_bigint c.
Proof.
  intros a b c Ha Hb Hmul.
  destruct a as [|a0 a'].
  - destruct b as [|b0 b']; simpl in Hmul.
    + inversion Hmul; subst. constructor.
    + inversion Hmul; subst. constructor.
  - destruct b as [|b0 b'].
    + simpl in Hmul.
      inversion Hmul; subst. constructor.
    + destruct
        (andb (Nat.leb (mul_total_log (a0 :: a') (b0 :: b')) supported_max_log)
           (Nat.leb (mul_needed_digits (a0 :: a') (b0 :: b')) coeff_array_max_digits))
        eqn:Hguard.
      * cbv [mul_bigint mul_total_log mul_block_log mul_needed_digits mul_needed_blocks] in Hmul.
        cbv [mul_total_log mul_block_log mul_needed_digits mul_needed_blocks] in Hguard.
        rewrite Hguard in Hmul.
        simpl in Hmul.
        inversion Hmul; subst; clear Hmul.
        apply normalize_coeff_array_to_bigint_canonical.
      * cbv [mul_bigint mul_total_log mul_block_log mul_needed_digits mul_needed_blocks] in Hmul.
        cbv [mul_total_log mul_block_log mul_needed_digits mul_needed_blocks] in Hguard.
        rewrite Hguard in Hmul.
        simpl in Hmul.
        discriminate Hmul.
Qed.

Lemma bigint_as_digit_canonical :
  forall x m,
    canonical_bigint x ->
    bigint_as_digit x = Some m ->
    canonical_digit m.
Proof.
  intros x m Hx Hdigit.
  destruct x as [|b bs].
  - simpl in Hdigit.
    inversion Hdigit; subst.
    apply canonical_zero_digit.
  - destruct bs as [|b' bs'].
    + simpl in Hdigit.
      destruct (limb8_high_zero b) eqn:Hhigh; inversion Hdigit; subst; clear Hdigit.
      inversion Hx as [|b0 bs0 Hb Hrest]; subst.
      destruct Hb as [Hd0 _].
      exact Hd0.
    + simpl in Hdigit.
      discriminate Hdigit.
Qed.

Lemma bigint_mul_by_bigint_add_bigint_some :
  forall x factor y z,
    canonical_bigint x ->
    canonical_bigint factor ->
    canonical_bigint y ->
    bigint_mul_by_bigint_add_bigint x factor y = Some z ->
    canonical_bigint z /\
    bigint_to_N z = (bigint_to_N x * bigint_to_N factor + bigint_to_N y)%N.
Proof.
  intros x factor y z Hx Hfactor Hy Hsome.
  unfold bigint_mul_by_bigint_add_bigint in Hsome.
  destruct x as [|x0 xs].
  - inversion Hsome; subst; clear Hsome.
    split.
    + exact Hy.
    + simpl. reflexivity.
  - destruct (bigint_as_digit factor) as [m|] eqn:Hdigit.
    + inversion Hsome; subst; clear Hsome.
      pose proof (bigint_as_digit_canonical factor m Hfactor Hdigit) as Hm.
      destruct (bigint_mul_digit_correct m (x0 :: xs) Hm Hx) as [Hmul_can _].
      destruct (bigint_add_correct (bigint_mul_digit m (x0 :: xs)) y Hmul_can Hy)
        as [Hz_can _].
      split.
      * exact Hz_can.
      * rewrite (bigint_add_to_N (bigint_mul_digit m (x0 :: xs)) y Hmul_can Hy).
        rewrite (bigint_mul_digit_to_N m (x0 :: xs) Hm Hx).
        assert (HfactorN : bigint_to_N factor = Z.to_N (Uint63.to_Z m)).
        {
          apply N2Z.inj.
          rewrite bigint_to_N_value by exact Hfactor.
          rewrite Z2N.id by (destruct Hm; lia).
          apply bigint_as_digit_correct; assumption.
        }
        rewrite HfactorN.
        rewrite N.mul_comm.
        reflexivity.
    + destruct (mul_bigint (x0 :: xs) factor) as [p|] eqn:Hmul.
      * inversion Hsome; subst; clear Hsome.
        pose proof (mul_bigint_some_canonical (x0 :: xs) factor p Hx Hfactor Hmul)
          as Hp.
        destruct (bigint_add_correct p y Hp Hy) as [Hz_can _].
        split.
        -- exact Hz_can.
        -- rewrite (bigint_add_to_N p y Hp Hy).
           assert (HmulN : bigint_to_N p = (bigint_to_N (x0 :: xs) * bigint_to_N factor)%N).
           {
             apply N2Z.inj.
             rewrite bigint_to_N_value by exact Hp.
             rewrite N2Z.inj_mul.
             rewrite bigint_to_N_value by exact Hx.
             rewrite bigint_to_N_value by exact Hfactor.
             apply mul_bigint_correct; assumption.
           }
           rewrite HmulN.
           reflexivity.
	      * discriminate Hsome.
Qed.

Lemma bigint_mul_by_bigint_add_bigint_nonempty :
  forall b bs factor y,
    bigint_mul_by_bigint_add_bigint (b :: bs) factor y =
      match bigint_as_digit factor with
      | Some m => Some (bigint_add (bigint_mul_digit m (b :: bs)) y)
      | None =>
          match mul_bigint (b :: bs) factor with
          | Some p => Some (bigint_add p y)
          | None => None
          end
      end.
Proof.
  reflexivity.
Qed.

Lemma mul_bigint_nonempty :
  forall b bs p,
    mul_bigint (b :: bs) p =
      match p with
      | [] => Some []
      | _ :: _ =>
          let needed_blocks := (S (List.length bs) + List.length p)%nat in
          let needed_digits := (8 * needed_blocks)%nat in
          let k := block_log needed_blocks in
          let total_log := transform_log_of_block_log k in
          if andb (Nat.leb total_log supported_max_log)
                  (Nat.leb needed_digits coeff_array_max_digits) then
            let built469a := build_tree469 k (b :: bs) in
            let built469b := build_tree469 k p in
            let built181a := build_tree181 k (b :: bs) in
            let built181b := build_tree181 k p in
            let conv469 := Prime469Ops.convolution_blocks k built469a built469b in
            let conv181 := Prime181Ops.convolution_blocks k built181a built181b in
            let coeffs :=
              coeff_array_from_packed_trees k (coeff_array_make needed_digits)
                zero_digit u63_one conv469 conv181 in
            Some (normalize_coeff_array_to_bigint (S needed_blocks) coeffs)
          else None
      end.
Proof.
  reflexivity.
Qed.

Lemma shift_right_bigint_small_aux_canonical :
  forall bits carry rev_blocks acc,
    (0 < bits < digit_shift_nat)%nat ->
    canonical_digit carry ->
    (0 <= Uint63.to_Z carry < 2 ^ Z.of_nat bits)%Z ->
    canonical_bigint rev_blocks ->
    canonical_bigint acc ->
    canonical_bigint
      (shift_right_bigint_small_aux
         (Uint63.of_Z (Z.of_nat bits))
         (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
         (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
         carry rev_blocks acc).
Proof.
  intros bits carry rev_blocks.
  revert carry.
  induction rev_blocks as [|b bs IH]; intros carry acc Hbits Hcarry Hcarry_range Hrev Hacc.
  - simpl. exact Hacc.
  - simpl.
    inversion Hrev as [|b' bs' Hb Hbs]; subst.
    destruct (shift_right_limb8_small
        (Uint63.of_Z (Z.of_nat bits))
        (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat bits))) u63_one)
        (Uint63.sub digit_shift (Uint63.of_Z (Z.of_nat bits)))
        carry b) as [block carry'] eqn:Hshift.
    pose proof
      (shift_right_limb8_small_correct bits carry b block carry'
         Hbits Hb Hcarry_range Hshift) as [Hblock [Hcarry' [Hcarry_range' _]]].
    apply IH.
    + exact Hbits.
    + exact Hcarry'.
    + split.
      * destruct Hcarry'; lia.
      * exact Hcarry_range'.
    + exact Hbs.
    + constructor.
      * exact Hblock.
      * exact Hacc.
Qed.

Lemma shift_right_bigint_small_canonical :
  forall bits x,
    (0 < bits < digit_shift_nat)%nat ->
    canonical_bigint x ->
    canonical_bigint (shift_right_bigint_small bits x).
Proof.
  intros bits x Hbits Hx.
  unfold shift_right_bigint_small.
  apply trim_bigint_canonical.
  apply shift_right_bigint_small_aux_canonical.
  - exact Hbits.
  - apply canonical_zero_digit.
  - rewrite zero_digit_to_Z.
    split.
    + lia.
    + apply Z.pow_pos_nonneg; lia.
  - apply Forall_rev.
    exact Hx.
  - constructor.
Qed.

Lemma bigint_divmod_pow2_canonical :
  forall n x,
    canonical_bigint x ->
    canonical_bigint (fst (bigint_divmod_pow2 n x)) /\
    canonical_bigint (snd (bigint_divmod_pow2 n x)).
Proof.
  intros n x Hx.
  unfold bigint_divmod_pow2.
  set (whole_digits := Nat.div n digit_shift_nat).
  set (rem_bits := Nat.modulo n digit_shift_nat).
  assert (Hrem_lt : (rem_bits < digit_shift_nat)%nat).
  {
    subst rem_bits.
    apply Nat.mod_upper_bound.
    cbv [digit_shift_nat].
    discriminate.
  }
  destruct (Nat.leb (8 * List.length x)%nat whole_digits) eqn:Hsmall.
  - split.
    + constructor.
    + exact Hx.
  - destruct (bigint_split_whole_digits whole_digits x) as [high_digits low_digits] eqn:Hsplit.
    pose proof (bigint_split_whole_digits_canonical whole_digits x Hx) as Hsplit_can.
    rewrite Hsplit in Hsplit_can.
    destruct Hsplit_can as [Hhigh_can Hlow_can].
    destruct rem_bits as [|rem_bits].
    + simpl.
      exact (conj Hhigh_can Hlow_can).
    + simpl.
      split.
      * apply shift_right_bigint_small_canonical.
        split; [lia|exact Hrem_lt].
        exact Hhigh_can.
      * apply trim_bigint_canonical.
        apply bigint_append_digit_canonical.
        -- exact Hlow_can.
        -- destruct high_digits as [|b bs].
	           ++ apply canonical_zero_digit.
	           ++ inversion Hhigh_can as [|b' bs' Hb _]; subst.
	              destruct Hb as [Hb0 _].
	              exact (canonical_digit_low_mask (S rem_bits) (d0 b)
	                (conj (Nat.lt_0_succ rem_bits) Hrem_lt) Hb0).
Qed.

Lemma bigint_divmod_pow2_bound :
  forall n x,
    canonical_bigint x ->
    (0 <= bigint_value (snd (bigint_divmod_pow2 n x)) < 2 ^ Z.of_nat n)%Z.
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
    destruct (bigint_value_range x Hx) as [H0 Hlt].
    split.
    + exact H0.
	    + eapply Z.lt_le_trans.
	      * exact Hlt.
	      * eapply Z.le_trans.
	        -- rewrite digit_base8_pow_eq_digit_base_pow.
	           apply Z.pow_le_mono_r.
	           ++ cbv [digit_base_z].
	              lia.
	           ++ apply Nat2Z.inj_le.
	              exact Hsmall.
	        -- replace (digit_base_z ^ Z.of_nat whole_digits)
	             with (digit_base_z ^ Z.of_nat whole_digits * 1)%Z by ring.
		           rewrite <- Hpow2.
		           apply Z.mul_le_mono_nonneg_l.
	           ++ assert (Hbase_nonneg : (0 <= digit_base_z ^ Z.of_nat whole_digits)%Z).
	              { apply Z.pow_nonneg. cbv [digit_base_z]. lia. }
	              exact Hbase_nonneg.
		           ++ assert (Hpow1 : (1 <= 2 ^ Z.of_nat rem_bits)%Z).
		              {
		                replace 1%Z with (2 ^ 0)%Z by reflexivity.
		                apply Z.pow_le_mono_r; lia.
		              }
		              exact Hpow1.
  - destruct (bigint_split_whole_digits whole_digits x) as [high_digits low_digits] eqn:Hsplit.
    pose proof (bigint_split_whole_digits_canonical whole_digits x Hx) as Hsplit_can.
    rewrite Hsplit in Hsplit_can.
    destruct Hsplit_can as [Hhigh_can Hlow_can].
    pose proof (bigint_split_whole_digits_low_bound whole_digits x Hx) as Hlow_bound.
    rewrite Hsplit in Hlow_bound.
    simpl in Hlow_bound.
	    destruct Hlow_bound as [Hlow0 Hlow1].
	    destruct rem_bits as [|rem_bits].
	    + simpl.
	      split.
	      * exact Hlow0.
	      * rewrite <- Hpow2.
	        simpl.
	        rewrite Z.mul_1_r.
	        exact Hlow1.
    + simpl.
      set (extra_low :=
        match high_digits with
        | [] => zero_digit
        | b :: _ =>
            Uint63.land (d0 b)
              (Uint63.sub (Uint63.lsl u63_one (Uint63.of_Z (Z.of_nat (S rem_bits)))) u63_one)
        end).
      assert (Hextra_can : canonical_digit extra_low).
      {
        subst extra_low.
        destruct high_digits as [|b bs].
        - apply canonical_zero_digit.
	        - inversion Hhigh_can as [|b' bs' Hb _]; subst.
	          destruct Hb as [Hb0 _].
	          apply canonical_digit_low_mask.
	          split; [lia|exact Hrem_lt].
	          exact Hb0.
      }
	      assert (Hextra_bound :
	        (0 <= Uint63.to_Z extra_low < 2 ^ Z.of_nat (S rem_bits))%Z).
      {
        subst extra_low.
        destruct high_digits as [|b bs].
        - rewrite zero_digit_to_Z.
          split.
          + lia.
          + apply Z.pow_pos_nonneg; lia.
	        - inversion Hhigh_can as [|b' bs' Hb _]; subst.
	          destruct Hb as [Hb0 _].
	          apply low_mask_bound.
	          split; [lia|exact Hrem_lt].
	          exact Hb0.
	      }
	      pose proof
	        (bigint_append_digit_value whole_digits low_digits extra_low
	           Hlow_can Hextra_can Hlow1) as Hrem_value.
	      change
	        (0 <= bigint_value (trim_bigint (bigint_append_digit whole_digits low_digits extra_low)) <
	         2 ^ Z.of_nat n)%Z.
	      rewrite Hrem_value.
      destruct Hextra_bound as [Hextra0 Hextra1].
      split.
	      * apply Z.add_nonneg_nonneg.
	        -- exact Hlow0.
	        -- apply Z.mul_nonneg_nonneg.
	           ++ apply Z.pow_nonneg. cbv [digit_base_z]. lia.
	           ++ exact Hextra0.
      * assert (Hlt' :
          (bigint_value low_digits +
             digit_base_z ^ Z.of_nat whole_digits * Uint63.to_Z extra_low <
           digit_base_z ^ Z.of_nat whole_digits +
             digit_base_z ^ Z.of_nat whole_digits *
               (2 ^ Z.of_nat (S rem_bits) - 1))%Z).
        { nia. }
        eapply Z.lt_le_trans.
        -- exact Hlt'.
        -- replace
             (digit_base_z ^ Z.of_nat whole_digits +
              digit_base_z ^ Z.of_nat whole_digits *
                (2 ^ Z.of_nat (S rem_bits) - 1))
             with
             (digit_base_z ^ Z.of_nat whole_digits * 2 ^ Z.of_nat (S rem_bits))%Z
             by ring.
           rewrite <- Hpow2.
           reflexivity.
Qed.

Lemma bigint_divmod_pow2_to_N :
  forall n x,
    canonical_bigint x ->
    let qr := bigint_divmod_pow2 n x in
    (bigint_to_N x =
       (N.shiftl (bigint_to_N (fst qr)) (N.of_nat n) + bigint_to_N (snd qr))%N) /\
    (bigint_to_N (snd qr) < (2 ^ N.of_nat n))%N.
	Proof.
	  intros n x Hx.
	  remember (bigint_divmod_pow2 n x) as qr eqn:Hqr.
	  destruct qr as [q r].
	  simpl.
	  pose proof (bigint_divmod_pow2_canonical n x Hx) as [Hq Hr].
	  pose proof (bigint_divmod_pow2_value n x Hx) as Hval.
	  pose proof (bigint_divmod_pow2_bound n x Hx) as Hbound.
	  rewrite <- Hqr in Hq, Hr, Hval, Hbound.
	  simpl in Hq, Hr, Hval, Hbound.
	  split.
  - apply N2Z.inj.
    rewrite N2Z.inj_add.
	    rewrite N.shiftl_mul_pow2.
	    rewrite N2Z.inj_mul.
	    rewrite !bigint_to_N_value by assumption.
	    rewrite N2Z.inj_pow.
	    rewrite nat_N_Z.
	    change
	      (bigint_value x =
	         bigint_value q * (Z.of_N 2 ^ Z.of_nat n) + bigint_value r)%Z.
	    replace (Z.of_N 2) with 2%Z by reflexivity.
	    nia.
	  - apply N2Z.inj_lt.
	    rewrite N2Z.inj_pow.
	    rewrite bigint_to_N_value by exact Hr.
	    rewrite nat_N_Z.
	    replace (Z.of_N 2) with 2%Z by reflexivity.
	    exact (proj2 Hbound).
Qed.

Definition pow9_cache_ok (cache : list bigint) : Prop :=
  forall i p,
    nth_error cache i = Some p ->
    canonical_bigint p /\ bigint_to_N p = pow9_pow2_N i.

Lemma bigint_of_N_spec :
  forall n,
    canonical_bigint (bigint_of_N n) /\ bigint_to_N (bigint_of_N n) = n.
Proof.
  intro n.
  split.
  - apply bigint_of_N_canonical.
  - apply bigint_to_N_bigint_of_N.
Qed.

Lemma pow9_cache_ok_nil :
  pow9_cache_ok [].
Proof.
  intros i p Hnth.
  destruct i; simpl in Hnth; discriminate.
Qed.

Lemma pow9_cache_ok_singleton9 :
  pow9_cache_ok [bigint_9].
Proof.
  intros i p Hnth.
  destruct i as [|i].
  - simpl in Hnth.
    inversion Hnth; subst; clear Hnth.
    unfold bigint_9.
    split.
    + apply bigint_of_N_canonical.
    + apply bigint_to_N_bigint_of_N.
	  - simpl in Hnth.
	    destruct i; simpl in Hnth; discriminate.
Qed.

Lemma rev_head_last_nth_error :
  forall (A : Type) (xs : list A) (x : A) (ys : list A),
    rev xs = x :: ys ->
    nth_error xs (List.length xs - 1) = Some x.
Proof.
  intros A xs x ys Hrev.
  apply (f_equal (@rev A)) in Hrev.
  rewrite rev_involutive in Hrev.
  simpl in Hrev.
	  rewrite Hrev.
	  rewrite nth_error_app2.
	  - replace
	      (List.length (rev ys ++ [x]) - 1 - List.length (rev ys))%nat
	      with 0%nat by (rewrite length_app, length_rev; simpl; lia).
	    simpl.
	    reflexivity.
	  - rewrite length_app, length_rev; simpl.
	    lia.
Qed.

Lemma pow9_cache_ok_last :
  forall cache p rest,
    pow9_cache_ok cache ->
    rev cache = p :: rest ->
    canonical_bigint p /\ bigint_to_N p = pow9_pow2_N (List.length cache - 1).
Proof.
  intros cache p rest Hok Hrev.
  apply Hok.
  apply rev_head_last_nth_error with (ys := rest).
  exact Hrev.
Qed.

Lemma pow9_cache_ok_append_square :
  forall cache p rest q,
    pow9_cache_ok cache ->
    rev cache = p :: rest ->
    mul_bigint p p = Some q ->
    pow9_cache_ok (cache ++ [q]).
Proof.
  intros cache p rest q Hok Hrev Hmul i z Hnth.
  destruct (Nat.lt_ge_cases i (List.length cache)) as [Hlt|Hge].
  - rewrite nth_error_app1 in Hnth by exact Hlt.
    apply Hok.
    exact Hnth.
  - destruct (Nat.eq_dec i (List.length cache)) as [Heq|Hgt].
	    + subst i.
	      rewrite nth_error_app2 in Hnth by lia.
	      replace (List.length cache - List.length cache)%nat with 0%nat in Hnth by lia.
	      replace z with q in * by (inversion Hnth; reflexivity).
	      clear Hnth.
	      pose proof (pow9_cache_ok_last cache p rest Hok Hrev) as [Hp_can Hp_val].
      pose proof (mul_bigint_some_canonical p p q Hp_can Hp_can Hmul) as Hq_can.
      split.
      * exact Hq_can.
      * assert (Hq_val : bigint_to_N q = (bigint_to_N p * bigint_to_N p)%N).
        {
          apply N2Z.inj.
          rewrite bigint_to_N_value by exact Hq_can.
          rewrite N2Z.inj_mul.
          rewrite !bigint_to_N_value by exact Hp_can.
          apply mul_bigint_correct; assumption.
        }
        rewrite Hq_val, Hp_val.
        assert (Hlen : List.length cache = S (List.length cache - 1)).
        {
          destruct cache as [|c cs].
          - simpl in Hrev. discriminate.
          - simpl. lia.
	        }
	        rewrite Hlen.
	        simpl.
	        rewrite Nat.sub_0_r.
	        reflexivity.
	    + rewrite nth_error_app2 in Hnth by lia.
	      assert (Hoff : (List.length cache < i)%nat) by lia.
	      replace (i - List.length cache)%nat with (S (i - S (List.length cache))) in Hnth by lia.
	      destruct (i - S (List.length cache))%nat; simpl in Hnth; discriminate.
Qed.

Lemma extend_pow9_cache_ok_nonempty :
  forall fuel target cache cache',
    cache <> [] ->
    pow9_cache_ok cache ->
    extend_pow9_cache fuel target cache = Some cache' ->
    pow9_cache_ok cache'.
Proof.
  induction fuel as [|fuel IH]; intros target cache cache' Hnz Hok Hext.
  - destruct cache as [|b bs].
    + contradiction.
    + unfold extend_pow9_cache at 1 in Hext.
      fold extend_pow9_cache in Hext.
      destruct (Nat.ltb target (List.length (b :: bs))) eqn:Hlt in Hext.
      * simpl in Hext.
        inversion Hext; subst; clear Hext.
        exact Hok.
      * simpl in Hext.
        discriminate Hext.
  - destruct cache as [|b bs].
    + contradiction.
    + unfold extend_pow9_cache at 1 in Hext.
      fold extend_pow9_cache in Hext.
      destruct (Nat.ltb target (List.length (b :: bs))) eqn:Hlt in Hext.
      * simpl in Hext.
        inversion Hext; subst; clear Hext.
        exact Hok.
      * simpl in Hext.
        destruct (rev (b :: bs)) as [|p rest] eqn:Hrev.
        -- apply (f_equal (@rev bigint)) in Hrev.
           rewrite rev_involutive in Hrev.
           discriminate.
        -- destruct (mul_bigint p p) as [q|] eqn:Hmul.
           ++ simpl in Hrev.
              rewrite Hrev in Hext.
              simpl in Hext.
              rewrite Hmul in Hext.
              simpl in Hext.
              change (extend_pow9_cache fuel target ((b :: bs) ++ [q]) = Some cache') in Hext.
              eapply IH; [| | exact Hext].
              ** intro Hnil.
                 discriminate Hnil.
              ** eapply pow9_cache_ok_append_square; eauto.
           ++ simpl in Hrev.
              rewrite Hrev in Hext.
              simpl in Hext.
              rewrite Hmul in Hext.
              simpl in Hext.
              discriminate Hext.
Qed.

Lemma pow9_cache_ok_bigint9_square :
  pow9_cache_ok (bigint_9 :: [bigint_of_N 81%N]).
Proof.
  change (pow9_cache_ok ([bigint_9] ++ [bigint_of_N 81%N])).
  apply pow9_cache_ok_append_square with (p := bigint_9) (rest := []).
  - apply pow9_cache_ok_singleton9.
  - reflexivity.
  - native_compute.
    reflexivity.
Qed.

Lemma ensure_pow9_cache_ok_nonempty :
  forall target cache cache',
    cache <> [] ->
    pow9_cache_ok cache ->
    ensure_pow9_cache target cache = Some cache' ->
    pow9_cache_ok cache'.
Proof.
  intros target cache cache' Hnz Hok Hensure.
  unfold ensure_pow9_cache in Hensure.
  eapply extend_pow9_cache_ok_nonempty.
  - exact Hnz.
  - exact Hok.
  - exact Hensure.
Qed.

Lemma ensure_pow9_cache_ok_empty_positive :
  forall target cache',
    (0 < target)%nat ->
    ensure_pow9_cache target [] = Some cache' ->
    pow9_cache_ok cache'.
Proof.
  intros target cache' Htarget Hensure.
  unfold ensure_pow9_cache in Hensure.
  unfold extend_pow9_cache at 1 in Hensure.
  fold extend_pow9_cache in Hensure.
  change (Nat.ltb target 0) with false in Hensure.
  cbn [List.length] in Hensure.
  assert (Hlt1 : Nat.ltb target 1 = false).
  {
    destruct target as [|[|target']]; simpl; try reflexivity; lia.
  }
  rewrite Hlt1 in Hensure.
  cbn [rev] in Hensure.
  change
    (match mul_bigint bigint_9 bigint_9 with
     | Some q => extend_pow9_cache target target (bigint_9 :: [q])
     | None => None
     end = Some cache') in Hensure.
  change (mul_bigint bigint_9 bigint_9) with (Some (bigint_of_N 81%N)) in Hensure.
  simpl in Hensure.
  eapply extend_pow9_cache_ok_nonempty; [| | exact Hensure].
  - intro Hnil.
    inversion Hnil.
  - apply pow9_cache_ok_bigint9_square.
Qed.

Lemma split_pow4_N_bigint :
  forall d a,
    canonical_bigint a ->
    let qr := bigint_divmod_pow2 (pow4pow2_bits d) a in
    split_pow4_N d (bigint_to_N a) =
      (bigint_to_N (fst qr), bigint_to_N (snd qr)).
Proof.
  intros d a Ha.
  pose proof (bigint_divmod_pow2_to_N (pow4pow2_bits d) a Ha) as [Hdecomp Hbound].
  remember (bigint_divmod_pow2 (pow4pow2_bits d) a) as qr eqn:Hqr.
  destruct qr as [q r].
  simpl in *.
  unfold split_pow4_N.
  simpl.
  apply f_equal2.
	  - rewrite N.shiftr_div_pow2.
	    symmetry.
	    apply N.div_unique with (r := bigint_to_N r).
	    + exact Hbound.
	    + rewrite Hdecomp.
	      rewrite N.shiftl_mul_pow2.
	      rewrite N.mul_comm.
	      reflexivity.
	  - rewrite Hdecomp.
	    change (N.pos (Pos.shiftl 1 (N.of_nat (pow4pow2_bits d))))
	      with (N.shiftl 1%N (N.of_nat (pow4pow2_bits d))).
	    rewrite N.shiftl_1_l.
	    rewrite N.shiftl_mul_pow2.
	    rewrite N.add_comm.
	    rewrite N.Div0.mod_add.
	    apply N.mod_small.
	    exact Hbound.
Qed.

Lemma bigint_9_spec :
  canonical_bigint bigint_9 /\ bigint_to_N bigint_9 = 9%N.
Proof.
  unfold bigint_9.
  apply bigint_of_N_spec.
Qed.

Lemma bigint_11_spec :
  canonical_bigint bigint_11 /\ bigint_to_N bigint_11 = 11%N.
Proof.
  unfold bigint_11.
  apply bigint_of_N_spec.
Qed.

Lemma bigint_12_spec :
  canonical_bigint bigint_12 /\ bigint_to_N bigint_12 = 12%N.
Proof.
  unfold bigint_12.
  apply bigint_of_N_spec.
Qed.

Lemma bigint_15_spec :
  canonical_bigint bigint_15 /\ bigint_to_N bigint_15 = 15%N.
Proof.
  unfold bigint_15.
  apply bigint_of_N_spec.
Qed.

Lemma bigint_16_spec :
  canonical_bigint bigint_16 /\ bigint_to_N bigint_16 = 16%N.
Proof.
  unfold bigint_16.
  apply bigint_of_N_spec.
Qed.

Lemma F_bigint_cached_some_correct_base :
  forall cache0 a c a' c' cache',
    pow9_cache_ok cache0 ->
    canonical_bigint a ->
    F_bigint_cached cache0 (a, c) 0 = Some ((a', c'), cache') ->
    pow9_cache_ok cache' /\
    canonical_bigint a' /\
    F_N (bigint_to_N a, c) 0 = Some (bigint_to_N a', c').
Proof.
  intros cache0 a c a' c' cache' Hok Ha Hf.
  cbn [F_bigint_cached] in Hf.
  destruct (bigint_divmod_pow2 (pow4pow2_bits 0) a) as [a1 a0] eqn:Hdiv.
  pose proof (bigint_divmod_pow2_canonical (pow4pow2_bits 0) a Ha) as Hdiv_can.
  rewrite Hdiv in Hdiv_can.
  destruct Hdiv_can as [Ha1 Ha0].
  pose proof (split_pow4_N_bigint 0 a Ha) as Hsplit.
  rewrite Hdiv in Hsplit.
  simpl in Hsplit.
  destruct bigint_9_spec as [H9_can H9_val].
  destruct bigint_11_spec as [H11_can H11_val].
  destruct bigint_12_spec as [H12_can H12_val].
  destruct bigint_15_spec as [H15_can H15_val].
  destruct bigint_16_spec as [H16_can H16_val].
  set (a0N := bigint_to_N a0) in *.
  destruct (N.ltb c 3)%N eqn:Hc in Hf.
  - discriminate.
  - destruct (N.eqb a0N 0)%N eqn:Ha00 in Hf.
    + destruct (bigint_mul_by_bigint_add_bigint a1 bigint_9 bigint_11) eqn:Hz in Hf.
      * inversion Hf; subst; clear Hf.
        pose proof
          (bigint_mul_by_bigint_add_bigint_some a1 bigint_9 bigint_11 a'
             Ha1 H9_can H11_can Hz) as [Hz_can Hz_val].
        split.
        -- exact Hok.
        -- split.
           ++ exact Hz_can.
           ++ cbn [F_N].
              rewrite Hsplit.
              simpl.
              rewrite Hc, Ha00.
              simpl.
              rewrite Hz_val, H9_val, H11_val.
              reflexivity.
      * discriminate.
    + destruct (N.eqb a0N 1)%N eqn:Ha01 in Hf.
      * destruct (bigint_mul_by_bigint_add_bigint a1 bigint_9 bigint_15) eqn:Hz in Hf.
        -- inversion Hf; subst; clear Hf.
           pose proof
             (bigint_mul_by_bigint_add_bigint_some a1 bigint_9 bigint_15 a'
                Ha1 H9_can H15_can Hz) as [Hz_can Hz_val].
           split.
           ++ exact Hok.
           ++ split.
              ** exact Hz_can.
              ** cbn [F_N].
                 rewrite Hsplit.
                 simpl.
                 rewrite Hc, Ha00, Ha01.
                 simpl.
                 rewrite Hz_val, H9_val, H15_val.
                 reflexivity.
        -- discriminate.
      * destruct (N.eqb a0N 2)%N eqn:Ha02 in Hf.
        -- destruct (bigint_mul_by_bigint_add_bigint a1 bigint_9 bigint_12) eqn:Hz in Hf.
           ++ inversion Hf; subst; clear Hf.
              pose proof
                (bigint_mul_by_bigint_add_bigint_some a1 bigint_9 bigint_12 a'
                   Ha1 H9_can H12_can Hz) as [Hz_can Hz_val].
              split.
              ** exact Hok.
              ** split.
                 --- exact Hz_can.
                 --- cbn [F_N].
                     rewrite Hsplit.
                     simpl.
                     rewrite Hc, Ha00, Ha01, Ha02.
                     simpl.
                     rewrite Hz_val, H9_val, H12_val.
                     reflexivity.
           ++ discriminate.
        -- destruct (bigint_mul_by_bigint_add_bigint a1 bigint_9 bigint_16) eqn:Hz in Hf.
           ++ inversion Hf; subst; clear Hf.
              pose proof
                (bigint_mul_by_bigint_add_bigint_some a1 bigint_9 bigint_16 a'
                   Ha1 H9_can H16_can Hz) as [Hz_can Hz_val].
              split.
              ** exact Hok.
              ** split.
                 --- exact Hz_can.
                 --- cbn [F_N].
                     rewrite Hsplit.
                     simpl.
                     rewrite Hc, Ha00, Ha01, Ha02.
                     simpl.
                     rewrite Hz_val, H9_val, H16_val.
                     reflexivity.
           ++ discriminate.
Qed.

Lemma F_bigint_cached_some_correct_step_nil_result :
  forall d a c a0 a0' c1 a0'' c2,
    canonical_bigint a ->
    bigint_divmod_pow2 (pow4pow2_bits (S d)) a = ([], a0) ->
    F_N (bigint_to_N a0, c) d = Some (bigint_to_N a0', c1) ->
    F_N (bigint_to_N a0', c1) d = Some (bigint_to_N a0'', c2) ->
    F_N (bigint_to_N a, c) (S d) = Some (bigint_to_N a0'', c2).
Proof.
  intros d a c a0 a0' c1 a0'' c2 Ha Hdiv HFN1 HFN2.
  pose proof (split_pow4_N_bigint (S d) a Ha) as Hsplit.
  rewrite Hdiv in Hsplit.
  cbn [F_N].
  rewrite Hsplit.
  simpl.
  rewrite HFN1, HFN2.
  simpl.
  reflexivity.
Qed.

Lemma F_bigint_cached_some_correct_step_cons_result :
  forall d a c b bs a0 a0' c1 a0'' c2 p a',
    canonical_bigint a ->
    canonical_bigint (b :: bs) ->
    canonical_bigint p ->
    canonical_bigint a0'' ->
    bigint_divmod_pow2 (pow4pow2_bits (S d)) a = (b :: bs, a0) ->
    F_N (bigint_to_N a0, c) d = Some (bigint_to_N a0', c1) ->
    F_N (bigint_to_N a0', c1) d = Some (bigint_to_N a0'', c2) ->
    bigint_to_N p = pow9_pow2_N (S d) ->
    bigint_mul_by_bigint_add_bigint (b :: bs) p a0'' = Some a' ->
    F_N (bigint_to_N a, c) (S d) = Some (bigint_to_N a', c2).
Proof.
  intros d a c b bs a0 a0' c1 a0'' c2 p a' Ha Ha1 Hp_can Ha0'' Hdiv HFN1 HFN2 Hp_val Hz.
  pose proof
    (bigint_mul_by_bigint_add_bigint_some (b :: bs) p a0'' a'
       Ha1 Hp_can Ha0'' Hz) as [_ Hz_val].
  pose proof (split_pow4_N_bigint (S d) a Ha) as Hsplit.
  rewrite Hdiv in Hsplit.
  cbn [F_N].
  rewrite Hsplit.
  simpl.
  rewrite HFN1, HFN2.
  simpl.
  rewrite Hz_val, Hp_val.
  reflexivity.
Qed.

Lemma F_bigint_cached_some_correct_step_nil :
  forall d cache0 a c a' c' cache' a0 a0' c1 cache1 a0'' c2 cache2,
    canonical_bigint a ->
    bigint_divmod_pow2 (pow4pow2_bits (S d)) a = ([], a0) ->
    F_bigint_cached cache0 (a0, c) d = Some ((a0', c1), cache1) ->
    F_bigint_cached cache1 (a0', c1) d = Some ((a0'', c2), cache2) ->
    pow9_cache_ok cache2 ->
    canonical_bigint a0'' ->
    F_N (bigint_to_N a0, c) d = Some (bigint_to_N a0', c1) ->
    F_N (bigint_to_N a0', c1) d = Some (bigint_to_N a0'', c2) ->
    F_bigint_cached cache0 (a, c) (S d) = Some ((a', c'), cache') ->
    pow9_cache_ok cache' /\
    canonical_bigint a' /\
    F_N (bigint_to_N a, c) (S d) = Some (bigint_to_N a', c').
Proof.
  intros d cache0 a c a' c' cache' a0 a0' c1 cache1 a0'' c2 cache2
    Ha Hdiv Hfirst Hsecond Hok2 Ha0'' HFN1 HFN2 Hf.
  simpl in Hf.
  rewrite Hdiv in Hf.
  rewrite Hfirst in Hf.
  rewrite Hsecond in Hf.
  simpl in Hf.
  inversion Hf; subst; clear Hf.
  split.
  - exact Hok2.
  - split.
    + exact Ha0''.
    + eapply F_bigint_cached_some_correct_step_nil_result.
      * exact Ha.
      * exact Hdiv.
      * exact HFN1.
      * exact HFN2.
Qed.

Definition F_bigint_cached_cons_body
    (d : nat) (cache2 : list bigint) (a1 a0'' : bigint) (c2 : N)
    : option ((bigint * N) * list bigint) :=
  match ensure_pow9_cache (S d) cache2 with
  | Some cache3 =>
      match nth_error cache3 (S d) with
      | Some p =>
          match bigint_mul_by_bigint_add_bigint a1 p a0'' with
          | Some a' => Some ((a', c2), cache3)
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Lemma F_bigint_cached_cons_body_inv :
  forall d cache2 a1 a0'' c2 a' c' cache',
    F_bigint_cached_cons_body d cache2 a1 a0'' c2 = Some ((a', c'), cache') ->
    exists cache3 p,
      ensure_pow9_cache (S d) cache2 = Some cache3 /\
      nth_error cache3 (S d) = Some p /\
      bigint_mul_by_bigint_add_bigint a1 p a0'' = Some a' /\
      cache' = cache3 /\
      c' = c2.
Proof.
  intros d cache2 a1 a0'' c2 a' c' cache' H.
  unfold F_bigint_cached_cons_body in H.
  destruct (ensure_pow9_cache (S d) cache2) as [cache3|] eqn:Hensure.
  2: discriminate.
  destruct (nth_error cache3 (S d)) as [p|] eqn:Hnth.
  2: discriminate.
  destruct (bigint_mul_by_bigint_add_bigint a1 p a0'') as [ax|] eqn:Hz.
  2: discriminate.
  inversion H; subst; clear H.
  exists cache', p.
  repeat split; auto.
Qed.

Lemma F_bigint_cached_step_cons_body_eq :
  forall d cache0 a c b bs a0 a0' c1 cache1 a0'' c2 cache2,
    bigint_divmod_pow2 (pow4pow2_bits (S d)) a = (b :: bs, a0) ->
    F_bigint_cached cache0 (a0, c) d = Some ((a0', c1), cache1) ->
    F_bigint_cached cache1 (a0', c1) d = Some ((a0'', c2), cache2) ->
    F_bigint_cached cache0 (a, c) (S d) =
    F_bigint_cached_cons_body d cache2 (b :: bs) a0'' c2.
Proof.
  intros d cache0 a c b bs a0 a0' c1 cache1 a0'' c2 cache2 Hdiv Hfirst Hsecond.
  simpl.
  rewrite Hdiv.
  rewrite Hfirst.
  rewrite Hsecond.
  reflexivity.
Qed.

Lemma F_bigint_cached_step_cons_inv :
  forall d cache0 a c a' c' cache' b bs a0 a0' c1 cache1 a0'' c2 cache2,
    bigint_divmod_pow2 (pow4pow2_bits (S d)) a = (b :: bs, a0) ->
    F_bigint_cached cache0 (a0, c) d = Some ((a0', c1), cache1) ->
    F_bigint_cached cache1 (a0', c1) d = Some ((a0'', c2), cache2) ->
    F_bigint_cached cache0 (a, c) (S d) = Some ((a', c'), cache') ->
    exists cache3 p,
      ensure_pow9_cache (S d) cache2 = Some cache3 /\
      nth_error cache3 (S d) = Some p /\
      bigint_mul_by_bigint_add_bigint (b :: bs) p a0'' = Some a' /\
      cache' = cache3 /\
      c' = c2.
Proof.
  intros d cache0 a c a' c' cache' b bs a0 a0' c1 cache1 a0'' c2 cache2
    Hdiv Hfirst Hsecond Hf.
  rewrite (F_bigint_cached_step_cons_body_eq d cache0 a c b bs a0 a0' c1 cache1 a0'' c2 cache2
             Hdiv Hfirst Hsecond) in Hf.
  eapply F_bigint_cached_cons_body_inv in Hf.
  exact Hf.
Qed.

Lemma F_bigint_cached_some_correct_step_cons :
  forall d cache0 a c a' c' cache' b bs a0 a0' c1 cache1 a0'' c2 cache2,
    canonical_bigint a ->
    canonical_bigint (b :: bs) ->
    bigint_divmod_pow2 (pow4pow2_bits (S d)) a = (b :: bs, a0) ->
    F_bigint_cached cache0 (a0, c) d = Some ((a0', c1), cache1) ->
    F_bigint_cached cache1 (a0', c1) d = Some ((a0'', c2), cache2) ->
    pow9_cache_ok cache2 ->
    canonical_bigint a0'' ->
    F_N (bigint_to_N a0, c) d = Some (bigint_to_N a0', c1) ->
    F_N (bigint_to_N a0', c1) d = Some (bigint_to_N a0'', c2) ->
    F_bigint_cached cache0 (a, c) (S d) = Some ((a', c'), cache') ->
    pow9_cache_ok cache' /\
    canonical_bigint a' /\
    F_N (bigint_to_N a, c) (S d) = Some (bigint_to_N a', c').
Proof.
  intros d cache0 a c a' c' cache' b bs a0 a0' c1 cache1 a0'' c2 cache2
    Ha Ha1 Hdiv Hfirst Hsecond Hok2 Ha0'' HFN1 HFN2 Hf.
  destruct (F_bigint_cached_step_cons_inv d cache0 a c a' c' cache' b bs a0 a0' c1 cache1 a0'' c2 cache2
              Hdiv Hfirst Hsecond Hf)
    as [cache3 [p [Hensure [Hnth [Hz [Hcache Hc]]]]]].
  subst cache' c'.
  assert (Hok3 : pow9_cache_ok cache3).
  {
    destruct cache2 as [|cblk crest].
    - eapply ensure_pow9_cache_ok_empty_positive.
      + exact (Nat.lt_0_succ d).
      + exact Hensure.
    - eapply ensure_pow9_cache_ok_nonempty; [| | exact Hensure].
      + intro Hnil.
        inversion Hnil.
      + exact Hok2.
  }
  destruct (Hok3 _ _ Hnth) as [Hp_can Hp_val].
  pose proof
    (bigint_mul_by_bigint_add_bigint_some (b :: bs) p a0'' a'
       Ha1 Hp_can Ha0'' Hz) as [Hz_can _].
  split.
  - exact Hok3.
  - split.
    + exact Hz_can.
    + eapply F_bigint_cached_some_correct_step_cons_result.
      * exact Ha.
      * exact Ha1.
      * exact Hp_can.
      * exact Ha0''.
      * exact Hdiv.
      * exact HFN1.
      * exact HFN2.
      * exact Hp_val.
      * exact Hz.
Qed.

Lemma F_bigint_cached_some_correct_step :
  forall d,
    (forall cache0 a c a' c' cache',
        pow9_cache_ok cache0 ->
        canonical_bigint a ->
        F_bigint_cached cache0 (a, c) d = Some ((a', c'), cache') ->
        pow9_cache_ok cache' /\
        canonical_bigint a' /\
        F_N (bigint_to_N a, c) d = Some (bigint_to_N a', c')) ->
    forall cache0 a c a' c' cache',
      pow9_cache_ok cache0 ->
      canonical_bigint a ->
      F_bigint_cached cache0 (a, c) (S d) = Some ((a', c'), cache') ->
      pow9_cache_ok cache' /\
      canonical_bigint a' /\
      F_N (bigint_to_N a, c) (S d) = Some (bigint_to_N a', c').
Proof.
  intros d IH cache0 a c a' c' cache' Hok Ha Hf.
  destruct (bigint_divmod_pow2 (pow4pow2_bits (S d)) a) as [a1 a0] eqn:Hdiv.
  pose proof (bigint_divmod_pow2_canonical (pow4pow2_bits (S d)) a Ha) as Hdiv_can.
  rewrite Hdiv in Hdiv_can.
  destruct Hdiv_can as [Ha1 Ha0].
  pose proof (split_pow4_N_bigint (S d) a Ha) as Hsplit.
  rewrite Hdiv in Hsplit.
  simpl in Hsplit.
  destruct (F_bigint_cached cache0 (a0, c) d) as [[[a0' c1] cache1]|] eqn:Hfirst.
  2: {
    cbn [F_bigint_cached] in Hf.
    rewrite Hdiv in Hf.
    simpl in Hf.
    rewrite Hfirst in Hf.
    simpl in Hf.
    discriminate.
  }
  destruct (IH cache0 a0 c a0' c1 cache1 Hok Ha0 Hfirst)
    as [Hok1 [Ha0' HFN1]].
  destruct (F_bigint_cached cache1 (a0', c1) d) as [[[a0'' c2] cache2]|] eqn:Hsecond.
  2: {
    cbn [F_bigint_cached] in Hf.
    rewrite Hdiv in Hf.
    simpl in Hf.
    rewrite Hfirst in Hf.
    rewrite Hsecond in Hf.
    simpl in Hf.
    discriminate.
  }
  destruct (IH cache1 a0' c1 a0'' c2 cache2 Hok1 Ha0' Hsecond)
    as [Hok2 [Ha0'' HFN2]].
  destruct a1 as [|b bs].
  - eapply F_bigint_cached_some_correct_step_nil.
    + exact Ha.
    + exact Hdiv.
    + exact Hfirst.
    + exact Hsecond.
    + exact Hok2.
    + exact Ha0''.
    + exact HFN1.
    + exact HFN2.
    + exact Hf.
  - eapply F_bigint_cached_some_correct_step_cons.
    + exact Ha.
    + exact Ha1.
    + exact Hdiv.
    + exact Hfirst.
    + exact Hsecond.
    + exact Hok2.
    + exact Ha0''.
    + exact HFN1.
    + exact HFN2.
    + exact Hf.
Qed.

Theorem F_bigint_cached_some_correct :
  forall cache0 a c d a' c' cache',
    pow9_cache_ok cache0 ->
    canonical_bigint a ->
    F_bigint_cached cache0 (a, c) d = Some ((a', c'), cache') ->
    pow9_cache_ok cache' /\
    canonical_bigint a' /\
    F_N (bigint_to_N a, c) d = Some (bigint_to_N a', c').
Proof.
  intros cache0 a c d.
  revert cache0 a c.
  induction d as [|d IH]; intros cache0 a c a' c' cache' Hok Ha Hf.
  - 
    eapply F_bigint_cached_some_correct_base; eauto.
  - 
    eapply (F_bigint_cached_some_correct_step d IH); eauto.
Qed.

Theorem F_bigint_some_equiv_F_N :
  forall a c d a' c',
    canonical_bigint a ->
    F_bigint (a, c) d = Some (a', c') ->
    F_N (bigint_to_N a, c) d = Some (bigint_to_N a', c').
Proof.
  intros a c d a' c' Ha Hf.
  unfold F_bigint in Hf.
  destruct (F_bigint_cached [] (a, c) d) as [[[ares cres] cache']|] eqn:Hcached.
  - destruct (F_bigint_cached_some_correct [] a c d ares cres cache'
                pow9_cache_ok_nil Ha Hcached) as [_ [_ HF]].
    inversion Hf; subst; clear Hf.
    exact HF.
  - discriminate.
Qed.

Local Open Scope nat_scope.

Definition pow4pow2_nat (d : nat) : nat :=
  Nat.pow 4 (Nat.pow 2 d).

Definition pow9pow2_nat (d : nat) : nat :=
  Nat.pow 9 (Nat.pow 2 d).

Definition pair_nat_to_N (ac : nat * nat) : N * N :=
  let '(a, c) := ac in
  (N.of_nat a, N.of_nat c).

Fixpoint F (ac : nat * nat) (d : nat) : option (nat * nat) :=
  let '(a, c) := ac in
  let a0 := Nat.modulo a (pow4pow2_nat d) in
  let a1 := Nat.div a (pow4pow2_nat d) in
  match d with
  | O =>
      if Nat.ltb c 3 then None
      else
        match a0 with
        | O => Some (a1 * 9 + 11, c - 3)
        | S O => Some (a1 * 9 + 15, c - 3)
        | S (S O) => Some (a1 * 9 + 12, c - 2)
        | _ => Some (a1 * 9 + 16, c - 2)
        end
  | S d0 =>
      match F (a0, c) d0 with
      | Some (a0', c1) =>
          match F (a0', c1) d0 with
          | Some (a0'', c2) => Some (a1 * pow9pow2_nat (S d0) + a0'', c2)
          | None => None
          end
      | None => None
      end
  end.

Lemma pow4pow2_nat_as_bitpow :
  forall d, pow4pow2_nat d = Nat.pow 2 (pow4pow2_bits d).
Proof.
  intros d.
  unfold pow4pow2_nat, pow4pow2_bits.
  change 4 with (2 ^ 2).
  rewrite <- Nat.pow_mul_r.
  rewrite Nat.pow_succ_r'.
  reflexivity.
Qed.

Lemma pow4pow2_nat_positive :
  forall d, 0 < pow4pow2_nat d.
Proof.
  intros d.
  unfold pow4pow2_nat.
  assert (Hnz : 4 ^ 2 ^ d <> 0).
  {
    apply Nat.pow_nonzero.
    lia.
  }
  lia.
Qed.

Lemma pow4pow2_nat_as_shiftl :
  forall d,
    N.of_nat (pow4pow2_nat d) =
    N.shiftl 1%N (N.of_nat (pow4pow2_bits d)).
Proof.
  intros d.
  rewrite pow4pow2_nat_as_bitpow.
  rewrite Nat2N.inj_pow.
  change (N.of_nat 2) with 2%N.
  symmetry.
  apply N.shiftl_1_l.
Qed.

Lemma pow9pow2_nat_rec :
  forall d,
    pow9pow2_nat (S d) = pow9pow2_nat d * pow9pow2_nat d.
Proof.
  intros d.
  unfold pow9pow2_nat at 1 2 3.
  rewrite Nat.pow_succ_r'.
  rewrite Nat.mul_comm.
  rewrite Nat.pow_mul_r.
  rewrite Nat.pow_2_r.
  reflexivity.
Qed.

Lemma pow9pow2_nat_to_N :
  forall d,
    N.of_nat (pow9pow2_nat d) = pow9_pow2_N d.
Proof.
  induction d as [|d IH].
  - reflexivity.
  - simpl pow9_pow2_N.
    rewrite pow9pow2_nat_rec.
    rewrite Nat2N.inj_mul.
    now rewrite IH.
Qed.

Lemma Nat2N_lt :
  forall a b,
    a < b ->
    (N.of_nat a < N.of_nat b)%N.
Proof.
  intros a b Hlt.
  apply N2Z.inj_lt.
  rewrite nat_N_Z, nat_N_Z.
  now apply Nat2Z.inj_lt.
Qed.

Lemma N_of_nat_ltb :
  forall a b,
    N.ltb (N.of_nat a) (N.of_nat b) = Nat.ltb a b.
Proof.
  intros a b.
  destruct (Nat.ltb a b) eqn:Hlt.
  - apply Nat.ltb_lt in Hlt.
    apply N.ltb_lt.
    now apply Nat2N_lt.
  - apply Nat.ltb_ge in Hlt.
    apply N.ltb_ge.
    apply N2Z.inj_le.
    rewrite nat_N_Z, nat_N_Z.
    now apply Nat2Z.inj_le.
Qed.

Lemma N_of_nat_eqb :
  forall a b,
    N.eqb (N.of_nat a) (N.of_nat b) = Nat.eqb a b.
Proof.
  intros a b.
  destruct (Nat.eqb a b) eqn:Heq.
  - apply Nat.eqb_eq in Heq.
    subst b.
    now rewrite N.eqb_refl.
  - destruct (N.eqb (N.of_nat a) (N.of_nat b)) eqn:Hneq; [|reflexivity].
    apply N.eqb_eq in Hneq.
    apply Nat2N.inj in Hneq.
    apply Nat.eqb_neq in Heq.
    exfalso.
    now apply Heq.
Qed.

Lemma split_pow4_N_of_nat :
  forall d a,
    split_pow4_N d (N.of_nat a) =
      (N.of_nat (Nat.div a (pow4pow2_nat d)),
       N.of_nat (Nat.modulo a (pow4pow2_nat d))).
Proof.
  intros d a.
  unfold split_pow4_N.
  set (m := pow4pow2_nat d).
  assert (Hm_pos : 0 < m).
  {
    subst m.
    apply pow4pow2_nat_positive.
  }
  assert (Hm_shift :
    N.of_nat m = N.shiftl 1%N (N.of_nat (pow4pow2_bits d))).
  {
    subst m.
    apply pow4pow2_nat_as_shiftl.
  }
  assert (Hm_pow :
    N.of_nat m = (2 ^ N.of_nat (pow4pow2_bits d))%N).
  {
    rewrite Hm_shift.
    apply N.shiftl_1_l.
  }
  simpl.
  apply f_equal2.
  - rewrite N.shiftr_div_pow2.
    rewrite <- Hm_pow.
    symmetry.
    apply N.div_unique with (r := N.of_nat (a mod m)).
    + apply Nat2N_lt.
      apply Nat.mod_upper_bound.
      lia.
    + replace (N.of_nat a)
        with (N.of_nat (m * (a / m) + a mod m)).
      2:{
        apply f_equal.
        symmetry.
        apply Nat.div_mod.
        lia.
      }
      rewrite Nat2N.inj_add.
      rewrite Nat2N.inj_mul.
      reflexivity.
  - replace (N.of_nat a) with (N.of_nat ((a / m) * m + a mod m)).
    2:{
      apply f_equal.
      rewrite Nat.mul_comm.
      symmetry.
      apply Nat.div_mod.
      lia.
    }
    symmetry.
    apply N.mod_unique with (q := N.of_nat (a / m)).
    + change (N.pos (Pos.shiftl 1 (N.of_nat (pow4pow2_bits d))))
        with (N.shiftl 1%N (N.of_nat (pow4pow2_bits d))).
      rewrite <- Hm_shift.
      apply Nat2N_lt.
      apply Nat.mod_upper_bound.
      lia.
    + change (N.pos (Pos.shiftl 1 (N.of_nat (pow4pow2_bits d))))
        with (N.shiftl 1%N (N.of_nat (pow4pow2_bits d))).
      rewrite <- Hm_shift.
      rewrite Nat2N.inj_add.
      rewrite Nat2N.inj_mul.
      rewrite N.mul_comm.
      reflexivity.
Qed.

Theorem F_N_equiv_F :
  forall a c d,
    F_N (N.of_nat a, N.of_nat c) d =
    option_map pair_nat_to_N (F (a, c) d).
Proof.
  intros a c d.
  revert a c.
  induction d as [|d IH]; intros a c.
  - cbn [F_N F].
    rewrite split_pow4_N_of_nat.
    change 3%N with (N.of_nat 3).
    rewrite N_of_nat_ltb.
    destruct (Nat.ltb c 3) eqn:Hc; [reflexivity|].
    set (a0 := a mod pow4pow2_nat 0).
    set (a1 := a / pow4pow2_nat 0).
    change 0%N with (N.of_nat 0).
    change 1%N with (N.of_nat 1).
    change 2%N with (N.of_nat 2).
    rewrite !N_of_nat_eqb.
    destruct a0 as [|[|[|n]]]; simpl.
    + rewrite Nat2N.inj_add, Nat2N.inj_mul.
      rewrite Nat2N.inj_sub by (apply Nat.ltb_ge in Hc; lia).
      reflexivity.
    + rewrite Nat2N.inj_add, Nat2N.inj_mul.
      rewrite Nat2N.inj_sub by (apply Nat.ltb_ge in Hc; lia).
      reflexivity.
    + rewrite Nat2N.inj_add, Nat2N.inj_mul.
      rewrite Nat2N.inj_sub by (apply Nat.ltb_ge in Hc; lia).
      reflexivity.
    + rewrite Nat2N.inj_add, Nat2N.inj_mul.
      rewrite Nat2N.inj_sub by (apply Nat.ltb_ge in Hc; lia).
      reflexivity.
  - cbn [F_N F].
    rewrite split_pow4_N_of_nat.
    set (a0 := a mod pow4pow2_nat (S d)).
    set (a1 := a / pow4pow2_nat (S d)).
    rewrite (IH a0 c).
    destruct (F (a0, c) d) as [[a0' c1]|] eqn:HF1; simpl; [| reflexivity].
    rewrite (IH a0' c1).
    destruct (F (a0', c1) d) as [[a0'' c2]|] eqn:HF2; simpl; [| reflexivity].
    rewrite Nat2N.inj_add, Nat2N.inj_mul.
    rewrite pow9pow2_nat_to_N.
    reflexivity.
Qed.

Theorem F_some_equiv_F_N :
  forall a c d a' c',
    F (a, c) d = Some (a', c') ->
    F_N (N.of_nat a, N.of_nat c) d = Some (N.of_nat a', N.of_nat c').
Proof.
  intros a c d a' c' HF.
  rewrite F_N_equiv_F.
  now rewrite HF.
Qed.

Theorem F_N_some_equiv_F :
  forall a c d a' c',
    F_N (N.of_nat a, N.of_nat c) d = Some (N.of_nat a', N.of_nat c') ->
    F (a, c) d = Some (a', c').
Proof.
  intros a c d a' c' HF.
  rewrite F_N_equiv_F in HF.
  destruct (F (a, c) d) as [[x y]|] eqn:Hx; simpl in HF.
  - injection HF as Hx1 Hx2.
    apply Nat2N.inj in Hx1.
    apply Nat2N.inj in Hx2.
    subst.
    reflexivity.
  - discriminate.
Qed.

Fixpoint F0_N (ac : N * N) (n : positive) (d : nat) : option (N * N) :=
  match n with
  | xH => F_N ac d
  | xI n' =>
      match F_N ac d with
      | Some ac' => F0_N ac' n' (S d)
      | None => None
      end
  | xO n' => F0_N ac n' (S d)
  end.

Fixpoint F0 (ac : nat * nat) (n : positive) (d : nat) : option (nat * nat) :=
  match n with
  | xH => F ac d
  | xI n' =>
      match F ac d with
      | Some ac' => F0 ac' n' (S d)
      | None => None
      end
  | xO n' => F0 ac n' (S d)
  end.

Fixpoint F0_bigint (ac : bigint * N) (n : positive) (d : nat)
    : option (bigint * N) :=
  match n with
  | xH => F_bigint ac d
  | xI n' =>
      match F_bigint ac d with
      | Some ac' => F0_bigint ac' n' (S d)
      | None => None
      end
  | xO n' => F0_bigint ac n' (S d)
  end.

Lemma F_bigint_some_correct :
  forall a c d a' c',
    canonical_bigint a ->
    F_bigint (a, c) d = Some (a', c') ->
    canonical_bigint a' /\
    F_N (bigint_to_N a, c) d = Some (bigint_to_N a', c').
Proof.
  intros a c d a' c' Ha Hf.
  unfold F_bigint in Hf.
  destruct (F_bigint_cached [] (a, c) d) as [[[ares cres] cache']|] eqn:Hcached.
  - inversion Hf; subst; clear Hf.
    destruct (F_bigint_cached_some_correct [] a c d a' c' cache'
                pow9_cache_ok_nil Ha Hcached) as [_ [Ha' HFN]].
    split; assumption.
  - discriminate.
Qed.

Theorem F0_N_equiv_F0 :
  forall a c n d,
    F0_N (N.of_nat a, N.of_nat c) n d =
    option_map pair_nat_to_N (F0 (a, c) n d).
Proof.
  intros a c n d.
  revert a c d.
  induction n as [n IH|n IH|]; intros a c d; simpl.
  - rewrite F_N_equiv_F.
    destruct (F (a, c) d) as [[a0 c0]|] eqn:HF; simpl.
    + apply IH.
    + reflexivity.
  - rewrite IH.
    reflexivity.
  - apply F_N_equiv_F.
Qed.

Theorem F0_N_some_equiv_F0 :
  forall a c n d a' c',
    F0_N (N.of_nat a, N.of_nat c) n d = Some (N.of_nat a', N.of_nat c') ->
    F0 (a, c) n d = Some (a', c').
Proof.
  intros a c n d a' c' HF.
  rewrite F0_N_equiv_F0 in HF.
  destruct (F0 (a, c) n d) as [[x y]|] eqn:Hx; simpl in HF.
  - injection HF as Hx1 Hx2.
    apply Nat2N.inj in Hx1.
    apply Nat2N.inj in Hx2.
    subst.
    reflexivity.
  - discriminate.
Qed.

Theorem F0_bigint_some_equiv_F0_N :
  forall a c n d a' c',
    canonical_bigint a ->
    F0_bigint (a, c) n d = Some (a', c') ->
    canonical_bigint a' /\
    F0_N (bigint_to_N a, c) n d = Some (bigint_to_N a', c').
Proof.
  intros a c n d a' c' Ha Hf.
  revert a c d a' c' Ha Hf.
  induction n as [n IH|n IH|]; intros a c d a' c' Ha Hf; simpl in Hf.
  - destruct (F_bigint (a, c) d) as [[a0 c0]|] eqn:Hstep; [| discriminate].
    destruct (F_bigint_some_correct a c d a0 c0 Ha Hstep) as [Ha0 HFN0].
    destruct (IH a0 c0 (S d) a' c' Ha0 Hf) as [Ha' HFN].
    split.
    + exact Ha'.
    + simpl.
      rewrite HFN0.
      exact HFN.
  - eapply IH; eauto.
  - exact (F_bigint_some_correct a c d a' c' Ha Hf).
Qed.

Lemma F0_bigint_spec :
  forall a c n d a' c',
    canonical_bigint a ->
    F0_bigint (a, c) n d = Some (a', c') ->
    F0 (N.to_nat (bigint_to_N a), N.to_nat c) n d =
      Some (N.to_nat (bigint_to_N a'), N.to_nat c').
Proof.
  intros a c n d a' c' Ha Hf.
  destruct (F0_bigint_some_equiv_F0_N a c n d a' c' Ha Hf) as [_ HFN].
  rewrite <- (N2Nat.id (bigint_to_N a)) in HFN at 1.
  rewrite <- (N2Nat.id c) in HFN at 1.
  rewrite <- (N2Nat.id (bigint_to_N a')) in HFN at 1.
  rewrite <- (N2Nat.id c') in HFN at 1.
  eapply F0_N_some_equiv_F0.
  exact HFN.
Qed.
