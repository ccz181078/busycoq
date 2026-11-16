From Coq Require Import Uint63 ZArith Lia Lists.List.
Require Import BigInt.NTTConcrete BigInt.BigIntMul BigInt.BigIntMulProof
  BigInt.BigIntMulNormalize BigInt.BigIntMulNormalizeArithmetic
  BigInt.BigIntMulNormalizeArray BigInt.BigIntMulNormalizeInvariant.

Import ListNotations.
Local Open Scope Z_scope.

Fixpoint coeff_digits_z
    (fuel : nat) (idx : Uint63.int) (arr : PArray.array Uint63.int) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      Uint63.to_Z (coeff_array_at arr idx) ::
      coeff_digits_z fuel' (Uint63.add idx u63_one) arr
  end.

Fixpoint advance_idx (fuel : nat) (idx : Uint63.int) : Uint63.int :=
  match fuel with
  | O => idx
  | S fuel' => advance_idx fuel' (Uint63.add idx u63_one)
  end.

Fixpoint normalize_coeff_digit_state
    (fuel : nat) (idx : Uint63.int) (carry : Uint63.int)
    (arr : PArray.array Uint63.int) : list Uint63.int * Uint63.int :=
  match fuel with
  | O => ([], carry)
  | S fuel' =>
      let '(digit, carry1) := normalize_coeff_step idx carry arr in
      let '(digits, carry2) :=
        normalize_coeff_digit_state fuel' (Uint63.add idx u63_one) carry1 arr in
      (digit :: digits, carry2)
  end.

Fixpoint normalize_coeff_block_state
    (fuel : nat) (idx : Uint63.int) (carry : Uint63.int)
    (arr : PArray.array Uint63.int) : list Uint63.int * Uint63.int :=
  match fuel with
  | O => ([], carry)
  | S fuel' =>
      let '(block, carry1) := normalize_coeff_block idx carry arr in
      let '(digits, carry2) :=
        normalize_coeff_block_state fuel' (Uint63.add idx u63_eight) carry1 arr in
      (limb8_digits_u63 block ++ digits, carry2)
  end.

Lemma u63_add_zero_r :
  forall x,
    Uint63.add x zero_digit = x.
Proof.
  intro x.
  apply Uint63.to_Z_inj.
  rewrite Uint63.add_spec.
  rewrite zero_digit_to_Z.
  rewrite Z.add_0_r.
  apply Z.mod_small.
  apply Uint63.to_Z_bounded.
Qed.

Lemma advance_idx_correct :
  forall fuel idx,
    (Z.of_nat fuel < Uint63.wB)%Z ->
    advance_idx fuel idx = Uint63.add idx (u63_of_nat fuel).
Proof.
  induction fuel as [|fuel IH]; intros idx Hfuel.
  - simpl.
    rewrite u63_add_zero_r.
    reflexivity.
  - simpl.
    rewrite IH by lia.
    rewrite <- Uint63.add_assoc.
    change u63_one with (u63_of_nat 1).
    replace (u63_of_nat (S fuel))
      with (Uint63.add (u63_of_nat fuel) (u63_of_nat 1)).
    2:{
      assert (Htmp :
        Uint63.add (u63_of_nat fuel) (u63_of_nat 1) = u63_of_nat (S fuel)).
      {
        replace (S fuel) with (fuel + 1)%nat by lia.
        apply u63_of_nat_add.
        replace (Z.of_nat (fuel + 1)) with (Z.of_nat (S fuel)) by lia.
        exact Hfuel.
      }
      exact Htmp.
    }
    rewrite (Uint63.add_comm (u63_of_nat 1) (u63_of_nat fuel)).
    reflexivity.
Qed.

Lemma advance_idx_8 :
  forall idx,
    advance_idx 8 idx = Uint63.add idx u63_eight.
Proof.
  intro idx.
  rewrite (advance_idx_correct 8 idx).
  2:{
    change (8 < 9223372036854775808)%Z.
    lia.
  }
  reflexivity.
Qed.

Lemma digit_base_shift :
  forall z,
    match z with
    | 0 => 0
    | Z.pos y => Z.pos y~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Z.neg y => Z.neg y~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    end = digit_base_z * z.
Proof.
  intros [|p|p]; reflexivity.
Qed.

Lemma normalize_coeff_digit_state_add_8 :
  forall fuel idx carry arr,
    normalize_coeff_digit_state (8 + fuel) idx carry arr =
    let '(digits1, carry1) := normalize_coeff_digit_state 8 idx carry arr in
    let '(digits2, carry2) :=
      normalize_coeff_digit_state fuel (advance_idx 8 idx) carry1 arr in
    (digits1 ++ digits2, carry2).
Proof.
  intros fuel idx carry arr.
  replace (8 + fuel)%nat with
    (S (S (S (S (S (S (S (S fuel)))))))) by lia.
  cbn [normalize_coeff_digit_state advance_idx].
  destruct (normalize_coeff_step idx carry arr) as [d0 carry0].
  destruct (normalize_coeff_step (Uint63.add idx u63_one) carry0 arr) as [d1 carry1].
  destruct (normalize_coeff_step (Uint63.add (Uint63.add idx u63_one) u63_one) carry1 arr) as [d2 carry2].
  destruct (normalize_coeff_step (Uint63.add (Uint63.add (Uint63.add idx u63_one) u63_one) u63_one) carry2 arr) as [d3 carry3].
  destruct (normalize_coeff_step (Uint63.add (Uint63.add (Uint63.add (Uint63.add idx u63_one) u63_one) u63_one) u63_one) carry3 arr) as [d4 carry4].
  destruct (normalize_coeff_step (Uint63.add (Uint63.add (Uint63.add (Uint63.add (Uint63.add idx u63_one) u63_one) u63_one) u63_one) u63_one) carry4 arr) as [d5 carry5].
  destruct (normalize_coeff_step (Uint63.add (Uint63.add (Uint63.add (Uint63.add (Uint63.add (Uint63.add idx u63_one) u63_one) u63_one) u63_one) u63_one) u63_one) carry5 arr) as [d6 carry6].
  destruct (normalize_coeff_step (Uint63.add (Uint63.add (Uint63.add (Uint63.add (Uint63.add (Uint63.add (Uint63.add idx u63_one) u63_one) u63_one) u63_one) u63_one) u63_one) u63_one) carry6 arr) as [d7 carry7].
  destruct (normalize_coeff_digit_state fuel
    (Uint63.add (Uint63.add (Uint63.add (Uint63.add (Uint63.add (Uint63.add (Uint63.add (Uint63.add idx u63_one) u63_one) u63_one) u63_one) u63_one) u63_one) u63_one) u63_one)
    carry7 arr) as [digits_tail carry_tail].
  reflexivity.
Qed.

Lemma normalize_coeff_digit_state_value :
  forall fuel idx carry arr,
    Forall (fun z => (0 <= z < crt_modulus_z)%Z) (coeff_digits_z fuel idx arr) ->
    (0 <= Uint63.to_Z carry < carry_limit_z)%Z ->
    let '(digits, carry') := normalize_coeff_digit_state fuel idx carry arr in
    (0 <= Uint63.to_Z carry' < carry_limit_z)%Z /\
    digits_value (map Uint63.to_Z digits) +
      (digit_base_z ^ Z.of_nat fuel) * Uint63.to_Z carry' =
    Uint63.to_Z carry + digits_value (coeff_digits_z fuel idx arr).
Proof.
  induction fuel as [|fuel IH]; intros idx carry arr Hcoeffs Hcarry.
  - simpl.
    split.
    + exact Hcarry.
    + simpl.
      change (digit_base_z ^ Z.of_nat 0) with 1%Z.
      destruct (Uint63.to_Z carry); reflexivity.
  - simpl in Hcoeffs.
    inversion Hcoeffs as [|coeff coeffs Hcoeff Hcoeffs']; subst.
    cbn [normalize_coeff_digit_state].
    destruct (normalize_coeff_step idx carry arr) as [digit carry1] eqn:Hstep.
    pose proof (normalize_coeff_step_carry_limit idx carry arr Hcoeff Hcarry) as Hcarry1.
    rewrite Hstep in Hcarry1.
    simpl in Hcarry1.
    destruct (normalize_coeff_digit_state fuel (Uint63.add idx u63_one) carry1 arr)
      as [digits carry'] eqn:Hstate.
    specialize (IH (Uint63.add idx u63_one) carry1 arr Hcoeffs' Hcarry1).
    rewrite Hstate in IH.
    simpl in IH.
    destruct IH as [Hcarry' IHvalue].
    split.
    + exact Hcarry'.
    + simpl.
      rewrite !digit_base_shift.
      rewrite Z.pow_pos_fold.
      rewrite Zpos_P_of_succ_nat.
      rewrite Z.pow_succ_r by lia.
      replace
        (Uint63.to_Z digit +
         digit_base_z * digits_value (map Uint63.to_Z digits) +
         digit_base_z * digit_base_z ^ Z.of_nat fuel * Uint63.to_Z carry')
        with
        (Uint63.to_Z digit +
         digit_base_z *
           (digits_value (map Uint63.to_Z digits) +
            digit_base_z ^ Z.of_nat fuel * Uint63.to_Z carry')) by ring.
      rewrite IHvalue.
      pose proof (normalize_coeff_step_value idx carry arr
        (coeff_plus_carry_lt_wB _ _ Hcoeff Hcarry)) as Hstep_value.
      rewrite Hstep in Hstep_value.
      simpl in Hstep_value.
      rewrite digit_base_shift in Hstep_value.
      lia.
Qed.

Lemma normalize_one_block_state :
  forall idx carry arr,
    normalize_coeff_block_state 1 idx carry arr =
    normalize_coeff_digit_state 8 idx carry arr.
Proof.
  intros idx carry arr.
  unfold normalize_coeff_block_state.
  fold normalize_coeff_block_state.
  unfold normalize_coeff_block.
  assert (Hu2 : Uint63.of_Z 2 = Uint63.add u63_one u63_one) by (vm_compute; reflexivity).
  assert (Hu3 : u63_three = Uint63.add (Uint63.add u63_one u63_one) u63_one) by (vm_compute; reflexivity).
  assert (Hu4 : Uint63.of_Z 4 = Uint63.add (Uint63.add (Uint63.add u63_one u63_one) u63_one) u63_one) by (vm_compute; reflexivity).
  assert (Hu5 : Uint63.of_Z 5 =
    Uint63.add (Uint63.add (Uint63.add (Uint63.add u63_one u63_one) u63_one) u63_one) u63_one) by (vm_compute; reflexivity).
  assert (Hu6 : Uint63.of_Z 6 =
    Uint63.add (Uint63.add (Uint63.add (Uint63.add (Uint63.add u63_one u63_one) u63_one) u63_one) u63_one) u63_one) by (vm_compute; reflexivity).
  assert (Hu7 : u63_seven =
    Uint63.add (Uint63.add (Uint63.add (Uint63.add (Uint63.add (Uint63.add u63_one u63_one) u63_one) u63_one) u63_one) u63_one) u63_one) by (vm_compute; reflexivity).
  rewrite Hu2, Hu3, Hu4, Hu5, Hu6, Hu7.
  repeat rewrite Uint63.add_assoc.
  change 8%nat with (S (S (S (S (S (S (S (S O)))))))).
  cbn [normalize_coeff_digit_state].
  destruct (normalize_coeff_step idx carry arr) as [d0 carry0] eqn:H0.
  destruct (normalize_coeff_step (Uint63.add idx u63_one) carry0 arr) as [d1 carry1] eqn:H1.
  destruct (normalize_coeff_step (Uint63.add (Uint63.add idx u63_one) u63_one) carry1 arr) as [d2 carry2] eqn:H2.
  destruct (normalize_coeff_step (Uint63.add (Uint63.add (Uint63.add idx u63_one) u63_one) u63_one) carry2 arr) as [d3 carry3] eqn:H3.
  destruct (normalize_coeff_step (Uint63.add (Uint63.add (Uint63.add (Uint63.add idx u63_one) u63_one) u63_one) u63_one) carry3 arr) as [d4 carry4] eqn:H4.
  destruct (normalize_coeff_step (Uint63.add (Uint63.add (Uint63.add (Uint63.add (Uint63.add idx u63_one) u63_one) u63_one) u63_one) u63_one) carry4 arr) as [d5 carry5] eqn:H5.
  destruct (normalize_coeff_step (Uint63.add (Uint63.add (Uint63.add (Uint63.add (Uint63.add (Uint63.add idx u63_one) u63_one) u63_one) u63_one) u63_one) u63_one) carry5 arr) as [d6 carry6] eqn:H6.
  destruct (normalize_coeff_step (Uint63.add (Uint63.add (Uint63.add (Uint63.add (Uint63.add (Uint63.add (Uint63.add idx u63_one) u63_one) u63_one) u63_one) u63_one) u63_one) u63_one) carry6 arr) as [d7 carry7] eqn:H7.
  reflexivity.
Qed.

Lemma normalize_coeff_block_state_eq_digit_state :
  forall fuel idx carry arr,
    normalize_coeff_block_state fuel idx carry arr =
    normalize_coeff_digit_state (8 * fuel) idx carry arr.
Proof.
  induction fuel as [|fuel IH]; intros idx carry arr.
  - reflexivity.
  - replace (8 * S fuel)%nat with (8 + 8 * fuel)%nat by lia.
    rewrite normalize_coeff_digit_state_add_8.
    rewrite <- normalize_one_block_state with (idx := idx) (carry := carry) (arr := arr).
    simpl normalize_coeff_block_state.
    destruct (normalize_coeff_block idx carry arr) as [block carry1] eqn:Hblock.
    simpl.
    rewrite IH.
    rewrite <- advance_idx_8.
    cbn [advance_idx].
    simpl.
    reflexivity.
Qed.

Lemma normalize_coeff_block_state_fst :
  forall fuel idx carry arr,
    fst (normalize_coeff_block_state fuel idx carry arr) =
    normalize_coeff_block_digits fuel idx carry arr.
Proof.
  induction fuel as [|fuel IH]; intros idx carry arr.
  - reflexivity.
  - cbn [normalize_coeff_block_state normalize_coeff_block_digits].
    destruct (normalize_coeff_block idx carry arr) as [block carry1].
    destruct (normalize_coeff_block_state fuel (Uint63.add idx u63_eight) carry1 arr)
      as [digits carry2] eqn:Hstate.
    specialize (IH (Uint63.add idx u63_eight) carry1 arr).
    rewrite Hstate in IH.
    simpl in IH.
    simpl.
    rewrite IH.
    reflexivity.
Qed.

Lemma normalize_coeff_block_state_value :
  forall fuel idx carry arr,
    Forall (fun z => (0 <= z < crt_modulus_z)%Z) (coeff_digits_z (8 * fuel) idx arr) ->
    (0 <= Uint63.to_Z carry < carry_limit_z)%Z ->
    let '(digits, carry') := normalize_coeff_block_state fuel idx carry arr in
    (0 <= Uint63.to_Z carry' < carry_limit_z)%Z /\
    digits_value (map Uint63.to_Z digits) +
      (digit_base_z ^ Z.of_nat (8 * fuel)) * Uint63.to_Z carry' =
    Uint63.to_Z carry + digits_value (coeff_digits_z (8 * fuel) idx arr).
Proof.
  intros fuel idx carry arr Hcoeffs Hcarry.
  rewrite normalize_coeff_block_state_eq_digit_state.
  apply normalize_coeff_digit_state_value; assumption.
Qed.

Corollary normalize_coeff_array_to_bigint_value_coeff_digits :
  forall fuel arr,
    Forall (fun z => (0 <= z < crt_modulus_z)%Z) (coeff_digits_z (8 * fuel) zero_digit arr) ->
    let '(digits, carry') := normalize_coeff_block_state fuel zero_digit zero_digit arr in
    bigint_value (normalize_coeff_array_to_bigint fuel arr) +
      (digit_base_z ^ Z.of_nat (8 * fuel)) * Uint63.to_Z carry' =
    digits_value (coeff_digits_z (8 * fuel) zero_digit arr).
Proof.
  intros fuel arr Hcoeffs.
  rewrite normalize_coeff_array_to_bigint_value.
  rewrite <- normalize_coeff_block_state_fst with (fuel := fuel) (idx := zero_digit) (carry := zero_digit) (arr := arr).
  destruct (normalize_coeff_block_state fuel zero_digit zero_digit arr) as [digits carry'] eqn:Hstate.
  simpl.
  pose proof (normalize_coeff_block_state_value fuel zero_digit zero_digit arr Hcoeffs) as Hvalue.
  assert (HzeroCarry : (0 <= Uint63.to_Z zero_digit < carry_limit_z)%Z).
  {
    rewrite zero_digit_to_Z.
    unfold carry_limit_z.
    lia.
  }
  specialize (Hvalue HzeroCarry).
  rewrite Hstate in Hvalue.
  simpl in Hvalue.
  pose proof (proj2 Hvalue) as Hdigits.
  change (Uint63.to_Z zero_digit) with 0%Z in Hdigits.
  exact Hdigits.
Qed.
