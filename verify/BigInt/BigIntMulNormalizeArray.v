From Coq Require Import Uint63 ZArith Lia Lists.List.
Require Import BigInt.BigIntMul BigInt.BigIntMulProof BigInt.BigIntMulNormalize.

Import ListNotations.
Local Open Scope Z_scope.

Fixpoint normalize_coeff_block_digits
    (fuel : nat) (idx : Uint63.int) (carry : Uint63.int)
    (arr : PArray.array Uint63.int) : list Uint63.int :=
  match fuel with
  | O => []
  | S fuel' =>
      let '(block, carry') := normalize_coeff_block idx carry arr in
      limb8_digits_u63 block ++
      normalize_coeff_block_digits fuel' (Uint63.add idx u63_eight) carry' arr
  end.

Lemma bigint_value_trimmed_block_cons :
  forall block rest,
    bigint_value
      match rest with
      | [] => if limb8_eqb block zero_limb8 then [] else [block]
      | _ => block :: rest
      end
    =
    limb8_value block + digit_base8_z * bigint_value rest.
Proof.
  intros block rest.
  destruct rest as [|r rs].
  - destruct (limb8_eqb block zero_limb8) eqn:Hblock.
    + apply limb8_eqb_eq in Hblock.
      subst block.
      rewrite limb8_value_zero_limb8.
      reflexivity.
    + rewrite (bigint_value_cons block []).
      simpl.
      ring.
  - rewrite (bigint_value_cons block (r :: rs)).
    reflexivity.
Qed.

Lemma normalize_coeff_array_to_bigint_aux_value :
  forall fuel idx carry arr,
    bigint_value (normalize_coeff_array_to_bigint_aux fuel idx carry arr) =
    digits_value (map Uint63.to_Z (normalize_coeff_block_digits fuel idx carry arr)).
Proof.
  induction fuel as [|fuel IH]; intros idx carry arr.
  - reflexivity.
  - cbn [normalize_coeff_array_to_bigint_aux normalize_coeff_block_digits].
    destruct (normalize_coeff_block idx carry arr) as [block carry'] eqn:Hblock.
    set (rest := normalize_coeff_array_to_bigint_aux fuel (Uint63.add idx u63_eight) carry' arr).
    change
      (bigint_value
         (match rest with
          | [] => if limb8_eqb block zero_limb8 then [] else [block]
          | _ => block :: rest
          end) =
       digits_value
         (map Uint63.to_Z
            (limb8_digits_u63 block ++
             normalize_coeff_block_digits fuel (Uint63.add idx u63_eight) carry' arr))).
    rewrite bigint_value_trimmed_block_cons.
    unfold rest.
    rewrite IH.
    rewrite map_app.
    rewrite digits_value_app.
    rewrite length_map.
    rewrite limb8_digits_u63_length.
    rewrite <- limb8_digits_z_eq_map.
    unfold limb8_value.
    change (Z.of_nat 8) with 8%Z.
    change (digit_base_z ^ 8) with digit_base8_z.
    reflexivity.
Qed.

Corollary normalize_coeff_array_to_bigint_value :
  forall fuel arr,
    bigint_value (normalize_coeff_array_to_bigint fuel arr) =
    digits_value (map Uint63.to_Z (normalize_coeff_block_digits fuel zero_digit zero_digit arr)).
Proof.
  intros fuel arr.
  unfold normalize_coeff_array_to_bigint.
  apply normalize_coeff_array_to_bigint_aux_value.
Qed.

Corollary normalize_coeff_array_to_bigint_value_digits_to_bigint :
  forall fuel arr,
    bigint_value (normalize_coeff_array_to_bigint fuel arr) =
    bigint_value (digits_to_bigint (normalize_coeff_block_digits fuel zero_digit zero_digit arr)).
Proof.
  intros fuel arr.
  rewrite normalize_coeff_array_to_bigint_value.
  rewrite digits_to_bigint_value.
  reflexivity.
Qed.
