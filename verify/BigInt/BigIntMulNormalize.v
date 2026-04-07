From Coq Require Import Uint63 ZArith Lia Lists.List.
Require Import BigInt.BigIntMul BigInt.BigIntMulProof.

Import ListNotations.
Local Open Scope Z_scope.

Lemma zero_digit_to_Z :
  Uint63.to_Z zero_digit = 0.
Proof.
  vm_compute.
  reflexivity.
Qed.

Fixpoint digits_to_bigint_blocks (fuel : nat) (xs : list Uint63.int) : bigint :=
  match fuel with
  | O => []
  | S fuel' =>
      match xs with
      | [] => []
      | _ =>
          let '(block, rest) := split_digits8 xs in
          block :: digits_to_bigint_blocks fuel' rest
      end
  end.

Lemma bigint_digits_z_flat_app :
  forall x y,
    bigint_digits_z_flat (x ++ y) = bigint_digits_z_flat x ++ bigint_digits_z_flat y.
Proof.
  intros x y.
  rewrite <- !bigint_digits_z_eq_flat.
  induction x as [|b bs IH]; simpl.
  - reflexivity.
  - rewrite IH.
    rewrite app_assoc.
    reflexivity.
Qed.

Lemma bigint_digits_z_flat_length :
  forall x,
    List.length (bigint_digits_z_flat x) = (8 * List.length x)%nat.
Proof.
  intros x.
  rewrite <- bigint_digits_z_eq_flat.
  induction x as [|b bs IH].
  - reflexivity.
  - simpl.
    rewrite length_app.
    rewrite limb8_digits_z_length.
    rewrite IH.
    lia.
Qed.

Lemma limb8_value_zero_limb8 :
  limb8_value zero_limb8 = 0.
Proof.
  reflexivity.
Qed.

Lemma bigint_value_app_blocks :
  forall x y,
    bigint_value (x ++ y) =
    bigint_value x +
    (digit_base8_z ^ Z.of_nat (List.length x)) * bigint_value y.
Proof.
  intros x y.
  unfold bigint_value.
  rewrite !bigint_digits_z_eq_flat.
  rewrite bigint_digits_z_flat_app.
  rewrite digits_value_app.
  rewrite bigint_digits_z_flat_length.
  rewrite Nat2Z.inj_mul.
  change (Z.of_nat 8) with 8%Z.
  rewrite Z.pow_mul_r by lia.
  change (digit_base_z ^ 8) with digit_base8_z.
  reflexivity.
Qed.

Lemma bigint_value_snoc_zero :
  forall x,
    bigint_value (x ++ [zero_limb8]) = bigint_value x.
Proof.
  intro x.
  rewrite bigint_value_app_blocks.
  assert (Hzero : bigint_value [zero_limb8] = 0).
  {
    reflexivity.
  }
  rewrite Hzero.
  ring.
Qed.

Lemma limb8_eqb_eq :
  forall x y,
    limb8_eqb x y = true ->
    x = y.
Proof.
  intros [x0 x1 x2 x3 x4 x5 x6 x7] [y0 y1 y2 y3 y4 y5 y6 y7] H.
  simpl in H.
  apply andb_prop in H.
  destruct H as [H0123456 H7].
  apply andb_prop in H0123456.
  destruct H0123456 as [H012345 H6].
  apply andb_prop in H012345.
  destruct H012345 as [H01234 H5].
  apply andb_prop in H01234.
  destruct H01234 as [H0123 H4].
  apply andb_prop in H0123.
  destruct H0123 as [H012 H3].
  apply andb_prop in H012.
  destruct H012 as [H01 H2].
  apply andb_prop in H01.
  destruct H01 as [H0 H1].
  apply Uint63.eqb_spec in H0.
  apply Uint63.eqb_spec in H1.
  apply Uint63.eqb_spec in H2.
  apply Uint63.eqb_spec in H3.
  apply Uint63.eqb_spec in H4.
  apply Uint63.eqb_spec in H5.
  apply Uint63.eqb_spec in H6.
  apply Uint63.eqb_spec in H7.
  subst.
  reflexivity.
Qed.

Lemma drop_zero_prefix_rev_value :
  forall xs,
    bigint_value (rev (drop_zero_prefix xs)) = bigint_value (rev xs).
Proof.
  induction xs as [|x xs IH].
  - reflexivity.
  - simpl drop_zero_prefix.
    destruct (limb8_eqb x zero_limb8) eqn:Hx.
    + rewrite IH.
      apply limb8_eqb_eq in Hx.
      subst x.
      simpl.
      symmetry.
      apply bigint_value_snoc_zero.
    + reflexivity.
Qed.

Lemma trim_bigint_value :
  forall x,
    bigint_value (trim_bigint x) = bigint_value x.
Proof.
  intros x.
  unfold trim_bigint.
  rewrite drop_zero_prefix_rev_value.
  rewrite rev_involutive.
  reflexivity.
Qed.

Lemma split_digits8_rest_length :
  forall xs block rest,
    split_digits8 xs = (block, rest) ->
    List.length rest = (List.length xs - 8)%nat.
Proof.
  intros xs block rest H.
  destruct xs as
      [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 xs]]]]]]]];
    simpl in H;
    inversion H; subst; simpl;
    lia.
Qed.

Lemma split_digits8_digits_value :
  forall xs block rest,
    split_digits8 xs = (block, rest) ->
    digits_value (map Uint63.to_Z xs) =
    digits_value (limb8_digits_z block ++ map Uint63.to_Z rest).
Proof.
  intros xs block rest H.
  destruct xs as
      [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 xs]]]]]]]];
    cbn [split_digits8 map digits_value limb8_digits_z limb8_digits_u63] in H |- *;
    inversion H; subst;
    unfold zero_limb8 in *;
    cbn [digits_value limb8_digits_z limb8_digits_u63 map app];
    repeat rewrite zero_digit_to_Z;
    try reflexivity;
    ring.
Qed.

Lemma split_digits8_value :
  forall xs block rest,
    split_digits8 xs = (block, rest) ->
    digits_value (map Uint63.to_Z xs) =
    limb8_value block + digit_base8_z * digits_value (map Uint63.to_Z rest).
Proof.
  intros xs block rest H.
  rewrite (split_digits8_digits_value xs block rest H).
  rewrite digits_value_app.
  unfold limb8_value.
  rewrite limb8_digits_z_length.
  change (Z.of_nat 8) with 8%Z.
  reflexivity.
Qed.

Lemma digits_to_bigint_rev_aux_rev :
  forall fuel xs acc,
    rev (digits_to_bigint_rev_aux fuel xs acc) =
    rev acc ++ digits_to_bigint_blocks fuel xs.
Proof.
  induction fuel as [|fuel IH]; intros xs acc.
  - simpl.
    rewrite app_nil_r.
    reflexivity.
  - destruct xs as [|x xs].
    + simpl.
      rewrite app_nil_r.
      reflexivity.
    + change
        (rev
           (let '(block, rest) := split_digits8 (x :: xs) in
            digits_to_bigint_rev_aux fuel rest (block :: acc)) =
         rev acc ++
         let '(block, rest) := split_digits8 (x :: xs) in
         block :: digits_to_bigint_blocks fuel rest).
      destruct (split_digits8 (x :: xs)) as [block rest] eqn:Hsplit.
      rewrite (IH rest (block :: acc)).
      simpl.
      change (block :: digits_to_bigint_blocks fuel rest)
        with ([block] ++ digits_to_bigint_blocks fuel rest).
      rewrite <- app_assoc.
      reflexivity.
Qed.

Lemma digits_to_bigint_blocks_value :
  forall fuel xs,
    (List.length xs <= 8 * fuel)%nat ->
    bigint_value (digits_to_bigint_blocks fuel xs) =
    digits_value (map Uint63.to_Z xs).
Proof.
  induction fuel as [|fuel IH]; intros xs Hlen.
  - destruct xs as [|x xs].
    + reflexivity.
    + simpl in Hlen.
      lia.
  - destruct xs as [|x xs].
    + reflexivity.
    + cbn [digits_to_bigint_blocks].
      destruct (split_digits8 (x :: xs)) as [block rest] eqn:Hsplit.
      rewrite (bigint_value_cons block (digits_to_bigint_blocks fuel rest)).
      rewrite IH.
      2:{
        pose proof (split_digits8_rest_length (x :: xs) block rest Hsplit) as Hrest.
        lia.
      }
      rewrite (split_digits8_value (x :: xs) block rest Hsplit).
      reflexivity.
Qed.

Lemma digits_to_bigint_value :
  forall xs,
    bigint_value (digits_to_bigint xs) = digits_value (map Uint63.to_Z xs).
Proof.
  intros xs.
  unfold digits_to_bigint.
  rewrite trim_bigint_value.
  rewrite digits_to_bigint_rev_aux_rev.
  simpl.
  apply digits_to_bigint_blocks_value.
  lia.
Qed.
