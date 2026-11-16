From Coq Require Import Uint63 ZArith Lia Lists.List.
Require Import BigInt.NTTConcrete BigInt.BigIntMul BigInt.BigIntMulProof
  BigInt.BigIntMulNormalizeArithmetic.

Import ListNotations.
Local Open Scope Z_scope.

Definition carry_limit_z : Z := 2 ^ 60.

Definition coeff_block_digits_z
    (idx : Uint63.int) (arr : PArray.array Uint63.int) : list Z :=
  [ Uint63.to_Z (coeff_array_at arr idx);
    Uint63.to_Z (coeff_array_at arr (Uint63.add idx u63_one));
    Uint63.to_Z (coeff_array_at arr (Uint63.add idx (Uint63.of_Z 2)));
    Uint63.to_Z (coeff_array_at arr (Uint63.add idx u63_three));
    Uint63.to_Z (coeff_array_at arr (Uint63.add idx (Uint63.of_Z 4)));
    Uint63.to_Z (coeff_array_at arr (Uint63.add idx (Uint63.of_Z 5)));
    Uint63.to_Z (coeff_array_at arr (Uint63.add idx (Uint63.of_Z 6)));
    Uint63.to_Z (coeff_array_at arr (Uint63.add idx u63_seven)) ].

Lemma carry_limit_lt_wB :
  (carry_limit_z < Uint63.wB)%Z.
Proof.
  change (1152921504606846976 < 9223372036854775808)%Z.
  lia.
Qed.

Lemma crt_modulus_lt_carry_limit :
  (crt_modulus_z < carry_limit_z)%Z.
Proof.
  change (851180331854725121 < 1152921504606846976)%Z.
  lia.
Qed.

Lemma coeff_plus_carry_lt_wB :
  forall coeff carry,
    (0 <= coeff < crt_modulus_z)%Z ->
    (0 <= carry < carry_limit_z)%Z ->
    (coeff + carry < Uint63.wB)%Z.
Proof.
  intros coeff carry Hcoeff Hcarry.
  destruct Hcoeff as [Hcoeff0 Hcoeff1].
  destruct Hcarry as [Hcarry0 Hcarry1].
  assert (Hsum :
    (coeff + carry < 851180331854725121 + 1152921504606846976)%Z).
  {
    change crt_modulus_z with 851180331854725121%Z in Hcoeff1.
    change carry_limit_z with 1152921504606846976%Z in Hcarry1.
    nia.
  }
  change (coeff + carry < 9223372036854775808)%Z.
  nia.
Qed.

Lemma normalize_coeff_step_carry_limit :
  forall idx carry arr,
    (0 <= Uint63.to_Z (coeff_array_at arr idx) < crt_modulus_z)%Z ->
    (0 <= Uint63.to_Z carry < carry_limit_z)%Z ->
    let '(_, carry') := normalize_coeff_step idx carry arr in
    (0 <= Uint63.to_Z carry' < carry_limit_z)%Z.
Proof.
  intros idx carry arr Hcoeff Hcarry.
  destruct (normalize_coeff_step idx carry arr) as [digit carry'] eqn:Hstep.
  simpl.
  assert (Hnowrap :
    (Uint63.to_Z (coeff_array_at arr idx) + Uint63.to_Z carry < Uint63.wB)%Z).
  {
    eapply coeff_plus_carry_lt_wB; eauto.
  }
  pose proof (Uint63.to_Z_bounded carry') as [Hcarry'0 _].
  destruct Hcoeff as [Hcoeff0 Hcoeff1].
  destruct Hcarry as [Hcarry0 Hcarry1].
  unfold normalize_coeff_step in Hstep.
  set (coeff := coeff_array_at arr idx) in *.
  set (total := Uint63.add coeff carry) in *.
  inversion Hstep; subst digit carry'; clear Hstep.
  split; [exact Hcarry'0|].
  rewrite Uint63.lsr_spec.
  change (Uint63.to_Z total / 2 ^ Uint63.to_Z digit_shift < carry_limit_z)%Z.
  assert (Htotal :
    Uint63.to_Z total = Uint63.to_Z coeff + Uint63.to_Z carry).
  {
    subst total coeff.
    rewrite Uint63.add_spec.
    apply Z.mod_small.
    split.
    - nia.
    - exact Hnowrap.
  }
  rewrite Htotal.
  rewrite digit_shift_to_Z.
  change carry_limit_z with 1152921504606846976%Z.
  change carry_limit_z with 1152921504606846976%Z in Hcarry1.
  change crt_modulus_z with 851180331854725121%Z in Hcoeff1.
  apply Z.div_lt_upper_bound; try lia.
Qed.

Lemma normalize_coeff_block_carry_limit :
  forall idx carry arr,
    Forall (fun z => (0 <= z < crt_modulus_z)%Z) (coeff_block_digits_z idx arr) ->
    (0 <= Uint63.to_Z carry < carry_limit_z)%Z ->
    let '(block, carry') := normalize_coeff_block idx carry arr in
    (0 <= Uint63.to_Z carry' < carry_limit_z)%Z.
Proof.
  intros idx carry arr Hcoeffs Hcarry.
  unfold coeff_block_digits_z in Hcoeffs.
  inversion Hcoeffs as [|? ? Hc0 Hrest0]; subst.
  inversion Hrest0 as [|? ? Hc1 Hrest1]; subst.
  inversion Hrest1 as [|? ? Hc2 Hrest2]; subst.
  inversion Hrest2 as [|? ? Hc3 Hrest3]; subst.
  inversion Hrest3 as [|? ? Hc4 Hrest4]; subst.
  inversion Hrest4 as [|? ? Hc5 Hrest5]; subst.
  inversion Hrest5 as [|? ? Hc6 Hrest6]; subst.
  inversion Hrest6 as [|? ? Hc7 Hrest7]; subst.
  inversion Hrest7; clear Hcoeffs Hrest0 Hrest1 Hrest2 Hrest3 Hrest4 Hrest5 Hrest6 Hrest7.
  unfold normalize_coeff_block.
  destruct (normalize_coeff_step idx carry arr) as [d0 carry0] eqn:H0.
  destruct (normalize_coeff_step (Uint63.add idx u63_one) carry0 arr) as [d1 carry1] eqn:H1.
  destruct (normalize_coeff_step (Uint63.add idx (Uint63.of_Z 2)) carry1 arr) as [d2 carry2] eqn:H2.
  destruct (normalize_coeff_step (Uint63.add idx u63_three) carry2 arr) as [d3 carry3] eqn:H3.
  destruct (normalize_coeff_step (Uint63.add idx (Uint63.of_Z 4)) carry3 arr) as [d4 carry4] eqn:H4.
  destruct (normalize_coeff_step (Uint63.add idx (Uint63.of_Z 5)) carry4 arr) as [d5 carry5] eqn:H5.
  destruct (normalize_coeff_step (Uint63.add idx (Uint63.of_Z 6)) carry5 arr) as [d6 carry6] eqn:H6.
  destruct (normalize_coeff_step (Uint63.add idx u63_seven) carry6 arr) as [d7 carry7] eqn:H7.
  pose proof (normalize_coeff_step_carry_limit idx carry arr Hc0 Hcarry) as Hcarry0.
  rewrite H0 in Hcarry0; simpl in Hcarry0.
  pose proof (normalize_coeff_step_carry_limit (Uint63.add idx u63_one) carry0 arr Hc1 Hcarry0) as Hcarry1.
  rewrite H1 in Hcarry1; simpl in Hcarry1.
  pose proof (normalize_coeff_step_carry_limit (Uint63.add idx (Uint63.of_Z 2)) carry1 arr Hc2 Hcarry1) as Hcarry2.
  rewrite H2 in Hcarry2; simpl in Hcarry2.
  pose proof (normalize_coeff_step_carry_limit (Uint63.add idx u63_three) carry2 arr Hc3 Hcarry2) as Hcarry3.
  rewrite H3 in Hcarry3; simpl in Hcarry3.
  pose proof (normalize_coeff_step_carry_limit (Uint63.add idx (Uint63.of_Z 4)) carry3 arr Hc4 Hcarry3) as Hcarry4.
  rewrite H4 in Hcarry4; simpl in Hcarry4.
  pose proof (normalize_coeff_step_carry_limit (Uint63.add idx (Uint63.of_Z 5)) carry4 arr Hc5 Hcarry4) as Hcarry5.
  rewrite H5 in Hcarry5; simpl in Hcarry5.
  pose proof (normalize_coeff_step_carry_limit (Uint63.add idx (Uint63.of_Z 6)) carry5 arr Hc6 Hcarry5) as Hcarry6.
  rewrite H6 in Hcarry6; simpl in Hcarry6.
  pose proof (normalize_coeff_step_carry_limit (Uint63.add idx u63_seven) carry6 arr Hc7 Hcarry6) as Hcarry7.
  rewrite H7 in Hcarry7; simpl in Hcarry7.
  simpl.
  exact Hcarry7.
Qed.
