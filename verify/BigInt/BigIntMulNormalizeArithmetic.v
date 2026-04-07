From Coq Require Import Uint63 ZArith Lia Array.PArray.
Require Import BigInt.BigIntMul.

Local Open Scope Z_scope.

Definition coeff_array_at (arr : PArray.array Uint63.int) (idx : Uint63.int) : Uint63.int :=
  if Uint63.ltb idx (PArray.length arr) then PArray.get arr idx else zero_digit.

Lemma digit_shift_to_Z :
  Uint63.to_Z digit_shift = 18.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma digit_mask_ones :
  Uint63.to_Z digit_mask = Z.ones 18.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma normalize_coeff_step_wrapped_value :
  forall idx carry arr,
    let '(digit, carry') := normalize_coeff_step idx carry arr in
    Uint63.to_Z digit + digit_base_z * Uint63.to_Z carry' =
    Uint63.to_Z (Uint63.add (coeff_array_at arr idx) carry).
  Proof.
  intros idx carry arr.
  unfold normalize_coeff_step, coeff_array_at.
  set (coeff := if Uint63.ltb idx (PArray.length arr) then PArray.get arr idx else zero_digit).
  set (total := Uint63.add coeff carry).
  change
    (Uint63.to_Z (Uint63.land total digit_mask) +
     digit_base_z * Uint63.to_Z (Uint63.lsr total digit_shift) =
     Uint63.to_Z total).
  rewrite Uint63.land_spec'.
  rewrite Uint63.lsr_spec.
  rewrite digit_mask_ones.
  rewrite digit_shift_to_Z.
  change digit_base_z with (2 ^ 18).
  assert (Htotal : (0 <= Uint63.to_Z total)%Z).
  {
    apply Uint63.to_Z_bounded.
  }
  rewrite Z.land_ones by lia.
  rewrite Z.add_comm.
  symmetry.
  apply Z.div_mod.
  lia.
Qed.

Lemma normalize_coeff_step_value :
  forall idx carry arr,
    (Uint63.to_Z (coeff_array_at arr idx) + Uint63.to_Z carry < Uint63.wB)%Z ->
    let '(digit, carry') := normalize_coeff_step idx carry arr in
    Uint63.to_Z digit + digit_base_z * Uint63.to_Z carry' =
    Uint63.to_Z (coeff_array_at arr idx) + Uint63.to_Z carry.
Proof.
  intros idx carry arr Hnowrap.
  destruct (normalize_coeff_step idx carry arr) as [digit carry'] eqn:Hstep.
  simpl.
  pose proof (normalize_coeff_step_wrapped_value idx carry arr) as Hwrapped.
  rewrite Hstep in Hwrapped.
  simpl in Hwrapped.
  rewrite Hwrapped.
  rewrite Uint63.add_spec.
  apply Z.mod_small.
  split.
  - pose proof Uint63.to_Z_bounded (coeff_array_at arr idx) as [Hcoeff _].
    pose proof Uint63.to_Z_bounded carry as [Hcarry _].
    lia.
  - exact Hnowrap.
Qed.
