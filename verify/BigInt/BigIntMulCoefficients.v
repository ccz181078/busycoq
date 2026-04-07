From Coq Require Import ZArith Lia Lists.List.
Require Import BigInt.BigIntMul BigInt.BigIntMulProof BigInt.BigIntMulCanonical BigInt.BigIntMulAlgebra.

Import ListNotations.
Local Open Scope Z_scope.

Fixpoint convolution_coeff (xs ys : list Z) (i : nat) : Z :=
  match xs with
  | [] => 0
  | x :: xs' =>
      x * nth i ys 0 +
      match i with
      | O => 0
      | S j => convolution_coeff xs' ys j
      end
  end.

Lemma nth_add_digits :
  forall xs ys i,
    nth i (add_digits xs ys) 0 = nth i xs 0 + nth i ys 0.
Proof.
  induction xs as [|x xs IH]; intros ys i.
  - destruct ys as [|y ys]; destruct i; reflexivity.
  - destruct ys as [|y ys].
    + destruct i; simpl; lia.
    + destruct i; simpl; [lia|apply IH].
Qed.

Lemma nth_scale_digits :
  forall c xs i,
    nth i (scale_digits c xs) 0 = c * nth i xs 0.
Proof.
  intros c xs.
  induction xs as [|x xs IH]; intros i.
  - destruct i; simpl; lia.
  - destruct i; simpl; [lia|apply IH].
Qed.

Lemma nth_convolution_digits :
  forall xs ys i,
    nth i (convolution_digits xs ys) 0 = convolution_coeff xs ys i.
Proof.
  induction xs as [|x xs IH]; intros ys i.
  - destruct i; reflexivity.
  - simpl.
    rewrite nth_add_digits.
    rewrite nth_scale_digits.
    destruct i as [|i].
    + simpl.
      lia.
    + simpl.
      rewrite IH.
      lia.
Qed.

Lemma convolution_coeff_zero_tail :
  forall xs ys i,
    (List.length xs + List.length ys <= S i)%nat ->
    convolution_coeff xs ys i = 0.
Proof.
  induction xs as [|x xs IH]; intros ys i Hlen.
  - reflexivity.
  - destruct i as [|i].
    + simpl.
      assert (Hys : ys = []).
      {
        destruct ys as [|y ys].
        - reflexivity.
        - simpl in Hlen.
          lia.
      }
      subst ys.
      simpl.
      lia.
    + simpl.
      simpl in Hlen.
      assert (Hnth : nth (S i) ys 0 = 0).
      {
        apply nth_overflow.
        lia.
      }
      rewrite Hnth.
      rewrite Z.mul_0_r.
      apply IH.
      lia.
Qed.

Corollary nth_convolution_digits_zero_tail :
  forall xs ys i,
    (List.length xs + List.length ys <= S i)%nat ->
    nth i (convolution_digits xs ys) 0 = 0.
Proof.
  intros xs ys i Hlen.
  rewrite nth_convolution_digits.
  apply convolution_coeff_zero_tail.
  exact Hlen.
Qed.

Lemma nth_range :
  forall xs i bound,
    (0 < bound)%Z ->
    Forall (fun z => (0 <= z < bound)%Z) xs ->
    (0 <= nth i xs 0 < bound)%Z.
Proof.
  intros xs i bound Hbound Hxs.
  eapply (@Forall_nth_default Z (fun z => (0 <= z < bound)%Z) xs 0 i) in Hxs.
  - exact Hxs.
  - lia.
Qed.

Lemma canonical_bigint_digits_z_range :
  forall x,
    canonical_bigint x ->
    Forall (fun z => (0 <= z < digit_base_z)%Z) (bigint_digits_z x).
Proof.
  induction x as [|b bs IH]; intros Hx.
  - constructor.
  - inversion Hx as [|b' bs' Hb Hbs]; subst.
    destruct b as [x0 x1 x2 x3 x4 x5 x6 x7].
    destruct Hb as [Hx0 [Hx1 [Hx2 [Hx3 [Hx4 [Hx5 [Hx6 Hx7]]]]]]].
    simpl.
    unfold canonical_digit in *.
    constructor; [exact Hx0|].
    constructor; [exact Hx1|].
    constructor; [exact Hx2|].
    constructor; [exact Hx3|].
    constructor; [exact Hx4|].
    constructor; [exact Hx5|].
    constructor; [exact Hx6|].
    constructor; [exact Hx7|].
    exact (IH Hbs).
Qed.

Lemma bigint_digits_z_length :
  forall x,
    List.length (bigint_digits_z x) = (8 * List.length x)%nat.
Proof.
  induction x as [|b bs IH].
  - reflexivity.
  - simpl.
    rewrite length_app.
    rewrite limb8_digits_z_length.
    rewrite IH.
    lia.
Qed.
