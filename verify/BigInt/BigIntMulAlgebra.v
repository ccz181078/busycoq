From Coq Require Import ZArith Lia Lists.List.
Require Import BigInt.BigIntMul BigInt.BigIntMulProof.

Import ListNotations.
Local Open Scope Z_scope.

Fixpoint add_digits (xs ys : list Z) : list Z :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x :: xs', y :: ys' => (x + y) :: add_digits xs' ys'
  end.

Definition scale_digits (c : Z) (xs : list Z) : list Z :=
  map (Z.mul c) xs.

Fixpoint convolution_digits (xs ys : list Z) : list Z :=
  match xs with
  | [] => []
  | x :: xs' => add_digits (scale_digits x ys) (0 :: convolution_digits xs' ys)
  end.

Lemma digits_value_add_digits :
  forall base xs ys,
    digits_value_base base (add_digits xs ys) =
    digits_value_base base xs + digits_value_base base ys.
Proof.
  intros base xs ys.
  revert ys.
  induction xs as [|x xs IH]; intros ys.
  - reflexivity.
  - destruct ys as [|y ys].
    + simpl.
      ring.
    + simpl.
      rewrite (IH ys).
      ring.
Qed.

Lemma digits_value_add_digits_concrete :
  forall xs ys,
    digits_value (add_digits xs ys) =
    digits_value xs + digits_value ys.
Proof.
  intros xs ys.
  repeat rewrite digits_value_eq_base.
  apply digits_value_add_digits.
Qed.

Lemma digits_value_scale_digits :
  forall base c xs,
    digits_value_base base (scale_digits c xs) =
    c * digits_value_base base xs.
Proof.
  intros base c xs.
  induction xs as [|x xs IH].
  - simpl.
    ring.
  - simpl.
    rewrite IH.
    ring.
Qed.

Lemma digits_value_scale_digits_concrete :
  forall c xs,
    digits_value (scale_digits c xs) = c * digits_value xs.
Proof.
  intros c xs.
  repeat rewrite digits_value_eq_base.
  apply digits_value_scale_digits.
Qed.

Lemma digits_value_zero_cons :
  forall base xs,
    digits_value_base base (0 :: xs) =
    base * digits_value_base base xs.
Proof.
  intros base xs.
  simpl.
  ring.
Qed.

Lemma digits_value_zero_cons_concrete :
  forall xs,
    digits_value (0 :: xs) = digit_base_z * digits_value xs.
Proof.
  intros xs.
  repeat rewrite digits_value_eq_base.
  apply digits_value_zero_cons.
Qed.

Lemma digits_value_convolution_digits :
  forall base xs ys,
    digits_value_base base (convolution_digits xs ys) =
    digits_value_base base xs * digits_value_base base ys.
Proof.
  intros base xs ys.
  revert ys.
  induction xs as [|x xs IH]; intros ys.
  - reflexivity.
  - simpl.
    rewrite (digits_value_add_digits base).
    rewrite (digits_value_scale_digits base).
    rewrite (digits_value_zero_cons base).
    rewrite (IH ys).
    simpl.
    ring.
Qed.

Lemma digits_value_convolution_digits_concrete :
  forall xs ys,
    digits_value (convolution_digits xs ys) =
    digits_value xs * digits_value ys.
Proof.
  intros xs ys.
  repeat rewrite digits_value_eq_base.
  apply digits_value_convolution_digits.
Qed.

Corollary bigint_value_digits_convolution :
  forall a b,
    digits_value (convolution_digits (bigint_digits_z a) (bigint_digits_z b)) =
    bigint_value a * bigint_value b.
Proof.
  intros a b.
  unfold bigint_value.
  apply digits_value_convolution_digits_concrete.
Qed.
