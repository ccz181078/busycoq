From Coq Require Import Uint63 Lists.List ZArith.
Require Import BigInt.BigIntMul.

Import ListNotations.

Definition small_modulus : Uint63.int := Uint63.of_Z 1237%Z.
Definition digit_base_mod_small : Uint63.int := Uint63.mod digit_base small_modulus.

Definition three_bigint : bigint := bigint_of_digits_z [3%Z].

Definition add_mul_mod_small (acc coeff weight : Uint63.int) : Uint63.int :=
  Uint63.mod (Uint63.add acc (Uint63.mul coeff weight)) small_modulus.

Definition step_digit_small
    (state : Uint63.int * Uint63.int) (digit : Uint63.int)
    : Uint63.int * Uint63.int :=
  let '(acc, weight) := state in
  ( add_mul_mod_small acc digit weight,
    Uint63.mod (Uint63.mul weight digit_base_mod_small) small_modulus ).

Definition limb8_mod_small
    (state : Uint63.int * Uint63.int) (x : limb8) : Uint63.int * Uint63.int :=
  let '{| d0 := x0; d1 := x1; d2 := x2; d3 := x3;
          d4 := x4; d5 := x5; d6 := x6; d7 := x7 |} := x in
  let s0 := step_digit_small state x0 in
  let s1 := step_digit_small s0 x1 in
  let s2 := step_digit_small s1 x2 in
  let s3 := step_digit_small s2 x3 in
  let s4 := step_digit_small s3 x4 in
  let s5 := step_digit_small s4 x5 in
  let s6 := step_digit_small s5 x6 in
  step_digit_small s6 x7.

Fixpoint bigint_mod_small_acc
    (xs : bigint) (state : Uint63.int * Uint63.int) : Uint63.int :=
  match xs with
  | [] => fst state
  | x :: xs' => bigint_mod_small_acc xs' (limb8_mod_small state x)
  end.

Definition bigint_mod_small (x : bigint) : Uint63.int :=
  bigint_mod_small_acc x (Uint63.of_Z 0%Z, Uint63.of_Z 1%Z).

Definition square_bigint (x : bigint) : option bigint :=
  mul_bigint x x.

Definition square_bigint_or_nil (x : bigint) : bigint :=
  match square_bigint x with
  | Some y => y
  | None => []
  end.

Fixpoint pow_two_bigint (i : nat) : bigint :=
  match i with
  | O => three_bigint
  | S j => square_bigint_or_nil (pow_two_bigint j)
  end.

Definition pow_two_bigint_mod_small (i : nat) : Uint63.int :=
  bigint_mod_small (pow_two_bigint i).

Time Definition pow_0_mod_small : Uint63.int := Eval native_compute in pow_two_bigint_mod_small 0%nat.
Time Definition pow_1_mod_small : Uint63.int := Eval native_compute in pow_two_bigint_mod_small 1%nat.
Time Definition pow_2_mod_small : Uint63.int := Eval native_compute in pow_two_bigint_mod_small 2%nat.
Time Definition pow_3_mod_small : Uint63.int := Eval native_compute in pow_two_bigint_mod_small 3%nat.
Time Definition pow_4_mod_small : Uint63.int := Eval native_compute in pow_two_bigint_mod_small 4%nat.
Time Definition pow_5_mod_small : Uint63.int := Eval native_compute in pow_two_bigint_mod_small 5%nat.
Time Definition pow_6_mod_small : Uint63.int := Eval native_compute in pow_two_bigint_mod_small 6%nat.
Time Definition pow_7_mod_small : Uint63.int := Eval native_compute in pow_two_bigint_mod_small 7%nat.
Time Definition pow_8_mod_small : Uint63.int := Eval native_compute in pow_two_bigint_mod_small 8%nat.
Time Definition pow_9_mod_small : Uint63.int := Eval native_compute in pow_two_bigint_mod_small 9%nat.
Time Definition pow_10_mod_small : Uint63.int := Eval native_compute in pow_two_bigint_mod_small 10%nat.
Time Definition pow_11_mod_small : Uint63.int := Eval native_compute in pow_two_bigint_mod_small 11%nat.
Time Definition pow_12_mod_small : Uint63.int := Eval native_compute in pow_two_bigint_mod_small 12%nat.
Time Definition pow_13_mod_small : Uint63.int := Eval native_compute in pow_two_bigint_mod_small 13%nat.
Time Definition pow_14_mod_small : Uint63.int := Eval native_compute in pow_two_bigint_mod_small 14%nat.
Time Definition pow_15_mod_small : Uint63.int := Eval native_compute in pow_two_bigint_mod_small 15%nat.
Time Definition pow_16_mod_small : Uint63.int := Eval native_compute in pow_two_bigint_mod_small 16%nat.
Time Definition pow_17_mod_small : Uint63.int := Eval native_compute in pow_two_bigint_mod_small 17%nat.
Time Definition pow_18_mod_small : Uint63.int := Eval native_compute in pow_two_bigint_mod_small 18%nat.
Time Definition pow_19_mod_small : Uint63.int := Eval native_compute in pow_two_bigint_mod_small 19%nat.
Time Definition pow_20_mod_small : Uint63.int := Eval native_compute in pow_two_bigint_mod_small 20%nat.
Time Definition pow_21_mod_small : Uint63.int := Eval native_compute in pow_two_bigint_mod_small 21%nat.
Time Definition pow_22_mod_small : Uint63.int := Eval native_compute in pow_two_bigint_mod_small 22%nat.
Time Definition pow_23_mod_small : Uint63.int := Eval native_compute in pow_two_bigint_mod_small 23%nat.

Definition three_pow_two_table : list Uint63.int :=
  [ pow_0_mod_small;
    pow_1_mod_small;
    pow_2_mod_small;
    pow_3_mod_small;
    pow_4_mod_small;
    pow_5_mod_small;
    pow_6_mod_small;
    pow_7_mod_small;
    pow_8_mod_small;
    pow_9_mod_small;
    pow_10_mod_small;
    pow_11_mod_small;
    pow_12_mod_small;
    pow_13_mod_small;
    pow_14_mod_small;
    pow_15_mod_small;
    pow_16_mod_small;
    pow_17_mod_small;
    pow_18_mod_small;
    pow_19_mod_small;
    pow_20_mod_small;
    pow_21_mod_small;
    pow_22_mod_small;
    pow_23_mod_small ].

Time Eval native_compute in three_pow_two_table.
