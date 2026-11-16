From Coq Require Import Uint63 ZArith NArith Lia Lists.List Arith.PeanoNat Array.PArray.
Require Import BigInt.NTTTree BigInt.NTTConcrete.

Import ListNotations.
Local Open Scope Z_scope.

Definition digit_base_z : Z := 262144.
Definition digit_base : Uint63.int := Uint63.of_Z digit_base_z.
Definition digit_mask : Uint63.int := Uint63.of_Z (digit_base_z - 1).
Definition digit_shift : Uint63.int := Uint63.of_Z 18.

Definition supported_max_log : nat := 23%nat.
Definition supported_max_block_log : nat := 20%nat.
Definition coeff_array_max_digits : nat := 4194303%nat.

Record limb8 := Limb8
  { d0 : Uint63.int;
    d1 : Uint63.int;
    d2 : Uint63.int;
    d3 : Uint63.int;
    d4 : Uint63.int;
    d5 : Uint63.int;
    d6 : Uint63.int;
    d7 : Uint63.int }.

Definition bigint := list limb8.

Definition zero_digit : Uint63.int := Uint63.of_Z 0.

Definition zero_limb8 : limb8 :=
  Limb8 zero_digit zero_digit zero_digit zero_digit
    zero_digit zero_digit zero_digit zero_digit.

Definition u63_one : Uint63.int := Uint63.of_Z 1.
Definition u63_three : Uint63.int := Uint63.of_Z 3.
Definition u63_seven : Uint63.int := Uint63.of_Z 7.
Definition u63_eight : Uint63.int := Uint63.of_Z 8.

Definition limb_index_shift : Uint63.int := Uint63.of_Z 3.

Fixpoint tree_map {A B : Type} (n : nat) (f : A -> B) : tree A n -> tree B n :=
  match n with
  | O => f
  | S m =>
      fun t =>
        let '(l, r) := t in
        (tree_map m f l, tree_map m f r)
  end.

Fixpoint tree_zip {A B C : Type} (n : nat) (f : A -> B -> C)
    : tree A n -> tree B n -> tree C n :=
  match n with
  | O => f
  | S m =>
      fun x y =>
        let '(xl, xr) := x in
        let '(yl, yr) := y in
        (tree_zip m f xl yl, tree_zip m f xr yr)
  end.

Fixpoint take_tree {A : Type} (zero : A) (n : nat)
    : list A -> tree A n * list A :=
  match n with
  | O =>
      fun xs =>
        match xs with
        | [] => (zero, [])
        | x :: xs' => (x, xs')
        end
  | S m =>
      fun xs =>
        let '(l, xs1) := take_tree zero m xs in
        let '(r, xs2) := take_tree zero m xs1 in
        ((l, r), xs2)
  end.

Definition list_to_tree {A : Type} (zero : A) (n : nat) (xs : list A) : tree A n :=
  fst (take_tree zero n xs).

Fixpoint split_even_odd_acc {A : Type} (xs evens odds : list A) : list A * list A :=
  match xs with
  | [] => (rev evens, rev odds)
  | x :: xs1 =>
      match xs1 with
      | [] => (rev (x :: evens), rev odds)
      | y :: xs2 =>
          split_even_odd_acc xs2 (x :: evens) (y :: odds)
      end
  end.

Definition split_even_odd {A : Type} (xs : list A) : list A * list A :=
  split_even_odd_acc xs [] [].

Fixpoint list_to_input_tree {A : Type} (zero : A) (n : nat) (xs : list A) : tree A n :=
  match n with
  | O =>
      match xs with
      | [] => zero
      | x :: _ => x
      end
  | S m =>
      let '(evens, odds) := split_even_odd xs in
      (list_to_input_tree zero m evens, list_to_input_tree zero m odds)
  end.

Fixpoint interleave_acc {A : Type} (xs ys acc : list A) : list A :=
  match xs, ys with
  | [], _ => rev_append acc ys
  | _, [] => rev_append acc xs
  | x :: xs', y :: ys' => interleave_acc xs' ys' (y :: x :: acc)
  end.

Definition interleave {A : Type} (xs ys : list A) : list A :=
  interleave_acc xs ys [].

Fixpoint tree_to_list_acc {A : Type} (n : nat) : tree A n -> list A -> list A :=
  match n with
  | O => fun t acc => t :: acc
  | S m =>
      fun t acc =>
        let '(l, r) := t in
        tree_to_list_acc m l (tree_to_list_acc m r acc)
  end.

Definition tree_to_list {A : Type} (n : nat) (t : tree A n) : list A :=
  tree_to_list_acc n t [].

Fixpoint input_tree_to_list {A : Type} (n : nat) : tree A n -> list A :=
  match n with
  | O => fun t => [t]
  | S m =>
      fun t =>
        let '(l, r) := t in
        interleave (input_tree_to_list m l) (input_tree_to_list m r)
  end.

Fixpoint block_log_aux (fuel need len k : nat) : nat :=
  match fuel with
  | O => k
  | S fuel' =>
      if Nat.leb need len then k
      else block_log_aux fuel' need (len * 2)%nat (S k)
  end.

Definition block_log (need : nat) : nat :=
  block_log_aux (S need) (Nat.max 1 need)%nat 1%nat 0%nat.

Definition transform_log_of_block_log (k : nat) : nat := (k + 3)%nat.

Definition limb8_digits_u63 (x : limb8) : list Uint63.int :=
  let '{| d0 := x0; d1 := x1; d2 := x2; d3 := x3;
          d4 := x4; d5 := x5; d6 := x6; d7 := x7 |} := x in
  [x0; x1; x2; x3; x4; x5; x6; x7].

Fixpoint bigint_digits_u63_rev (x : bigint) (acc : list Uint63.int) : list Uint63.int :=
  match x with
  | [] => acc
  | b :: bs => bigint_digits_u63_rev bs (rev_append (limb8_digits_u63 b) acc)
  end.

Definition bigint_digits_u63 (x : bigint) : list Uint63.int :=
  rev (bigint_digits_u63_rev x []).

Definition limb8_digits_z (x : limb8) : list Z :=
  map Uint63.to_Z (limb8_digits_u63 x).

Fixpoint bigint_digits_z (x : bigint) : list Z :=
  match x with
  | [] => []
  | b :: bs => limb8_digits_z b ++ bigint_digits_z bs
  end.

Fixpoint digits_value (digits : list Z) : Z :=
  match digits with
  | [] => 0
  | d :: ds => d + digit_base_z * digits_value ds
  end.

Definition bigint_value (x : bigint) : Z :=
  digits_value (bigint_digits_z x).

Definition limb8_eqb (x y : limb8) : bool :=
  let '{| d0 := x0; d1 := x1; d2 := x2; d3 := x3;
          d4 := x4; d5 := x5; d6 := x6; d7 := x7 |} := x in
  let '{| d0 := y0; d1 := y1; d2 := y2; d3 := y3;
          d4 := y4; d5 := y5; d6 := y6; d7 := y7 |} := y in
  Uint63.eqb x0 y0 &&
  Uint63.eqb x1 y1 &&
  Uint63.eqb x2 y2 &&
  Uint63.eqb x3 y3 &&
  Uint63.eqb x4 y4 &&
  Uint63.eqb x5 y5 &&
  Uint63.eqb x6 y6 &&
  Uint63.eqb x7 y7.

Fixpoint drop_zero_prefix (xs : bigint) : bigint :=
  match xs with
  | [] => []
  | x :: xs' => if limb8_eqb x zero_limb8 then drop_zero_prefix xs' else xs
  end.

Definition trim_bigint (x : bigint) : bigint :=
  rev (drop_zero_prefix (rev x)).

Definition split_digits8 (xs : list Uint63.int) : limb8 * list Uint63.int :=
  match xs with
  | x0 :: xs1 =>
      match xs1 with
      | x1 :: xs2 =>
          match xs2 with
          | x2 :: xs3 =>
              match xs3 with
              | x3 :: xs4 =>
                  match xs4 with
                  | x4 :: xs5 =>
                      match xs5 with
                      | x5 :: xs6 =>
                          match xs6 with
                          | x6 :: xs7 =>
                              match xs7 with
                              | x7 :: rest => (Limb8 x0 x1 x2 x3 x4 x5 x6 x7, rest)
                              | [] => (Limb8 x0 x1 x2 x3 x4 x5 x6 zero_digit, [])
                              end
                          | [] => (Limb8 x0 x1 x2 x3 x4 x5 zero_digit zero_digit, [])
                          end
                      | [] => (Limb8 x0 x1 x2 x3 x4 zero_digit zero_digit zero_digit, [])
                      end
                  | [] => (Limb8 x0 x1 x2 x3 zero_digit zero_digit zero_digit zero_digit, [])
                  end
              | [] => (Limb8 x0 x1 x2 zero_digit zero_digit zero_digit zero_digit zero_digit, [])
              end
          | [] => (Limb8 x0 x1 zero_digit zero_digit zero_digit zero_digit zero_digit zero_digit, [])
          end
      | [] => (Limb8 x0 zero_digit zero_digit zero_digit zero_digit zero_digit zero_digit zero_digit, [])
      end
  | [] => (zero_limb8, [])
  end.

Fixpoint digits_to_bigint_rev_aux (fuel : nat) (xs : list Uint63.int) (acc : bigint) : bigint :=
  match fuel with
  | O => acc
  | S fuel' =>
      match xs with
      | [] => acc
      | _ =>
          let '(block, rest) := split_digits8 xs in
          digits_to_bigint_rev_aux fuel' rest (block :: acc)
      end
  end.

Definition digits_to_bigint (xs : list Uint63.int) : bigint :=
  trim_bigint (rev (digits_to_bigint_rev_aux (List.length xs) xs [])).

Definition bigint_of_digits_z (xs : list Z) : bigint :=
  digits_to_bigint (map Uint63.of_Z xs).

Definition digit_base_N : N := 262144%N.
Definition digit_mask_N : N := 262143%N.
Definition digit_shift_nat : nat := 18%nat.

Fixpoint digits_to_N (digits : list Uint63.int) : N :=
  match digits with
  | [] => 0%N
  | d :: ds => (Z.to_N (Uint63.to_Z d) + digit_base_N * digits_to_N ds)%N
  end.

Definition bigint_to_N (x : bigint) : N :=
  digits_to_N (bigint_digits_u63 x).

Fixpoint digits_of_N_aux (fuel : nat) (x : N) : list Uint63.int :=
  match fuel with
  | O => []
  | S fuel' =>
      if N.eqb x 0%N then []
      else
        Uint63.of_Z (Z.of_N (N.land x digit_mask_N)) ::
        digits_of_N_aux fuel' (N.shiftr x (N.of_nat digit_shift_nat))
  end.

Definition bigint_of_N (x : N) : bigint :=
  digits_to_bigint (digits_of_N_aux (S (N.to_nat (N.size x))) x).

Definition add_digit_with_carry
    (x y carry : Uint63.int) : Uint63.int * Uint63.int :=
  let total := Uint63.add (Uint63.add x y) carry in
  (Uint63.land total digit_mask, Uint63.lsr total digit_shift).

Definition add_limb8_with_carry
    (x y : limb8) (carry : Uint63.int) : limb8 * Uint63.int :=
  let '(x0, y0) := (d0 x, d0 y) in
  let '(x1, y1) := (d1 x, d1 y) in
  let '(x2, y2) := (d2 x, d2 y) in
  let '(x3, y3) := (d3 x, d3 y) in
  let '(x4, y4) := (d4 x, d4 y) in
  let '(x5, y5) := (d5 x, d5 y) in
  let '(x6, y6) := (d6 x, d6 y) in
  let '(x7, y7) := (d7 x, d7 y) in
  let '(z0, c0) := add_digit_with_carry x0 y0 carry in
  let '(z1, c1) := add_digit_with_carry x1 y1 c0 in
  let '(z2, c2) := add_digit_with_carry x2 y2 c1 in
  let '(z3, c3) := add_digit_with_carry x3 y3 c2 in
  let '(z4, c4) := add_digit_with_carry x4 y4 c3 in
  let '(z5, c5) := add_digit_with_carry x5 y5 c4 in
  let '(z6, c6) := add_digit_with_carry x6 y6 c5 in
  let '(z7, c7) := add_digit_with_carry x7 y7 c6 in
  (Limb8 z0 z1 z2 z3 z4 z5 z6 z7, c7).

Definition cons_block_if_needed (x : limb8) (xs : bigint) : bigint :=
  match xs with
  | [] => if limb8_eqb x zero_limb8 then [] else [x]
  | _ => x :: xs
  end.

Fixpoint add_bigint_aux (fuel : nat) (carry : Uint63.int)
    (xs ys : bigint) : bigint :=
  match fuel with
  | O => []
  | S fuel' =>
      match xs, ys with
      | [], [] =>
          if Uint63.eqb carry zero_digit then []
          else [Limb8 carry zero_digit zero_digit zero_digit
                  zero_digit zero_digit zero_digit zero_digit]
      | x :: xs', [] =>
          let '(block, carry') := add_limb8_with_carry x zero_limb8 carry in
          cons_block_if_needed block (add_bigint_aux fuel' carry' xs' [])
      | [], y :: ys' =>
          let '(block, carry') := add_limb8_with_carry zero_limb8 y carry in
          cons_block_if_needed block (add_bigint_aux fuel' carry' [] ys')
      | x :: xs', y :: ys' =>
          let '(block, carry') := add_limb8_with_carry x y carry in
          cons_block_if_needed block (add_bigint_aux fuel' carry' xs' ys')
      end
  end.

Definition bigint_add (x y : bigint) : bigint :=
  add_bigint_aux (S (Nat.max (List.length x) (List.length y))) zero_digit x y.

Definition mul_digit_with_carry
    (m x carry : Uint63.int) : Uint63.int * Uint63.int :=
  let total := Uint63.add (Uint63.mul m x) carry in
  (Uint63.land total digit_mask, Uint63.lsr total digit_shift).

Definition mul_limb8_digit_with_carry
    (m : Uint63.int) (x : limb8) (carry : Uint63.int) : limb8 * Uint63.int :=
  let '(z0, c0) := mul_digit_with_carry m (d0 x) carry in
  let '(z1, c1) := mul_digit_with_carry m (d1 x) c0 in
  let '(z2, c2) := mul_digit_with_carry m (d2 x) c1 in
  let '(z3, c3) := mul_digit_with_carry m (d3 x) c2 in
  let '(z4, c4) := mul_digit_with_carry m (d4 x) c3 in
  let '(z5, c5) := mul_digit_with_carry m (d5 x) c4 in
  let '(z6, c6) := mul_digit_with_carry m (d6 x) c5 in
  let '(z7, c7) := mul_digit_with_carry m (d7 x) c6 in
  (Limb8 z0 z1 z2 z3 z4 z5 z6 z7, c7).

Fixpoint bigint_mul_digit_aux (fuel : nat) (m carry : Uint63.int)
    (xs : bigint) : bigint :=
  match fuel with
  | O => []
  | S fuel' =>
      match xs with
      | [] =>
          if Uint63.eqb carry zero_digit then []
          else [Limb8 carry zero_digit zero_digit zero_digit
                  zero_digit zero_digit zero_digit zero_digit]
      | x :: xs' =>
          let '(block, carry') := mul_limb8_digit_with_carry m x carry in
          cons_block_if_needed block (bigint_mul_digit_aux fuel' m carry' xs')
      end
  end.

Definition bigint_mul_digit (m : Uint63.int) (x : bigint) : bigint :=
  if Uint63.eqb m zero_digit then []
  else if Uint63.eqb m u63_one then x
  else bigint_mul_digit_aux (S (List.length x)) m zero_digit x.

Definition limb8_high_zero (x : limb8) : bool :=
  Uint63.eqb (d1 x) zero_digit &&
  Uint63.eqb (d2 x) zero_digit &&
  Uint63.eqb (d3 x) zero_digit &&
  Uint63.eqb (d4 x) zero_digit &&
  Uint63.eqb (d5 x) zero_digit &&
  Uint63.eqb (d6 x) zero_digit &&
  Uint63.eqb (d7 x) zero_digit.

Definition bigint_as_digit (x : bigint) : option Uint63.int :=
  match x with
  | [] => Some zero_digit
  | [b] => if limb8_high_zero b then Some (d0 b) else None
  | _ => None
  end.

Definition limb8_take_digits (k : nat) (x : limb8) : limb8 :=
  let '{| d0 := x0; d1 := x1; d2 := x2; d3 := x3;
          d4 := x4; d5 := x5; d6 := x6; d7 := x7 |} := x in
  match k with
  | O => zero_limb8
  | S O => Limb8 x0 zero_digit zero_digit zero_digit zero_digit zero_digit zero_digit zero_digit
  | S (S O) => Limb8 x0 x1 zero_digit zero_digit zero_digit zero_digit zero_digit zero_digit
  | S (S (S O)) => Limb8 x0 x1 x2 zero_digit zero_digit zero_digit zero_digit zero_digit
  | S (S (S (S O))) => Limb8 x0 x1 x2 x3 zero_digit zero_digit zero_digit zero_digit
  | S (S (S (S (S O)))) => Limb8 x0 x1 x2 x3 x4 zero_digit zero_digit zero_digit
  | S (S (S (S (S (S O))))) => Limb8 x0 x1 x2 x3 x4 x5 zero_digit zero_digit
  | S (S (S (S (S (S (S O)))))) => Limb8 x0 x1 x2 x3 x4 x5 x6 zero_digit
  | _ => x
  end.

Definition limb8_single_digit (d : Uint63.int) : limb8 :=
  Limb8 d zero_digit zero_digit zero_digit zero_digit zero_digit zero_digit zero_digit.

Definition snoc_nonzero_block (xs : bigint) (x : limb8) : bigint :=
  if limb8_eqb x zero_limb8 then xs else xs ++ [x].

Definition limb8_set_digit (slot : nat) (d : Uint63.int) (x : limb8) : limb8 :=
  let '{| d0 := x0; d1 := x1; d2 := x2; d3 := x3;
          d4 := x4; d5 := x5; d6 := x6; d7 := x7 |} := x in
  match slot with
  | O => Limb8 d x1 x2 x3 x4 x5 x6 x7
  | S O => Limb8 x0 d x2 x3 x4 x5 x6 x7
  | S (S O) => Limb8 x0 x1 d x3 x4 x5 x6 x7
  | S (S (S O)) => Limb8 x0 x1 x2 d x4 x5 x6 x7
  | S (S (S (S O))) => Limb8 x0 x1 x2 x3 d x5 x6 x7
  | S (S (S (S (S O)))) => Limb8 x0 x1 x2 x3 x4 d x6 x7
  | S (S (S (S (S (S O))))) => Limb8 x0 x1 x2 x3 x4 x5 d x7
  | _ => Limb8 x0 x1 x2 x3 x4 x5 x6 d
  end.

Fixpoint bigint_set_digit_at
    (block_index slot : nat) (xs : bigint) (d : Uint63.int) : bigint :=
  match block_index, xs with
  | O, [] => [limb8_set_digit slot d zero_limb8]
  | O, x :: xs' => limb8_set_digit slot d x :: xs'
  | S block_index', [] => zero_limb8 :: bigint_set_digit_at block_index' slot [] d
  | S block_index', x :: xs' =>
      x :: bigint_set_digit_at block_index' slot xs' d
  end.

Definition bigint_append_digit (digit_count : nat) (xs : bigint) (d : Uint63.int) : bigint :=
  if Uint63.eqb d zero_digit then xs
  else
    bigint_set_digit_at
      (Nat.div digit_count 8%nat)
      (Nat.modulo digit_count 8%nat)
      xs d.

Definition shift_right_limb8_digits_small (k : nat) (carry x : limb8)
    : limb8 * limb8 :=
  let '{| d0 := c0; d1 := c1; d2 := c2; d3 := c3;
          d4 := c4; d5 := c5; d6 := c6; d7 := c7 |} := carry in
  let '{| d0 := x0; d1 := x1; d2 := x2; d3 := x3;
          d4 := x4; d5 := x5; d6 := x6; d7 := x7 |} := x in
  match k with
  | O => (x, zero_limb8)
  | S O =>
      (Limb8 x1 x2 x3 x4 x5 x6 x7 c0, limb8_take_digits 1%nat x)
  | S (S O) =>
      (Limb8 x2 x3 x4 x5 x6 x7 c0 c1, limb8_take_digits 2%nat x)
  | S (S (S O)) =>
      (Limb8 x3 x4 x5 x6 x7 c0 c1 c2, limb8_take_digits 3%nat x)
  | S (S (S (S O))) =>
      (Limb8 x4 x5 x6 x7 c0 c1 c2 c3, limb8_take_digits 4%nat x)
  | S (S (S (S (S O)))) =>
      (Limb8 x5 x6 x7 c0 c1 c2 c3 c4, limb8_take_digits 5%nat x)
  | S (S (S (S (S (S O))))) =>
      (Limb8 x6 x7 c0 c1 c2 c3 c4 c5, limb8_take_digits 6%nat x)
  | S (S (S (S (S (S (S O)))))) =>
      (Limb8 x7 c0 c1 c2 c3 c4 c5 c6, limb8_take_digits 7%nat x)
  | _ => (zero_limb8, x)
  end.

Fixpoint shift_right_bigint_digits_small_aux (k : nat) (carry : limb8)
    (rev_blocks acc : bigint) : bigint :=
  match rev_blocks with
  | [] => acc
  | b :: bs =>
      let '(b', carry') := shift_right_limb8_digits_small k carry b in
      shift_right_bigint_digits_small_aux k carry' bs (b' :: acc)
  end.

Definition shift_right_bigint_digits_small (k : nat) (x : bigint) : bigint :=
  trim_bigint (shift_right_bigint_digits_small_aux k zero_limb8 (rev x) []).

Definition bigint_split_whole_digits (whole_digits : nat) (x : bigint)
    : bigint * bigint :=
  let whole_blocks := Nat.div whole_digits 8%nat in
  let rem_digits := Nat.modulo whole_digits 8%nat in
  let low_blocks := firstn whole_blocks x in
  let high_blocks := skipn whole_blocks x in
  match rem_digits with
  | O => (trim_bigint high_blocks, trim_bigint low_blocks)
  | _ =>
      let extra_low :=
        match high_blocks with
        | [] => zero_limb8
        | b :: _ => limb8_take_digits rem_digits b
        end in
      ( shift_right_bigint_digits_small rem_digits high_blocks,
        trim_bigint (snoc_nonzero_block low_blocks extra_low) )
  end.

Definition shift_right_digit_small
    (shift low_mask shift_left carry d : Uint63.int)
    : Uint63.int * Uint63.int :=
  ( Uint63.lor (Uint63.lsr d shift) (Uint63.lsl carry shift_left),
    Uint63.land d low_mask ).

Definition shift_right_limb8_small
    (shift low_mask shift_left carry : Uint63.int) (x : limb8)
    : limb8 * Uint63.int :=
  let '{| d0 := x0; d1 := x1; d2 := x2; d3 := x3;
          d4 := x4; d5 := x5; d6 := x6; d7 := x7 |} := x in
  let '(y7, c7) := shift_right_digit_small shift low_mask shift_left carry x7 in
  let '(y6, c6) := shift_right_digit_small shift low_mask shift_left c7 x6 in
  let '(y5, c5) := shift_right_digit_small shift low_mask shift_left c6 x5 in
  let '(y4, c4) := shift_right_digit_small shift low_mask shift_left c5 x4 in
  let '(y3, c3) := shift_right_digit_small shift low_mask shift_left c4 x3 in
  let '(y2, c2) := shift_right_digit_small shift low_mask shift_left c3 x2 in
  let '(y1, c1) := shift_right_digit_small shift low_mask shift_left c2 x1 in
  let '(y0, c0) := shift_right_digit_small shift low_mask shift_left c1 x0 in
  (Limb8 y0 y1 y2 y3 y4 y5 y6 y7, c0).

Fixpoint shift_right_bigint_small_aux
    (shift low_mask shift_left carry : Uint63.int)
    (rev_blocks acc : bigint) : bigint :=
  match rev_blocks with
  | [] => acc
  | b :: bs =>
      let '(b', carry') := shift_right_limb8_small shift low_mask shift_left carry b in
      shift_right_bigint_small_aux shift low_mask shift_left carry' bs (b' :: acc)
  end.

Definition shift_right_bigint_small (bits : nat) (x : bigint) : bigint :=
  let shift := Uint63.of_Z (Z.of_nat bits) in
  let low_mask := Uint63.sub (Uint63.lsl u63_one shift) u63_one in
  let shift_left := Uint63.sub digit_shift shift in
  trim_bigint (shift_right_bigint_small_aux shift low_mask shift_left zero_digit (rev x) []).

Definition bigint_divmod_pow2 (n : nat) (x : bigint) : bigint * bigint :=
  let whole_digits := Nat.div n digit_shift_nat in
  let rem_bits := Nat.modulo n digit_shift_nat in
  if Nat.leb (8 * List.length x)%nat whole_digits then ([], x)
  else
    let '(high_digits, low_digits) := bigint_split_whole_digits whole_digits x in
    match rem_bits with
    | O => (high_digits, low_digits)
    | S _ =>
        let shift := Uint63.of_Z (Z.of_nat rem_bits) in
        let low_mask := Uint63.sub (Uint63.lsl u63_one shift) u63_one in
        let extra_low :=
          match high_digits with
          | [] => zero_digit
          | b :: _ => Uint63.land (d0 b) low_mask
          end in
        ( shift_right_bigint_small rem_bits high_digits,
          trim_bigint (bigint_append_digit whole_digits low_digits extra_low) )
    end.

Fixpoint normalize_digits_aux (fuel : nat) (carry : Z) (coeffs : list Z)
    : list Uint63.int :=
  match fuel with
  | O => []
  | S fuel' =>
      match coeffs with
      | [] =>
          if Z.eqb carry 0 then []
          else
            let digit := Z.modulo carry digit_base_z in
            Uint63.of_Z digit ::
            normalize_digits_aux fuel' (Z.div carry digit_base_z) []
      | c :: cs =>
          let total := c + carry in
          let digit := Z.modulo total digit_base_z in
          Uint63.of_Z digit ::
          normalize_digits_aux fuel' (Z.div total digit_base_z) cs
      end
  end.

Definition normalize_coeffs (coeffs : list Z) : list Uint63.int :=
  normalize_digits_aux (S (List.length coeffs)) 0 coeffs.

Module Prime469Ops.
  Module T := Prime469.

  Definition zero_block : T.block8 :=
    T.Block8 zero_digit zero_digit zero_digit zero_digit
      zero_digit zero_digit zero_digit zero_digit.

  Definition mul_block (x y : T.block8) : T.block8 :=
    let '{| T.b0 := x0; T.b1 := x1; T.b2 := x2; T.b3 := x3;
            T.b4 := x4; T.b5 := x5; T.b6 := x6; T.b7 := x7 |} := x in
    let '{| T.b0 := y0; T.b1 := y1; T.b2 := y2; T.b3 := y3;
            T.b4 := y4; T.b5 := y5; T.b6 := y6; T.b7 := y7 |} := y in
    T.Block8
      (T.mul_mod_fast x0 y0) (T.mul_mod_fast x1 y1)
      (T.mul_mod_fast x2 y2) (T.mul_mod_fast x3 y3)
      (T.mul_mod_fast x4 y4) (T.mul_mod_fast x5 y5)
      (T.mul_mod_fast x6 y6) (T.mul_mod_fast x7 y7).

  Definition scale_block (c : T.int) (x : T.block8) : T.block8 :=
    let '{| T.b0 := x0; T.b1 := x1; T.b2 := x2; T.b3 := x3;
            T.b4 := x4; T.b5 := x5; T.b6 := x6; T.b7 := x7 |} := x in
    T.Block8
      (T.mul_mod_fast c x0) (T.mul_mod_fast c x1)
      (T.mul_mod_fast c x2) (T.mul_mod_fast c x3)
      (T.mul_mod_fast c x4) (T.mul_mod_fast c x5)
      (T.mul_mod_fast c x6) (T.mul_mod_fast c x7).

  Definition convolution_blocks (k : nat)
      (a b : tree T.block8 k) : tree T.block8 k :=
    let fa := T.ntt_fast_block8_ge3 k a in
    let fb := T.ntt_fast_block8_ge3 k b in
    let freq := tree_zip k mul_block fa fb in
    let raw := T.intt_fast_block8_ge3_raw k freq in
    tree_map k (scale_block (T.inv_pow2 (transform_log_of_block_log k))) raw.
End Prime469Ops.

Module Prime181Ops.
  Module T := Prime181.

  Definition zero_block : T.block8 :=
    T.Block8 zero_digit zero_digit zero_digit zero_digit
      zero_digit zero_digit zero_digit zero_digit.

  Definition mul_block (x y : T.block8) : T.block8 :=
    let '{| T.b0 := x0; T.b1 := x1; T.b2 := x2; T.b3 := x3;
            T.b4 := x4; T.b5 := x5; T.b6 := x6; T.b7 := x7 |} := x in
    let '{| T.b0 := y0; T.b1 := y1; T.b2 := y2; T.b3 := y3;
            T.b4 := y4; T.b5 := y5; T.b6 := y6; T.b7 := y7 |} := y in
    T.Block8
      (T.mul_mod_fast x0 y0) (T.mul_mod_fast x1 y1)
      (T.mul_mod_fast x2 y2) (T.mul_mod_fast x3 y3)
      (T.mul_mod_fast x4 y4) (T.mul_mod_fast x5 y5)
      (T.mul_mod_fast x6 y6) (T.mul_mod_fast x7 y7).

  Definition scale_block (c : T.int) (x : T.block8) : T.block8 :=
    let '{| T.b0 := x0; T.b1 := x1; T.b2 := x2; T.b3 := x3;
            T.b4 := x4; T.b5 := x5; T.b6 := x6; T.b7 := x7 |} := x in
    T.Block8
      (T.mul_mod_fast c x0) (T.mul_mod_fast c x1)
      (T.mul_mod_fast c x2) (T.mul_mod_fast c x3)
      (T.mul_mod_fast c x4) (T.mul_mod_fast c x5)
      (T.mul_mod_fast c x6) (T.mul_mod_fast c x7).

  Definition convolution_blocks (k : nat)
      (a b : tree T.block8 k) : tree T.block8 k :=
    let fa := T.ntt_fast_block8_ge3 k a in
    let fb := T.ntt_fast_block8_ge3 k b in
    let freq := tree_zip k mul_block fa fb in
    let raw := T.intt_fast_block8_ge3_raw k freq in
    tree_map k (scale_block (T.inv_pow2 (transform_log_of_block_log k))) raw.
End Prime181Ops.

Definition prime469_z : Z := Uint63.to_Z Prime469Cfg.modulus.
Definition prime181_z : Z := Uint63.to_Z Prime181Cfg.modulus.
Definition prime469_u63 : Uint63.int := Prime469Cfg.modulus.
Definition prime181_u63 : Uint63.int := Prime181Cfg.modulus.

Definition crt_combine (x469 x181 : Uint63.int) : Z :=
  let a := Uint63.to_Z x469 in
  let b := Uint63.to_Z x181 in
  let t :=
    Z.modulo
      (Z.modulo (b - a) prime181_z *
       Uint63.to_Z crt_inv_prime469_mod_prime181)
      prime181_z in
  a + prime469_z * t.

Definition crt_delta_u63 (a b : Uint63.int) : Uint63.int :=
  if Uint63.ltb b a
  then Uint63.sub (Uint63.add b prime181_u63) a
  else Uint63.sub b a.

Definition crt_combine_u63 (x469 x181 : Uint63.int) : Uint63.int :=
  let t :=
    Uint63.mod
      (Uint63.mul (crt_delta_u63 x469 x181) crt_inv_prime469_mod_prime181)
      prime181_u63 in
  Uint63.add x469 (Uint63.mul prime469_u63 t).

Fixpoint crt_coeffs_digits
    (xs469 xs181 : list Uint63.int) : list Z :=
  match xs469, xs181 with
  | x469 :: xs469', x181 :: xs181' =>
      crt_combine x469 x181 :: crt_coeffs_digits xs469' xs181'
  | _, _ => []
  end.

Fixpoint crt_coeffs_digits_u63
    (xs469 xs181 : list Uint63.int) : list Uint63.int :=
  match xs469, xs181 with
  | x469 :: xs469', x181 :: xs181' =>
      crt_combine_u63 x469 x181 :: crt_coeffs_digits_u63 xs469' xs181'
  | _, _ => []
  end.

Fixpoint normalize_digits_u63_aux (fuel : nat) (carry : Uint63.int)
    (coeffs : list Uint63.int) : list Uint63.int :=
  match fuel with
  | O => []
  | S fuel' =>
      match coeffs with
      | [] =>
          if Uint63.eqb carry zero_digit then []
          else
            Uint63.land carry digit_mask ::
            normalize_digits_u63_aux fuel' (Uint63.lsr carry digit_shift) []
      | c :: cs =>
          let total := Uint63.add c carry in
          Uint63.land total digit_mask ::
          normalize_digits_u63_aux fuel' (Uint63.lsr total digit_shift) cs
      end
  end.

Definition normalize_coeffs_u63 (coeffs : list Uint63.int) : list Uint63.int :=
  normalize_digits_u63_aux (S (List.length coeffs)) zero_digit coeffs.

Definition limb8_get (x : limb8) (offset : Uint63.int) : Uint63.int :=
  let '{| d0 := x0; d1 := x1; d2 := x2; d3 := x3;
          d4 := x4; d5 := x5; d6 := x6; d7 := x7 |} := x in
  if Uint63.eqb offset zero_digit then x0 else
  if Uint63.eqb offset u63_one then x1 else
  if Uint63.eqb offset (Uint63.of_Z 2) then x2 else
  if Uint63.eqb offset u63_three then x3 else
  if Uint63.eqb offset (Uint63.of_Z 4) then x4 else
  if Uint63.eqb offset (Uint63.of_Z 5) then x5 else
  if Uint63.eqb offset (Uint63.of_Z 6) then x6 else
  x7.

Definition u63_of_nat (n : nat) : Uint63.int :=
  Uint63.of_Z (Z.of_nat n).

Fixpoint limb_array_of_bigint_aux (idx : Uint63.int) (xs : bigint)
    (acc : PArray.array limb8) : PArray.array limb8 :=
  match xs with
  | [] => acc
  | x :: xs' => limb_array_of_bigint_aux (Uint63.add idx u63_one) xs' (PArray.set acc idx x)
  end.

Definition limb_array_of_bigint (xs : bigint) : PArray.array limb8 :=
  limb_array_of_bigint_aux zero_digit xs (PArray.make (u63_of_nat (List.length xs)) zero_limb8).

Definition limb_array_get_digit (arr : PArray.array limb8) (idx : Uint63.int) : Uint63.int :=
  let limb := PArray.get arr (Uint63.lsr idx limb_index_shift) in
  limb8_get limb (Uint63.land idx u63_seven).

Definition u63_mul2 (x : Uint63.int) : Uint63.int := Uint63.add x x.
Definition u63_mul3 (x : Uint63.int) : Uint63.int := Uint63.add (u63_mul2 x) x.
Definition u63_mul4 (x : Uint63.int) : Uint63.int := u63_mul2 (u63_mul2 x).
Definition u63_mul5 (x : Uint63.int) : Uint63.int := Uint63.add (u63_mul4 x) x.
Definition u63_mul6 (x : Uint63.int) : Uint63.int := Uint63.add (u63_mul4 x) (u63_mul2 x).
Definition u63_mul7 (x : Uint63.int) : Uint63.int := Uint63.add (u63_mul4 x) (u63_mul3 x).

Definition block_index_0 (base step : Uint63.int) : Uint63.int := base.
Definition block_index_1 (base step : Uint63.int) : Uint63.int :=
  Uint63.add base (u63_mul4 step).
Definition block_index_2 (base step : Uint63.int) : Uint63.int :=
  Uint63.add base (u63_mul2 step).
Definition block_index_3 (base step : Uint63.int) : Uint63.int :=
  Uint63.add base (u63_mul6 step).
Definition block_index_4 (base step : Uint63.int) : Uint63.int :=
  Uint63.add base step.
Definition block_index_5 (base step : Uint63.int) : Uint63.int :=
  Uint63.add base (u63_mul5 step).
Definition block_index_6 (base step : Uint63.int) : Uint63.int :=
  Uint63.add base (u63_mul3 step).
Definition block_index_7 (base step : Uint63.int) : Uint63.int :=
  Uint63.add base (u63_mul7 step).

Definition mk_block_from_limb_array {B : Type}
    (ctor : Uint63.int -> Uint63.int -> Uint63.int -> Uint63.int ->
            Uint63.int -> Uint63.int -> Uint63.int -> Uint63.int -> B)
    (arr : PArray.array limb8) (base step : Uint63.int) : B :=
  ctor
    (limb_array_get_digit arr (block_index_0 base step))
    (limb_array_get_digit arr (block_index_1 base step))
    (limb_array_get_digit arr (block_index_2 base step))
    (limb_array_get_digit arr (block_index_3 base step))
    (limb_array_get_digit arr (block_index_4 base step))
    (limb_array_get_digit arr (block_index_5 base step))
    (limb_array_get_digit arr (block_index_6 base step))
    (limb_array_get_digit arr (block_index_7 base step)).

Fixpoint packed_tree_from_limb_array {B : Type}
    (ctor : Uint63.int -> Uint63.int -> Uint63.int -> Uint63.int ->
            Uint63.int -> Uint63.int -> Uint63.int -> Uint63.int -> B)
    (k : nat) (arr : PArray.array limb8) (base step : Uint63.int) : tree B k :=
  match k with
  | O => mk_block_from_limb_array ctor arr base step
  | S m =>
      let step2 := Uint63.add step step in
      (packed_tree_from_limb_array ctor m arr base step2,
       packed_tree_from_limb_array ctor m arr (Uint63.add base step) step2)
  end.

Definition coeff_array_make (n : nat) : PArray.array Uint63.int :=
  PArray.make (u63_of_nat n) zero_digit.

Definition coeff_array_set_if_in_bounds
    (arr : PArray.array Uint63.int) (idx value : Uint63.int) : PArray.array Uint63.int :=
  if Uint63.ltb idx (PArray.length arr) then PArray.set arr idx value else arr.

Definition fill_crt_block
    (arr : PArray.array Uint63.int) (base step : Uint63.int)
    (x469 : Prime469.block8) (x181 : Prime181.block8) : PArray.array Uint63.int :=
  let arr0 := coeff_array_set_if_in_bounds arr (block_index_0 base step)
      (crt_combine_u63 (Prime469.b0 x469) (Prime181.b0 x181)) in
  let arr1 := coeff_array_set_if_in_bounds arr0 (block_index_1 base step)
      (crt_combine_u63 (Prime469.b1 x469) (Prime181.b1 x181)) in
  let arr2 := coeff_array_set_if_in_bounds arr1 (block_index_2 base step)
      (crt_combine_u63 (Prime469.b2 x469) (Prime181.b2 x181)) in
  let arr3 := coeff_array_set_if_in_bounds arr2 (block_index_3 base step)
      (crt_combine_u63 (Prime469.b3 x469) (Prime181.b3 x181)) in
  let arr4 := coeff_array_set_if_in_bounds arr3 (block_index_4 base step)
      (crt_combine_u63 (Prime469.b4 x469) (Prime181.b4 x181)) in
  let arr5 := coeff_array_set_if_in_bounds arr4 (block_index_5 base step)
      (crt_combine_u63 (Prime469.b5 x469) (Prime181.b5 x181)) in
  let arr6 := coeff_array_set_if_in_bounds arr5 (block_index_6 base step)
      (crt_combine_u63 (Prime469.b6 x469) (Prime181.b6 x181)) in
  coeff_array_set_if_in_bounds arr6 (block_index_7 base step)
    (crt_combine_u63 (Prime469.b7 x469) (Prime181.b7 x181)).

Fixpoint coeff_array_from_packed_trees
    (k : nat) (arr : PArray.array Uint63.int) (base step : Uint63.int)
    (x469 : tree Prime469.block8 k) (x181 : tree Prime181.block8 k)
    : PArray.array Uint63.int :=
  match k as k0
    return tree Prime469.block8 k0 -> tree Prime181.block8 k0 -> PArray.array Uint63.int with
  | O =>
      fun b469 b181 => fill_crt_block arr base step b469 b181
  | S m =>
      fun t469 t181 =>
        let '(l469, r469) := t469 in
        let '(l181, r181) := t181 in
        let step2 := Uint63.add step step in
        let arr1 := coeff_array_from_packed_trees m arr base step2 l469 l181 in
        coeff_array_from_packed_trees m arr1 (Uint63.add base step) step2 r469 r181
  end x469 x181.

Fixpoint normalize_coeff_array_aux
    (fuel : nat) (idx : Uint63.int) (carry : Uint63.int)
    (arr : PArray.array Uint63.int) : list Uint63.int :=
  match fuel with
  | O => []
  | S fuel' =>
      let coeff :=
        if Uint63.ltb idx (PArray.length arr) then PArray.get arr idx else zero_digit in
      let total := Uint63.add coeff carry in
      let digit := Uint63.land total digit_mask in
      let carry' := Uint63.lsr total digit_shift in
      if andb (Uint63.eqb coeff zero_digit) (Uint63.eqb carry zero_digit)
      then []
      else digit :: normalize_coeff_array_aux fuel' (Uint63.add idx u63_one) carry' arr
  end.

Definition normalize_coeff_step
    (idx : Uint63.int) (carry : Uint63.int) (arr : PArray.array Uint63.int)
    : Uint63.int * Uint63.int :=
  let coeff :=
    if Uint63.ltb idx (PArray.length arr) then PArray.get arr idx else zero_digit in
  let total := Uint63.add coeff carry in
  (Uint63.land total digit_mask, Uint63.lsr total digit_shift).

Definition normalize_coeff_block
    (idx : Uint63.int) (carry : Uint63.int) (arr : PArray.array Uint63.int)
    : limb8 * Uint63.int :=
  let '(d0, carry0) := normalize_coeff_step idx carry arr in
  let '(d1, carry1) := normalize_coeff_step (Uint63.add idx u63_one) carry0 arr in
  let '(d2, carry2) := normalize_coeff_step (Uint63.add idx (Uint63.of_Z 2)) carry1 arr in
  let '(d3, carry3) := normalize_coeff_step (Uint63.add idx u63_three) carry2 arr in
  let '(d4, carry4) := normalize_coeff_step (Uint63.add idx (Uint63.of_Z 4)) carry3 arr in
  let '(d5, carry5) := normalize_coeff_step (Uint63.add idx (Uint63.of_Z 5)) carry4 arr in
  let '(d6, carry6) := normalize_coeff_step (Uint63.add idx (Uint63.of_Z 6)) carry5 arr in
  let '(d7, carry7) := normalize_coeff_step (Uint63.add idx u63_seven) carry6 arr in
  (Limb8 d0 d1 d2 d3 d4 d5 d6 d7, carry7).

Fixpoint normalize_coeff_array_to_bigint_aux
    (fuel : nat) (idx : Uint63.int) (carry : Uint63.int)
    (arr : PArray.array Uint63.int) : bigint :=
  match fuel with
  | O => []
  | S fuel' =>
      let '(block, carry') := normalize_coeff_block idx carry arr in
      let rest := normalize_coeff_array_to_bigint_aux fuel' (Uint63.add idx u63_eight) carry' arr in
      match rest with
      | [] => if limb8_eqb block zero_limb8 then [] else [block]
      | _ => block :: rest
      end
  end.

Definition normalize_coeff_array_to_bigint
    (block_fuel : nat) (arr : PArray.array Uint63.int) : bigint :=
  normalize_coeff_array_to_bigint_aux block_fuel zero_digit zero_digit arr.

Definition build_tree469 (k : nat) (x : bigint) : tree Prime469.block8 k :=
  packed_tree_from_limb_array Prime469.Block8 k (limb_array_of_bigint x) zero_digit u63_one.

Definition build_tree181 (k : nat) (x : bigint) : tree Prime181.block8 k :=
  packed_tree_from_limb_array Prime181.Block8 k (limb_array_of_bigint x) zero_digit u63_one.

Definition mul_bigint (a b : bigint) : option bigint :=
  match a, b with
  | [], _ => Some []
  | _, [] => Some []
  | _, _ =>
      let needed_blocks := (List.length a + List.length b)%nat in
      let needed_digits := (8 * needed_blocks)%nat in
      let k := block_log needed_blocks in
      let total_log := transform_log_of_block_log k in
      if andb (Nat.leb total_log supported_max_log)
              (Nat.leb needed_digits coeff_array_max_digits) then
        let built469a := build_tree469 k a in
        let built469b := build_tree469 k b in
        let built181a := build_tree181 k a in
        let built181b := build_tree181 k b in
        let conv469 := Prime469Ops.convolution_blocks k built469a built469b in
        let conv181 := Prime181Ops.convolution_blocks k built181a built181b in
        let coeffs :=
          coeff_array_from_packed_trees k (coeff_array_make needed_digits) zero_digit u63_one conv469 conv181 in
        Some (normalize_coeff_array_to_bigint (S needed_blocks) coeffs)
      else
        None
  end.
