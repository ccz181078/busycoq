From Coq Require Import Uint63 ZArith NArith Lists.List.
Require Import BigInt.BigIntMul.

Import ListNotations.
Local Open Scope Z_scope.

Definition max_digit : Uint63.int := Uint63.of_Z (digit_base_z - 1).

Definition max_limb8 : limb8 :=
  Limb8 max_digit max_digit max_digit max_digit
    max_digit max_digit max_digit max_digit.

Fixpoint repeat_limb8 (n : nat) (x : limb8) : bigint :=
  match n with
  | O => []
  | S m => x :: repeat_limb8 m x
  end.

Definition value_check (a b : bigint) : bool :=
  match mul_bigint a b with
  | Some r => Z.eqb (bigint_value r) (bigint_value a * bigint_value b)
  | None => false
  end.

Definition case_small_a : bigint := bigint_of_digits_z [3; 5; 7].
Definition case_small_b : bigint := bigint_of_digits_z [11; 13; 17; 19].

Definition case_carry_a : bigint := repeat_limb8 2%nat max_limb8.
Definition case_carry_b : bigint := repeat_limb8 3%nat max_limb8.

Definition case_mixed_a : bigint :=
  bigint_of_digits_z
    [ 1; 200000; 17; 42; 262143; 12345; 999; 7;
      8; 9; 10; 11; 12; 13; 14; 15; 16; 17 ].

Definition case_mixed_b : bigint :=
  bigint_of_digits_z
    [ 18; 19; 20; 21; 22; 23; 24; 25;
      262143; 777; 55555; 333; 99 ].

Definition case_roundtrip_N : N :=
  1234567890123456789012345678901234567890%N.

Definition case_divmod_x : bigint :=
  bigint_of_digits_z
    [ 262143; 1; 200000; 17; 42; 262143; 12345; 999; 7; 8; 9 ].

Example mul_bigint_small_value :
  value_check case_small_a case_small_b = true.
Proof.
  native_compute.
  reflexivity.
Qed.

Example mul_bigint_carry_value :
  value_check case_carry_a case_carry_b = true.
Proof.
  native_compute.
  reflexivity.
Qed.

Example mul_bigint_mixed_value :
  value_check case_mixed_a case_mixed_b = true.
Proof.
  native_compute.
  reflexivity.
Qed.

Example bigint_N_roundtrip :
  bigint_to_N (bigint_of_N case_roundtrip_N) = case_roundtrip_N.
Proof.
  native_compute.
  reflexivity.
Qed.

Example bigint_case_to_from_N :
  bigint_of_N (bigint_to_N case_mixed_a) = case_mixed_a.
Proof.
  native_compute.
  reflexivity.
Qed.

Example bigint_add_value :
  Z.eqb (bigint_value (bigint_add case_small_a case_mixed_b))
    (bigint_value case_small_a + bigint_value case_mixed_b) = true.
Proof.
  native_compute.
  reflexivity.
Qed.

Example bigint_add_roundtrip_N :
  bigint_to_N (bigint_add (bigint_of_N 1234567890123%N) (bigint_of_N 9876543210987%N)) =
  (1234567890123 + 9876543210987)%N.
Proof.
  native_compute.
  reflexivity.
Qed.

Example bigint_divmod_pow2_value :
  let '(q, r) := bigint_divmod_pow2 37%nat case_divmod_x in
  andb
    (Z.eqb (bigint_value case_divmod_x)
      ((2 ^ Z.of_nat 37) * bigint_value q + bigint_value r))
    (Z.ltb (bigint_value r) (2 ^ Z.of_nat 37)) = true.
Proof.
  native_compute.
  reflexivity.
Qed.

Example bigint_divmod_pow2_zero :
  bigint_divmod_pow2 0%nat case_mixed_a = (case_mixed_a, []).
Proof.
  native_compute.
  reflexivity.
Qed.

Definition pow4pow2_bits (d : nat) : nat :=
  Nat.pow 2 (S d).

Definition split_pow4_N (d : nat) (a : N) : N * N :=
  let bits := pow4pow2_bits d in
  let modulus := N.shiftl 1%N (N.of_nat bits) in
  (N.shiftr a (N.of_nat bits), N.modulo a modulus).

Fixpoint pow9_pow2_N (d : nat) : N :=
  match d with
  | O => 9%N
  | S d0 =>
      let x := pow9_pow2_N d0 in
      (x * x)%N
  end.

Definition bigint_mul_by_N_add (x : bigint) (m k : N) : option bigint :=
  match mul_bigint x (bigint_of_N m) with
  | Some p => Some (bigint_add p (bigint_of_N k))
  | None => None
  end.

Definition bigint_mul_by_bigint_add_bigint (x factor y : bigint)
    : option bigint :=
  match x with
  | [] => Some y
  | _ =>
      match bigint_as_digit factor with
      | Some m => Some (bigint_add (bigint_mul_digit m x) y)
      | None =>
          match mul_bigint x factor with
          | Some p => Some (bigint_add p y)
          | None => None
          end
      end
  end.

Definition bigint_9 : bigint := bigint_of_N 9%N.
Definition bigint_11 : bigint := bigint_of_N 11%N.
Definition bigint_12 : bigint := bigint_of_N 12%N.
Definition bigint_15 : bigint := bigint_of_N 15%N.
Definition bigint_16 : bigint := bigint_of_N 16%N.

Definition option_attach_c (c : N) (x : option bigint) : option (bigint * N) :=
  match x with
  | Some a => Some (a, c)
  | None => None
  end.

Fixpoint F_N (ac : N * N) (d : nat) : option (N * N) :=
  let '(a, c) := ac in
  let '(a1, a0) := split_pow4_N d a in
  match d with
  | O =>
      if N.ltb c 3%N then None
      else if N.eqb a0 0%N then Some ((a1 * 9 + 11)%N, (c - 3)%N)
      else if N.eqb a0 1%N then Some ((a1 * 9 + 15)%N, (c - 3)%N)
      else if N.eqb a0 2%N then Some ((a1 * 9 + 12)%N, (c - 2)%N)
      else Some ((a1 * 9 + 16)%N, (c - 2)%N)
  | S d0 =>
      match F_N (a0, c) d0 with
      | Some (a0', c1) =>
          match F_N (a0', c1) d0 with
          | Some (a0'', c2) =>
              Some ((a1 * pow9_pow2_N (S d0) + a0'')%N, c2)
          | None => None
          end
      | None => None
      end
  end.

Fixpoint extend_pow9_cache (fuel target : nat) (cache : list bigint)
    : option (list bigint) :=
  if Nat.ltb target (List.length cache) then Some cache
  else
    match fuel with
    | O => None
    | S fuel' =>
        let cache1 :=
          match cache with
          | [] => [bigint_9]
          | _ => cache
          end in
        if Nat.ltb target (List.length cache1) then Some cache1
        else
          match rev cache1 with
          | [] => Some [bigint_9]
          | p :: _ =>
              match mul_bigint p p with
              | Some q => extend_pow9_cache fuel' target (cache1 ++ [q])
              | None => None
              end
          end
    end.

Definition ensure_pow9_cache (target : nat) (cache : list bigint)
    : option (list bigint) :=
  extend_pow9_cache (S target) target cache.

Fixpoint F_bigint_cached (cache : list bigint) (ac : bigint * N) (d : nat)
    : option ((bigint * N) * list bigint) :=
  let '(a, c) := ac in
  let '(a1, a0) := bigint_divmod_pow2 (pow4pow2_bits d) a in
  match d with
  | O =>
      let a0N := bigint_to_N a0 in
      if N.ltb c 3%N then None
      else
        let out :=
          if N.eqb a0N 0%N then bigint_mul_by_bigint_add_bigint a1 bigint_9 bigint_11
          else if N.eqb a0N 1%N then bigint_mul_by_bigint_add_bigint a1 bigint_9 bigint_15
          else if N.eqb a0N 2%N then bigint_mul_by_bigint_add_bigint a1 bigint_9 bigint_12
          else bigint_mul_by_bigint_add_bigint a1 bigint_9 bigint_16 in
        match out with
        | Some a' =>
            let c' :=
              if N.eqb a0N 0%N then (c - 3)%N
              else if N.eqb a0N 1%N then (c - 3)%N
              else (c - 2)%N in
            Some ((a', c'), cache)
        | None => None
        end
  | S d0 =>
      match F_bigint_cached cache (a0, c) d0 with
      | Some ((a0', c1), cache1) =>
          match F_bigint_cached cache1 (a0', c1) d0 with
          | Some ((a0'', c2), cache2) =>
              match a1 with
              | [] => Some ((a0'', c2), cache2)
              | _ =>
                  match ensure_pow9_cache (S d0) cache2 with
                  | Some cache3 =>
                      match nth_error cache3 (S d0) with
                      | Some p =>
                          match bigint_mul_by_bigint_add_bigint a1 p a0'' with
                          | Some a' => Some ((a', c2), cache3)
                          | None => None
                          end
                      | None => None
                      end
                  | None => None
                  end
              end
          | None => None
          end
      | None => None
      end
  end
.

Definition F_bigint (ac : bigint * N) (d : nat) : option (bigint * N) :=
  match F_bigint_cached [] ac d with
  | Some (res, _) => Some res
  | None => None
  end.

Definition bigint_result_to_N (x : option (bigint * N)) : option (N * N) :=
  match x with
  | Some (a, c) => Some (bigint_to_N a, c)
  | None => None
  end.

Definition option_pair_N_eqb (x y : option (N * N)) : bool :=
  match x, y with
  | Some (a, c), Some (a', c') => N.eqb a a' && N.eqb c c'
  | None, None => true
  | _, _ => false
  end.

Definition F_test_input_N : N * N := (3%N, 119114451%N).
Definition F_test_input_bigint : bigint * N := (bigint_of_N 3%N, 119114451%N).

Definition F_test_ds : list nat :=
  [0%nat; 1%nat; 2%nat; 3%nat; 4%nat; 5%nat; 6%nat; 7%nat; 8%nat; 9%nat; 10%nat].

Definition F_compare_table : list (nat * option (N * N) * option (N * N)) :=
  map (fun d => (d, F_N F_test_input_N d, bigint_result_to_N (F_bigint F_test_input_bigint d))) F_test_ds.

Example F_bigint_matches_reference :
  forallb
    (fun d =>
       option_pair_N_eqb
         (bigint_result_to_N (F_bigint F_test_input_bigint d))
         (F_N F_test_input_N d))
    F_test_ds = true.
Proof.
  native_compute.
  reflexivity.
Qed.
