From Coq Require Import Uint63 ZArith.
Require Import BigInt.NTTTree BigInt.NTTTreeBench.

Definition prng_mul : Uint63.int := Uint63.of_Z 48271.
Definition prng_inc : Uint63.int := Uint63.of_Z 1.

Definition prng_next (x : Uint63.int) : Uint63.int :=
  Uint63.mod (Uint63.add (Uint63.mul x prng_mul) prng_inc) BenchCfg.modulus.

Fixpoint random_tree (n : nat) : Uint63.int -> tree Uint63.int n * Uint63.int :=
  match n as n0 return Uint63.int -> tree Uint63.int n0 * Uint63.int with
  | O =>
      fun seed => (seed, prng_next seed)
  | S m =>
      fun seed =>
        let '(l, seed1) := random_tree m seed in
        let '(r, seed2) := random_tree m seed1 in
        ((l, r), seed2)
  end.

Definition sample_tree (n : nat) (seed : Z) : tree Uint63.int n :=
  fst (random_tree n (Uint63.of_Z seed)).

Example ntt_equiv_3_seed_1 :
  B.ntt_fast 3 (sample_tree 3 1%Z) = B.ntt 3 (sample_tree 3 1%Z).
Proof.
  native_compute.
  reflexivity.
Qed.

Example ntt_record16_equiv_record8_3_seed_1 :
  B.ntt_fast_record16 3 (sample_tree 3 1%Z) = B.ntt_fast_record8 3 (sample_tree 3 1%Z).
Proof.
  native_compute.
  reflexivity.
Qed.

Example intt_equiv_3_seed_1 :
  B.intt_fast 3 (sample_tree 3 1%Z) = B.intt 3 (sample_tree 3 1%Z).
Proof.
  native_compute.
  reflexivity.
Qed.

Example roundtrip_fast_3_seed_1 :
  B.intt_fast 3 (B.ntt_fast 3 (sample_tree 3 1%Z)) = sample_tree 3 1%Z.
Proof.
  native_compute.
  reflexivity.
Qed.

Example ntt_equiv_4_seed_42 :
  B.ntt_fast 4 (sample_tree 4 42%Z) = B.ntt 4 (sample_tree 4 42%Z).
Proof.
  native_compute.
  reflexivity.
Qed.

Example ntt_record16_equiv_record8_4_seed_42 :
  B.ntt_fast_record16 4 (sample_tree 4 42%Z) = B.ntt_fast_record8 4 (sample_tree 4 42%Z).
Proof.
  native_compute.
  reflexivity.
Qed.

Example intt_equiv_4_seed_42 :
  B.intt_fast 4 (sample_tree 4 42%Z) = B.intt 4 (sample_tree 4 42%Z).
Proof.
  native_compute.
  reflexivity.
Qed.

Example roundtrip_fast_4_seed_42 :
  B.intt_fast 4 (B.ntt_fast 4 (sample_tree 4 42%Z)) = sample_tree 4 42%Z.
Proof.
  native_compute.
  reflexivity.
Qed.

Example ntt_equiv_5_seed_2024 :
  B.ntt_fast 5 (sample_tree 5 2024%Z) = B.ntt 5 (sample_tree 5 2024%Z).
Proof.
  native_compute.
  reflexivity.
Qed.

Example ntt_record16_equiv_record8_5_seed_2024 :
  B.ntt_fast_record16 5 (sample_tree 5 2024%Z) = B.ntt_fast_record8 5 (sample_tree 5 2024%Z).
Proof.
  native_compute.
  reflexivity.
Qed.

Example intt_equiv_5_seed_2024 :
  B.intt_fast 5 (sample_tree 5 2024%Z) = B.intt 5 (sample_tree 5 2024%Z).
Proof.
  native_compute.
  reflexivity.
Qed.

Example roundtrip_fast_5_seed_2024 :
  B.intt_fast 5 (B.ntt_fast 5 (sample_tree 5 2024%Z)) = sample_tree 5 2024%Z.
Proof.
  native_compute.
  reflexivity.
Qed.

Example ntt_equiv_6_seed_777 :
  B.ntt_fast 6 (sample_tree 6 777%Z) = B.ntt 6 (sample_tree 6 777%Z).
Proof.
  native_compute.
  reflexivity.
Qed.

Example ntt_record16_equiv_record8_6_seed_777 :
  B.ntt_fast_record16 6 (sample_tree 6 777%Z) = B.ntt_fast_record8 6 (sample_tree 6 777%Z).
Proof.
  native_compute.
  reflexivity.
Qed.

Example intt_equiv_6_seed_777 :
  B.intt_fast 6 (sample_tree 6 777%Z) = B.intt 6 (sample_tree 6 777%Z).
Proof.
  native_compute.
  reflexivity.
Qed.

Example roundtrip_fast_6_seed_777 :
  B.intt_fast 6 (B.ntt_fast 6 (sample_tree 6 777%Z)) = sample_tree 6 777%Z.
Proof.
  native_compute.
  reflexivity.
Qed.

Example ntt_equiv_7_seed_12345 :
  B.ntt_fast 7 (sample_tree 7 12345%Z) = B.ntt 7 (sample_tree 7 12345%Z).
Proof.
  native_compute.
  reflexivity.
Qed.

Example ntt_record16_equiv_record8_7_seed_12345 :
  B.ntt_fast_record16 7 (sample_tree 7 12345%Z) = B.ntt_fast_record8 7 (sample_tree 7 12345%Z).
Proof.
  native_compute.
  reflexivity.
Qed.

Example intt_equiv_7_seed_12345 :
  B.intt_fast 7 (sample_tree 7 12345%Z) = B.intt 7 (sample_tree 7 12345%Z).
Proof.
  native_compute.
  reflexivity.
Qed.

Example roundtrip_fast_7_seed_12345 :
  B.intt_fast 7 (B.ntt_fast 7 (sample_tree 7 12345%Z)) = sample_tree 7 12345%Z.
Proof.
  native_compute.
  reflexivity.
Qed.

Example ntt_equiv_8_seed_271828 :
  B.ntt_fast 8 (sample_tree 8 271828%Z) = B.ntt 8 (sample_tree 8 271828%Z).
Proof.
  native_compute.
  reflexivity.
Qed.

Example ntt_record16_equiv_record8_8_seed_271828 :
  B.ntt_fast_record16 8 (sample_tree 8 271828%Z) = B.ntt_fast_record8 8 (sample_tree 8 271828%Z).
Proof.
  native_compute.
  reflexivity.
Qed.

Example intt_equiv_8_seed_271828 :
  B.intt_fast 8 (sample_tree 8 271828%Z) = B.intt 8 (sample_tree 8 271828%Z).
Proof.
  native_compute.
  reflexivity.
Qed.

Example roundtrip_fast_8_seed_271828 :
  B.intt_fast 8 (B.ntt_fast 8 (sample_tree 8 271828%Z)) = sample_tree 8 271828%Z.
Proof.
  native_compute.
  reflexivity.
Qed.
