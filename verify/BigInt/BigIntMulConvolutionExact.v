From Coq Require Import Uint63 ZArith Lia Array.PArray.
Require Import BigInt.NTTConcrete BigInt.BigIntMul BigInt.BigIntMulProof BigInt.BigIntMulCanonical
  BigInt.BigIntMulCRTArrayExact BigInt.BigIntMulConvolutionCanonical.

Local Open Scope Z_scope.

Lemma coeff_array_from_convolution_blocks_make_get_exact :
  forall k len
    (a469 b469 : NTTTree.tree Prime469.block8 k)
    (a181 b181 : NTTTree.tree Prime181.block8 k) i z,
    (Z.of_nat len <= Uint63.to_Z PArray.max_length)%Z ->
    (Z.of_nat len < Uint63.wB)%Z ->
    (Prime469.pow2 (S (S (S k))) <= len)%nat ->
    (i < Prime469.pow2 (S (S (S k))))%nat ->
    Prime469.canonical_tree (S (S (S k))) (Prime469.unpack_tree8 k a469) ->
    Prime469.canonical_tree (S (S (S k))) (Prime469.unpack_tree8 k b469) ->
    Prime181.canonical_tree (S (S (S k))) (Prime181.unpack_tree8 k a181) ->
    Prime181.canonical_tree (S (S (S k))) (Prime181.unpack_tree8 k b181) ->
    (0 <= z < crt_modulus_z)%Z ->
    Z.modulo z prime469_z =
      Uint63.to_Z (prime469_coeff_at k (Prime469Ops.convolution_blocks k a469 b469) i) ->
    Z.modulo z prime181_z =
      Uint63.to_Z (prime181_coeff_at k (Prime181Ops.convolution_blocks k a181 b181) i) ->
    Uint63.to_Z
      (PArray.get
        (coeff_array_from_packed_trees k (coeff_array_make len) zero_digit u63_one
          (Prime469Ops.convolution_blocks k a469 b469)
          (Prime181Ops.convolution_blocks k a181 b181))
        (u63_of_nat i)) = z.
Proof.
  intros k len a469 b469 a181 b181 i z Hmax HlenB Hpow Hi Ha469 Hb469 Ha181 Hb181 Hz Hz469 Hz181.
  apply
    (coeff_array_from_packed_trees_make_get_exact
       k len
       (Prime469Ops.convolution_blocks k a469 b469)
       (Prime181Ops.convolution_blocks k a181 b181)
       i z);
    try assumption.
  - apply prime469_convolution_coeff_at_range; assumption.
  - apply prime181_convolution_coeff_at_range; assumption.
Qed.

Lemma coeff_array_from_built_trees_make_get_exact :
  forall k len (a b : bigint) i z,
    (k <= supported_max_block_log)%nat ->
    (Z.of_nat (List.length a) <= Uint63.to_Z PArray.max_length)%Z ->
    (Z.of_nat (List.length b) <= Uint63.to_Z PArray.max_length)%Z ->
    canonical_bigint a ->
    canonical_bigint b ->
    (Z.of_nat len <= Uint63.to_Z PArray.max_length)%Z ->
    (Z.of_nat len < Uint63.wB)%Z ->
    (Prime469.pow2 (S (S (S k))) <= len)%nat ->
    (i < Prime469.pow2 (S (S (S k))))%nat ->
    (0 <= z < crt_modulus_z)%Z ->
    Z.modulo z prime469_z =
      Uint63.to_Z
        (prime469_coeff_at k
          (Prime469Ops.convolution_blocks k (build_tree469 k a) (build_tree469 k b)) i) ->
    Z.modulo z prime181_z =
      Uint63.to_Z
        (prime181_coeff_at k
          (Prime181Ops.convolution_blocks k (build_tree181 k a) (build_tree181 k b)) i) ->
    Uint63.to_Z
      (PArray.get
        (coeff_array_from_packed_trees k (coeff_array_make len) zero_digit u63_one
          (Prime469Ops.convolution_blocks k (build_tree469 k a) (build_tree469 k b))
          (Prime181Ops.convolution_blocks k (build_tree181 k a) (build_tree181 k b)))
        (u63_of_nat i)) = z.
Proof.
  intros k len a b i z Hk HlenA HlenB Ha Hb Hmax HlenPow Hpow Hi Hz Hz469 Hz181.
  apply
    (coeff_array_from_convolution_blocks_make_get_exact
       k len
       (build_tree469 k a) (build_tree469 k b)
       (build_tree181 k a) (build_tree181 k b)
       i z);
    try assumption.
  - apply build_tree469_canonical; assumption.
  - apply build_tree469_canonical; assumption.
  - apply build_tree181_canonical; assumption.
  - apply build_tree181_canonical; assumption.
Qed.
