From Coq Require Import Uint63 ZArith Lia Array.PArray.
Require Import BigInt.NTTTree BigInt.NTTConcrete BigInt.BigIntMul BigInt.BigIntMulCRT BigInt.BigIntMulCRTExact.

Local Open Scope Z_scope.

Definition prime469_coeff_at (k : nat) (t : NTTTree.tree Prime469.block8 k) (i : nat) : Uint63.int :=
  Prime469.input_get (S (S (S k))) (Prime469.unpack_tree8 k t) i.

Definition prime181_coeff_at (k : nat) (t : NTTTree.tree Prime181.block8 k) (i : nat) : Uint63.int :=
  Prime181.input_get (S (S (S k))) (Prime181.unpack_tree8 k t) i.

Lemma coeff_array_from_packed_trees_make_get_exact :
  forall k len x469 x181 i z,
    (Z.of_nat len <= Uint63.to_Z PArray.max_length)%Z ->
    (Z.of_nat len < Uint63.wB)%Z ->
    (Prime469.pow2 (S (S (S k))) <= len)%nat ->
    (i < Prime469.pow2 (S (S (S k))))%nat ->
    let c469 := prime469_coeff_at k x469 i in
    let c181 := prime181_coeff_at k x181 i in
    (0 <= Uint63.to_Z c469 < prime469_z)%Z ->
    (0 <= Uint63.to_Z c181 < prime181_z)%Z ->
    (0 <= z < crt_modulus_z)%Z ->
    Z.modulo z prime469_z = Uint63.to_Z c469 ->
    Z.modulo z prime181_z = Uint63.to_Z c181 ->
    Uint63.to_Z
      (PArray.get
        (coeff_array_from_packed_trees k (coeff_array_make len) zero_digit u63_one x469 x181)
        (u63_of_nat i)) = z.
Proof.
  intros k len x469 x181 i z Hmax HlenB Hpow Hi c469 c181 H469 H181 Hz Hz469 Hz181.
  unfold c469, c181, prime469_coeff_at, prime181_coeff_at in *.
  pose proof
    (coeff_array_from_packed_trees_make_get k len x469 x181 i Hmax HlenB Hpow Hi)
    as Hget.
  eapply eq_trans.
  - exact (f_equal Uint63.to_Z Hget).
  - apply crt_combine_u63_exact; assumption.
Qed.
