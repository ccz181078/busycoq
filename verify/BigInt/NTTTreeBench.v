From Coq Require Import Uint63 ZArith Lia.
Require Import BigInt.NTTTree.

Module BenchCfg <: NTTBaseCfg.
  Definition modulus : Uint63.int := Uint63.of_Z 2013265921.

  Definition root (n : nat) : Uint63.int :=
    match n with
    | 1 => Uint63.of_Z 2013265920
    | 2 => Uint63.of_Z 1728404513
    | 3 => Uint63.of_Z 1592366214
    | 4 => Uint63.of_Z 196396260
    | 5 => Uint63.of_Z 760005850
    | 6 => Uint63.of_Z 1721589904
    | 7 => Uint63.of_Z 397765732
    | 8 => Uint63.of_Z 1732600167
    | 9 => Uint63.of_Z 1753498361
    | 10 => Uint63.of_Z 341742893
    | 11 => Uint63.of_Z 1340477990
    | 12 => Uint63.of_Z 1282623253
    | 13 => Uint63.of_Z 298008106
    | 14 => Uint63.of_Z 1657000625
    | 15 => Uint63.of_Z 2009781145
    | _ => Uint63.of_Z 1
    end.

  Definition inv_root (n : nat) : Uint63.int :=
    match n with
    | 1 => Uint63.of_Z 2013265920
    | 2 => Uint63.of_Z 284861408
    | 3 => Uint63.of_Z 1801542727
    | 4 => Uint63.of_Z 567209306
    | 5 => Uint63.of_Z 1273220281
    | 6 => Uint63.of_Z 662200255
    | 7 => Uint63.of_Z 1856545343
    | 8 => Uint63.of_Z 1611842161
    | 9 => Uint63.of_Z 1861675199
    | 10 => Uint63.of_Z 774513262
    | 11 => Uint63.of_Z 449056851
    | 12 => Uint63.of_Z 1255670133
    | 13 => Uint63.of_Z 1976924129
    | 14 => Uint63.of_Z 106301669
    | 15 => Uint63.of_Z 1411306935
    | _ => Uint63.of_Z 1
    end.

  Definition inv2 : Uint63.int := Uint63.of_Z 1006632961.

  Fixpoint inv_pow2 (n : nat) : Uint63.int :=
    match n with
    | O => Uint63.of_Z 1
    | S m => Uint63.mod (Uint63.mul inv2 (inv_pow2 m)) modulus
    end.

  Axiom modulus_range : (1 < Uint63.to_Z modulus < Uint63.wB)%Z.
  Axiom root_range : forall n, (0 <= Uint63.to_Z (root n) < Uint63.to_Z modulus)%Z.
  Axiom inv_root_range : forall n, (0 <= Uint63.to_Z (inv_root n) < Uint63.to_Z modulus)%Z.
  Axiom inv_pow2_range : forall n, (0 <= Uint63.to_Z (inv_pow2 n) < Uint63.to_Z modulus)%Z.
  Axiom two_modulus_le_wB : (2 * Uint63.to_Z modulus <= Uint63.wB)%Z.
  Axiom modulus_square_le_wB :
    (Uint63.to_Z modulus * Uint63.to_Z modulus <= Uint63.wB)%Z.
End BenchCfg.

Module B := TreeNTT(BenchCfg).

Fixpoint fill_tree (n : nat) (x : Uint63.int) : tree Uint63.int n :=
  match n as n0 return tree Uint63.int n0 with
  | O => x
  | S m => (fill_tree m x, fill_tree m x)
  end.

Fixpoint checksum_tree (n : nat) : tree Uint63.int n -> Uint63.int :=
  match n as n0 return tree Uint63.int n0 -> Uint63.int with
  | O => fun x => x
  | S m =>
      fun t =>
        let '(l, r) := t in
        Uint63.add (checksum_tree m l) (checksum_tree m r)
  end.
