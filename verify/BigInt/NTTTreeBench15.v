From Coq Require Import Uint63 ZArith.
Require Import BigInt.NTTTreeBench.

Time Eval native_compute in
  checksum_tree 15 (B.ntt_fast 15 (fill_tree 15 (Uint63.of_Z 1%Z))).
