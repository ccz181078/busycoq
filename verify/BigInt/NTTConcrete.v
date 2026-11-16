From Coq Require Import Uint63 ZArith Lia.
Require Import BigInt.NTTTree.

Definition concrete_max_log : nat := 26%nat.

Module Prime469Cfg <: NTTBaseCfg.
  Definition modulus : Uint63.int := Uint63.of_Z 469762049.

  Definition root (n : nat) : Uint63.int :=
    match n with
    | 1 => Uint63.of_Z 469762048
    | 2 => Uint63.of_Z 450151958
    | 3 => Uint63.of_Z 129701348
    | 4 => Uint63.of_Z 426037461
    | 5 => Uint63.of_Z 244709223
    | 6 => Uint63.of_Z 210853138
    | 7 => Uint63.of_Z 189158148
    | 8 => Uint63.of_Z 338628632
    | 9 => Uint63.of_Z 25153357
    | 10 => Uint63.of_Z 110059487
    | 11 => Uint63.of_Z 165447688
    | 12 => Uint63.of_Z 244412522
    | 13 => Uint63.of_Z 62025685
    | 14 => Uint63.of_Z 19512135
    | 15 => Uint63.of_Z 372627191
    | 16 => Uint63.of_Z 386080322
    | 17 => Uint63.of_Z 321129726
    | 18 => Uint63.of_Z 422997289
    | 19 => Uint63.of_Z 49553715
    | 20 => Uint63.of_Z 197868229
    | 21 => Uint63.of_Z 297449090
    | 22 => Uint63.of_Z 391371999
    | 23 => Uint63.of_Z 385303873
    | 24 => Uint63.of_Z 320192759
    | 25 => Uint63.of_Z 4782969
    | 26 => Uint63.of_Z 2187
    | _ => Uint63.of_Z 1
    end.

  Definition inv_root (n : nat) : Uint63.int :=
    match n with
    | 1 => Uint63.of_Z 469762048
    | 2 => Uint63.of_Z 19610091
    | 3 => Uint63.of_Z 26623616
    | 4 => Uint63.of_Z 358191614
    | 5 => Uint63.of_Z 278703339
    | 6 => Uint63.of_Z 58439238
    | 7 => Uint63.of_Z 230980285
    | 8 => Uint63.of_Z 215855482
    | 9 => Uint63.of_Z 436579181
    | 10 => Uint63.of_Z 458753944
    | 11 => Uint63.of_Z 63413564
    | 12 => Uint63.of_Z 309717554
    | 13 => Uint63.of_Z 318475127
    | 14 => Uint63.of_Z 317243944
    | 15 => Uint63.of_Z 271119509
    | 16 => Uint63.of_Z 380600599
    | 17 => Uint63.of_Z 417932558
    | 18 => Uint63.of_Z 44275780
    | 19 => Uint63.of_Z 96523612
    | 20 => Uint63.of_Z 256026808
    | 21 => Uint63.of_Z 131257384
    | 22 => Uint63.of_Z 426545640
    | 23 => Uint63.of_Z 300035530
    | 24 => Uint63.of_Z 49490419
    | 25 => Uint63.of_Z 392193156
    | 26 => Uint63.of_Z 410692747
    | _ => Uint63.of_Z 1
    end.

  Definition inv2 : Uint63.int := Uint63.of_Z 234881025.

  Fixpoint inv_pow2 (n : nat) : Uint63.int :=
    match n with
    | O => Uint63.of_Z 1
    | S m => Uint63.mod (Uint63.mul inv2 (inv_pow2 m)) modulus
    end.

  Lemma modulus_range : (1 < Uint63.to_Z modulus < Uint63.wB)%Z.
  Proof.
    vm_compute.
    split; reflexivity.
  Qed.

  Lemma root_range : forall n, (0 <= Uint63.to_Z (root n) < Uint63.to_Z modulus)%Z.
  Proof.
    intros n.
    do 27 (try destruct n as [|n]).
    all: vm_compute; split; [discriminate|reflexivity].
  Qed.

  Lemma inv_root_range :
    forall n, (0 <= Uint63.to_Z (inv_root n) < Uint63.to_Z modulus)%Z.
  Proof.
    intros n.
    do 27 (try destruct n as [|n]).
    all: vm_compute; split; [discriminate|reflexivity].
  Qed.

  Lemma inv_pow2_range :
    forall n, (0 <= Uint63.to_Z (inv_pow2 n) < Uint63.to_Z modulus)%Z.
  Proof.
    induction n as [|n IH].
    - vm_compute. split; [discriminate|reflexivity].
    - simpl.
      unfold modulus.
      rewrite Uint63.mod_spec.
      pose proof modulus_range as Hm.
      unfold Uint63.to_Z in *.
      destruct IH as [IH0 IH1].
      apply Z.mod_pos_bound.
      vm_compute.
      reflexivity.
  Qed.

  Lemma two_modulus_le_wB : (2 * Uint63.to_Z modulus <= Uint63.wB)%Z.
  Proof.
    vm_compute.
    discriminate.
  Qed.

  Lemma modulus_square_le_wB :
    (Uint63.to_Z modulus * Uint63.to_Z modulus <= Uint63.wB)%Z.
  Proof.
    vm_compute.
    discriminate.
  Qed.
End Prime469Cfg.

Module Prime181Cfg <: NTTBaseCfg.
  Definition modulus : Uint63.int := Uint63.of_Z 1811939329.

  Definition root (n : nat) : Uint63.int :=
    match n with
    | 1 => Uint63.of_Z 1811939328
    | 2 => Uint63.of_Z 1416949424
    | 3 => Uint63.of_Z 1452317833
    | 4 => Uint63.of_Z 659408637
    | 5 => Uint63.of_Z 860297611
    | 6 => Uint63.of_Z 1472666535
    | 7 => Uint63.of_Z 1109739630
    | 8 => Uint63.of_Z 18116277
    | 9 => Uint63.of_Z 209403217
    | 10 => Uint63.of_Z 69915711
    | 11 => Uint63.of_Z 1154101769
    | 12 => Uint63.of_Z 606837284
    | 13 => Uint63.of_Z 1489399950
    | 14 => Uint63.of_Z 465083369
    | 15 => Uint63.of_Z 517598978
    | 16 => Uint63.of_Z 1456252962
    | 17 => Uint63.of_Z 1784331046
    | 18 => Uint63.of_Z 1330130053
    | 19 => Uint63.of_Z 1138266161
    | 20 => Uint63.of_Z 971241113
    | 21 => Uint63.of_Z 121895319
    | 22 => Uint63.of_Z 579520204
    | 23 => Uint63.of_Z 388825445
    | 24 => Uint63.of_Z 1762019879
    | 25 => Uint63.of_Z 209208363
    | 26 => Uint63.of_Z 72705542
    | _ => Uint63.of_Z 1
    end.

  Definition inv_root (n : nat) : Uint63.int :=
    match n with
    | 1 => Uint63.of_Z 1811939328
    | 2 => Uint63.of_Z 394989905
    | 3 => Uint63.of_Z 1756022077
    | 4 => Uint63.of_Z 1368643352
    | 5 => Uint63.of_Z 1681104208
    | 6 => Uint63.of_Z 1594001182
    | 7 => Uint63.of_Z 842788380
    | 8 => Uint63.of_Z 576638474
    | 9 => Uint63.of_Z 770487725
    | 10 => Uint63.of_Z 1682986047
    | 11 => Uint63.of_Z 488136043
    | 12 => Uint63.of_Z 450492458
    | 13 => Uint63.of_Z 669232625
    | 14 => Uint63.of_Z 1720000667
    | 15 => Uint63.of_Z 110413286
    | 16 => Uint63.of_Z 1537158106
    | 17 => Uint63.of_Z 1125316264
    | 18 => Uint63.of_Z 1363276908
    | 19 => Uint63.of_Z 925937071
    | 20 => Uint63.of_Z 311798718
    | 21 => Uint63.of_Z 1506675331
    | 22 => Uint63.of_Z 1748414954
    | 23 => Uint63.of_Z 1510677230
    | 24 => Uint63.of_Z 964549597
    | 25 => Uint63.of_Z 461327191
    | 26 => Uint63.of_Z 801700081
    | _ => Uint63.of_Z 1
    end.

  Definition inv2 : Uint63.int := Uint63.of_Z 905969665.

  Fixpoint inv_pow2 (n : nat) : Uint63.int :=
    match n with
    | O => Uint63.of_Z 1
    | S m => Uint63.mod (Uint63.mul inv2 (inv_pow2 m)) modulus
    end.

  Lemma modulus_range : (1 < Uint63.to_Z modulus < Uint63.wB)%Z.
  Proof.
    vm_compute.
    split; reflexivity.
  Qed.

  Lemma root_range : forall n, (0 <= Uint63.to_Z (root n) < Uint63.to_Z modulus)%Z.
  Proof.
    intros n.
    do 27 (try destruct n as [|n]).
    all: vm_compute; split; [discriminate|reflexivity].
  Qed.

  Lemma inv_root_range :
    forall n, (0 <= Uint63.to_Z (inv_root n) < Uint63.to_Z modulus)%Z.
  Proof.
    intros n.
    do 27 (try destruct n as [|n]).
    all: vm_compute; split; [discriminate|reflexivity].
  Qed.

  Lemma inv_pow2_range :
    forall n, (0 <= Uint63.to_Z (inv_pow2 n) < Uint63.to_Z modulus)%Z.
  Proof.
    induction n as [|n IH].
    - vm_compute. split; [discriminate|reflexivity].
    - simpl.
      unfold modulus.
      rewrite Uint63.mod_spec.
      pose proof modulus_range as Hm.
      unfold Uint63.to_Z in *.
      destruct IH as [IH0 IH1].
      apply Z.mod_pos_bound.
      vm_compute.
      reflexivity.
  Qed.

  Lemma two_modulus_le_wB : (2 * Uint63.to_Z modulus <= Uint63.wB)%Z.
  Proof.
    vm_compute.
    discriminate.
  Qed.

  Lemma modulus_square_le_wB :
    (Uint63.to_Z modulus * Uint63.to_Z modulus <= Uint63.wB)%Z.
  Proof.
    vm_compute.
    discriminate.
  Qed.
End Prime181Cfg.

Module Prime469 := TreeNTT(Prime469Cfg).
Module Prime181 := TreeNTT(Prime181Cfg).

Definition crt_modulus_z : Z :=
  Uint63.to_Z Prime469Cfg.modulus * Uint63.to_Z Prime181Cfg.modulus.

Definition crt_inv_prime469_mod_prime181 : Uint63.int :=
  Uint63.of_Z 1540148431.

Definition crt_inv_prime181_mod_prime469 : Uint63.int :=
  Uint63.of_Z 70464307.
