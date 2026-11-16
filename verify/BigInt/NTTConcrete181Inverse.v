From Coq Require Import Lia.
Require Import BigInt.NTTConcrete BigInt.NTTKernelBounded BigInt.BigIntMul.

Module Prime181KBInv := TreeNTTKernelBounded(Prime181Cfg).
Module Prime181InverseFacts.
  Module T := Prime181KBInv.T.
  Import T.

  Lemma root_inv_mul_one_0 : zmul (value (root 0%nat)) (value (inv_root 0%nat)) = zone.
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_inv_mul_one_1 : zmul (value (root 1%nat)) (value (inv_root 1%nat)) = zone.
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_inv_mul_one_2 : zmul (value (root 2%nat)) (value (inv_root 2%nat)) = zone.
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_inv_mul_one_3 : zmul (value (root 3%nat)) (value (inv_root 3%nat)) = zone.
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_inv_mul_one_4 : zmul (value (root 4%nat)) (value (inv_root 4%nat)) = zone.
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_inv_mul_one_5 : zmul (value (root 5%nat)) (value (inv_root 5%nat)) = zone.
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_inv_mul_one_6 : zmul (value (root 6%nat)) (value (inv_root 6%nat)) = zone.
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_inv_mul_one_7 : zmul (value (root 7%nat)) (value (inv_root 7%nat)) = zone.
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_inv_mul_one_8 : zmul (value (root 8%nat)) (value (inv_root 8%nat)) = zone.
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_inv_mul_one_9 : zmul (value (root 9%nat)) (value (inv_root 9%nat)) = zone.
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_inv_mul_one_10 : zmul (value (root 10%nat)) (value (inv_root 10%nat)) = zone.
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_inv_mul_one_11 : zmul (value (root 11%nat)) (value (inv_root 11%nat)) = zone.
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_inv_mul_one_12 : zmul (value (root 12%nat)) (value (inv_root 12%nat)) = zone.
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_inv_mul_one_13 : zmul (value (root 13%nat)) (value (inv_root 13%nat)) = zone.
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_inv_mul_one_14 : zmul (value (root 14%nat)) (value (inv_root 14%nat)) = zone.
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_inv_mul_one_15 : zmul (value (root 15%nat)) (value (inv_root 15%nat)) = zone.
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_inv_mul_one_16 : zmul (value (root 16%nat)) (value (inv_root 16%nat)) = zone.
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_inv_mul_one_17 : zmul (value (root 17%nat)) (value (inv_root 17%nat)) = zone.
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_inv_mul_one_18 : zmul (value (root 18%nat)) (value (inv_root 18%nat)) = zone.
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_inv_mul_one_19 : zmul (value (root 19%nat)) (value (inv_root 19%nat)) = zone.
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_inv_mul_one_20 : zmul (value (root 20%nat)) (value (inv_root 20%nat)) = zone.
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_inv_mul_one_21 : zmul (value (root 21%nat)) (value (inv_root 21%nat)) = zone.
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_inv_mul_one_22 : zmul (value (root 22%nat)) (value (inv_root 22%nat)) = zone.
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_inv_mul_one_23 : zmul (value (root 23%nat)) (value (inv_root 23%nat)) = zone.
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_inv_mul_one_24 : zmul (value (root 24%nat)) (value (inv_root 24%nat)) = zone.
  Proof. vm_compute. reflexivity. Qed.

  Lemma root_inv_mul_one_upto :
    forall n, (n <= S supported_max_log)%nat ->
      zmul (value (root n)) (value (inv_root n)) = zone.
  Proof.
    intros n Hn.
    destruct n as [|n]; [apply root_inv_mul_one_0|].
    destruct n as [|n]; [apply root_inv_mul_one_1|].
    destruct n as [|n]; [apply root_inv_mul_one_2|].
    destruct n as [|n]; [apply root_inv_mul_one_3|].
    destruct n as [|n]; [apply root_inv_mul_one_4|].
    destruct n as [|n]; [apply root_inv_mul_one_5|].
    destruct n as [|n]; [apply root_inv_mul_one_6|].
    destruct n as [|n]; [apply root_inv_mul_one_7|].
    destruct n as [|n]; [apply root_inv_mul_one_8|].
    destruct n as [|n]; [apply root_inv_mul_one_9|].
    destruct n as [|n]; [apply root_inv_mul_one_10|].
    destruct n as [|n]; [apply root_inv_mul_one_11|].
    destruct n as [|n]; [apply root_inv_mul_one_12|].
    destruct n as [|n]; [apply root_inv_mul_one_13|].
    destruct n as [|n]; [apply root_inv_mul_one_14|].
    destruct n as [|n]; [apply root_inv_mul_one_15|].
    destruct n as [|n]; [apply root_inv_mul_one_16|].
    destruct n as [|n]; [apply root_inv_mul_one_17|].
    destruct n as [|n]; [apply root_inv_mul_one_18|].
    destruct n as [|n]; [apply root_inv_mul_one_19|].
    destruct n as [|n]; [apply root_inv_mul_one_20|].
    destruct n as [|n]; [apply root_inv_mul_one_21|].
    destruct n as [|n]; [apply root_inv_mul_one_22|].
    destruct n as [|n]; [apply root_inv_mul_one_23|].
    destruct n as [|n]; [apply root_inv_mul_one_24|].
    cbv [supported_max_log] in Hn.
    lia.
  Qed.
End Prime181InverseFacts.
