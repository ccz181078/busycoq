From Coq Require Import Lia.
Require Import BigInt.NTTConcrete BigInt.NTTKernelBounded BigInt.BigIntMul.

Module Prime181KB := TreeNTTKernelBounded(Prime181Cfg).
Module Prime181SquareFacts.
  Module T := Prime181KB.T.
  Import T.

  Lemma root_square_0 : zpow (value (root 1%nat)) 2%nat = value (root 0%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_square_1 : zpow (value (root 2%nat)) 2%nat = value (root 1%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_square_2 : zpow (value (root 3%nat)) 2%nat = value (root 2%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_square_3 : zpow (value (root 4%nat)) 2%nat = value (root 3%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_square_4 : zpow (value (root 5%nat)) 2%nat = value (root 4%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_square_5 : zpow (value (root 6%nat)) 2%nat = value (root 5%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_square_6 : zpow (value (root 7%nat)) 2%nat = value (root 6%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_square_7 : zpow (value (root 8%nat)) 2%nat = value (root 7%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_square_8 : zpow (value (root 9%nat)) 2%nat = value (root 8%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_square_9 : zpow (value (root 10%nat)) 2%nat = value (root 9%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_square_10 : zpow (value (root 11%nat)) 2%nat = value (root 10%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_square_11 : zpow (value (root 12%nat)) 2%nat = value (root 11%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_square_12 : zpow (value (root 13%nat)) 2%nat = value (root 12%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_square_13 : zpow (value (root 14%nat)) 2%nat = value (root 13%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_square_14 : zpow (value (root 15%nat)) 2%nat = value (root 14%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_square_15 : zpow (value (root 16%nat)) 2%nat = value (root 15%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_square_16 : zpow (value (root 17%nat)) 2%nat = value (root 16%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_square_17 : zpow (value (root 18%nat)) 2%nat = value (root 17%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_square_18 : zpow (value (root 19%nat)) 2%nat = value (root 18%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_square_19 : zpow (value (root 20%nat)) 2%nat = value (root 19%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_square_20 : zpow (value (root 21%nat)) 2%nat = value (root 20%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_square_21 : zpow (value (root 22%nat)) 2%nat = value (root 21%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_square_22 : zpow (value (root 23%nat)) 2%nat = value (root 22%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma root_square_23 : zpow (value (root 24%nat)) 2%nat = value (root 23%nat).
  Proof. vm_compute. reflexivity. Qed.

  Lemma root_square_upto :
    forall n, (n < S supported_max_log)%nat ->
      zpow (value (root (S n))) 2%nat = value (root n).
  Proof.
    intros n Hn.
    destruct n as [|n]; [apply root_square_0|].
    destruct n as [|n]; [apply root_square_1|].
    destruct n as [|n]; [apply root_square_2|].
    destruct n as [|n]; [apply root_square_3|].
    destruct n as [|n]; [apply root_square_4|].
    destruct n as [|n]; [apply root_square_5|].
    destruct n as [|n]; [apply root_square_6|].
    destruct n as [|n]; [apply root_square_7|].
    destruct n as [|n]; [apply root_square_8|].
    destruct n as [|n]; [apply root_square_9|].
    destruct n as [|n]; [apply root_square_10|].
    destruct n as [|n]; [apply root_square_11|].
    destruct n as [|n]; [apply root_square_12|].
    destruct n as [|n]; [apply root_square_13|].
    destruct n as [|n]; [apply root_square_14|].
    destruct n as [|n]; [apply root_square_15|].
    destruct n as [|n]; [apply root_square_16|].
    destruct n as [|n]; [apply root_square_17|].
    destruct n as [|n]; [apply root_square_18|].
    destruct n as [|n]; [apply root_square_19|].
    destruct n as [|n]; [apply root_square_20|].
    destruct n as [|n]; [apply root_square_21|].
    destruct n as [|n]; [apply root_square_22|].
    destruct n as [|n]; [apply root_square_23|].
    cbv [supported_max_log] in Hn.
    lia.
  Qed.

  Lemma inv_root_square_0 : zpow (value (inv_root 1%nat)) 2%nat = value (inv_root 0%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_root_square_1 : zpow (value (inv_root 2%nat)) 2%nat = value (inv_root 1%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_root_square_2 : zpow (value (inv_root 3%nat)) 2%nat = value (inv_root 2%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_root_square_3 : zpow (value (inv_root 4%nat)) 2%nat = value (inv_root 3%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_root_square_4 : zpow (value (inv_root 5%nat)) 2%nat = value (inv_root 4%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_root_square_5 : zpow (value (inv_root 6%nat)) 2%nat = value (inv_root 5%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_root_square_6 : zpow (value (inv_root 7%nat)) 2%nat = value (inv_root 6%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_root_square_7 : zpow (value (inv_root 8%nat)) 2%nat = value (inv_root 7%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_root_square_8 : zpow (value (inv_root 9%nat)) 2%nat = value (inv_root 8%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_root_square_9 : zpow (value (inv_root 10%nat)) 2%nat = value (inv_root 9%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_root_square_10 : zpow (value (inv_root 11%nat)) 2%nat = value (inv_root 10%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_root_square_11 : zpow (value (inv_root 12%nat)) 2%nat = value (inv_root 11%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_root_square_12 : zpow (value (inv_root 13%nat)) 2%nat = value (inv_root 12%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_root_square_13 : zpow (value (inv_root 14%nat)) 2%nat = value (inv_root 13%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_root_square_14 : zpow (value (inv_root 15%nat)) 2%nat = value (inv_root 14%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_root_square_15 : zpow (value (inv_root 16%nat)) 2%nat = value (inv_root 15%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_root_square_16 : zpow (value (inv_root 17%nat)) 2%nat = value (inv_root 16%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_root_square_17 : zpow (value (inv_root 18%nat)) 2%nat = value (inv_root 17%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_root_square_18 : zpow (value (inv_root 19%nat)) 2%nat = value (inv_root 18%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_root_square_19 : zpow (value (inv_root 20%nat)) 2%nat = value (inv_root 19%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_root_square_20 : zpow (value (inv_root 21%nat)) 2%nat = value (inv_root 20%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_root_square_21 : zpow (value (inv_root 22%nat)) 2%nat = value (inv_root 21%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_root_square_22 : zpow (value (inv_root 23%nat)) 2%nat = value (inv_root 22%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_root_square_23 : zpow (value (inv_root 24%nat)) 2%nat = value (inv_root 23%nat).
  Proof. vm_compute. reflexivity. Qed.

  Lemma inv_root_square_upto :
    forall n, (n < S supported_max_log)%nat ->
      zpow (value (inv_root (S n))) 2%nat = value (inv_root n).
  Proof.
    intros n Hn.
    destruct n as [|n]; [apply inv_root_square_0|].
    destruct n as [|n]; [apply inv_root_square_1|].
    destruct n as [|n]; [apply inv_root_square_2|].
    destruct n as [|n]; [apply inv_root_square_3|].
    destruct n as [|n]; [apply inv_root_square_4|].
    destruct n as [|n]; [apply inv_root_square_5|].
    destruct n as [|n]; [apply inv_root_square_6|].
    destruct n as [|n]; [apply inv_root_square_7|].
    destruct n as [|n]; [apply inv_root_square_8|].
    destruct n as [|n]; [apply inv_root_square_9|].
    destruct n as [|n]; [apply inv_root_square_10|].
    destruct n as [|n]; [apply inv_root_square_11|].
    destruct n as [|n]; [apply inv_root_square_12|].
    destruct n as [|n]; [apply inv_root_square_13|].
    destruct n as [|n]; [apply inv_root_square_14|].
    destruct n as [|n]; [apply inv_root_square_15|].
    destruct n as [|n]; [apply inv_root_square_16|].
    destruct n as [|n]; [apply inv_root_square_17|].
    destruct n as [|n]; [apply inv_root_square_18|].
    destruct n as [|n]; [apply inv_root_square_19|].
    destruct n as [|n]; [apply inv_root_square_20|].
    destruct n as [|n]; [apply inv_root_square_21|].
    destruct n as [|n]; [apply inv_root_square_22|].
    destruct n as [|n]; [apply inv_root_square_23|].
    cbv [supported_max_log] in Hn.
    lia.
  Qed.
End Prime181SquareFacts.
