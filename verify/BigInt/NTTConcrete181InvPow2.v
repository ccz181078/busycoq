From Coq Require Import Lia.
Require Import BigInt.NTTConcrete BigInt.NTTKernelBounded BigInt.BigIntMul.

Module Prime181KBPow := TreeNTTKernelBounded(Prime181Cfg).
Module Prime181InvPow2Facts.
  Module T := Prime181KBPow.T.
  Import T.

  Lemma inv_pow2_zero :
    value (inv_pow2 0%nat) = zone.
  Proof. vm_compute. reflexivity. Qed.

  Lemma inv_pow2_double_0 :
    zadd (value (inv_pow2 1%nat)) (value (inv_pow2 1%nat)) = value (inv_pow2 0%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_pow2_double_1 :
    zadd (value (inv_pow2 2%nat)) (value (inv_pow2 2%nat)) = value (inv_pow2 1%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_pow2_double_2 :
    zadd (value (inv_pow2 3%nat)) (value (inv_pow2 3%nat)) = value (inv_pow2 2%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_pow2_double_3 :
    zadd (value (inv_pow2 4%nat)) (value (inv_pow2 4%nat)) = value (inv_pow2 3%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_pow2_double_4 :
    zadd (value (inv_pow2 5%nat)) (value (inv_pow2 5%nat)) = value (inv_pow2 4%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_pow2_double_5 :
    zadd (value (inv_pow2 6%nat)) (value (inv_pow2 6%nat)) = value (inv_pow2 5%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_pow2_double_6 :
    zadd (value (inv_pow2 7%nat)) (value (inv_pow2 7%nat)) = value (inv_pow2 6%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_pow2_double_7 :
    zadd (value (inv_pow2 8%nat)) (value (inv_pow2 8%nat)) = value (inv_pow2 7%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_pow2_double_8 :
    zadd (value (inv_pow2 9%nat)) (value (inv_pow2 9%nat)) = value (inv_pow2 8%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_pow2_double_9 :
    zadd (value (inv_pow2 10%nat)) (value (inv_pow2 10%nat)) = value (inv_pow2 9%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_pow2_double_10 :
    zadd (value (inv_pow2 11%nat)) (value (inv_pow2 11%nat)) = value (inv_pow2 10%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_pow2_double_11 :
    zadd (value (inv_pow2 12%nat)) (value (inv_pow2 12%nat)) = value (inv_pow2 11%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_pow2_double_12 :
    zadd (value (inv_pow2 13%nat)) (value (inv_pow2 13%nat)) = value (inv_pow2 12%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_pow2_double_13 :
    zadd (value (inv_pow2 14%nat)) (value (inv_pow2 14%nat)) = value (inv_pow2 13%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_pow2_double_14 :
    zadd (value (inv_pow2 15%nat)) (value (inv_pow2 15%nat)) = value (inv_pow2 14%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_pow2_double_15 :
    zadd (value (inv_pow2 16%nat)) (value (inv_pow2 16%nat)) = value (inv_pow2 15%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_pow2_double_16 :
    zadd (value (inv_pow2 17%nat)) (value (inv_pow2 17%nat)) = value (inv_pow2 16%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_pow2_double_17 :
    zadd (value (inv_pow2 18%nat)) (value (inv_pow2 18%nat)) = value (inv_pow2 17%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_pow2_double_18 :
    zadd (value (inv_pow2 19%nat)) (value (inv_pow2 19%nat)) = value (inv_pow2 18%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_pow2_double_19 :
    zadd (value (inv_pow2 20%nat)) (value (inv_pow2 20%nat)) = value (inv_pow2 19%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_pow2_double_20 :
    zadd (value (inv_pow2 21%nat)) (value (inv_pow2 21%nat)) = value (inv_pow2 20%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_pow2_double_21 :
    zadd (value (inv_pow2 22%nat)) (value (inv_pow2 22%nat)) = value (inv_pow2 21%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_pow2_double_22 :
    zadd (value (inv_pow2 23%nat)) (value (inv_pow2 23%nat)) = value (inv_pow2 22%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma inv_pow2_double_23 :
    zadd (value (inv_pow2 24%nat)) (value (inv_pow2 24%nat)) = value (inv_pow2 23%nat).
  Proof. vm_compute. reflexivity. Qed.

  Lemma inv_pow2_double_upto :
    forall n, (n < S supported_max_log)%nat ->
      zadd (value (inv_pow2 (S n))) (value (inv_pow2 (S n))) = value (inv_pow2 n).
  Proof.
    intros n Hn.
    destruct n as [|n]; [apply inv_pow2_double_0|].
    destruct n as [|n]; [apply inv_pow2_double_1|].
    destruct n as [|n]; [apply inv_pow2_double_2|].
    destruct n as [|n]; [apply inv_pow2_double_3|].
    destruct n as [|n]; [apply inv_pow2_double_4|].
    destruct n as [|n]; [apply inv_pow2_double_5|].
    destruct n as [|n]; [apply inv_pow2_double_6|].
    destruct n as [|n]; [apply inv_pow2_double_7|].
    destruct n as [|n]; [apply inv_pow2_double_8|].
    destruct n as [|n]; [apply inv_pow2_double_9|].
    destruct n as [|n]; [apply inv_pow2_double_10|].
    destruct n as [|n]; [apply inv_pow2_double_11|].
    destruct n as [|n]; [apply inv_pow2_double_12|].
    destruct n as [|n]; [apply inv_pow2_double_13|].
    destruct n as [|n]; [apply inv_pow2_double_14|].
    destruct n as [|n]; [apply inv_pow2_double_15|].
    destruct n as [|n]; [apply inv_pow2_double_16|].
    destruct n as [|n]; [apply inv_pow2_double_17|].
    destruct n as [|n]; [apply inv_pow2_double_18|].
    destruct n as [|n]; [apply inv_pow2_double_19|].
    destruct n as [|n]; [apply inv_pow2_double_20|].
    destruct n as [|n]; [apply inv_pow2_double_21|].
    destruct n as [|n]; [apply inv_pow2_double_22|].
    destruct n as [|n]; [apply inv_pow2_double_23|].
    cbv [supported_max_log] in Hn.
    lia.
  Qed.
End Prime181InvPow2Facts.
