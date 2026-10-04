From Coq Require Import List Arith Lia.
From BusyCoq Require Export Row9Eval Row9Algebra Row9Operators.
Import ListNotations.
Local Opaque f.

Definition D (x:result) := lift_plus 4 x.
Definition L1 (x:result) := prefix 1 x.

Lemma acc_F_valid x : F x <> Some [].
Proof.
  destruct x as [w|]; [|discriminate].
  change (f w <> Some []). intro E.
  exact (f_success_nonempty w [] E eq_refl).
Qed.
Lemma acc_power_valid n x : x <> Some [] -> power F n x <> Some [].
Proof. intros E; destruct n; [exact E|apply acc_F_valid]. Qed.
Lemma acc_F_D x : x <> Some [] -> F (D x) = L1 x.
Proof.
  destruct x as [[|a u]|]; try reflexivity; [tauto|].
  intros _. change (f ((a+4)::u) = Some (1::a::u)).
  apply f_large.
Qed.
Lemma acc_F_L x : F (L1 x) = D (F x).
Proof. destruct x as [w|]; [apply f_one|reflexivity]. Qed.
Lemma acc_D_even n x : x <> Some [] ->
  power F (2*n) (D x) = D (power F n x).
Proof.
  intros E. induction n; [reflexivity|].
  replace (2*S n) with (S(S(2*n))) by lia.
  cbn [power]. rewrite IHn, acc_F_D by (apply acc_power_valid; exact E).
  apply acc_F_L.
Qed.
Lemma acc_D_odd n x : x <> Some [] ->
  power F (2*n+1) (D x) = L1 (power F n x).
Proof.
  intros E. replace (2*n+1) with (S(2*n)) by lia.
  cbn [power]. rewrite acc_D_even by exact E.
  apply acc_F_D, acc_power_valid, E.
Qed.
Lemma acc_L_even n x :
  power F (2*n) (L1 x) = L1 (power F n x).
Proof.
  induction n; [reflexivity|].
  replace (2*S n) with (S(S(2*n))) by lia.
  cbn [power]. rewrite IHn, acc_F_L, acc_F_D by apply acc_F_valid.
  reflexivity.
Qed.
Lemma acc_L_odd n x :
  power F (2*n+1) (L1 x) = D (power F (S n) x).
Proof.
  replace (2*n+1) with (S(2*n)) by lia.
  cbn [power]. rewrite acc_L_even. apply acc_F_L.
Qed.
Lemma acc_power_two n x : power F n (prefix 2 x) = prefix 2 (power F n x).
Proof.
  induction n; [reflexivity|]. cbn [power]. rewrite IHn.
  destruct (power F n x) as [w|]; [apply f_two|reflexivity].
Qed.
Lemma acc_power_three n x : power F n (prefix 3 x) = prefix 3 (power F (2*n) x).
Proof.
  induction n; [reflexivity|]. change (F(power F n(prefix 3 x)) = prefix 3(power F (2*S n) x)). rewrite IHn.
  replace (2*S n) with (S(S(2*n))) by lia.
  cbn [power]. destruct (power F (2*n) x) as [w|]; [apply f_three|reflexivity].
Qed.
Lemma acc_split_count n :
  n = if Nat.odd n then 2*Nat.div2 n+1 else 2*Nat.div2 n.
Proof.
  pose proof (Nat.div2_odd n) as H.
  destruct (Nat.odd n); cbn in *; lia.
Qed.
Lemma acc_D_binary n x : x <> Some [] ->
 power F n (D x) =
 if Nat.odd n then L1 (power F (Nat.div2 n) x)
 else D (power F (Nat.div2 n) x).
Proof.
  intro E. pose proof (acc_split_count n) as H.
  destruct (Nat.odd n); rewrite H at 1; [apply acc_D_odd|apply acc_D_even]; exact E.
Qed.
Lemma acc_L_binary n x :
 power F n (L1 x) =
 if Nat.odd n then D (power F (S(Nat.div2 n)) x)
 else L1 (power F (Nat.div2 n) x).
Proof.
  pose proof (acc_split_count n) as H.
  destruct (Nat.odd n); rewrite H at 1; [apply acc_L_odd|apply acc_L_even].
Qed.
