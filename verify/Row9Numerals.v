From Coq Require Import List Arith Lia NArith.
From BusyCoq Require Import Row9Eval Row9Operators.
Import ListNotations.

(** Binary gap numerals and the productive nonhalting family.
    The constructor [first_plus 4] doubles the represented number,
    while prefixing [1] maps n to 2*n+1. *)
Fixpoint numeral_pos (p : positive) : word :=
  match p with
  | xH => [1]
  | xO q => first_plus 4 (numeral_pos q)
  | xI q => 1 :: numeral_pos q
  end.
Definition numeral_N (n:N) : word :=
  match n with N0 => [] | Npos p => numeral_pos p end.
Definition numeral (n:nat) : word := numeral_N (N.of_nat n).

Lemma numeral_pos_nonempty p : numeral_pos p <> [].
Proof.
  induction p as [p IH|p IH|]; simpl; try discriminate.
  destruct (numeral_pos p); simpl in *; congruence.
Qed.
Lemma Eval_numeral_pos_succ p :
  Eval (numeral_pos p) (Some (numeral_pos (Pos.succ p))).
Proof.
  induction p as [p IH|p IH|].
  - cbn [numeral_pos Pos.succ]. change (Eval (1::numeral_pos p) (lift_plus 4 (Some (numeral_pos (Pos.succ p))))).
    now apply Eval_one.
  - cbn [numeral_pos Pos.succ].
    destruct (numeral_pos p) as [|a U] eqn:E.
    + exfalso. exact (numeral_pos_nonempty p E).
    + cbn [first_plus]. replace (a+4) with (S(S(S(S a)))) by lia.
      apply Eval_large.
  - change (Eval [1] (lift_plus 4 (Some [1]))).
    apply Eval_one, Eval_nil.
Qed.
Lemma Eval_numeral_succ n : Eval (numeral n) (Some (numeral (S n))).
Proof.
  unfold numeral. rewrite Nat2N.inj_succ.
  destruct (N.of_nat n) as [|p]; cbn [numeral_N N.succ].
  - apply Eval_nil.
  - apply Eval_numeral_pos_succ.
Qed.
Lemma numeral_double n : numeral (2*n) = first_plus 4 (numeral n).
Proof.
  unfold numeral. rewrite Nat2N.inj_double.
  destruct (N.of_nat n); reflexivity.
Qed.
Lemma numeral_odd n : numeral (2*n+1) = 1::numeral n.
Proof.
  replace (2*n+1) with (S(2*n)) by lia.
  unfold numeral. rewrite Nat2N.inj_succ_double.
  destruct (N.of_nat n); reflexivity.
Qed.
Lemma numeral_eight_four n : numeral (8*n+4) = 9::numeral n.
Proof.
  replace (8*n+4) with (2*(2*(2*n+1))) by lia.
  rewrite !numeral_double, numeral_odd. reflexivity.
Qed.
Lemma numeral_boundary m : 2<=m -> numeral (m+(7*m-12)) = 9::numeral (m-2).
Proof.
  intros Hm. replace (m+(7*m-12)) with (8*(m-2)+4) by lia.
  apply numeral_eight_four.
Qed.

Lemma numeral_gap q n : numeral (2^q*(2*n+1)) = (4*q+1)::numeral n.
Proof.
  induction q as [|q IH].
  - replace (2^0*(2*n+1)) with (2*n+1) by (cbn; lia).
    change (numeral (2*n+1) = 1::numeral n).
    apply numeral_odd.
  - replace (2^S q*(2*n+1)) with (2*(2^q*(2*n+1))) by (simpl Nat.pow; nia).
    rewrite numeral_double, IH. cbn [first_plus].
    f_equal. lia.
Qed.

Lemma numeral_zero : numeral 0 = [].
Proof. reflexivity. Qed.

(** The frozen selected endpoint's finite numeric tail. *)
Lemma numeral_9070 : numeral 9070 = [5;1;1;5;1;5;1;13].
Proof. vm_compute. reflexivity. Qed.

(** These conversion lemmas keep large certificate numerals binary. *)
Lemma numeral_of_N n : numeral (N.to_nat n) = numeral_N n.
Proof. unfold numeral. now rewrite N2Nat.id. Qed.
Lemma numeral_of_pos p : numeral (Pos.to_nat p) = numeral_pos p.
Proof. exact (numeral_of_N (Npos p)). Qed.

Theorem f_numeral n : f (numeral n) = Some (numeral (S n)).
Proof. apply Eval_iff_f, Eval_numeral_succ. Qed.

Theorem F_numeral n : F (Some (numeral n)) = Some (numeral (S n)).
Proof. apply f_numeral. Qed.

Theorem power_F_numeral a n :
  power F a (Some (numeral n)) = Some (numeral (n+a)).
Proof.
  induction a as [|a IH].
  - cbn [power]. now rewrite Nat.add_0_r.
  - cbn [power]. now rewrite IH, F_numeral, Nat.add_succ_r.
Qed.

Corollary power_F_nil a : power F a (Some []) = Some (numeral a).
Proof. exact (power_F_numeral a 0). Qed.

Corollary power_F_numeral_N a n :
  power F (N.to_nat a) (Some (numeral_N n)) = Some (numeral_N (n+a)%N).
Proof.
  rewrite <- (numeral_of_N n), <- (numeral_of_N (n+a)%N).
  now rewrite power_F_numeral, N2Nat.inj_add.
Qed.
