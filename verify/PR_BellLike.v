(* Classification: bell-like.
   Consolidated from busycoq PR #21, #22, pinned in PR19_28_INVENTORY.json.
   Original proofs: Dahoas.
   Common declarations are reused; each blank-state initialization is checked separately. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Lia ZifyNat ZifyN PeanoNat NArith String List.

Module TM1.
Import BusyCoq.Individual62.

Import Lia ZifyNat ZifyN PeanoNat NArith String List.

Import ListNotations.

Open Scope list.

Open Scope sym.

Definition tm := Eval compute in (TM_from_str "1RB0RE_1RC1LF_0LD0RE_---1LE_1RA0LB_1LB0LC").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Open Scope nat_scope.

Ltac simpl_lhs :=
  autorewrite with tape_pre;
  cbn [move_left move_right Streams.hd Streams.tl Str_app];
  repeat rewrite <- const_unfold.

Ltac tstep :=
  (eapply evstep_step || eapply progress_step); [prove_step | simpl_lhs].

Lemma pow_add_append_right (u : list sym) (m n : nat) (r : side) :
  (u ^^ (m + n)) *> r = (u ^^ m) *> ((u ^^ n) *> r).
Proof.
  rewrite lpow_add, Str_app_assoc. reflexivity.
Qed.

Lemma pow_succ_append_right (u : list sym) (n : nat) (r : side) :
  (u ^^ (n + 1)) *> r = u *> ((u ^^ n) *> r).
Proof.
  replace (n + 1) with (S n) by lia.
  cbn [lpow]. apply Str_app_assoc.
Qed.

Lemma pow_succ_append_right' (u : list sym) (k : nat) (r : side) :
  (u ^^ k) *> (u *> r) = (u ^^ (k + 1)) *> r.
Proof.
  replace (k + 1) with (S k) by lia.
  cbn [lpow]. rewrite <- Str_app_assoc, lpow_shift. reflexivity.
Qed.

Lemma pow_add_append_left (s : side) (u : list sym) (m n : nat) :
  s <* (u ^^ (m + n)) = (s <* (u ^^ m)) <* (u ^^ n).
Proof.
  replace (m + n) with (n + m) by lia.
  rewrite lpow_add, Str_app_assoc. reflexivity.
Qed.

Lemma cons_0_pow_10 (k : nat) : forall (r : side),
  [0]%sym *> ([1; 0]%sym ^^ k *> r) = [0; 1]%sym ^^ k *> ([0]%sym *> r).
Proof.
  induction k as [| k IH]; intro r.
  - reflexivity.
  - cbn [lpow app Str_app]. f_equal. f_equal. exact (IH r).
Qed.

Lemma cons_1_pow_01 (k : nat) : forall (r : side),
  [1]%sym *> ([0; 1]%sym ^^ k *> r) = [1; 0]%sym ^^ k *> ([1]%sym *> r).
Proof.
  induction k as [| k IH]; intro r.
  - reflexivity.
  - cbn [lpow app Str_app]. f_equal. f_equal. exact (IH r).
Qed.

Lemma append_0_pow_01 (X : side) (k : nat) :
  (X <* [0]%sym) <* ([0; 1]%sym ^^ k) = (X <* ([1; 0]%sym ^^ k)) <* [0]%sym.
Proof.
  symmetry. exact (cons_0_pow_10 k X).
Qed.

Lemma append_1_pow_01 (X : side) (k : nat) :
  (X <* ([0; 1]%sym ^^ k)) <* [1]%sym = (X <* [1]%sym) <* ([1; 0]%sym ^^ k).
Proof.
  exact (cons_1_pow_01 k X).
Qed.

Lemma append_1_1 (X : side) : (X <* [1]%sym) <* [1]%sym = X <* [1; 1]%sym.
Proof. reflexivity. Qed.

Lemma append_11_1 (X : side) : (X <* [1; 1]%sym) <* [1]%sym = X <* [1; 1; 1]%sym.
Proof. reflexivity. Qed.

Lemma append_011 (X : side) : X <* [0; 1; 1]%sym = (X <* [1; 1]%sym) <* [0]%sym.
Proof. reflexivity. Qed.

Lemma pow2_11_append (X : side) :
  [1; 1]%sym ^^ 2 *> X = [1; 1; 1; 1]%sym *> X.
Proof. reflexivity. Qed.

Lemma mul_pow2_ge (c k : nat) : c <= c * 2 ^ k.
Proof.
  assert (H : 1 <= 2 ^ k) by (induction k; cbn [Nat.pow]; lia).
  nia.
Qed.

Lemma cons_1_pow_11 (k : nat) : forall (r : side),
  [1]%sym *> ([1; 1]%sym ^^ k *> r) = [1; 1]%sym ^^ k *> ([1]%sym *> r).
Proof.
  induction k as [| k IH]; intro r.
  - reflexivity.
  - cbn [lpow app Str_app]. f_equal. f_equal. exact (IH r).
Qed.

Lemma pow_11_even (k : nat) (r : side) :
  [1; 1]%sym ^^ (2 * k) *> r = [1; 1; 1; 1]%sym ^^ k *> r.
Proof.
  induction k as [| k IH].
  - reflexivity.
  - replace (2 * S k) with (2 + 2 * k) by lia.
    rewrite pow_add_append_right, IH.
    reflexivity.
Qed.

Lemma shift_E_right_01 (k : nat) : forall (l r : side),
  l {{E}}> ([0; 1]%sym ^^ k *> r) -->* (l <* ([0; 1]%sym ^^ k)) {{E}}> r.
Proof.
  induction k as [| k IH]; intros l r.
  - finish.
  - cbn [lpow app Str_app].
    do 2 tstep.
    eapply evstep_trans; [exact (IH (l <* [0; 1]%sym) r) |].
    change (l <* [0; 1]%sym) with ([0; 1]%sym *> l).
    rewrite <- Str_app_assoc, lpow_shift, Str_app_assoc.
    finish.
Qed.

Lemma shift_B_left_10 (k : nat) : forall (l r : side),
  (l <* ([1; 0]%sym ^^ k)) <{{B}} r -->* l <{{B}} ([1; 1]%sym ^^ k *> r).
Proof.
  induction k as [| k IH]; intros l r.
  - finish.
  - cbn [lpow app Str_app].
    do 2 tstep.
    eapply evstep_trans; [exact (IH l ([1; 1]%sym *> r)) |].
    rewrite <- Str_app_assoc, lpow_shift, Str_app_assoc.
    finish.
Qed.

Lemma shift_E_left_10 (k : nat) : forall (l r : side),
  (l <* ([1; 0]%sym ^^ k)) <{{E}} r -->* l <{{E}} ([1; 0]%sym ^^ k *> r).
Proof.
  induction k as [| k IH]; intros l r.
  - finish.
  - cbn [lpow app Str_app].
    do 4 tstep.
    eapply evstep_trans; [exact (IH l ([1; 0]%sym *> r)) |].
    rewrite <- Str_app_assoc, lpow_shift, Str_app_assoc.
    finish.
Qed.

Definition r0 : side := [0; 1; 0; 1; 1; 0; 1]%sym *> 0inf%sym.

Lemma bounce_E_01 (l : side) (d : nat) (r : side) :
  (l <* [0; 1]%sym) {{E}}> ([0; 1]%sym ^^ d *> ([1]%sym *> r)) -->+
  (l <* [1]%sym) <{{E}} ([1; 0]%sym ^^ (d + 1) *> r).
Proof.
  pose proof (shift_E_right_01 d (l <* [0; 1]%sym) ([1]%sym *> r)) as H1.
  replace (l <* [0; 1]%sym) with ((l <* [1]%sym) <* [0]%sym) in H1 by reflexivity.
  rewrite (append_0_pow_01 (l <* [1]%sym) d) in H1.
  eapply evstep_progress_trans; [exact H1 |].
  assert (H2 : (((l <* [1]%sym) <* ([1; 0]%sym ^^ d)) <* [0]%sym) {{E}}> ([1]%sym *> r) -->+
               ((l <* [1]%sym) <* ([1; 0]%sym ^^ d)) <{{E}} ([1; 0]%sym *> r)).
  { eapply progress_intro; [prove_step | simpl_lhs]. do 3 tstep. finish. }
  eapply progress_evstep_trans; [exact H2 |].
  pose proof (shift_E_left_10 d (l <* [1]%sym) ([1; 0]%sym *> r)) as H3.
  rewrite pow_succ_append_right' in H3.
  exact H3.
Qed.

Lemma bounce_E_end (l : side) (d : nat) :
  (l <* [0; 1]%sym) {{E}}> ([0; 1]%sym ^^ d *> ([0; 0; 1]%sym *> 0inf%sym)) -->+
  (l <* [1]%sym) <{{B}} ([1; 1]%sym ^^ d *> r0).
Proof.
  pose proof (shift_E_right_01 d (l <* [0; 1]%sym) ([0; 0; 1]%sym *> 0inf%sym)) as H1.
  replace (l <* [0; 1]%sym) with ((l <* [1]%sym) <* [0]%sym) in H1 by reflexivity.
  rewrite (append_0_pow_01 (l <* [1]%sym) d) in H1.
  eapply evstep_progress_trans; [exact H1 |].
  assert (H2 : (((l <* [1]%sym) <* ([1; 0]%sym ^^ d)) <* [0]%sym) {{E}}> ([0; 0; 1]%sym *> 0inf%sym) -->+
               ((l <* [1]%sym) <* ([1; 0]%sym ^^ d)) <{{B}} r0).
  { unfold r0. eapply progress_intro; [prove_step | simpl_lhs]. do 23 tstep. finish. }
  eapply progress_evstep_trans; [exact H2 |].
  exact (shift_B_left_10 d (l <* [1]%sym) r0).
Qed.

Lemma rule1_step (a : nat) (r : side) :
  0inf%sym <{{E}} ([1; 0]%sym ^^ (a + 1) *> ([1; 1]%sym *> r)) -->+
  0inf%sym <{{E}} ([1; 0]%sym ^^ (a + 3) *> r).
Proof.
  rewrite pow_succ_append_right.
  assert (H1 : 0inf%sym <{{E}} ([1; 0]%sym *> ([1; 0]%sym ^^ a *> ([1; 1]%sym *> r))) -->+
               (0inf%sym <* [0; 1]%sym) {{E}}> ([0]%sym *> ([1; 0]%sym ^^ a *> ([1; 1]%sym *> r)))).
  { eapply progress_intro; [prove_step | simpl_lhs]. do 1 tstep. finish. }
  rewrite cons_0_pow_10 in H1.
  change ([0]%sym *> ([1; 1]%sym *> r)) with ([0; 1]%sym *> ([1]%sym *> r)) in H1.
  rewrite pow_succ_append_right' in H1.
  eapply progress_trans; [exact H1 |].
  eapply progress_trans; [exact (bounce_E_01 0inf%sym (a + 1) r) |].
  replace (a + 1 + 1) with (a + 2) by lia.
  assert (H3 : (0inf%sym <* [1]%sym) <{{E}} ([1; 0]%sym ^^ (a + 2) *> r) -->+
               0inf%sym <{{E}} ([1; 0]%sym *> ([1; 0]%sym ^^ (a + 2) *> r))).
  { eapply progress_intro; [prove_step | simpl_lhs]. do 3 tstep. finish. }
  rewrite <- pow_succ_append_right in H3.
  replace (a + 2 + 1) with (a + 3) in H3 by lia.
  exact H3.
Qed.

Lemma rule1_loop (k : nat) : forall (a : nat) (r : side),
  0inf%sym <{{E}} ([1; 0]%sym ^^ (a + 1) *> ([1; 1]%sym ^^ k *> r)) -->*
  0inf%sym <{{E}} ([1; 0]%sym ^^ (a + 2 * k + 1) *> r).
Proof.
  induction k as [| k IH]; intros a r.
  - replace (a + 2 * 0 + 1) with (a + 1) by lia.
    cbn [lpow Str_app]. finish.
  - cbn [lpow app Str_app].
    change (1%sym >> 1%sym >> ([1; 1]%sym ^^ k *> r)) with ([1; 1]%sym *> ([1; 1]%sym ^^ k *> r)).
    eapply evstep_trans.
    + apply progress_evstep. exact (rule1_step a ([1; 1]%sym ^^ k *> r)).
    + replace (a + 3) with ((a + 2) + 1) by lia.
      eapply evstep_trans; [exact (IH (a + 2) r) |].
      replace (a + 2 + 2 * k + 1) with (a + 2 * S k + 1) by lia.
      finish.
Qed.

Lemma finish_B_left (m : nat) (r : side) :
  ((0inf%sym <* [1]%sym) <* ([1; 0]%sym ^^ m)) <{{B}} r -->+
  0inf%sym <{{E}} ([1; 0]%sym ^^ (2 * m + 2) *> r).
Proof.
  eapply evstep_progress_trans; [exact (shift_B_left_10 m (0inf%sym <* [1]%sym) r) |].
  assert (H2 : (0inf%sym <* [1]%sym) <{{B}} ([1; 1]%sym ^^ m *> r) -->+
               0inf%sym <{{E}} ([1; 0]%sym ^^ 2 *> ([1; 1]%sym ^^ m *> r))).
  { eapply progress_intro; [prove_step | simpl_lhs]. do 11 tstep. finish. }
  eapply progress_evstep_trans; [exact H2 |].
  pose proof (rule1_loop m 1 r) as H3.
  replace (1 + 2 * m + 1) with (2 * m + 2) in H3 by lia.
  exact H3.
Qed.

Lemma sweep_mid (a b : nat) (r' : side) :
  0inf%sym <{{E}} ([1; 0]%sym ^^ (a + 2) *> ([0; 1]%sym ^^ (b + 1) *> r')) -->+
  (((0inf%sym <* ([0; 1]%sym ^^ (a + 1))) <* [0; 0; 1]%sym) <* [0; 1]%sym) {{E}}>
    ([0; 1]%sym ^^ b *> r').
Proof.
  replace (a + 2) with ((a + 1) + 1) by lia.
  rewrite pow_succ_append_right.
  assert (H1 : 0inf%sym <{{E}} ([1; 0]%sym *> ([1; 0]%sym ^^ (a + 1) *> ([0; 1]%sym ^^ (b + 1) *> r'))) -->+
               (0inf%sym <* [0; 1]%sym) {{E}}> ([0]%sym *> ([1; 0]%sym ^^ (a + 1) *> ([0; 1]%sym ^^ (b + 1) *> r')))).
  { eapply progress_intro; [prove_step | simpl_lhs]. do 1 tstep. finish. }
  rewrite cons_0_pow_10 in H1.
  eapply progress_trans; [exact H1 |].
  rewrite (pow_succ_append_right [0; 1]%sym b).
  pose proof (shift_E_right_01 (a + 1) (0inf%sym <* [0; 1]%sym) ([0]%sym *> ([0; 1]%sym *> ([0; 1]%sym ^^ b *> r')))) as H2.
  assert (Heq1 : (0inf%sym <* [0; 1]%sym) <* ([0; 1]%sym ^^ (a + 1)) =
                 (0inf%sym <* ([0; 1]%sym ^^ (a + 1))) <* [0; 1]%sym).
  { rewrite pow_succ_append_right', <- pow_succ_append_right. reflexivity. }
  rewrite Heq1 in H2.
  eapply evstep_progress_trans; [exact H2 |].
  eapply progress_intro; [prove_step | simpl_lhs]. do 6 tstep. finish.
Qed.

Lemma sweep_init (a b : nat) (r : side) :
  0inf%sym <{{E}} ([1; 0]%sym ^^ (a + 2) *> ([0; 1]%sym ^^ (b + 1) *> ([1]%sym *> r))) -->+
  ((0inf%sym <* ([0; 1]%sym ^^ (a + 1))) <* [0; 1]%sym) <{{E}} ([1; 0]%sym ^^ (b + 2) *> r).
Proof.
  eapply progress_trans; [exact (sweep_mid a b ([1]%sym *> r)) |].
  eapply progress_trans; [exact (bounce_E_01 ((0inf%sym <* ([0; 1]%sym ^^ (a + 1))) <* [0; 0; 1]%sym) b r) |].
  assert (H3 : (((0inf%sym <* ([0; 1]%sym ^^ (a + 1))) <* [0; 0; 1]%sym) <* [1]%sym) <{{E}}
                 ([1; 0]%sym ^^ (b + 1) *> r) -->+
               ((0inf%sym <* ([0; 1]%sym ^^ (a + 1))) <* [0; 1]%sym) <{{E}}
                 ([1; 0]%sym *> ([1; 0]%sym ^^ (b + 1) *> r))).
  { eapply progress_intro; [prove_step | simpl_lhs]. do 3 tstep. finish. }
  rewrite <- (pow_succ_append_right [1; 0]%sym) in H3.
  replace (b + 1 + 1) with (b + 2) in H3 by lia.
  exact H3.
Qed.

Lemma step14_E111 (l s : side) :
  ((l <* ([0; 1]%sym ^^ 2)) <* [1; 1; 1]%sym) <{{E}} s -->+
  ((l <* [0; 0; 1; 1]%sym) <* [0; 1]%sym) {{E}}> ([0]%sym *> s).
Proof.
  eapply progress_intro; [prove_step | simpl_lhs]. do 13 tstep. finish.
Qed.

Lemma half_E1_a (l : side) (d : nat) (r : side) :
  ((l <* ([0; 1]%sym ^^ 2)) <* [1; 1; 1]%sym) <{{E}} ([1; 0]%sym ^^ d *> ([1; 1]%sym *> r)) -->+
  (l <* [0; 1; 1]%sym) <{{E}} ([1; 0]%sym ^^ (d + 3) *> r).
Proof.
  pose proof (step14_E111 l ([1; 0]%sym ^^ d *> ([1; 1]%sym *> r))) as H1.
  rewrite cons_0_pow_10 in H1.
  change ([0]%sym *> ([1; 1]%sym *> r)) with ([0; 1]%sym *> ([1]%sym *> r)) in H1.
  rewrite pow_succ_append_right' in H1.
  eapply progress_trans; [exact H1 |].
  eapply progress_trans; [exact (bounce_E_01 (l <* [0; 0; 1; 1]%sym) (d + 1) r) |].
  replace (d + 1 + 1) with (d + 2) by lia.
  assert (H3 : ((l <* [0; 0; 1; 1]%sym) <* [1]%sym) <{{E}} ([1; 0]%sym ^^ (d + 2) *> r) -->+
               (l <* [0; 1; 1]%sym) <{{E}} ([1; 0]%sym *> ([1; 0]%sym ^^ (d + 2) *> r))).
  { eapply progress_intro; [prove_step | simpl_lhs]. do 3 tstep. finish. }
  rewrite <- pow_succ_append_right in H3.
  replace (d + 2 + 1) with (d + 3) in H3 by lia.
  exact H3.
Qed.

Lemma half_E1_b (l : side) (d : nat) (r : side) :
  (l <* [0]%sym) <{{E}} ([1; 0]%sym ^^ (d + 1) *> ([1; 1]%sym *> r)) -->+
  (l <* [1]%sym) <{{E}} ([1; 0]%sym ^^ (d + 2) *> r).
Proof.
  rewrite pow_succ_append_right.
  assert (H1 : (l <* [0]%sym) <{{E}} ([1; 0]%sym *> ([1; 0]%sym ^^ d *> ([1; 1]%sym *> r))) -->+
               (l <* [0; 1]%sym) {{E}}> ([0]%sym *> ([1; 0]%sym ^^ d *> ([1; 1]%sym *> r)))).
  { eapply progress_intro; [prove_step | simpl_lhs]. do 1 tstep. finish. }
  rewrite cons_0_pow_10 in H1.
  change ([0]%sym *> ([1; 1]%sym *> r)) with ([0; 1]%sym *> ([1]%sym *> r)) in H1.
  rewrite pow_succ_append_right' in H1.
  eapply progress_trans; [exact H1 |].
  pose proof (bounce_E_01 l (d + 1) r) as H2.
  replace (d + 1 + 1) with (d + 2) in H2 by lia.
  exact H2.
Qed.

Lemma loop_E1_step (l : side) (d : nat) (r : side) :
  ((l <* ([0; 1]%sym ^^ 2)) <* [1; 1; 1]%sym) <{{E}} ([1; 0]%sym ^^ d *> ([1; 1; 1; 1]%sym *> r)) -->+
  (l <* [1; 1; 1]%sym) <{{E}} ([1; 0]%sym ^^ (d + 4) *> r).
Proof.
  change ([1; 1; 1; 1]%sym *> r) with ([1; 1]%sym *> ([1; 1]%sym *> r)).
  pose proof (half_E1_a l d ([1; 1]%sym *> r)) as H1.
  change (l <* [0; 1; 1]%sym) with ((l <* [1; 1]%sym) <* [0]%sym) in H1.
  replace (d + 3) with ((d + 2) + 1) in H1 by lia.
  eapply progress_trans; [exact H1 |].
  pose proof (half_E1_b (l <* [1; 1]%sym) (d + 2) r) as H2.
  replace (d + 2 + 2) with (d + 4) in H2 by lia.
  exact H2.
Qed.

Lemma loop_E1_iter (k : nat) : forall (l : side) (d : nat) (r : side),
  ((l <* ([0; 1]%sym ^^ (2 * k))) <* [1; 1; 1]%sym) <{{E}}
    ([1; 0]%sym ^^ d *> ([1; 1; 1; 1]%sym ^^ k *> r)) -->*
  (l <* [1; 1; 1]%sym) <{{E}} ([1; 0]%sym ^^ (d + 4 * k) *> r).
Proof.
  induction k as [| k IH]; intros l d r.
  - replace (2 * 0) with 0 by lia.
    replace (d + 4 * 0) with d by lia.
    cbn [lpow Str_app]. finish.
  - replace (2 * S k) with (2 * k + 2) by lia.
    rewrite pow_add_append_left.
    replace (S k) with (k + 1) by lia.
    rewrite (pow_succ_append_right [1; 1; 1; 1]%sym k).
    eapply evstep_trans.
    + apply progress_evstep.
      exact (loop_E1_step (l <* ([0; 1]%sym ^^ (2 * k))) d ([1; 1; 1; 1]%sym ^^ k *> r)).
    + eapply evstep_trans; [exact (IH l (d + 4) r) |].
      replace (d + 4 + 4 * k) with (d + 4 * (k + 1)) by lia.
      finish.
Qed.

Lemma rule2_gen (a b m : nat) (r : side) :
  0inf%sym <{{E}} ([1; 0]%sym ^^ (a + 2) *> ([0; 1]%sym ^^ (b + 1) *>
    ([1]%sym *> ([1; 0]%sym ^^ m *> ([1; 1]%sym *> r))))) -->+
  0inf%sym <{{E}} ([1; 0]%sym ^^ (2 * a + 4) *> ([0; 1]%sym ^^ (b + m + 3) *> ([0]%sym *> r))).
Proof.
  pose proof (sweep_init a b ([1; 0]%sym ^^ m *> ([1; 1]%sym *> r))) as H1.
  rewrite <- pow_add_append_right in H1.
  replace (b + 2 + m) with ((b + m + 1) + 1) in H1 by lia.
  change ((0inf%sym <* ([0; 1]%sym ^^ (a + 1))) <* [0; 1]%sym)
    with (((0inf%sym <* ([0; 1]%sym ^^ (a + 1))) <* [1]%sym) <* [0]%sym) in H1.
  eapply progress_trans; [exact H1 |].
  pose proof (half_E1_b ((0inf%sym <* ([0; 1]%sym ^^ (a + 1))) <* [1]%sym) (b + m + 1) r) as H2.
  replace (b + m + 1 + 2) with (b + m + 3) in H2 by lia.
  eapply progress_trans; [exact H2 |].
  assert (H3 : (((0inf%sym <* ([0; 1]%sym ^^ (a + 1))) <* [1]%sym) <* [1]%sym) <{{E}}
                 ([1; 0]%sym ^^ (b + m + 3) *> r) -->+
               ((0inf%sym <* [1]%sym) <* ([1; 0]%sym ^^ (a + 1))) <{{B}}
                 ([0; 1]%sym ^^ (b + m + 3) *> ([0]%sym *> r))).
  { rewrite <- cons_0_pow_10, <- append_1_pow_01.
    eapply progress_intro; [prove_step | simpl_lhs]. finish. }
  eapply progress_trans; [exact H3 |].
  pose proof (finish_B_left (a + 1) ([0; 1]%sym ^^ (b + m + 3) *> ([0]%sym *> r))) as H4.
  replace (2 * (a + 1) + 2) with (2 * a + 4) in H4 by lia.
  exact H4.
Qed.

Lemma rule2_step (a b : nat) (r : side) :
  0inf%sym <{{E}} ([1; 0]%sym ^^ (a + 2) *> ([0; 1]%sym ^^ (b + 1) *> ([1; 1; 1; 1]%sym *> r))) -->+
  0inf%sym <{{E}} ([1; 0]%sym ^^ (2 * a + 4) *> ([0; 1]%sym ^^ (b + 4) *> r)).
Proof.
  pose proof (rule2_gen a b 0 ([1]%sym *> r)) as H1.
  cbn [lpow Str_app] in H1.
  replace (b + 0 + 3) with (b + 3) in H1 by lia.
  change (1%sym >> 1%sym >> 1%sym >> 1%sym >> r) with ([1; 1; 1; 1]%sym *> r) in H1.
  change (0%sym >> 1%sym >> r) with ([0; 1]%sym *> r) in H1.
  rewrite pow_succ_append_right' in H1.
  replace (b + 3 + 1) with (b + 4) in H1 by lia.
  exact H1.
Qed.

Lemma rule2_loop (k : nat) : forall (a b : nat) (r : side),
  0inf%sym <{{E}} ([1; 0]%sym ^^ (a + 2) *> ([0; 1]%sym ^^ (b + 1) *>
    ([1; 1; 1; 1]%sym ^^ k *> r))) -->*
  0inf%sym <{{E}} ([1; 0]%sym ^^ ((a + 2) * 2 ^ k) *>
    ([0; 1]%sym ^^ (b + 3 * k + 1) *> r)).
Proof.
  induction k as [| k IH]; intros a b r.
  - replace ((a + 2) * 2 ^ 0) with (a + 2) by (cbn [Nat.pow]; lia).
    replace (b + 3 * 0 + 1) with (b + 1) by lia.
    cbn [lpow Str_app]. finish.
  - replace (S k) with (k + 1) by lia.
    rewrite (pow_succ_append_right [1; 1; 1; 1]%sym k).
    eapply evstep_trans.
    + apply progress_evstep.
      exact (rule2_step a b ([1; 1; 1; 1]%sym ^^ k *> r)).
    + replace (2 * a + 4) with ((2 * a + 2) + 2) by lia.
      replace (b + 4) with ((b + 3) + 1) by lia.
      eapply evstep_trans; [exact (IH (2 * a + 2) (b + 3) r) |].
      assert (Ha : (2 * a + 2 + 2) * 2 ^ k = (a + 2) * 2 ^ (k + 1)).
      { replace (k + 1) with (S k) by lia. cbn [Nat.pow]. lia. }
      rewrite Ha.
      replace (b + 3 + 3 * k + 1) with (b + 3 * (k + 1) + 1) by lia.
      finish.
Qed.

Lemma trans_c2_v1 (a b : nat) :
  0inf%sym <{{E}} ([1; 0]%sym ^^ (a + 2) *> ([0; 1]%sym ^^ (b + 1) *> ([1; 1]%sym *> r0))) -->+
  0inf%sym <{{E}} ([1; 0]%sym ^^ (2 * a + 4) *> ([0; 1]%sym ^^ (b + 5) *> ([0; 0; 1]%sym *> 0inf%sym))).
Proof.
  assert (Heq_r0 : [1; 1]%sym *> r0 =
    [1]%sym *> ([1; 0]%sym ^^ 2 *> ([1; 1]%sym *> ([0; 1]%sym *> 0inf%sym)))) by reflexivity.
  rewrite Heq_r0.
  pose proof (rule2_gen a b 2 ([0; 1]%sym *> 0inf%sym)) as H1.
  replace (b + 2 + 3) with (b + 5) in H1 by lia.
  exact H1.
Qed.

Lemma trans_c2_v2 (a b : nat) :
  0inf%sym <{{E}} ([1; 0]%sym ^^ (a + 2) *> ([0; 1]%sym ^^ (b + 2) *> ([0; 0; 1]%sym *> 0inf%sym))) -->+
  0inf%sym <{{E}} ([1; 0]%sym ^^ (2 * a + 4) *>
    ([0; 1]%sym ^^ 2 *> ([1; 1]%sym ^^ b *> ([1]%sym *> r0)))).
Proof.
  replace (b + 2) with ((b + 1) + 1) by lia.
  eapply progress_trans; [exact (sweep_mid a (b + 1) ([0; 0; 1]%sym *> 0inf%sym)) |].
  pose proof (bounce_E_end ((0inf%sym <* ([0; 1]%sym ^^ (a + 1))) <* [0; 0; 1]%sym) (b + 1)) as H2.
  rewrite (pow_succ_append_right [1; 1]%sym) in H2.
  eapply progress_trans; [exact H2 |].
  assert (H3 : (((0inf%sym <* ([0; 1]%sym ^^ (a + 1))) <* [0; 0; 1]%sym) <* [1]%sym) <{{B}}
                 ([1; 1]%sym *> ([1; 1]%sym ^^ b *> r0)) -->+
               ((0inf%sym <* ([0; 1]%sym ^^ (a + 1))) <* [1]%sym) <{{B}}
                 ([0; 1]%sym ^^ 2 *> ([1]%sym *> ([1; 1]%sym ^^ b *> r0)))).
  { eapply progress_intro; [prove_step | simpl_lhs]. do 8 tstep. finish. }
  rewrite append_1_pow_01, cons_1_pow_11 in H3.
  eapply progress_trans; [exact H3 |].
  pose proof (finish_B_left (a + 1) ([0; 1]%sym ^^ 2 *> ([1; 1]%sym ^^ b *> ([1]%sym *> r0)))) as H4.
  replace (2 * (a + 1) + 2) with (2 * a + 4) in H4 by lia.
  exact H4.
Qed.

Lemma stepPlus_E_congr {c_in : Q * tape} {A0 A1 : nat} {R0 R1 : side}
  (hA : A0 = A1) (hR : R0 = R1)
  (h : c_in -->+ 0inf%sym <{{E}} ([1; 0]%sym ^^ A0 *> R0)) :
  c_in -->+ 0inf%sym <{{E}} ([1; 0]%sym ^^ A1 *> R1).
Proof. subst. exact h. Qed.

Lemma stepStar_E_congr {c_in : Q * tape} {A0 A1 : nat} {R0 R1 : side}
  (hA : A0 = A1) (hR : R0 = R1)
  (h : c_in -->* 0inf%sym <{{E}} ([1; 0]%sym ^^ A0 *> R0)) :
  c_in -->* 0inf%sym <{{E}} ([1; 0]%sym ^^ A1 *> R1).
Proof. subst. exact h. Qed.

Lemma tail_01_congr {B0 B1 : nat} {r r' : side}
  (hB : B0 = B1) (hr : r = r') :
  ([0; 1]%sym ^^ B0 *> r) = ([0; 1]%sym ^^ B1 *> r').
Proof. subst. reflexivity. Qed.

Lemma cycle_c2_to_c1 (a k : nat) :
  0inf%sym <{{E}} ([1; 0]%sym ^^ (a + 2) *> ([0; 1]%sym ^^ (2 * k + 2) *> ([1; 1]%sym *> r0))) -->+
  0inf%sym <{{E}} ([1; 0]%sym ^^ ((4 * a + 8) * 2 ^ (k + 2)) *>
    ([0; 1]%sym ^^ (3 * k + 8) *> ([1]%sym *> r0))).
Proof.
  replace (2 * k + 2) with ((2 * k + 1) + 1) by lia.
  pose proof (trans_c2_v1 a (2 * k + 1)) as H1.
  replace (2 * a + 4) with ((2 * a + 2) + 2) in H1 by lia.
  replace (2 * k + 1 + 5) with (2 * (k + 2) + 2) in H1 by lia.
  pose proof (trans_c2_v2 (2 * a + 2) (2 * (k + 2))) as H2.
  replace (2 * (2 * a + 2) + 4) with ((4 * a + 6) + 2) in H2 by lia.
  rewrite pow_11_even in H2.
  assert (Ha4 : (4 * a + 6 + 2) * 2 ^ (k + 2) = (4 * a + 8) * 2 ^ (k + 2)) by
    (replace (4 * a + 6 + 2) with (4 * a + 8) by lia; reflexivity).
  assert (Hb4 : 1 + 3 * (k + 2) + 1 = 3 * k + 8) by lia.
  pose proof (stepStar_E_congr Ha4 (tail_01_congr Hb4 eq_refl)
    (rule2_loop (k + 2) (4 * a + 6) 1 ([1]%sym *> r0))) as H3.
  eapply progress_evstep_trans; [| exact H3].
  eapply progress_trans; [exact H1 | exact H2].
Qed.

Lemma cap_c1_part1 (Y : side) :
  (Y <* [0; 1; 0]%sym) {{E}}> ([0; 1]%sym ^^ 5 *> ([0]%sym *> r0)) -->+
  (Y <* [0; 1; 0; 1; 0; 0; 1; 1; 0; 1; 0]%sym) {{E}}> ([0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1]%sym *> 0inf%sym).
Proof.
  unfold r0. eapply progress_intro; [prove_step | simpl_lhs]. do 119 tstep. finish.
Qed.

Lemma cap_c1_part2 (Y : side) :
  (Y <* [0; 1; 0; 1; 0; 0; 1; 1; 0; 1; 0]%sym) {{E}}> ([0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1]%sym *> 0inf%sym) -->+
  (Y <* [1; 0]%sym) <{{B}} ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0)).
Proof.
  unfold r0. eapply progress_intro; [prove_step | simpl_lhs]. do 127 tstep. finish.
Qed.

Lemma cap_c1_248 (Y : side) :
  (Y <* [0; 1; 0]%sym) {{E}}> ([0; 1]%sym ^^ 5 *> ([0]%sym *> r0)) -->+
  (Y <* [1; 0]%sym) <{{B}} ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0)).
Proof.
  eapply progress_trans; [exact (cap_c1_part1 Y) | exact (cap_c1_part2 Y)].
Qed.

Lemma pass_cap_c1 (X : side) (d : nat) :
  (X <* [0; 1]%sym) {{E}}> ([0; 1]%sym ^^ (d + 6) *> ([0]%sym *> r0)) -->+
  (X <* [1]%sym) <{{B}} ([1; 1]%sym ^^ (d + 1) *> ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0))).
Proof.
  replace (d + 6) with ((d + 1) + 5) by lia.
  rewrite pow_add_append_right.
  pose proof (shift_E_right_01 (d + 1) (X <* [0; 1]%sym) ([0; 1]%sym ^^ 5 *> ([0]%sym *> r0))) as H1.
  assert (Heq1 : (X <* [0; 1]%sym) <* ([0; 1]%sym ^^ (d + 1)) =
                 ((X <* [1]%sym) <* ([1; 0]%sym ^^ d)) <* [0; 1; 0]%sym).
  { replace (X <* [0; 1]%sym) with ((X <* [1]%sym) <* [0]%sym) by reflexivity.
    rewrite (append_0_pow_01 (X <* [1]%sym) (d + 1)).
    replace (d + 1) with (S d) by lia.
    reflexivity. }
  rewrite Heq1 in H1.
  eapply evstep_progress_trans; [exact H1 |].
  pose proof (cap_c1_248 ((X <* [1]%sym) <* ([1; 0]%sym ^^ d))) as H2.
  assert (Heq2 : ((X <* [1]%sym) <* ([1; 0]%sym ^^ d)) <* [1; 0]%sym =
                 (X <* [1]%sym) <* ([1; 0]%sym ^^ (d + 1))).
  { replace (d + 1) with (S d) by lia. reflexivity. }
  rewrite Heq2 in H2.
  eapply progress_evstep_trans; [exact H2 |].
  exact (shift_B_left_10 (d + 1) (X <* [1]%sym) ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0))).
Qed.

Lemma glue_B_11_to_E011 (l s : side) :
  ((l <* ([0; 1]%sym ^^ 2)) <* [1; 1]%sym) <{{B}} ([1; 1; 1; 1]%sym *> s) -->+
  (l <* [0; 1; 1]%sym) <{{E}} ([1; 0]%sym ^^ 2 *> ([1; 1]%sym *> ([1]%sym *> s))).
Proof.
  eapply progress_intro; [prove_step | simpl_lhs]. do 20 tstep. finish.
Qed.

Lemma glue_B_111_to_E111 (l s : side) :
  ((l <* ([0; 1]%sym ^^ 2)) <* [1; 1]%sym) <{{B}} ([1; 1; 1; 1]%sym *> s) -->+
  (l <* [1; 1; 1]%sym) <{{E}} ([1; 0]%sym ^^ 3 *> ([1]%sym *> s)).
Proof.
  pose proof (glue_B_11_to_E011 l s) as H1.
  change (l <* [0; 1; 1]%sym) with ((l <* [1; 1]%sym) <* [0]%sym) in H1.
  eapply progress_trans; [exact H1 |].
  exact (half_E1_b (l <* [1; 1]%sym) 1 ([1]%sym *> s)).
Qed.

Lemma glue_B10011_to_E111 (l s : side) :
  ((l <* [0; 0; 1; 1]%sym) <* [1]%sym) <{{B}} s -->+
  (l <* [1; 1; 1]%sym) <{{E}} ([1; 0]%sym *> s).
Proof.
  eapply progress_intro; [prove_step | simpl_lhs]. do 7 tstep. finish.
Qed.

Lemma bounce_E111_end (l : side) (d : nat) :
  ((l <* ([0; 1]%sym ^^ 2)) <* [1; 1; 1]%sym) <{{E}}
    ([1; 0]%sym ^^ (d + 1) *> ([0; 1]%sym *> 0inf%sym)) -->+
  (l <* [1; 1; 1]%sym) <{{E}} ([1; 0]%sym ^^ 1 *> ([1; 1]%sym ^^ (d + 1) *> r0)).
Proof.
  pose proof (step14_E111 l ([1; 0]%sym ^^ (d + 1) *> ([0; 1]%sym *> 0inf%sym))) as H1.
  rewrite cons_0_pow_10 in H1.
  change ([0]%sym *> ([0; 1]%sym *> 0inf%sym)) with ([0; 0; 1]%sym *> 0inf%sym) in H1.
  eapply progress_trans; [exact H1 |].
  eapply progress_trans; [exact (bounce_E_end (l <* [0; 0; 1; 1]%sym) (d + 1)) |].
  exact (glue_B10011_to_E111 l ([1; 1]%sym ^^ (d + 1) *> r0)).
Qed.

Lemma glue_B_11101_to_B1 (l s : side) :
  ((l <* ([0; 1]%sym ^^ 2)) <* [1; 1; 1]%sym) <{{B}} ([1; 1; 1; 1]%sym *> s) -->+
  ((l <* [0; 1]%sym) <* [1]%sym) <{{B}} ([0; 1]%sym ^^ 4 *> s).
Proof.
  eapply progress_intro; [prove_step | simpl_lhs]. do 31 tstep. finish.
Qed.

Lemma step_E01_10 (X Y : side) :
  (X <* [0; 1]%sym) <{{E}} ([1; 0]%sym *> Y) -->+
  ((X <* [1]%sym) <* [0; 1]%sym) {{E}}> ([0]%sym *> Y).
Proof.
  eapply progress_intro; [prove_step | simpl_lhs]. do 1 tstep. finish.
Qed.

Lemma step_E011_10 (X Y : side) :
  (X <* [0; 1; 1]%sym) <{{E}} ([1; 0]%sym *> Y) -->+
  ((X <* [1; 1]%sym) <* [0; 1]%sym) {{E}}> ([0]%sym *> Y).
Proof.
  eapply progress_intro; [prove_step | simpl_lhs]. do 1 tstep. finish.
Qed.

Lemma r0_11_pow5_1 :
  ([1; 1]%sym ^^ 5 *> ([1]%sym *> r0)) =
  [1; 1]%sym *> ([1; 1; 1; 1]%sym *> ([1; 1; 1; 1]%sym *> ([1; 0]%sym ^^ 2 *> ([1; 1]%sym *> ([0; 1]%sym *> 0inf%sym))))).
Proof. reflexivity. Qed.

Lemma r0_11_pow5_2 :
  ([1; 1]%sym ^^ 5 *> ([1]%sym *> r0)) =
  [1; 1; 1; 1]%sym *> ([1; 1; 1; 1]%sym *> ([1; 1]%sym *> ([1; 0]%sym ^^ 2 *> ([1; 1]%sym *> ([0; 1]%sym *> 0inf%sym))))).
Proof. reflexivity. Qed.

Lemma r0_11_pow5_3 :
  ([1; 1]%sym ^^ 5 *> r0) =
  ([1; 1; 1; 1]%sym ^^ 2 *> ([1; 1]%sym *> r0)).
Proof. reflexivity. Qed.

Lemma stem_part1 :
  c0 -->+
  (0inf%sym <* [1]%sym) <{{E}} ([1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 1; 0; 1; 0; 1; 1; 0; 1]%sym *> 0inf%sym).
Proof.
  eapply progress_intro; [prove_step | simpl_lhs]. do 199 tstep. finish.
Qed.

Lemma stem_part2 :
  (0inf%sym <* [1]%sym) <{{E}} ([1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 1; 0; 1; 0; 1; 1; 0; 1]%sym *> 0inf%sym) -->+
  (0inf%sym <* [0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1]%sym) {{E}}> ([0; 1; 0; 0; 1; 0; 1; 1; 0; 1]%sym *> 0inf%sym).
Proof.
  eapply progress_intro; [prove_step | simpl_lhs]. do 199 tstep. finish.
Qed.

Lemma stem_part3 :
  (0inf%sym <* [0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1]%sym) {{E}}> ([0; 1; 0; 0; 1; 0; 1; 1; 0; 1]%sym *> 0inf%sym) -->+
  (0inf%sym <* [1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1]%sym) <{{B}} ([1; 1; 1; 1; 1; 1; 0; 1; 0; 1; 1; 0; 1]%sym *> 0inf%sym).
Proof.
  eapply progress_intro; [prove_step | simpl_lhs]. do 199 tstep. finish.
Qed.

Lemma stem_part4 :
  (0inf%sym <* [1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1]%sym) <{{B}} ([1; 1; 1; 1; 1; 1; 0; 1; 0; 1; 1; 0; 1]%sym *> 0inf%sym) -->+
  (0inf%sym <* [1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1]%sym) <{{E}} ([1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 1; 0; 1; 1; 0; 1]%sym *> 0inf%sym).
Proof.
  eapply progress_intro; [prove_step | simpl_lhs]. do 199 tstep. finish.
Qed.

Lemma stem_part5 :
  (0inf%sym <* [1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1]%sym) <{{E}} ([1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 1; 0; 1; 1; 0; 1]%sym *> 0inf%sym) -->+
  0inf%sym <{{E}} ([1; 0]%sym ^^ 14 *> ([0; 1]%sym ^^ 4 *>
    ([1; 1; 1; 1]%sym ^^ 2 *> ([1; 1]%sym *> r0)))).
Proof.
  unfold r0. eapply progress_intro; [prove_step | simpl_lhs]. do 175 tstep. finish.
Qed.

Lemma trans_c1_even (a m : nat) :
  0inf%sym <{{E}} ([1; 0]%sym ^^ (a + 2 * m + 17) *>
    ([0; 1]%sym ^^ (2 * m + 8) *> ([1]%sym *> r0))) -->+
  0inf%sym <{{E}} ([1; 0]%sym ^^ (2 * a + 12) *>
    ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ (4 * m + 21) *> r0))).
Proof.
  replace (a + 2 * m + 17) with ((a + 2 * m + 15) + 2) by lia.
  replace (2 * m + 8) with ((2 * m + 7) + 1) by lia.
  pose proof (sweep_init (a + 2 * m + 15) (2 * m + 7) r0) as H1.
  replace (2 * m + 7 + 2) with (((2 * m + 2) + 6) + 1) in H1 by lia.
  rewrite (pow_succ_append_right [1; 0]%sym ((2 * m + 2) + 6) r0) in H1.
  pose proof (step_E01_10
    (0inf%sym <* ([0; 1]%sym ^^ (a + 2 * m + 15 + 1)))
    ([1; 0]%sym ^^ ((2 * m + 2) + 6) *> r0)) as H2.
  rewrite cons_0_pow_10 in H2.
  pose proof (pass_cap_c1 ((0inf%sym <* ([0; 1]%sym ^^ (a + 2 * m + 15 + 1))) <* [1]%sym) (2 * m + 2)) as H3.
  assert (Heq3 : ((0inf%sym <* ([0; 1]%sym ^^ (a + 2 * m + 15 + 1))) <* [1]%sym) <* [1]%sym =
                 (((0inf%sym <* ([0; 1]%sym ^^ (a + 14))) <* ([0; 1]%sym ^^ (2 * m))) <*
                   ([0; 1]%sym ^^ 2)) <* [1; 1]%sym).
  { replace (a + 2 * m + 15 + 1) with (((a + 14) + 2 * m) + 2) by lia.
    rewrite !pow_add_append_left, append_1_1. reflexivity. }
  assert (Hr3 : ([1; 1]%sym ^^ (2 * m + 2 + 1) *> ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0))) =
                [1; 1; 1; 1]%sym *> ([1; 1]%sym ^^ (2 * m) *> ([1; 1]%sym *> ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0))))).
  { replace (2 * m + 2 + 1) with (2 + (2 * m + 1)) by lia.
    rewrite pow_add_append_right, <- pow_succ_append_right', pow2_11_append. reflexivity. }
  rewrite Heq3, Hr3 in H3.
  pose proof (glue_B_111_to_E111
    ((0inf%sym <* ([0; 1]%sym ^^ (a + 14))) <* ([0; 1]%sym ^^ (2 * m)))
    ([1; 1]%sym ^^ (2 * m) *> ([1; 1]%sym *> ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0))))) as H4.
  rewrite cons_1_pow_11, (pow_11_even m ([1]%sym *> ([1; 1]%sym *> ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0))))) in H4.
  pose proof (loop_E1_iter m (0inf%sym <* ([0; 1]%sym ^^ (a + 14))) 3
    ([1]%sym *> ([1; 1]%sym *> ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0))))) as H5.
  assert (Hl5 : (0inf%sym <* ([0; 1]%sym ^^ (a + 14))) <* [1; 1; 1]%sym =
                ((0inf%sym <* ([0; 1]%sym ^^ (((a + 6) + 2) + 2 + 2))) <* ([0; 1]%sym ^^ 2)) <* [1; 1; 1]%sym).
  { replace (a + 14) with ((((a + 6) + 2) + 2 + 2) + 2) by lia.
    rewrite pow_add_append_left. reflexivity. }
  assert (Hr5 : ([1; 0]%sym ^^ (3 + 4 * m) *> ([1]%sym *> ([1; 1]%sym *> ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0))))) =
                ([1; 0]%sym ^^ (3 + 4 * m) *> ([1; 1]%sym *> ([1]%sym *> ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0)))))) by reflexivity.
  rewrite Hl5, Hr5 in H5.
  pose proof (half_E1_a
    (0inf%sym <* ([0; 1]%sym ^^ (((a + 6) + 2) + 2 + 2)))
    (3 + 4 * m)
    ([1]%sym *> ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0)))) as H6.
  assert (Hl6 : (0inf%sym <* ([0; 1]%sym ^^ (((a + 6) + 2) + 2 + 2))) <* [0; 1; 1]%sym =
                ((0inf%sym <* ([0; 1]%sym ^^ (((a + 6) + 2) + 2 + 2))) <* [1; 1]%sym) <* [0]%sym) by exact (append_011 _).
  assert (Hr6 : ([1; 0]%sym ^^ (3 + 4 * m + 3) *> ([1]%sym *> ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0)))) =
                ([1; 0]%sym ^^ ((4 * m + 9) + 1) *> ([1; 1]%sym *> ([1; 1; 1; 1]%sym *> ([1; 1; 1; 1]%sym *> ([1; 0]%sym ^^ 2 *> ([1; 1]%sym *> ([0; 1]%sym *> 0inf%sym)))))))).
  { rewrite cons_1_pow_01, cons_1_pow_11, <- (pow_add_append_right [1; 0]%sym).
    replace (3 + 4 * m + 3 + 4) with ((4 * m + 9) + 1) by lia.
    rewrite r0_11_pow5_1. reflexivity. }
  rewrite Hl6, Hr6 in H6.
  pose proof (half_E1_b
    ((0inf%sym <* ([0; 1]%sym ^^ (((a + 6) + 2) + 2 + 2))) <* [1; 1]%sym)
    (4 * m + 9)
    ([1; 1; 1; 1]%sym *> ([1; 1; 1; 1]%sym *> ([1; 0]%sym ^^ 2 *> ([1; 1]%sym *> ([0; 1]%sym *> 0inf%sym)))))) as H7.
  assert (Hl7 : (((0inf%sym <* ([0; 1]%sym ^^ (((a + 6) + 2) + 2 + 2))) <* [1; 1]%sym) <* [1]%sym) =
                ((((0inf%sym <* ([0; 1]%sym ^^ (a + 6))) <* ([0; 1]%sym ^^ 2)) <* ([0; 1]%sym ^^ 2)) <*
                  ([0; 1]%sym ^^ 2)) <* [1; 1; 1]%sym).
  { rewrite !pow_add_append_left, append_11_1. reflexivity. }
  rewrite Hl7 in H7.
  pose proof (loop_E1_step
    (((0inf%sym <* ([0; 1]%sym ^^ (a + 6))) <* ([0; 1]%sym ^^ 2)) <* ([0; 1]%sym ^^ 2))
    (4 * m + 9 + 2)
    ([1; 1; 1; 1]%sym *> ([1; 0]%sym ^^ 2 *> ([1; 1]%sym *> ([0; 1]%sym *> 0inf%sym))))) as H8.
  pose proof (loop_E1_step
    ((0inf%sym <* ([0; 1]%sym ^^ (a + 6))) <* ([0; 1]%sym ^^ 2))
    (4 * m + 9 + 2 + 4)
    ([1; 0]%sym ^^ 2 *> ([1; 1]%sym *> ([0; 1]%sym *> 0inf%sym)))) as H9.
  rewrite <- (pow_add_append_right [1; 0]%sym) in H9.
  pose proof (half_E1_a
    (0inf%sym <* ([0; 1]%sym ^^ (a + 6)))
    (4 * m + 9 + 2 + 4 + 4 + 2)
    ([0; 1]%sym *> 0inf%sym)) as H10.
  replace (4 * m + 9 + 2 + 4 + 4 + 2 + 3) with ((4 * m + 23) + 1) in H10 by lia.
  rewrite (pow_succ_append_right [1; 0]%sym (4 * m + 23) ([0; 1]%sym *> 0inf%sym)) in H10.
  pose proof (step_E011_10
    (0inf%sym <* ([0; 1]%sym ^^ (a + 6)))
    ([1; 0]%sym ^^ (4 * m + 23) *> ([0; 1]%sym *> 0inf%sym))) as H11.
  rewrite cons_0_pow_10 in H11.
  change ([0]%sym *> ([0; 1]%sym *> 0inf%sym)) with ([0; 0; 1]%sym *> 0inf%sym) in H11.
  pose proof (bounce_E_end
    ((0inf%sym <* ([0; 1]%sym ^^ (a + 6))) <* [1; 1]%sym)
    (4 * m + 23)) as H12.
  assert (Hl12 : (((0inf%sym <* ([0; 1]%sym ^^ (a + 6))) <* [1; 1]%sym) <* [1]%sym) =
                 (((0inf%sym <* ([0; 1]%sym ^^ (a + 4))) <* ([0; 1]%sym ^^ 2)) <* [1; 1; 1]%sym)).
  { replace (a + 6) with ((a + 4) + 2) by lia.
    rewrite pow_add_append_left, append_11_1. reflexivity. }
  assert (Hr12 : ([1; 1]%sym ^^ (4 * m + 23) *> r0) =
                 [1; 1; 1; 1]%sym *> ([1; 1]%sym ^^ (4 * m + 21) *> r0)).
  { replace (4 * m + 23) with (2 + (4 * m + 21)) by lia.
    rewrite pow_add_append_right, pow2_11_append. reflexivity. }
  rewrite Hl12, Hr12 in H12.
  pose proof (glue_B_11101_to_B1
    (0inf%sym <* ([0; 1]%sym ^^ (a + 4)))
    ([1; 1]%sym ^^ (4 * m + 21) *> r0)) as H13.
  assert (Hl13 : (((0inf%sym <* ([0; 1]%sym ^^ (a + 4))) <* [0; 1]%sym) <* [1]%sym) =
                 (0inf%sym <* [1]%sym) <* ([1; 0]%sym ^^ (a + 5))).
  { assert (Htmp : (0inf%sym <* ([0; 1]%sym ^^ (a + 4))) <* [0; 1]%sym =
                   0inf%sym <* ([0; 1]%sym ^^ (a + 5))).
    { symmetry. replace (a + 5) with ((a + 4) + 1) by lia.
      exact (pow_succ_append_right [0; 1]%sym (a + 4) 0inf%sym). }
    rewrite Htmp, append_1_pow_01. reflexivity. }
  rewrite Hl13 in H13.
  pose proof (finish_B_left (a + 5)
    ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ (4 * m + 21) *> r0))) as H14.
  replace (2 * (a + 5) + 2) with (2 * a + 12) in H14 by lia.
  eapply progress_trans; [exact H1 |].
  eapply progress_trans; [exact H2 |].
  eapply progress_trans; [exact H3 |].
  eapply progress_trans; [exact H4 |].
  eapply evstep_progress_trans; [exact H5 |].
  eapply progress_trans; [exact H6 |].
  eapply progress_trans; [exact H7 |].
  eapply progress_trans; [exact H8 |].
  eapply progress_trans; [exact H9 |].
  eapply progress_trans; [exact H10 |].
  eapply progress_trans; [exact H11 |].
  eapply progress_trans; [exact H12 |].
  eapply progress_trans; [exact H13 | exact H14].
Qed.

Lemma trans_c1_odd (a m : nat) :
  0inf%sym <{{E}} ([1; 0]%sym ^^ (a + 6 * m + 36) *>
    ([0; 1]%sym ^^ (2 * m + 7) *> ([1]%sym *> r0))) -->+
  0inf%sym <{{E}} ([1; 0]%sym ^^ (2 * a + 6) *>
    ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ (8 * m + 36) *>
      ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0))))).
Proof.
  replace (a + 6 * m + 36) with ((a + 6 * m + 34) + 2) by lia.
  replace (2 * m + 7) with ((2 * m + 6) + 1) by lia.
  pose proof (sweep_init (a + 6 * m + 34) (2 * m + 6) r0) as H1.
  replace (2 * m + 6 + 2) with (((2 * m + 1) + 6) + 1) in H1 by lia.
  rewrite (pow_succ_append_right [1; 0]%sym ((2 * m + 1) + 6) r0) in H1.
  pose proof (step_E01_10
    (0inf%sym <* ([0; 1]%sym ^^ (a + 6 * m + 34 + 1)))
    ([1; 0]%sym ^^ ((2 * m + 1) + 6) *> r0)) as H2.
  rewrite cons_0_pow_10 in H2.
  pose proof (pass_cap_c1 ((0inf%sym <* ([0; 1]%sym ^^ (a + 6 * m + 34 + 1))) <* [1]%sym) (2 * m + 1)) as H3.
  assert (Heq3 : ((0inf%sym <* ([0; 1]%sym ^^ (a + 6 * m + 34 + 1))) <* [1]%sym) <* [1]%sym =
                 (((0inf%sym <* ([0; 1]%sym ^^ (a + 4 * m + 33))) <* ([0; 1]%sym ^^ (2 * m))) <*
                   ([0; 1]%sym ^^ 2)) <* [1; 1]%sym).
  { replace (a + 6 * m + 34 + 1) with (((a + 4 * m + 33) + 2 * m) + 2) by lia.
    rewrite !pow_add_append_left, append_1_1. reflexivity. }
  assert (Hr3 : ([1; 1]%sym ^^ (2 * m + 1 + 1) *> ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0))) =
                [1; 1; 1; 1]%sym *> ([1; 1]%sym ^^ (2 * m) *> ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0)))).
  { replace (2 * m + 1 + 1) with (2 + 2 * m) by lia.
    rewrite pow_add_append_right, pow2_11_append. reflexivity. }
  rewrite Heq3, Hr3 in H3.
  pose proof (glue_B_111_to_E111
    ((0inf%sym <* ([0; 1]%sym ^^ (a + 4 * m + 33))) <* ([0; 1]%sym ^^ (2 * m)))
    ([1; 1]%sym ^^ (2 * m) *> ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0)))) as H4.
  rewrite cons_1_pow_11, (pow_11_even m ([1]%sym *> ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0)))) in H4.
  pose proof (loop_E1_iter m (0inf%sym <* ([0; 1]%sym ^^ (a + 4 * m + 33))) 3
    ([1]%sym *> ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0)))) as H5.
  assert (Hl5 : (0inf%sym <* ([0; 1]%sym ^^ (a + 4 * m + 33))) <* [1; 1; 1]%sym =
                ((((0inf%sym <* ([0; 1]%sym ^^ (a + 4 * m + 27))) <* ([0; 1]%sym ^^ 2)) <*
                  ([0; 1]%sym ^^ 2)) <* ([0; 1]%sym ^^ 2)) <* [1; 1; 1]%sym).
  { replace (a + 4 * m + 33) with ((((a + 4 * m + 27) + 2) + 2) + 2) by lia.
    rewrite !pow_add_append_left. reflexivity. }
  assert (Hr5 : ([1; 0]%sym ^^ (3 + 4 * m) *> ([1]%sym *> ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0)))) =
                ([1; 0]%sym ^^ (4 * m + 7) *> ([1; 1; 1; 1]%sym *> ([1; 1; 1; 1]%sym *> ([1; 1]%sym *> ([1; 0]%sym ^^ 2 *> ([1; 1]%sym *> ([0; 1]%sym *> 0inf%sym)))))))).
  { rewrite cons_1_pow_01, cons_1_pow_11, <- (pow_add_append_right [1; 0]%sym).
    replace (3 + 4 * m + 4) with (4 * m + 7) by lia.
    rewrite r0_11_pow5_2. reflexivity. }
  rewrite Hl5, Hr5 in H5.
  pose proof (loop_E1_step
    (((0inf%sym <* ([0; 1]%sym ^^ (a + 4 * m + 27))) <* ([0; 1]%sym ^^ 2)) <* ([0; 1]%sym ^^ 2))
    (4 * m + 7)
    ([1; 1; 1; 1]%sym *> ([1; 1]%sym *> ([1; 0]%sym ^^ 2 *> ([1; 1]%sym *> ([0; 1]%sym *> 0inf%sym)))))) as H6.
  pose proof (loop_E1_step
    ((0inf%sym <* ([0; 1]%sym ^^ (a + 4 * m + 27))) <* ([0; 1]%sym ^^ 2))
    (4 * m + 7 + 4)
    ([1; 1]%sym *> ([1; 0]%sym ^^ 2 *> ([1; 1]%sym *> ([0; 1]%sym *> 0inf%sym))))) as H7.
  pose proof (half_E1_a
    (0inf%sym <* ([0; 1]%sym ^^ (a + 4 * m + 27)))
    (4 * m + 7 + 4 + 4)
    ([1; 0]%sym ^^ 2 *> ([1; 1]%sym *> ([0; 1]%sym *> 0inf%sym)))) as H8.
  rewrite <- (pow_add_append_right [1; 0]%sym) in H8.
  replace (4 * m + 7 + 4 + 4 + 3 + 2) with ((4 * m + 19) + 1) in H8 by lia.
  assert (Hl8 : (0inf%sym <* ([0; 1]%sym ^^ (a + 4 * m + 27))) <* [0; 1; 1]%sym =
                ((0inf%sym <* ([0; 1]%sym ^^ (a + 4 * m + 27))) <* [1; 1]%sym) <* [0]%sym) by exact (append_011 _).
  rewrite Hl8 in H8.
  pose proof (half_E1_b
    ((0inf%sym <* ([0; 1]%sym ^^ (a + 4 * m + 27))) <* [1; 1]%sym)
    (4 * m + 19)
    ([0; 1]%sym *> 0inf%sym)) as H9.
  replace (4 * m + 19 + 2) with ((4 * m + 20) + 1) in H9 by lia.
  assert (Hl9 : (((0inf%sym <* ([0; 1]%sym ^^ (a + 4 * m + 27))) <* [1; 1]%sym) <* [1]%sym) =
                (((0inf%sym <* ([0; 1]%sym ^^ (a + 4 * m + 25))) <* ([0; 1]%sym ^^ 2)) <* [1; 1; 1]%sym)).
  { replace (a + 4 * m + 27) with ((a + 4 * m + 25) + 2) by lia.
    rewrite pow_add_append_left, append_11_1. reflexivity. }
  rewrite Hl9 in H9.
  pose proof (bounce_E111_end
    (0inf%sym <* ([0; 1]%sym ^^ (a + 4 * m + 25)))
    (4 * m + 20)) as H10.
  assert (Hl10 : (0inf%sym <* ([0; 1]%sym ^^ (a + 4 * m + 25))) <* [1; 1; 1]%sym =
                 ((0inf%sym <* ([0; 1]%sym ^^ (a + 5))) <* ([0; 1]%sym ^^ (2 * (2 * m + 10)))) <* [1; 1; 1]%sym).
  { replace (a + 4 * m + 25) with ((a + 5) + 2 * (2 * m + 10)) by lia.
    rewrite pow_add_append_left. reflexivity. }
  assert (Hr10 : ([1; 1]%sym ^^ (4 * m + 20 + 1) *> r0) =
                 ([1; 1; 1; 1]%sym ^^ (2 * m + 10) *> ([1; 1]%sym *> r0))).
  { replace (4 * m + 20 + 1) with (2 * (2 * m + 10) + 1) by lia.
    rewrite <- pow_succ_append_right', pow_11_even. reflexivity. }
  rewrite Hl10, Hr10 in H10.
  pose proof (loop_E1_iter (2 * m + 10)
    (0inf%sym <* ([0; 1]%sym ^^ (a + 5)))
    1
    ([1; 1]%sym *> r0)) as H11.
  assert (Hl11 : (0inf%sym <* ([0; 1]%sym ^^ (a + 5))) <* [1; 1; 1]%sym =
                 ((0inf%sym <* ([0; 1]%sym ^^ (a + 3))) <* ([0; 1]%sym ^^ 2)) <* [1; 1; 1]%sym).
  { replace (a + 5) with ((a + 3) + 2) by lia.
    rewrite pow_add_append_left. reflexivity. }
  rewrite Hl11 in H11.
  pose proof (half_E1_a
    (0inf%sym <* ([0; 1]%sym ^^ (a + 3)))
    (1 + 4 * (2 * m + 10))
    r0) as H12.
  replace (1 + 4 * (2 * m + 10) + 3) with (((8 * m + 37) + 6) + 1) in H12 by lia.
  rewrite (pow_succ_append_right [1; 0]%sym ((8 * m + 37) + 6) r0) in H12.
  pose proof (step_E011_10
    (0inf%sym <* ([0; 1]%sym ^^ (a + 3)))
    ([1; 0]%sym ^^ ((8 * m + 37) + 6) *> r0)) as H13.
  rewrite cons_0_pow_10 in H13.
  pose proof (pass_cap_c1
    ((0inf%sym <* ([0; 1]%sym ^^ (a + 3))) <* [1; 1]%sym)
    (8 * m + 37)) as H14.
  assert (Hl14 : (((0inf%sym <* ([0; 1]%sym ^^ (a + 3))) <* [1; 1]%sym) <* [1]%sym) =
                 (((0inf%sym <* ([0; 1]%sym ^^ (a + 1))) <* ([0; 1]%sym ^^ 2)) <* [1; 1; 1]%sym)).
  { replace (a + 3) with ((a + 1) + 2) by lia.
    rewrite pow_add_append_left, append_11_1. reflexivity. }
  assert (Hr14 : ([1; 1]%sym ^^ (8 * m + 37 + 1) *> ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0))) =
                 [1; 1; 1; 1]%sym *> ([1; 1]%sym ^^ (8 * m + 36) *> ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0)))).
  { replace (8 * m + 37 + 1) with (2 + (8 * m + 36)) by lia.
    rewrite pow_add_append_right, pow2_11_append. reflexivity. }
  rewrite Hl14, Hr14 in H14.
  pose proof (glue_B_11101_to_B1
    (0inf%sym <* ([0; 1]%sym ^^ (a + 1)))
    ([1; 1]%sym ^^ (8 * m + 36) *> ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0)))) as H15.
  assert (Hl15 : (((0inf%sym <* ([0; 1]%sym ^^ (a + 1))) <* [0; 1]%sym) <* [1]%sym) =
                 (0inf%sym <* [1]%sym) <* ([1; 0]%sym ^^ (a + 2))).
  { assert (Htmp : (0inf%sym <* ([0; 1]%sym ^^ (a + 1))) <* [0; 1]%sym =
                   0inf%sym <* ([0; 1]%sym ^^ (a + 2))).
    { symmetry. replace (a + 2) with ((a + 1) + 1) by lia.
      exact (pow_succ_append_right [0; 1]%sym (a + 1) 0inf%sym). }
    rewrite Htmp, append_1_pow_01. reflexivity. }
  rewrite Hl15 in H15.
  pose proof (finish_B_left (a + 2)
    ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ (8 * m + 36) *>
      ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0))))) as H16.
  replace (2 * (a + 2) + 2) with (2 * a + 6) in H16 by lia.
  eapply progress_trans; [exact H1 |].
  eapply progress_trans; [exact H2 |].
  eapply progress_trans; [exact H3 |].
  eapply progress_trans; [exact H4 |].
  eapply evstep_progress_trans; [exact H5 |].
  eapply progress_trans; [exact H6 |].
  eapply progress_trans; [exact H7 |].
  eapply progress_trans; [exact H8 |].
  eapply progress_trans; [exact H9 |].
  eapply progress_trans; [exact H10 |].
  eapply evstep_progress_trans; [exact H11 |].
  eapply progress_trans; [exact H12 |].
  eapply progress_trans; [exact H13 |].
  eapply progress_trans; [exact H14 |].
  eapply progress_trans; [exact H15 | exact H16].
Qed.

Definition P (a j : nat) : Q * tape :=
  0inf%sym <{{E}} ([1; 0]%sym ^^ (a + 18 * j + 100) *>
    ([0; 1]%sym ^^ (4 * j + 16) *> ([1; 1]%sym *> r0))).

Lemma hide_mul_pow2 (X p : nat) : exists N0, X * 2 ^ p = N0 /\ X <= N0.
Proof.
  exists (X * 2 ^ p). split; [reflexivity | apply mul_pow2_ge].
Qed.

Lemma drain_c1_even (a m : nat) :
  0inf%sym <{{E}} ([1; 0]%sym ^^ (a + 2 * m + 17) *>
    ([0; 1]%sym ^^ (2 * m + 8) *> ([1]%sym *> r0))) -->+
  0inf%sym <{{E}} ([1; 0]%sym ^^ ((2 * a + 12) * 2 ^ (2 * m + 10)) *>
    ([0; 1]%sym ^^ (6 * m + 34) *> ([1; 1]%sym *> r0))).
Proof.
  assert (Ha1 : 2 * a + 12 = (2 * a + 10) + 2) by lia.
  assert (Hr1 : ([1; 1]%sym ^^ (4 * m + 21) *> r0) =
                ([1; 1; 1; 1]%sym ^^ (2 * m + 10) *> ([1; 1]%sym *> r0))).
  { replace (4 * m + 21) with (2 * (2 * m + 10) + 1) by lia.
    rewrite <- pow_succ_append_right', pow_11_even. reflexivity. }
  assert (Ha2 : (2 * a + 10 + 2) * 2 ^ (2 * m + 10) = (2 * a + 12) * 2 ^ (2 * m + 10)) by
    (replace (2 * a + 10 + 2) with (2 * a + 12) by lia; reflexivity).
  assert (Hb2 : 3 + 3 * (2 * m + 10) + 1 = 6 * m + 34) by lia.
  pose proof (stepPlus_E_congr Ha1 (tail_01_congr eq_refl Hr1) (trans_c1_even a m)) as H1.
  pose proof (stepStar_E_congr Ha2 (tail_01_congr Hb2 eq_refl)
    (rule2_loop (2 * m + 10) (2 * a + 10) 3 ([1; 1]%sym *> r0))) as H2.
  eapply progress_evstep_trans; [exact H1 | exact H2].
Qed.

Definition n14307 : nat := N.to_nat 14307%N.

Lemma init_to_P :
  exists a0, c0 -->+ P a0 81.
Proof.
  assert (Heq1 : (4 * 54 + 8) * 2 ^ (4 + 2) = n14307 + 2 * 6 + 17) by
    (unfold n14307; cbn [Nat.pow]; lia).
  assert (Heq1_b : 3 * 4 + 8 = 2 * 6 + 8) by (clear; lia).
  destruct (hide_mul_pow2 (2 * n14307 + 12) (2 * 6 + 10)) as [N1 [HN1_eq HN1_ge]].
  assert (HN1_split : N1 = (N1 - 2) + 2) by
    (clear - HN1_ge; unfold n14307 in HN1_ge; lia).
  assert (Ha_split1 : (2 * n14307 + 12) * 2 ^ (2 * 6 + 10) = (N1 - 2) + 2) by
    (rewrite HN1_eq; exact HN1_split).
  assert (Hb_next : 6 * 6 + 34 = 2 * 34 + 2) by (clear; lia).
  destruct (hide_mul_pow2 (4 * (N1 - 2) + 8) (34 + 2)) as [N2 [HN2_eq HN2_ge]].
  assert (HN2_split : N2 = (N2 - 119) + 2 * 51 + 17) by
    (clear - HN1_ge HN2_ge; unfold n14307 in HN1_ge; lia).
  assert (Ha_split2 : (4 * (N1 - 2) + 8) * 2 ^ (34 + 2) = (N2 - 119) + 2 * 51 + 17) by
    (rewrite HN2_eq; exact HN2_split).
  assert (Hb_split2 : 3 * 34 + 8 = 2 * 51 + 8) by (clear; lia).
  destruct (hide_mul_pow2 (2 * (N2 - 119) + 12) (2 * 51 + 10)) as [N3 [HN3_eq HN3_ge]].
  set (a0 := N3 - (18 * 81 + 100)).
  assert (HN3_split : N3 = a0 + 18 * 81 + 100) by
    (unfold a0; clear - HN1_ge HN2_ge HN3_ge; unfold n14307 in HN1_ge; lia).
  assert (Ha_final : (2 * (N2 - 119) + 12) * 2 ^ (2 * 51 + 10) = a0 + 18 * 81 + 100) by
    (rewrite HN3_eq; exact HN3_split).
  assert (Hb_final : 6 * 51 + 34 = 4 * 81 + 16) by (clear; lia).
  assert (Hstem : c0 -->+ 0inf%sym <{{E}} ([1; 0]%sym ^^ 14 *> ([0; 1]%sym ^^ 4 *>
    ([1; 1; 1; 1]%sym ^^ 2 *> ([1; 1]%sym *> r0))))).
  { eapply progress_trans; [exact stem_part1 |].
    eapply progress_trans; [exact stem_part2 |].
    eapply progress_trans; [exact stem_part3 |].
    eapply progress_trans; [exact stem_part4 | exact stem_part5]. }
  pose proof (rule2_loop 2 12 3 ([1; 1]%sym *> r0)) as Hr2.
  replace (12 + 2) with 14 in Hr2 by (clear; lia).
  replace (3 + 1) with 4 in Hr2 by (clear; lia).
  replace (14 * 2 ^ 2) with (54 + 2) in Hr2 by (clear; cbn [Nat.pow]; lia).
  replace (3 + 3 * 2 + 1) with (2 * 4 + 2) in Hr2 by (clear; lia).
  assert (Hev4 : c0 -->+ 0inf%sym <{{E}} ([1; 0]%sym ^^ (54 + 2) *>
    ([0; 1]%sym ^^ (2 * 4 + 2) *> ([1; 1]%sym *> r0)))).
  { eapply progress_evstep_trans; [exact Hstem | exact Hr2]. }
  pose proof (stepPlus_E_congr Heq1 (tail_01_congr Heq1_b eq_refl) (cycle_c2_to_c1 54 4)) as Hc2_1.
  pose proof (stepPlus_E_congr Ha_split1 (tail_01_congr Hb_next eq_refl) (drain_c1_even n14307 6)) as Hc1_1.
  pose proof (stepPlus_E_congr Ha_split2 (tail_01_congr Hb_split2 eq_refl) (cycle_c2_to_c1 (N1 - 2) 34)) as Hc2_2.
  pose proof (stepPlus_E_congr Ha_final (tail_01_congr Hb_final eq_refl) (drain_c1_even (N2 - 119) 51)) as Hc1_2.
  exists a0. unfold P.
  eapply progress_trans; [exact Hev4 |].
  eapply progress_trans; [exact Hc2_1 |].
  eapply progress_trans; [exact Hc1_1 |].
  eapply progress_trans; [exact Hc2_2 | exact Hc1_2].
Qed.

Lemma P_step (a j : nat) :
  exists a', P a j -->+ P a' (9 * j + 46).
Proof.
  unfold P.
  assert (Ha0 : a + 18 * j + 100 = (a + 18 * j + 98) + 2) by (clear; lia).
  assert (Hb0 : 4 * j + 16 = 2 * (2 * j + 7) + 2) by (clear; lia).
  destruct (hide_mul_pow2 (4 * (a + 18 * j + 98) + 8) (2 * j + 7 + 2)) as [M1 [HM1_eq HM1_ge]].
  set (a1 := M1 - (6 * (3 * j + 11) + 36)).
  assert (HM1_split : M1 = a1 + 6 * (3 * j + 11) + 36) by
    (unfold a1; clear - HM1_ge; lia).
  assert (Ha1 : (4 * (a + 18 * j + 98) + 8) * 2 ^ (2 * j + 7 + 2) = a1 + 6 * (3 * j + 11) + 36) by
    (rewrite HM1_eq; exact HM1_split).
  assert (Hb1 : 3 * (2 * j + 7) + 8 = 2 * (3 * j + 11) + 7) by (clear; lia).
  assert (Ha2 : 2 * a1 + 6 = (2 * a1 + 4) + 2) by (clear; lia).
  assert (Hr2 : ([1; 1]%sym ^^ (8 * (3 * j + 11) + 36) *>
                  ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0))) =
                ([1; 1; 1; 1]%sym ^^ (12 * j + 62) *>
                  ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0)))).
  { replace (8 * (3 * j + 11) + 36) with (2 * (12 * j + 62)) by (clear; lia).
    rewrite pow_11_even. reflexivity. }
  destruct (hide_mul_pow2 (2 * a1 + 4 + 2) (12 * j + 62)) as [M2 [HM2_eq HM2_ge]].
  assert (HM2_split : M2 = (M2 - 2) + 2) by
    (unfold a1 in HM2_ge; clear - HM1_ge HM2_ge; lia).
  assert (Ha3 : (2 * a1 + 4 + 2) * 2 ^ (12 * j + 62) = (M2 - 2) + 2) by
    (rewrite HM2_eq; exact HM2_split).
  assert (Hr3_full : ([0; 1]%sym ^^ (3 + 3 * (12 * j + 62) + 1) *>
                       ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0))) =
                     ([0; 1]%sym ^^ ((36 * j + 193) + 1) *>
                       ([1; 1; 1; 1]%sym ^^ 2 *> ([1; 1]%sym *> r0)))).
  { rewrite <- (pow_add_append_right [0; 1]%sym).
    replace (3 + 3 * (12 * j + 62) + 1 + 4) with ((36 * j + 193) + 1) by (clear; lia).
    rewrite r0_11_pow5_3. reflexivity. }
  set (a' := (M2 - 2 + 2) * 4 - (18 * (9 * j + 46) + 100)).
  assert (Ha4 : (M2 - 2 + 2) * 2 ^ 2 = a' + 18 * (9 * j + 46) + 100) by
    (cbn [Nat.pow]; unfold a', a1 in *; clear - HM1_ge HM2_ge; lia).
  assert (Hb4 : 36 * j + 193 + 3 * 2 + 1 = 4 * (9 * j + 46) + 16) by (clear; lia).
  rewrite Ha0, Hb0.
  pose proof (stepPlus_E_congr Ha1 (tail_01_congr Hb1 eq_refl)
    (cycle_c2_to_c1 (a + 18 * j + 98) (2 * j + 7))) as H1.
  pose proof (stepPlus_E_congr Ha2 (tail_01_congr eq_refl Hr2)
    (trans_c1_odd a1 (3 * j + 11))) as H2.
  pose proof (stepStar_E_congr Ha3 Hr3_full
    (rule2_loop (12 * j + 62) (2 * a1 + 4) 3 ([0; 1]%sym ^^ 4 *> ([1; 1]%sym ^^ 5 *> r0)))) as H3.
  pose proof (stepStar_E_congr Ha4 (tail_01_congr Hb4 eq_refl)
    (rule2_loop 2 (M2 - 2) (36 * j + 193) ([1; 1]%sym *> r0))) as H4.
  exists a'.
  eapply progress_evstep_trans.
  - eapply progress_trans; [exact H1 | exact H2].
  - eapply evstep_trans; [exact H3 | exact H4].
Qed.

Definition Hub (s : nat * nat) : Q * tape :=
  let '(a, j) := s in P a j.

Theorem nonhalt: ~ halts tm c0.
Proof.
  destruct init_to_P as [a0 Hinit].
  eapply multistep_nonhalt with (c' := Hub (a0, 81)).
  - apply progress_evstep. exact Hinit.
  - eapply progress_nonhalt_simple with (C := Hub) (i0 := (a0, 81)).
    intros [a j].
    destruct (P_step a j) as [a' Hstep].
    exists (a', 9 * j + 46).
    exact Hstep.
Qed.

End TM1.
Print Assumptions TM1.nonhalt.



Module TM2.
Import BusyCoq.Individual62.

Import Lia ZifyNat ZifyN PeanoNat NArith String List.

Import ListNotations.

Open Scope list.

Open Scope sym.

Definition tm := Eval compute in (TM_from_str "1RB0RC_1LC1RA_0RF0LD_1LE0RB_1LB0LD_---1RD").

Notation tm_0829 := TM1.tm.

Notation "c --> c'" := (c -[ tm_0829 ]-> c')   (at level 40).

Notation "c -->* c'" := (c -[ tm_0829 ]->* c') (at level 40).

Notation "c -->+ c'" := (c -[ tm_0829 ]->+ c') (at level 40).

Open Scope nat_scope.

Ltac simpl_lhs :=
  autorewrite with tape_pre;
  cbn [move_left move_right Streams.hd Streams.tl Str_app];
  repeat rewrite <- const_unfold.

Ltac tstep :=
  (eapply evstep_step || eapply progress_step); [prove_step | simpl_lhs].

Notation pow_add_append_right := TM1.pow_add_append_right.

Notation pow_succ_append_right := TM1.pow_succ_append_right.

Notation pow_succ_append_right' := TM1.pow_succ_append_right'.

Notation pow_add_append_left := TM1.pow_add_append_left.

Notation cons_0_pow_10 := TM1.cons_0_pow_10.

Notation cons_1_pow_01 := TM1.cons_1_pow_01.

Notation append_0_pow_01 := TM1.append_0_pow_01.

Notation append_1_pow_01 := TM1.append_1_pow_01.

Notation append_1_1 := TM1.append_1_1.

Notation append_11_1 := TM1.append_11_1.

Notation append_011 := TM1.append_011.

Notation pow2_11_append := TM1.pow2_11_append.

Notation mul_pow2_ge := TM1.mul_pow2_ge.

Notation cons_1_pow_11 := TM1.cons_1_pow_11.

Notation pow_11_even := TM1.pow_11_even.

Notation shift_E_right_01 := TM1.shift_E_right_01.

Notation shift_B_left_10 := TM1.shift_B_left_10.

Notation shift_E_left_10 := TM1.shift_E_left_10.

Notation r0 := TM1.r0.

Notation bounce_E_01 := TM1.bounce_E_01.

Notation bounce_E_end := TM1.bounce_E_end.

Notation rule1_step := TM1.rule1_step.

Notation rule1_loop := TM1.rule1_loop.

Notation finish_B_left := TM1.finish_B_left.

Notation sweep_mid := TM1.sweep_mid.

Notation sweep_init := TM1.sweep_init.

Notation step14_E111 := TM1.step14_E111.

Notation half_E1_a := TM1.half_E1_a.

Notation half_E1_b := TM1.half_E1_b.

Notation loop_E1_step := TM1.loop_E1_step.

Notation loop_E1_iter := TM1.loop_E1_iter.

Notation rule2_gen := TM1.rule2_gen.

Notation rule2_step := TM1.rule2_step.

Notation rule2_loop := TM1.rule2_loop.

Notation trans_c2_v1 := TM1.trans_c2_v1.

Notation trans_c2_v2 := TM1.trans_c2_v2.

Notation stepPlus_E_congr := TM1.stepPlus_E_congr.

Notation stepStar_E_congr := TM1.stepStar_E_congr.

Notation tail_01_congr := TM1.tail_01_congr.

Notation cycle_c2_to_c1 := TM1.cycle_c2_to_c1.

Notation cap_c1_part1 := TM1.cap_c1_part1.

Notation cap_c1_part2 := TM1.cap_c1_part2.

Notation cap_c1_248 := TM1.cap_c1_248.

Notation pass_cap_c1 := TM1.pass_cap_c1.

Notation glue_B_11_to_E011 := TM1.glue_B_11_to_E011.

Notation glue_B_111_to_E111 := TM1.glue_B_111_to_E111.

Notation glue_B10011_to_E111 := TM1.glue_B10011_to_E111.

Notation bounce_E111_end := TM1.bounce_E111_end.

Notation glue_B_11101_to_B1 := TM1.glue_B_11101_to_B1.

Notation step_E01_10 := TM1.step_E01_10.

Notation step_E011_10 := TM1.step_E011_10.

Notation r0_11_pow5_1 := TM1.r0_11_pow5_1.

Notation r0_11_pow5_2 := TM1.r0_11_pow5_2.

Notation r0_11_pow5_3 := TM1.r0_11_pow5_3.

Notation trans_c1_even := TM1.trans_c1_even.

Notation trans_c1_odd := TM1.trans_c1_odd.

Definition mapState (q : Q) : Q :=
  match q with
  | A => E
  | B => B
  | C => C
  | D => F
  | E => D
  | F => A
  end.

Definition mirrorTape (t : tape) : tape :=
  match t with
  | l {{s}} r => r {{s}} l
  end.

Definition mirrorCfg (c : Q * tape) : Q * tape :=
  let '(q, t) := c in (mapState q, mirrorTape t).

Lemma step_mirror (c c' : Q * tape) :
  c -[ tm_0829 ]-> c' ->
  mirrorCfg c -[ tm ]-> mirrorCfg c'.
Proof.
  intros H.
  inversion H as [q q' s s' l r Htr | q q' s s' l r Htr]; subst;
    destruct q, s; cbn in Htr; inversion Htr; subst;
    cbn [mirrorCfg mirrorTape move_left move_right];
    ((apply step_right; reflexivity) || (apply step_left; reflexivity)).
Qed.

Lemma progress_mirror {c c' : Q * tape} :
  c -[ tm_0829 ]->+ c' ->
  mirrorCfg c -[ tm ]->+ mirrorCfg c'.
Proof.
  intros H. induction H as [c c' H | c c' c'' H _ IH].
  - apply progress_base. exact (step_mirror c c' H).
  - eapply progress_step; [exact (step_mirror c c' H) | exact IH].
Qed.

Lemma stem_0426_part1 :
  c0 -[ tm ]->+
  (0inf%sym <* [0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 1; 0; 1]%sym) {{F}}> ([1; 1; 0; 1; 0; 1; 0; 1]%sym *> 0inf%sym).
Proof.
  eapply progress_intro; [prove_step | simpl_lhs]. do 179 tstep. finish.
Qed.

Lemma stem_0426_part2 :
  (0inf%sym <* [0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 1; 0; 1]%sym) {{F}}> ([1; 1; 0; 1; 0; 1; 0; 1]%sym *> 0inf%sym) -[ tm ]->+
  (0inf%sym <* [0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1]%sym) {{B}}> ([0; 1; 0; 1; 0; 1; 0; 0; 1; 1; 0; 1; 0; 1; 0; 1]%sym *> 0inf%sym).
Proof.
  eapply progress_intro; [prove_step | simpl_lhs]. do 169 tstep. finish.
Qed.

Lemma stem_0426_part3 :
  (0inf%sym <* [0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1]%sym) {{B}}> ([0; 1; 0; 1; 0; 1; 0; 0; 1; 1; 0; 1; 0; 1; 0; 1]%sym *> 0inf%sym) -[ tm ]->+
  mirrorCfg (0inf%sym <{{E}} ([1; 0]%sym ^^ 6 *> ([0; 1]%sym ^^ 4 *>
    ([1; 1; 1; 1]%sym ^^ 2 *> ([1; 1]%sym *> r0))))).
Proof.
  unfold mirrorCfg, mirrorTape, mapState, r0.
  eapply progress_intro; [prove_step | simpl_lhs]. do 172 tstep. finish.
Qed.

Notation P := TM1.P.

Notation hide_mul_pow2 := TM1.hide_mul_pow2.

Notation drain_c1_even := TM1.drain_c1_even.

Definition n6115 : nat := N.to_nat 6115%N.

Lemma c_523_0829_to_P :
  exists a0,
    0inf%sym <{{E}} ([1; 0]%sym ^^ 6 *> ([0; 1]%sym ^^ 4 *>
      ([1; 1; 1; 1]%sym ^^ 2 *> ([1; 1]%sym *> r0)))) -->+ P a0 81.
Proof.
  assert (Heq1 : (4 * 22 + 8) * 2 ^ (4 + 2) = n6115 + 2 * 6 + 17) by
    (unfold n6115; cbn [Nat.pow]; lia).
  assert (Heq1_b : 3 * 4 + 8 = 2 * 6 + 8) by (clear; lia).
  destruct (hide_mul_pow2 (2 * n6115 + 12) (2 * 6 + 10)) as [N1 [HN1_eq HN1_ge]].
  assert (HN1_split : N1 = (N1 - 2) + 2) by
    (clear - HN1_ge; unfold n6115 in HN1_ge; lia).
  assert (Ha_split1 : (2 * n6115 + 12) * 2 ^ (2 * 6 + 10) = (N1 - 2) + 2) by
    (rewrite HN1_eq; exact HN1_split).
  assert (Hb_next : 6 * 6 + 34 = 2 * 34 + 2) by (clear; lia).
  destruct (hide_mul_pow2 (4 * (N1 - 2) + 8) (34 + 2)) as [N2 [HN2_eq HN2_ge]].
  assert (HN2_split : N2 = (N2 - 119) + 2 * 51 + 17) by
    (clear - HN1_ge HN2_ge; unfold n6115 in HN1_ge; lia).
  assert (Ha_split2 : (4 * (N1 - 2) + 8) * 2 ^ (34 + 2) = (N2 - 119) + 2 * 51 + 17) by
    (rewrite HN2_eq; exact HN2_split).
  assert (Hb_split2 : 3 * 34 + 8 = 2 * 51 + 8) by (clear; lia).
  destruct (hide_mul_pow2 (2 * (N2 - 119) + 12) (2 * 51 + 10)) as [N3 [HN3_eq HN3_ge]].
  set (a0 := N3 - (18 * 81 + 100)).
  assert (HN3_split : N3 = a0 + 18 * 81 + 100) by
    (unfold a0; clear - HN1_ge HN2_ge HN3_ge; unfold n6115 in HN1_ge; lia).
  assert (Ha_final : (2 * (N2 - 119) + 12) * 2 ^ (2 * 51 + 10) = a0 + 18 * 81 + 100) by
    (rewrite HN3_eq; exact HN3_split).
  assert (Hb_final : 6 * 51 + 34 = 4 * 81 + 16) by (clear; lia).
  pose proof (rule2_loop 2 4 3 ([1; 1]%sym *> r0)) as Hr2.
  replace (4 + 2) with 6 in Hr2 by (clear; lia).
  replace (3 + 1) with 4 in Hr2 by (clear; lia).
  replace (6 * 2 ^ 2) with (22 + 2) in Hr2 by (clear; cbn [Nat.pow]; lia).
  replace (3 + 3 * 2 + 1) with (2 * 4 + 2) in Hr2 by (clear; lia).
  assert (Hev4_c1_raw :
    0inf%sym <{{E}} ([1; 0]%sym ^^ 6 *> ([0; 1]%sym ^^ 4 *>
      ([1; 1; 1; 1]%sym ^^ 2 *> ([1; 1]%sym *> r0)))) -->+
    0inf%sym <{{E}} ([1; 0]%sym ^^ ((4 * 22 + 8) * 2 ^ (4 + 2)) *>
      ([0; 1]%sym ^^ (3 * 4 + 8) *> ([1]%sym *> r0)))).
  { eapply evstep_progress_trans; [exact Hr2 | exact (cycle_c2_to_c1 22 4)]. }
  pose proof (stepPlus_E_congr Heq1 (tail_01_congr Heq1_b eq_refl) Hev4_c1_raw) as Hev4_c1.
  pose proof (stepPlus_E_congr Ha_split1 (tail_01_congr Hb_next eq_refl) (drain_c1_even n6115 6)) as Hc1_1.
  pose proof (stepPlus_E_congr Ha_split2 (tail_01_congr Hb_split2 eq_refl) (cycle_c2_to_c1 (N1 - 2) 34)) as Hc2_2.
  pose proof (stepPlus_E_congr Ha_final (tail_01_congr Hb_final eq_refl) (drain_c1_even (N2 - 119) 51)) as Hc1_2.
  exists a0. unfold P.
  eapply progress_trans; [exact Hev4_c1 |].
  eapply progress_trans; [exact Hc1_1 |].
  eapply progress_trans; [exact Hc2_2 | exact Hc1_2].
Qed.

Lemma init_to_P_0426 :
  exists a0, c0 -[ tm ]->+ mirrorCfg (P a0 81).
Proof.
  destruct c_523_0829_to_P as [a0 HtoP].
  exists a0.
  eapply progress_trans; [exact stem_0426_part1 |].
  eapply progress_trans; [exact stem_0426_part2 |].
  eapply progress_trans; [exact stem_0426_part3 |].
  exact (progress_mirror HtoP).
Qed.

Notation P_step := TM1.P_step.

Definition Hub (s : nat * nat) : Q * tape :=
  let '(a, j) := s in mirrorCfg (P a j).

Theorem nonhalt: ~ halts tm c0.
Proof.
  destruct init_to_P_0426 as [a0 Hinit].
  eapply multistep_nonhalt with (c' := Hub (a0, 81)).
  - apply progress_evstep. exact Hinit.
  - eapply progress_nonhalt_simple with (C := Hub) (i0 := (a0, 81)).
    intros [a j].
    destruct (P_step a j) as [a' Hstep].
    exists (a', 9 * j + 46).
    exact (progress_mirror Hstep).
Qed.

End TM2.
Print Assumptions TM2.nonhalt.

From Coq Require Import Lia ZifyNat PeanoNat String Lists.List.

Module TM3.
Import BusyCoq.Individual62.

Import Lia ZifyNat PeanoNat String List.

Import ListNotations.

Open Scope list_scope.

Open Scope nat_scope.

Definition tm := Eval compute in (TM_from_str "1RB1RC_1LC0LE_0RA1RD_1RF1LB_1LD0LA_---0RC").

Definition holdout_0311_tm : TM := tm.

Lemma stepPlus_stepStar {m c1 c2} (H : c1 -[ m ]->+ c2) : c1 -[ m ]->* c2.
Proof. exact (progress_evstep m c1 c2 H). Qed.

Lemma stepPlus_stepPlus_stepPlus {m c1 c2 c3}
  (H1 : c1 -[ m ]->+ c2) (H2 : c2 -[ m ]->+ c3) : c1 -[ m ]->+ c3.
Proof. exact (progress_trans m c1 c2 c3 H1 H2). Qed.

Lemma stepPlus_stepStar_stepPlus {m c1 c2 c3}
  (H1 : c1 -[ m ]->+ c2) (H2 : c2 -[ m ]->* c3) : c1 -[ m ]->+ c3.
Proof. exact (progress_evstep_trans m c1 c2 c3 H1 H2). Qed.

Lemma stepStar_stepPlus_stepPlus {m c1 c2 c3}
  (H1 : c1 -[ m ]->* c2) (H2 : c2 -[ m ]->+ c3) : c1 -[ m ]->+ c3.
Proof. exact (evstep_progress_trans m c1 c2 c3 H1 H2). Qed.

Lemma stepStar_trans {m c1 c2 c3}
  (H1 : c1 -[ m ]->* c2) (H2 : c2 -[ m ]->* c3) : c1 -[ m ]->* c3.
Proof. exact (evstep_trans m c1 c2 c3 H1 H2). Qed.

Definition cfg_of (q : Q) (d : dir) (l r : side) : Q * tape :=
  match d with
  | L => l <{{q}} r
  | R => l {{q}}> r
  end.

Record LocalState := mkLocalState {
  ls_l : list Sym;
  ls_r : list Sym;
  ls_q : Q;
  ls_d : dir
}.

Definition step_local (m : TM) (s : LocalState) : option LocalState :=
  match ls_d s with
  | L =>
    match ls_l s with
    | [] => None
    | b :: l =>
      match m (ls_q s, b) with
      | Some (b', L, q') => Some (mkLocalState l (b' :: ls_r s) q' L)
      | Some (b', R, q') => Some (mkLocalState (b' :: l) (ls_r s) q' R)
      | None => None
      end
    end
  | R =>
    match ls_r s with
    | [] => None
    | b :: r =>
      match m (ls_q s, b) with
      | Some (b', L, q') => Some (mkLocalState (ls_l s) (b' :: r) q' L)
      | Some (b', R, q') => Some (mkLocalState (b' :: ls_l s) r q' R)
      | None => None
      end
    end
  end.

Lemma step_local_spec (m : TM) (s1 s2 : LocalState) (L0 R0 : side) :
  step_local m s1 = Some s2 ->
  cfg_of (ls_q s1) (ls_d s1) (ls_l s1 *> L0) (ls_r s1 *> R0) -[ m ]->
  cfg_of (ls_q s2) (ls_d s2) (ls_l s2 *> L0) (ls_r s2 *> R0).
Proof.
  unfold step_local, cfg_of; destruct s1 as [l1 r1 q1 [|]], s2 as [l2 r2 q2 d2]; simpl.
  - destruct l1 as [|b l]; [discriminate|].
    destruct (m (q1, b)) as [[[b' [|]] q']|] eqn:Hm; intros H; inversion H; subst; clear H; simpl.
    + apply step_left; exact Hm.
    + apply step_right; exact Hm.
  - destruct r1 as [|b r]; [discriminate|].
    destruct (m (q1, b)) as [[[b' [|]] q']|] eqn:Hm; intros H; inversion H; subst; clear H; simpl.
    + apply step_left; exact Hm.
    + apply step_right; exact Hm.
Qed.

Fixpoint run_local (m : TM) (n : nat) (s : LocalState) : option LocalState :=
  match n with
  | O => Some s
  | S n' =>
    match step_local m s with
    | Some s' => run_local m n' s'
    | None => None
    end
  end.

Lemma run_local_spec (m : TM) (n : nat) (s1 s2 : LocalState) (L0 R0 : side) :
  run_local m n s1 = Some s2 ->
  cfg_of (ls_q s1) (ls_d s1) (ls_l s1 *> L0) (ls_r s1 *> R0) -[ m ]->*
  cfg_of (ls_q s2) (ls_d s2) (ls_l s2 *> L0) (ls_r s2 *> R0).
Proof.
  revert s1.
  induction n as [|n IH]; intros s1 H; simpl in H.
  - inversion H; subst; apply evstep_refl.
  - destruct (step_local m s1) as [sm|] eqn:Hs; [|discriminate].
    eapply evstep_step.
    + exact (step_local_spec m s1 sm L0 R0 Hs).
    + exact (IH sm H).
Qed.

Lemma run_local_plus_eq (m : TM) (n : nat) (s1 s2 : LocalState) (c1 c2 : Q * tape) (L0 R0 : side) :
  run_local m (S n) s1 = Some s2 ->
  cfg_of (ls_q s1) (ls_d s1) (ls_l s1 *> L0) (ls_r s1 *> R0) = c1 ->
  cfg_of (ls_q s2) (ls_d s2) (ls_l s2 *> L0) (ls_r s2 *> R0) = c2 ->
  c1 -[ m ]->+ c2.
Proof.
  intros H <- <-.
  simpl in H.
  destruct (step_local m s1) as [sm|] eqn:Hs; [|discriminate].
  eapply progress_intro.
  - exact (step_local_spec m s1 sm L0 R0 Hs).
  - exact (run_local_spec m n sm s2 L0 R0 H).
Qed.

Definition cfg_modeC (l r : side) : Q * tape :=
  (S1 >> S0 >> l) {{C}}> r.

Definition cfg_modeE1 (l r : side) : Q * tape :=
  (S1 >> S0 >> l) <{{E}} (S0 >> S1 >> r).

Definition cfg_modeE0_first (l : side) : Q * tape :=
  (S0 >> S1 >> S0 >> l) <{{E}} (S0 >> S1 >> const S0).

Definition cfg_modeE0_loop (l r : side) : Q * tape :=
  (S0 >> l) <{{E}} (S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> r).

Definition cfg_b101_mid (l : side) : Q * tape :=
  (S1 >> S1 >> S1 >> S1 >> S0 >> S1 >> S0 >> l) <{{E}} (S0 >> S1 >> S0 >> S1 >> S0 >> S1 >> const S0).

Definition cfg_e0f_mid (l : side) : Q * tape :=
  (S1 >> S1 >> S1 >> S0 >> S1 >> S0 >> l) {{B}}> (S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> const S0).

Definition cfg_e0l_mid (l r : side) : Q * tape :=
  (S1 >> S1 >> S1 >> S0 >> S1 >> S0 >> l) {{B}}> (S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> r)).

Definition cfg_transA_mid (l : side) : Q * tape :=
  (S1 >> S1 >> S1 >> S1 >> S0 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> S0 >> l) {{B}}> (S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> const S0).

Definition cfg_transB_mid (l r : side) : Q * tape :=
  (S1 >> S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> l) {{B}}> (S1 >> S0 >> S1 >> S0 >> S1 >> S0 >> S1 >> S0 >> S1 >> r).

Ltac norm_cfg :=
  unfold cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop,
         cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, cfg_transA_mid, cfg_transB_mid,
         cfg_of, c0, tape0, q0, s0;
  cbn [ls_q ls_d ls_l ls_r Str_app hd tl];
  repeat rewrite <- const_unfold;
  reflexivity.

Ltac solve_local m n s1 L0 R0 :=
  eapply (run_local_plus_eq m n s1 _ _ _ L0 R0);
  [ cbv; reflexivity | norm_cfg | norm_cfg ].

Lemma init_reaches_modeC :
  c0 -[ holdout_0311_tm ]->+ cfg_modeC (S0 >> S1 >> const S0) (const S0).
Proof.
  solve_local holdout_0311_tm 9 (mkLocalState [S0; S0] [S0; S0] A R) (const S0) (const S0).
Qed.

Lemma step_modeC_nil (l : side) :
  cfg_modeC l (const S0) -[ holdout_0311_tm ]->+ cfg_modeE0_first l.
Proof.
  solve_local holdout_0311_tm 5 (mkLocalState [S1; S0] [S0; S0; S0] C R) l (const S0).
Qed.

Lemma step_modeC_b01 (l r : side) :
  cfg_modeC l (S0 >> S1 >> r) -[ holdout_0311_tm ]->+ cfg_modeC (S1 >> S0 >> l) r.
Proof.
  solve_local holdout_0311_tm 1 (mkLocalState [S1; S0] [S0; S1] C R) l r.
Qed.

Lemma step_modeC_b01_b10101 (l r : side) :
  cfg_modeC l (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> r) -[ holdout_0311_tm ]->+
    cfg_modeC (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l)) r.
Proof.
  solve_local holdout_0311_tm 6 (mkLocalState [S1; S0] [S0; S1; S1; S0; S1; S0; S1] C R) l r.
Qed.

Lemma step_modeC_b11 (l r : side) :
  cfg_modeC l (S1 >> S1 >> r) -[ holdout_0311_tm ]->+ cfg_modeE1 l r.
Proof.
  solve_local holdout_0311_tm 2 (mkLocalState [S1; S0] [S1; S1] C R) l r.
Qed.

Lemma step_modeC_b01_b000 (l r : side) :
  cfg_modeC l (S0 >> S1 >> S0 >> S0 >> S0 >> r) -[ holdout_0311_tm ]->+ cfg_modeE0_loop l r.
Proof.
  solve_local holdout_0311_tm 13 (mkLocalState [S1; S0] [S0; S1; S0; S0; S0] C R) l r.
Qed.

Lemma step_modeC_b01_b101_nil_1 (l : side) :
  cfg_modeC (S1 >> S0 >> l) (S1 >> S0 >> S1 >> const S0) -[ holdout_0311_tm ]->+ cfg_b101_mid l.
Proof.
  solve_local holdout_0311_tm 33
    (mkLocalState [S1; S0; S1; S0] [S1; S0; S1; S0; S0; S0; S0; S0; S0] C R) l (const S0).
Qed.

Lemma step_modeC_b01_b101_nil_2 (l : side) :
  cfg_b101_mid l -[ holdout_0311_tm ]->+
    cfg_modeE1 (S1 >> S0 >> l) (S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> const S0).
Proof.
  solve_local holdout_0311_tm 32
    (mkLocalState [S1; S1; S1; S1; S0; S1; S0] [S0; S1; S0; S1; S0; S1] E L) l (const S0).
Qed.

Lemma step_modeC_b01_b1011101 (l r : side) :
  cfg_modeC l (S0 >> S1 >> S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> r) -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> r).
Proof.
  solve_local holdout_0311_tm 16
    (mkLocalState [S1; S0] [S0; S1; S1; S0; S1; S1; S1; S0; S1] C R) l r.
Qed.

Lemma step_modeE1_base (r : side) :
  cfg_modeE1 (S0 >> S1 >> const S0) r -[ holdout_0311_tm ]->+
    cfg_modeC (S0 >> S1 >> const S0) (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> r))).
Proof.
  solve_local holdout_0311_tm 24
    (mkLocalState [S1; S0; S0; S1; S0; S0; S0; S0] [S0; S1] E L) (const S0) r.
Qed.

Lemma step_modeE1_b10 (l r : side) :
  cfg_modeE1 (S1 >> S0 >> l) r -[ holdout_0311_tm ]->+ cfg_modeE1 l (S0 >> S1 >> r).
Proof.
  solve_local holdout_0311_tm 5 (mkLocalState [S1; S0; S1; S0] [S0; S1] E L) l r.
Qed.

Lemma step_modeC_b01_b101_nil (l : side) :
  cfg_modeC l (S0 >> S1 >> S1 >> S0 >> S1 >> const S0) -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S0 >> S0 >> S0 >> (S0 >> S1 >> (S0 >> S1 >> const S0))).
Proof.
  exact (stepPlus_stepPlus_stepPlus (step_modeC_b01 l _)
    (stepPlus_stepPlus_stepPlus (step_modeC_b01_b101_nil_1 l)
      (stepPlus_stepPlus_stepPlus (step_modeC_b01_b101_nil_2 l) (step_modeE1_b10 l _)))).
Qed.

Lemma step_modeE1_b011_10_base (r : side) :
  cfg_modeE1 (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0)) r -[ holdout_0311_tm ]->+
    cfg_modeC (S0 >> S1 >> const S0)
      (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> r))).
Proof.
  solve_local holdout_0311_tm 33
    (mkLocalState [S1; S0; S0; S1; S1; S1; S0; S0; S1; S0; S0; S0; S0] [S0; S1] E L) (const S0) r.
Qed.

Lemma step_modeE1_b011_10_b10 (l r : side) :
  cfg_modeE1 (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l)) r -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> r).
Proof.
  solve_local holdout_0311_tm 14
    (mkLocalState [S1; S0; S0; S1; S1; S1; S0; S1; S0] [S0; S1] E L) l r.
Qed.

Lemma step_modeE0_first_base :
  cfg_modeE0_first (S0 >> S1 >> const S0) -[ holdout_0311_tm ]->+
    cfg_modeC (S0 >> S1 >> const S0)
      (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> const S0))).
Proof.
  solve_local holdout_0311_tm 24
    (mkLocalState [S0; S1; S0; S0; S1; S0; S0; S0] [S0; S1] E L) (const S0) (const S0).
Qed.

Lemma step_modeE0_first_b10 (l : side) :
  cfg_modeE0_first (S1 >> S0 >> l) -[ holdout_0311_tm ]->+ cfg_modeE0_loop l (const S0).
Proof.
  solve_local holdout_0311_tm 5 (mkLocalState [S0; S1; S0; S1; S0] [S0; S1] E L) l (const S0).
Qed.

Lemma step_modeE0_first_b011_10_base_1 :
  cfg_modeE0_first (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0)) -[ holdout_0311_tm ]->+
    cfg_modeE1 (S0 >> S1 >> const S0) (S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> const S0)).
Proof.
  solve_local holdout_0311_tm 35
    (mkLocalState [S0; S1; S0; S0; S1; S1; S1; S0; S0; S1] [S0; S1] E L) (const S0) (const S0).
Qed.

Lemma step_modeE0_first_b011_10_base :
  cfg_modeE0_first (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0)) -[ holdout_0311_tm ]->+
    cfg_modeC (S0 >> S1 >> const S0)
      (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> const S0)))).
Proof.
  exact (stepPlus_stepPlus_stepPlus step_modeE0_first_b011_10_base_1 (step_modeE1_base _)).
Qed.

Lemma step_modeE0_first_b011_10_b10_1 (l : side) :
  cfg_modeE0_first (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l)) -[ holdout_0311_tm ]->+ cfg_e0f_mid l.
Proof.
  solve_local holdout_0311_tm 20
    (mkLocalState [S0; S1; S0; S0; S1; S1; S1; S0; S1; S0] [S0; S1] E L) l (const S0).
Qed.

Lemma step_modeE0_first_b011_10_b10_2 (l : side) :
  cfg_e0f_mid l -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> const S0)).
Proof.
  solve_local holdout_0311_tm 20
    (mkLocalState [S1; S1; S1; S0; S1; S0] [S0; S0; S0; S1; S0; S1] B R) l (const S0).
Qed.

Lemma step_modeE0_first_b011_10_b10 (l : side) :
  cfg_modeE0_first (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l)) -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> const S0)).
Proof.
  exact (stepPlus_stepPlus_stepPlus (step_modeE0_first_b011_10_b10_1 l) (step_modeE0_first_b011_10_b10_2 l)).
Qed.

Lemma step_modeE0_loop_base (r : side) :
  cfg_modeE0_loop (S0 >> S1 >> const S0) r -[ holdout_0311_tm ]->+
    cfg_modeC (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0)) (S0 >> S1 >> r).
Proof.
  solve_local holdout_0311_tm 26
    (mkLocalState [S0; S0; S1; S0; S0] [S0; S1; S1; S1; S0; S1] E L) (const S0) r.
Qed.

Lemma step_modeE0_loop_b10_base (r : side) :
  cfg_modeE0_loop (S1 >> S0 >> (S0 >> S1 >> const S0)) r -[ holdout_0311_tm ]->+
    cfg_modeC (S0 >> S1 >> const S0)
      (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S1 >> S1 >> (S0 >> S1 >> r))))).
Proof.
  solve_local holdout_0311_tm 24
    (mkLocalState [S0; S1; S0; S0; S1; S0; S0; S0] [S0; S1; S1; S1; S0; S1] E L) (const S0) r.
Qed.

Lemma step_modeE0_loop_b10_b10 (l r : side) :
  cfg_modeE0_loop (S1 >> S0 >> (S1 >> S0 >> l)) r -[ holdout_0311_tm ]->+
    cfg_modeE0_loop l (S1 >> S1 >> (S0 >> S1 >> r)).
Proof.
  solve_local holdout_0311_tm 5
    (mkLocalState [S0; S1; S0; S1; S0] [S0; S1; S1; S1; S0; S1] E L) l r.
Qed.

Lemma step_modeE0_loop_b10_b011_10_base_1 (r : side) :
  cfg_modeE0_loop (S1 >> S0 >> (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0))) r -[ holdout_0311_tm ]->+
    cfg_modeE1 (S0 >> S1 >> const S0)
      (S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> r)).
Proof.
  solve_local holdout_0311_tm 35
    (mkLocalState [S0; S1; S0; S0; S1; S1; S1; S0; S0; S1] [S0; S1; S1; S1; S0; S1] E L) (const S0) r.
Qed.

Lemma step_modeE0_loop_b10_b011_10_base (r : side) :
  cfg_modeE0_loop (S1 >> S0 >> (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0))) r -[ holdout_0311_tm ]->+
    cfg_modeC (S0 >> S1 >> const S0)
      (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> r)))).
Proof.
  exact (stepPlus_stepPlus_stepPlus (step_modeE0_loop_b10_b011_10_base_1 r) (step_modeE1_base _)).
Qed.

Lemma step_modeE0_loop_b10_b011_10_b10_1 (l r : side) :
  cfg_modeE0_loop (S1 >> S0 >> (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l))) r -[ holdout_0311_tm ]->+
    cfg_e0l_mid l r.
Proof.
  solve_local holdout_0311_tm 20
    (mkLocalState [S0; S1; S0; S0; S1; S1; S1; S0; S1; S0] [S0; S1; S1; S1; S0; S1] E L) l r.
Qed.

Lemma step_modeE0_loop_b10_b011_10_b10_2 (l r : side) :
  cfg_e0l_mid l r -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> r)).
Proof.
  solve_local holdout_0311_tm 20
    (mkLocalState [S1; S1; S1; S0; S1; S0] [S0; S0; S0; S1; S0; S1; S1; S1; S0; S1] B R) l r.
Qed.

Lemma step_modeE0_loop_b10_b011_10_b10 (l r : side) :
  cfg_modeE0_loop (S1 >> S0 >> (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l))) r -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> r)).
Proof.
  exact (stepPlus_stepPlus_stepPlus (step_modeE0_loop_b10_b011_10_b10_1 l r) (step_modeE0_loop_b10_b011_10_b10_2 l r)).
Qed.

Lemma step_modeE0_loop_b011_10 (l r : side) :
  cfg_modeE0_loop (S0 >> S1 >> S1 >> S1 >> S0 >> l) r -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> r)))).
Proof.
  solve_local holdout_0311_tm 27
    (mkLocalState [S0; S0; S1; S1; S1; S0] [S0; S1; S1; S1; S0; S1] E L) l r.
Qed.

Lemma step_modeC_b01110_b10_b101_nil_1 (l : side) :
  cfg_modeC (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l))
    (S1 >> S0 >> S1 >> const S0) -[ holdout_0311_tm ]->+ cfg_transA_mid l.
Proof.
  solve_local holdout_0311_tm 40
    (mkLocalState [S1; S0; S0; S1; S1; S1; S0; S1; S0] [S1; S0; S1; S0; S0; S0; S0; S0; S0] C R) l (const S0).
Qed.

Lemma step_modeC_b01110_b10_b101_nil_2 (l : side) :
  cfg_transA_mid l -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >>
      (S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> const S0)).
Proof.
  solve_local holdout_0311_tm 40
    (mkLocalState [S1; S1; S1; S1; S0; S0; S1; S1; S1; S0; S1; S0] [S0; S0; S0; S1; S0; S1] B R) l (const S0).
Qed.

Lemma step_modeC_b01110_b10_b101_nil (l : side) :
  cfg_modeC (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l))
    (S1 >> S0 >> S1 >> const S0) -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >>
      (S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> const S0)).
Proof.
  exact (stepPlus_stepPlus_stepPlus (step_modeC_b01110_b10_b101_nil_1 l) (step_modeC_b01110_b10_b101_nil_2 l)).
Qed.

Lemma step_modeC_b01110_b10_b0000101_1 (l r : side) :
  cfg_modeC (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l))
    (S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> r) -[ holdout_0311_tm ]->+ cfg_transB_mid l r.
Proof.
  solve_local holdout_0311_tm 23
    (mkLocalState [S1; S0; S0; S1; S1; S1; S0; S1; S0] [S0; S0; S0; S0; S1; S0; S1] C R) l r.
Qed.

Lemma step_modeC_b01110_b10_b0000101_2 (l r : side) :
  cfg_transB_mid l r -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S0 >> S0 >> S0 >>
      (S1 >> S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> r)))).
Proof.
  solve_local holdout_0311_tm 23
    (mkLocalState [S1; S0; S1; S1; S0; S1; S0] [S1; S0; S1; S0; S1; S0; S1; S0; S1] B R) l r.
Qed.

Lemma step_modeC_b01110_b10_b0000101 (l r : side) :
  cfg_modeC (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l))
    (S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> r) -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S0 >> S0 >> S0 >>
      (S1 >> S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> r)))).
Proof.
  exact (stepPlus_stepPlus_stepPlus (step_modeC_b01110_b10_b0000101_1 l r) (step_modeC_b01110_b10_b0000101_2 l r)).
Qed.

Fixpoint prepend10 (k : nat) (l : side) : side :=
  match k with
  | O => l
  | S k' => S1 >> S0 >> prepend10 k' l
  end.

Fixpoint encL_tail (ks : list nat) : side :=
  match ks with
  | [] => S0 >> S1 >> const S0
  | k :: ks' => S0 >> S1 >> S1 >> S1 >> S0 >> prepend10 k (encL_tail ks')
  end.

Definition encL (k0 : nat) (ks : list nat) : side :=
  prepend10 k0 (encL_tail ks).

Lemma encL_zero_nil : encL 0 [] = S0 >> S1 >> const S0.
Proof. reflexivity. Qed.

Lemma encL_S (k : nat) (ks : list nat) :
  encL (S k) ks = S1 >> S0 >> encL k ks.
Proof. reflexivity. Qed.

Lemma encL_succ (k : nat) (ks : list nat) :
  encL (k + 1) ks = S1 >> S0 >> encL k ks.
Proof. rewrite Nat.add_1_r. reflexivity. Qed.

Lemma encL_zero_cons (k : nat) (ks : list nat) :
  encL 0 (k :: ks) = S0 >> S1 >> S1 >> S1 >> S0 >> encL k ks.
Proof. reflexivity. Qed.

Lemma step_modeC_b01_encL (k0 : nat) (ks : list nat) (r : side) :
  cfg_modeC (encL k0 ks) (S0 >> S1 >> r) -[ holdout_0311_tm ]->+
    cfg_modeC (encL (k0 + 1) ks) r.
Proof. rewrite Nat.add_1_r. exact (step_modeC_b01 (encL k0 ks) r). Qed.

Lemma step_modeC_b01_b10101_encL (k0 : nat) (ks : list nat) (r : side) :
  cfg_modeC (encL k0 ks) (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> r) -[ holdout_0311_tm ]->+
    cfg_modeC (encL 0 ((k0 + 1) :: ks)) r.
Proof. rewrite Nat.add_1_r. exact (step_modeC_b01_b10101 (encL k0 ks) r). Qed.

Lemma step_modeE1_b10_encL (k0 : nat) (ks : list nat) (r : side) :
  cfg_modeE1 (encL (k0 + 1) ks) r -[ holdout_0311_tm ]->+
    cfg_modeE1 (encL k0 ks) (S0 >> S1 >> r).
Proof. rewrite Nat.add_1_r. exact (step_modeE1_b10 (encL k0 ks) r). Qed.

Lemma step_modeE1_b011_10_b10_encL (k1 : nat) (ks : list nat) (r : side) :
  cfg_modeE1 (encL 0 ((k1 + 1) :: ks)) r -[ holdout_0311_tm ]->+
    cfg_modeE1 (encL k1 ks) (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> r).
Proof. rewrite Nat.add_1_r. exact (step_modeE1_b011_10_b10 (encL k1 ks) r). Qed.

Lemma step_modeE0_first_b10_encL (x0 : nat) (ks : list nat) :
  cfg_modeE0_first (encL (x0 + 1) ks) -[ holdout_0311_tm ]->+
    cfg_modeE0_loop (encL x0 ks) (const S0).
Proof. rewrite Nat.add_1_r. exact (step_modeE0_first_b10 (encL x0 ks)). Qed.

Lemma step_modeE0_first_b011_10_b10_encL (x1 : nat) (ks : list nat) :
  cfg_modeE0_first (encL 0 ((x1 + 1) :: ks)) -[ holdout_0311_tm ]->+
    cfg_modeE1 (encL x1 ks) (S0 >> S1 >> S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> const S0)).
Proof. rewrite Nat.add_1_r. exact (step_modeE0_first_b011_10_b10 (encL x1 ks)). Qed.

Lemma step_modeE0_loop_b10_b011_10_b10_encL (x1 : nat) (ks : list nat) (r : side) :
  cfg_modeE0_loop (encL 1 ((x1 + 1) :: ks)) r -[ holdout_0311_tm ]->+
    cfg_modeE1 (encL x1 ks) (S0 >> S1 >> S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> r)).
Proof. rewrite Nat.add_1_r. exact (step_modeE0_loop_b10_b011_10_b10 (encL x1 ks) r). Qed.

Lemma step_modeC_b01110_b10_b101_nil_encL (z1 : nat) (zs : list nat) :
  cfg_modeC (encL 0 ((z1 + 1) :: zs)) (S1 >> S0 >> S1 >> const S0) -[ holdout_0311_tm ]->+
    cfg_modeE1 (encL z1 zs) (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >>
      (S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> const S0)).
Proof. rewrite Nat.add_1_r. exact (step_modeC_b01110_b10_b101_nil (encL z1 zs)). Qed.

Lemma step_modeC_b01110_b10_b0000101_encL (z1 : nat) (zs : list nat) (r : side) :
  cfg_modeC (encL 0 ((z1 + 1) :: zs)) (S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> r) -[ holdout_0311_tm ]->+
    cfg_modeE1 (encL z1 zs) (S0 >> S1 >> S0 >> S0 >> S0 >>
      (S1 >> S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> r)))).
Proof. rewrite Nat.add_1_r. exact (step_modeC_b01110_b10_b0000101 (encL z1 zs) r). Qed.

Fixpoint prepend01 (k : nat) (r : side) : side :=
  match k with
  | O => r
  | S k' => S0 >> S1 >> prepend01 k' r
  end.

Lemma prepend01_add (a b : nat) (r : side) :
  prepend01 (a + b) r = prepend01 a (prepend01 b r).
Proof.
  induction a as [|a IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Fixpoint prepend11_01 (d : nat) (r : side) : side :=
  match d with
  | O => r
  | S d' => S1 >> S1 >> S0 >> S1 >> prepend11_01 d' r
  end.

Lemma prepend11_01_add (a b : nat) (r : side) :
  prepend11_01 (a + b) r = prepend11_01 a (prepend11_01 b r).
Proof.
  induction a as [|a IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Fixpoint add_last (ks : list nat) (c : nat) : list nat :=
  match ks with
  | [] => []
  | [x] => [x + c]
  | x :: ((_ :: _) as rest) => x :: add_last rest c
  end.

Lemma add_last_cons (x : nat) (ks : list nat) (c : nat) :
  ks <> [] -> add_last (x :: ks) c = x :: add_last ks c.
Proof.
  destruct ks as [|y rest]; [congruence | reflexivity].
Qed.

Lemma add_last_length (ks : list nat) (c : nat) :
  List.length (add_last ks c) = List.length ks.
Proof.
  induction ks as [|x [|y rest] IH]; simpl; [reflexivity | reflexivity | f_equal; exact IH].
Qed.

Lemma add_last_ne_nil (ks : list nat) (c : nat) :
  ks <> [] -> add_last ks c <> [].
Proof.
  destruct ks as [|x [|y rest]]; simpl; congruence.
Qed.

Lemma add_last_zero (ks : list nat) :
  add_last ks 0 = ks.
Proof.
  induction ks as [|x [|y rest] IH]; simpl; [reflexivity | f_equal; lia | f_equal; exact IH].
Qed.

Lemma add_last_add (ks : list nat) (a b : nat) :
  add_last (add_last ks a) b = add_last ks (a + b).
Proof.
  induction ks as [|x [|y rest] IH].
  - reflexivity.
  - simpl; f_equal; lia.
  - rewrite (add_last_cons x (y :: rest) a ltac:(discriminate)).
    rewrite (add_last_cons x (add_last (y :: rest) a) b (add_last_ne_nil (y :: rest) a ltac:(discriminate))).
    rewrite (add_last_cons x (y :: rest) (a + b) ltac:(discriminate)).
    f_equal; exact IH.
Qed.

Definition bump_enc (k0 : nat) (ks : list nat) : nat * list nat :=
  match ks with
  | [] => (k0 + 3, [])
  | k1 :: ks' => (k0, add_last (k1 :: ks') 3)
  end.

Definition bump_enc_twice (m0 : nat) (ms : list nat) : nat * list nat :=
  let p := bump_enc m0 ms in
  bump_enc (fst p) (snd p).

Lemma bump_enc_nonempty (k0 : nat) (ks : list nat) :
  ks <> [] -> bump_enc k0 ks = (k0, add_last ks 3).
Proof.
  destruct ks as [|k1 ks']; [congruence | reflexivity].
Qed.

Lemma bump_enc_twice_nonempty (m0 : nat) (ms : list nat) :
  ms <> [] -> bump_enc_twice m0 ms = (m0, add_last ms 6).
Proof.
  intros Hne. unfold bump_enc_twice.
  rewrite (bump_enc_nonempty m0 ms Hne); simpl.
  rewrite (bump_enc_nonempty m0 (add_last ms 3) (add_last_ne_nil ms 3 Hne)).
  rewrite add_last_add. reflexivity.
Qed.

Fixpoint ValidKS (ks : list nat) : Prop :=
  match ks with
  | [] => True
  | [_] => True
  | k :: ((_ :: _) as rest) => k >= 1 /\ ValidKS rest
  end.

Lemma ValidKS_add_last (ks : list nat) (c : nat) :
  ValidKS ks -> ValidKS (add_last ks c).
Proof.
  induction ks as [|k [|y rest] IH]; intros Hval; [exact I | exact I |].
  destruct Hval as [Hk Hrest].
  rewrite (add_last_cons k (y :: rest) c ltac:(discriminate)).
  pose proof (add_last_ne_nil (y :: rest) c ltac:(discriminate)) as Hne.
  pose proof (IH Hrest) as Hih.
  destruct (add_last (y :: rest) c) as [|z zs]; [congruence | exact (conj Hk Hih)].
Qed.

Fixpoint GoodKS (s : nat) (ks : list nat) : Prop :=
  match ks with
  | [] => True
  | k :: rest => s <= 35 * (k + 2) /\ GoodKS (s + 63 * (k + 2)) rest
  end.

Lemma GoodKS_mono (ks : list nat) :
  forall (s1 s2 : nat), s1 <= s2 -> GoodKS s2 ks -> GoodKS s1 ks.
Proof.
  induction ks as [|k rest IH]; simpl; intros s1 s2 Hle Hg; [exact I |].
  destruct Hg as [H1 H2].
  split; [lia | apply (IH _ (s2 + 63 * (k + 2))); [lia | exact H2]].
Qed.

Lemma GoodKS_add_last (ks : list nat) :
  forall (s c : nat), GoodKS s ks -> GoodKS s (add_last ks c).
Proof.
  induction ks as [|k [|y rest] IH]; simpl; intros s c Hg; [exact I | |].
  - destruct Hg as [H1 _]; split; [lia | exact I].
  - destruct Hg as [H1 H2]; split; [exact H1 | apply IH; exact H2].
Qed.

Lemma GoodKS_valid (ks : list nat) :
  forall (s : nat), s >= 71 -> GoodKS s ks -> ValidKS ks.
Proof.
  induction ks as [|k [|y rest] IH]; simpl; intros s Hs Hg; [exact I | exact I |].
  destruct Hg as [H1 H2].
  split; [lia | apply (IH (s + 63 * (k + 2))); [lia | exact H2]].
Qed.

Lemma GoodKS_succ_valid (s w : nat) (ws : list nat) :
  GoodKS s ((w + 1) :: ws) -> ValidKS ((w + 1) :: ws).
Proof.
  destruct ws as [|y rest]; simpl; intros Hg; [exact I |].
  destruct Hg as [H1 H2].
  split; [lia | apply (GoodKS_valid (y :: rest) (s + 63 * (w + 1 + 2))); [lia | exact H2]].
Qed.

Definition InvNil (k0 : nat) (ks : list nat) : Prop :=
  (ks = [] /\ k0 >= 5) \/
  (ks <> [] /\ GoodKS (if Nat.eqb k0 1 then 81 else 36 * (k0 + 2)) ks).

Lemma modeC_prepend01_star (n : nat) :
  forall (k0 : nat) (ks : list nat) (r : side),
    cfg_modeC (encL k0 ks) (prepend01 n r) -[ holdout_0311_tm ]->*
      cfg_modeC (encL (k0 + n) ks) r.
Proof.
  induction n as [|n IH]; intros k0 ks r; cbn [prepend01].
  - replace (k0 + 0) with k0 by lia. apply evstep_refl.
  - pose proof (step_modeC_b01_encL k0 ks (prepend01 n r)) as H1.
    pose proof (IH (k0 + 1) ks r) as H2.
    replace (k0 + 1 + n) with (k0 + S n) in H2 by lia.
    exact (stepPlus_stepStar (stepPlus_stepStar_stepPlus H1 H2)).
Qed.

Lemma e0_loop_drain_pairs (d : nat) :
  forall (rem : nat) (xs : list nat) (r : side),
    cfg_modeE0_loop (encL (rem + 2 * d) xs) r -[ holdout_0311_tm ]->*
      cfg_modeE0_loop (encL rem xs) (prepend11_01 d r).
Proof.
  induction d as [|d IH]; intros rem xs r; cbn [prepend11_01].
  - replace (rem + 2 * 0) with rem by lia. apply evstep_refl.
  - replace (rem + 2 * S d) with (S (S (rem + 2 * d))) by lia.
    pose proof (step_modeE0_loop_b10_b10 (encL (rem + 2 * d) xs) r) as H1.
    change (S1 >> S1 >> (S0 >> S1 >> r)) with (prepend11_01 1 r) in H1.
    pose proof (IH rem xs (prepend11_01 1 r)) as H2.
    rewrite <- prepend11_01_add in H2.
    replace (d + 1) with (S d) in H2 by lia.
    exact (stepPlus_stepStar (stepPlus_stepStar_stepPlus H1 H2)).
Qed.

Lemma modeE1_drain_k0 (k0 : nat) :
  forall (ks : list nat) (r : side),
    cfg_modeE1 (encL k0 ks) r -[ holdout_0311_tm ]->*
      cfg_modeE1 (encL 0 ks) (prepend01 k0 r).
Proof.
  induction k0 as [|k0 IH]; intros ks r.
  - apply evstep_refl.
  - pose proof (step_modeE1_b10 (encL k0 ks) r) as H1.
    change (S0 >> S1 >> r) with (prepend01 1 r) in H1.
    pose proof (IH ks (prepend01 1 r)) as H2.
    rewrite <- prepend01_add in H2.
    replace (k0 + 1) with (S k0) in H2 by lia.
    exact (stepPlus_stepStar (stepPlus_stepStar_stepPlus H1 H2)).
Qed.

Lemma modeE1_to_modeC (ks : list nat) :
  forall (k0 : nat) (r : side),
    ValidKS ks ->
    let b := bump_enc k0 ks in
    cfg_modeE1 (encL k0 ks) r -[ holdout_0311_tm ]->+ cfg_modeC (encL (fst b) (snd b)) r.
Proof.
  induction ks as [|k1 ks' IH]; intros k0 r Hval; simpl.
  - pose proof (modeE1_drain_k0 k0 [] r) as H1.
    pose proof (step_modeE1_base (prepend01 k0 r)) as H2.
    change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> prepend01 k0 r)))
      with (prepend01 3 (prepend01 k0 r)) in H2.
    rewrite <- prepend01_add in H2.
    replace (3 + k0) with (k0 + 3) in H2 by lia.
    pose proof (modeC_prepend01_star (k0 + 3) 0 [] r) as H3; simpl in H3.
    exact (stepStar_stepPlus_stepPlus H1 (stepPlus_stepStar_stepPlus H2 H3)).
  - destruct ks' as [|k2 ks''].
    + simpl.
      pose proof (modeE1_drain_k0 k0 [k1] r) as H1.
      destruct k1 as [|k1'].
      * pose proof (step_modeE1_b011_10_base (prepend01 k0 r)) as H2.
        pose proof (step_modeC_b01 (encL 0 [])
          (S0 >> S1 >> (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> prepend01 k0 r))) as H3.
        pose proof (step_modeC_b01 (encL 1 [])
          (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> prepend01 k0 r)) as H4.
        pose proof (step_modeC_b01_b10101_encL 2 [] (prepend01 k0 r)) as H5; simpl in H5.
        pose proof (modeC_prepend01_star k0 0 [3] r) as H6; simpl in H6.
        exact (stepStar_stepPlus_stepPlus H1
          (stepPlus_stepPlus_stepPlus H2
            (stepPlus_stepPlus_stepPlus H3
              (stepPlus_stepPlus_stepPlus H4
                (stepPlus_stepStar_stepPlus H5 H6))))).
      * pose proof (step_modeE1_b011_10_b10 (encL k1' []) (prepend01 k0 r)) as H2.
        pose proof (IH k1' (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> prepend01 k0 r) I) as H3.
        simpl in H3.
        pose proof (step_modeC_b01_b10101_encL (k1' + 3) [] (prepend01 k0 r)) as H4.
        replace (k1' + 3 + 1) with (S k1' + 3) in H4 by lia.
        pose proof (modeC_prepend01_star k0 0 [S k1' + 3] r) as H5; simpl in H5.
        exact (stepStar_stepPlus_stepPlus H1
          (stepPlus_stepPlus_stepPlus H2
            (stepPlus_stepPlus_stepPlus H3
              (stepPlus_stepStar_stepPlus H4 H5)))).
    + simpl in Hval. destruct Hval as [Hk1 Hval'].
      destruct k1 as [|k1']; [lia|].
      simpl.
      pose proof (modeE1_drain_k0 k0 (S k1' :: k2 :: ks'') r) as H1.
      pose proof (step_modeE1_b011_10_b10 (encL k1' (k2 :: ks'')) (prepend01 k0 r)) as H2.
      pose proof (IH k1' (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> prepend01 k0 r) Hval') as H3.
      simpl in H3.
      pose proof (step_modeC_b01_b10101 (encL k1' (add_last (k2 :: ks'') 3)) (prepend01 k0 r)) as H4.
      pose proof (modeC_prepend01_star k0 0 (S k1' :: add_last (k2 :: ks'') 3) r) as H5; simpl in H5.
      exact (stepStar_stepPlus_stepPlus H1
        (stepPlus_stepPlus_stepPlus H2
          (stepPlus_stepPlus_stepPlus H3
            (stepPlus_stepStar_stepPlus H4 H5)))).
Qed.

Lemma modeC_consume_11_01_nil (n : nat) :
  forall (k0 : nat) (r : side),
    cfg_modeC (encL k0 []) (prepend11_01 n r) -[ holdout_0311_tm ]->*
      cfg_modeC (encL (k0 + 4 * n) []) r.
Proof.
  induction n as [|n IH]; intros k0 r; cbn [prepend11_01].
  - replace (k0 + 4 * 0) with k0 by lia. apply evstep_refl.
  - pose proof (step_modeC_b11 (encL k0 []) (S0 >> S1 >> prepend11_01 n r)) as H1.
    pose proof (modeE1_to_modeC [] k0 (S0 >> S1 >> prepend11_01 n r) I) as H2; simpl in H2.
    pose proof (step_modeC_b01_encL (k0 + 3) [] (prepend11_01 n r)) as H3.
    replace (k0 + 3 + 1) with (k0 + 4) in H3 by lia.
    pose proof (IH (k0 + 4) r) as H4.
    replace (k0 + 4 + 4 * n) with (k0 + 4 * S n) in H4 by lia.
    exact (stepPlus_stepStar
      (stepPlus_stepPlus_stepPlus H1
        (stepPlus_stepPlus_stepPlus H2
          (stepPlus_stepStar_stepPlus H3 H4)))).
Qed.

Lemma modeC_consume_11_01_nonempty (n : nat) :
  forall (k0 : nat) (ks : list nat) (r : side),
    ks <> [] -> ValidKS ks ->
    cfg_modeC (encL k0 ks) (prepend11_01 n r) -[ holdout_0311_tm ]->*
      cfg_modeC (encL (k0 + n) (add_last ks (3 * n))) r.
Proof.
  induction n as [|n IH]; intros k0 ks r Hne Hval; cbn [prepend11_01].
  - replace (k0 + 0) with k0 by lia. replace (3 * 0) with 0 by lia.
    rewrite add_last_zero. apply evstep_refl.
  - pose proof (step_modeC_b11 (encL k0 ks) (S0 >> S1 >> prepend11_01 n r)) as H1.
    pose proof (modeE1_to_modeC ks k0 (S0 >> S1 >> prepend11_01 n r) Hval) as H2; simpl in H2.
    rewrite (bump_enc_nonempty k0 ks Hne) in H2; simpl in H2.
    pose proof (step_modeC_b01_encL k0 (add_last ks 3) (prepend11_01 n r)) as H3.
    pose proof (IH (k0 + 1) (add_last ks 3) r
      (add_last_ne_nil ks 3 Hne) (ValidKS_add_last ks 3 Hval)) as H4.
    rewrite add_last_add in H4.
    replace (k0 + 1 + n) with (k0 + S n) in H4 by lia.
    replace (3 + 3 * n) with (3 * S n) in H4 by lia.
    exact (stepPlus_stepStar
      (stepPlus_stepPlus_stepPlus H1
        (stepPlus_stepPlus_stepPlus H2
          (stepPlus_stepStar_stepPlus H3 H4)))).
Qed.

Lemma ValidKS_bump_enc (m0 : nat) (ms : list nat) :
  ValidKS ms -> ValidKS (snd (bump_enc m0 ms)).
Proof.
  destruct ms as [|x rest]; simpl; intros H; [exact I | exact (ValidKS_add_last (x :: rest) 3 H)].
Qed.

Lemma unwrap_11_01_1011101_step (m0 : nat) (ms : list nat) (R0 : side) :
  ValidKS ms ->
  let p := bump_enc_twice m0 ms in
  cfg_modeC (encL m0 ms)
    (S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> R0)
    -[ holdout_0311_tm ]->+
    cfg_modeC (encL 0 ((fst p + 1) :: snd p)) R0.
Proof.
  intros Hval. simpl.
  set (p1 := bump_enc m0 ms).
  set (p2 := bump_enc (fst p1) (snd p1)).
  pose proof (step_modeC_b11 (encL m0 ms)
    (S0 >> S1 >> S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> R0)) as H1.
  pose proof (modeE1_to_modeC ms m0
    (S0 >> S1 >> S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> R0) Hval) as H2.
  fold p1 in H2.
  pose proof (step_modeC_b01_b1011101 (encL (fst p1) (snd p1)) R0) as H3.
  pose proof (modeE1_to_modeC (snd p1) (fst p1)
    (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> R0)
    (ValidKS_bump_enc m0 ms Hval)) as H4.
  fold p2 in H4.
  pose proof (step_modeC_b01_b10101_encL (fst p2) (snd p2) R0) as H5.
  exact (stepPlus_stepPlus_stepPlus H1
    (stepPlus_stepPlus_stepPlus H2
      (stepPlus_stepPlus_stepPlus H3
        (stepPlus_stepPlus_stepPlus H4 H5)))).
Qed.

Lemma prepend11_01_split_last (d : nat) (R0 : side) :
  d >= 1 ->
  prepend11_01 d R0 = prepend11_01 (d - 1) (S1 >> S1 >> S0 >> S1 >> R0).
Proof.
  intros Hd.
  replace d with ((d - 1) + 1) at 1 by lia.
  rewrite prepend11_01_add. reflexivity.
Qed.

Lemma prepend11_01_S_split (d : nat) (R0 : side) :
  prepend11_01 (S d) R0 = prepend11_01 d (S1 >> S1 >> S0 >> S1 >> R0).
Proof.
  replace (S d) with (d + 1) by lia.
  rewrite prepend11_01_add. reflexivity.
Qed.

Lemma e0_loop_leave1_goodks (n : nat) :
  forall (x0 : nat) (xs : list nat) (S0_val : nat) (R0 : side),
    List.length xs = n ->
    S0_val >= 36 ->
    (xs = [] -> 2 * S0_val <= 35 * x0) ->
    (xs <> [] -> x0 >= 2 /\ 2 * S0_val <= 35 * (x0 + 3)) ->
    GoodKS (2 * S0_val + 63 * (x0 + 3)) xs ->
    exists m0 ms,
      (cfg_modeE0_loop (encL x0 xs) R0 -[ holdout_0311_tm ]->+
        cfg_modeC (encL m0 ms) (S1 >> S1 >> S0 >> S1 >> R0)) /\
      ValidKS ms /\
      (ms = [] -> m0 >= 7) /\
      (let p := bump_enc_twice m0 ms in GoodKS S0_val ((fst p + 1) :: snd p)) /\
      ((xs = [] -> x0 >= 10) -> S0_val = 81 ->
        let p1 := bump_enc m0 ms in GoodKS 81 ((fst p1 + 1) :: snd p1)).
Proof.
  induction n as [|n' IH]; intros x0 xs S0_val R0 Hlen HS Hnil Hcons Hgks.
  - destruct xs as [|x1 xs_rest]; [|simpl in Hlen; lia].
    pose proof (Hnil eq_refl) as Hx0.
    assert (Hx0_ge : x0 >= 3) by lia.
    set (d := x0 / 2).
    set (rem := x0 mod 2).
    assert (Hdiv : rem + 2 * d = x0) by (unfold d, rem; lia).
    assert (Hrem : rem = 0 \/ rem = 1) by (unfold rem; lia).
    destruct Hrem as [Heven | Hodd].
    + assert (Hd : d >= 2) by lia.
      exists d, [3 * d - 3].
      split; [|split; [exact I | split; [discriminate | split]]].
      * assert (Hd_split : x0 = 0 + 2 * d) by lia.
        rewrite Hd_split.
        pose proof (e0_loop_drain_pairs d 0 [] R0) as H1.
        pose proof (step_modeE0_loop_base (prepend11_01 d R0)) as H2.
        change (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0)) with (encL 0 [0]) in H2.
        pose proof (step_modeC_b01_encL 0 [0] (prepend11_01 d R0)) as H3; simpl in H3.
        pose proof (modeC_consume_11_01_nonempty (d - 1) 1 [0]
          (S1 >> S1 >> S0 >> S1 >> R0) ltac:(discriminate) I) as H4.
        cbn [add_last] in H4.
        rewrite <- (prepend11_01_split_last d R0 ltac:(lia)) in H4.
        replace (1 + (d - 1)) with d in H4 by lia.
        replace (0 + 3 * (d - 1)) with (3 * d - 3) in H4 by lia.
        exact (stepStar_stepPlus_stepPlus H1 (stepPlus_stepPlus_stepPlus H2 (stepPlus_stepStar_stepPlus H3 H4))).
      * unfold bump_enc_twice, bump_enc; cbn [fst snd add_last GoodKS].
        split; [lia | split; [lia | exact I]].
      * intros Hx10 HS81.
        pose proof (Hx10 eq_refl) as Hx10'.
        assert (Hd5 : d >= 5) by lia.
        unfold bump_enc; cbn [fst snd add_last GoodKS].
        split; [lia | split; [lia | exact I]].
    + assert (Hd : d >= 1) by lia.
      exists (4 * d + 3), (@nil nat).
      split; [|split; [exact I | split; [intros _; lia | split]]].
      * assert (Hd_split : x0 = 1 + 2 * d) by lia.
        rewrite Hd_split.
        pose proof (e0_loop_drain_pairs d 1 [] R0) as H1.
        pose proof (step_modeE0_loop_b10_base (prepend11_01 d R0)) as H2.
        change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S1 >> S1 >> (S0 >> S1 >> prepend11_01 d R0)))))
          with (prepend01 3 (prepend11_01 (S d) R0)) in H2.
        pose proof (modeC_prepend01_star 3 0 [] (prepend11_01 (S d) R0)) as H3; simpl in H3.
        pose proof (modeC_consume_11_01_nil d 3 (S1 >> S1 >> S0 >> S1 >> R0)) as H4.
        rewrite <- (prepend11_01_S_split d R0) in H4.
        replace (3 + 4 * d) with (4 * d + 3) in H4 by lia.
        exact (stepStar_stepPlus_stepPlus H1 (stepPlus_stepStar_stepPlus H2 (stepStar_trans H3 H4))).
      * unfold bump_enc_twice, bump_enc; cbn [fst snd GoodKS].
        split; [lia | exact I].
      * intros _ _.
        unfold bump_enc; cbn [fst snd GoodKS].
        split; [lia | exact I].
  - destruct xs as [|x1 xs_rest]; [simpl in Hlen; lia|].
    assert (Hlen' : List.length xs_rest = n') by (simpl in Hlen; lia).
    destruct (Hcons ltac:(discriminate)) as [Hx0_ge Hx0_bound].
    cbn [GoodKS] in Hgks; destruct Hgks as [Hx1_bound Hgks_rest].
    assert (Hx1_ge : x1 >= 1) by lia.
    pose proof (GoodKS_valid xs_rest (2 * S0_val + 63 * (x0 + 3) + 63 * (x1 + 2)) ltac:(lia) Hgks_rest) as Hval_rest.
    set (d := x0 / 2).
    set (rem := x0 mod 2).
    assert (Hd : d >= 1) by (unfold d; lia).
    assert (Hdiv : rem + 2 * d = x0) by (unfold d, rem; lia).
    assert (Hrem : rem = 0 \/ rem = 1) by (unfold rem; lia).
    destruct Hrem as [Heven | Hodd].
    + assert (Hd_split : x0 = 0 + 2 * d) by lia.
      destruct xs_rest as [|x2 rest'].
      * exists (x1 + 4 * d + 3), (@nil nat).
        split; [|split; [exact I | split; [intros _; lia | split]]].
        -- rewrite Hd_split.
           pose proof (e0_loop_drain_pairs d 0 [x1] R0) as H1.
           pose proof (step_modeE0_loop_b011_10 (encL x1 []) (prepend11_01 d R0)) as H2.
           change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> prepend11_01 d R0))))
             with (prepend01 4 (prepend11_01 d R0)) in H2.
           pose proof (modeE1_to_modeC [] x1 (prepend01 4 (prepend11_01 d R0)) I) as H3; simpl in H3.
           pose proof (modeC_prepend01_star 4 (x1 + 3) [] (prepend11_01 d R0)) as H4.
           pose proof (modeC_consume_11_01_nil (d - 1) (x1 + 3 + 4) (S1 >> S1 >> S0 >> S1 >> R0)) as H5.
           rewrite <- (prepend11_01_split_last d R0 Hd) in H5.
           replace (x1 + 3 + 4 + 4 * (d - 1)) with (x1 + 4 * d + 3) in H5 by lia.
           exact (stepStar_stepPlus_stepPlus H1
             (stepPlus_stepPlus_stepPlus H2
               (stepPlus_stepStar_stepPlus H3 (stepStar_trans H4 H5)))).
        -- unfold bump_enc_twice, bump_enc; cbn [fst snd GoodKS].
           split; [lia | exact I].
        -- intros _ _.
           unfold bump_enc; cbn [fst snd GoodKS].
           split; [lia | exact I].
      * assert (Hne_rest : x2 :: rest' <> []) by discriminate.
        exists (x1 + d + 3), (add_last (x2 :: rest') (3 * d)).
        split; [|split; [exact (ValidKS_add_last (x2 :: rest') (3 * d) Hval_rest) |
                 split; [intros Hemp; exfalso; exact (add_last_ne_nil (x2 :: rest') (3 * d) Hne_rest Hemp) | split]]].
        -- rewrite Hd_split.
           pose proof (e0_loop_drain_pairs d 0 (x1 :: x2 :: rest') R0) as H1.
           pose proof (step_modeE0_loop_b011_10 (encL x1 (x2 :: rest')) (prepend11_01 d R0)) as H2.
           change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> prepend11_01 d R0))))
             with (prepend01 4 (prepend11_01 d R0)) in H2.
           pose proof (modeE1_to_modeC (x2 :: rest') x1 (prepend01 4 (prepend11_01 d R0)) Hval_rest) as H3.
           rewrite (bump_enc_nonempty x1 (x2 :: rest') Hne_rest) in H3; simpl in H3.
           pose proof (modeC_prepend01_star 4 x1 (add_last (x2 :: rest') 3) (prepend11_01 d R0)) as H4.
           pose proof (modeC_consume_11_01_nonempty (d - 1) (x1 + 4) (add_last (x2 :: rest') 3)
             (S1 >> S1 >> S0 >> S1 >> R0)
             (add_last_ne_nil (x2 :: rest') 3 Hne_rest)
             (ValidKS_add_last (x2 :: rest') 3 Hval_rest)) as H5.
           rewrite add_last_add in H5.
           rewrite <- (prepend11_01_split_last d R0 Hd) in H5.
           replace (x1 + 4 + (d - 1)) with (x1 + d + 3) in H5 by lia.
           replace (3 + 3 * (d - 1)) with (3 * d) in H5 by lia.
           exact (stepStar_stepPlus_stepPlus H1
             (stepPlus_stepPlus_stepPlus H2
               (stepPlus_stepStar_stepPlus H3 (stepStar_trans H4 H5)))).
        -- cbv zeta.
           rewrite (bump_enc_twice_nonempty (x1 + d + 3) (add_last (x2 :: rest') (3 * d))
             (add_last_ne_nil (x2 :: rest') (3 * d) Hne_rest)).
           rewrite add_last_add; cbn [fst snd GoodKS].
           split; [lia |].
           apply GoodKS_add_last.
           eapply GoodKS_mono; [|exact Hgks_rest]; lia.
        -- intros _ HS81; subst S0_val. cbv zeta.
           rewrite (bump_enc_nonempty (x1 + d + 3) (add_last (x2 :: rest') (3 * d))
             (add_last_ne_nil (x2 :: rest') (3 * d) Hne_rest)).
           rewrite add_last_add; cbn [fst snd GoodKS].
           split; [lia |].
           apply GoodKS_add_last.
           eapply GoodKS_mono; [|exact Hgks_rest]; lia.
    + assert (Hd_split : x0 = 1 + 2 * d) by lia.
      set (S_sub := S0_val + 63 * (d + 2)).
      assert (HS_sub : S_sub >= 36) by (unfold S_sub; lia).
      assert (Hx1_ge10 : x1 >= 10) by lia.
      set (sub := bump_enc (x1 - 1) xs_rest).
      assert (Hsub_len : List.length (snd sub) = n').
      { unfold sub, bump_enc; destruct xs_rest; cbn [fst snd]; [exact Hlen' | rewrite add_last_length; exact Hlen']. }
      assert (Hsub_nil : snd sub = [] -> 2 * S_sub <= 35 * fst sub).
      { unfold sub, bump_enc; destruct xs_rest as [|y ys]; cbn [fst snd]; [intros _; unfold S_sub; lia |].
        intros Hemp; exfalso; exact (add_last_ne_nil (y :: ys) 3 ltac:(discriminate) Hemp). }
      assert (Hsub_cons : snd sub <> [] -> fst sub >= 2 /\ 2 * S_sub <= 35 * (fst sub + 3)).
      { unfold sub, bump_enc; destruct xs_rest as [|y ys]; cbn [fst snd]; [congruence | intros _; unfold S_sub; lia]. }
      assert (Hsub_gks : GoodKS (2 * S_sub + 63 * (fst sub + 3)) (snd sub)).
      { unfold sub, bump_enc; destruct xs_rest as [|y ys]; cbn [fst snd]; [exact I |].
        replace (2 * S_sub + 63 * (x1 - 1 + 3)) with (2 * S0_val + 63 * (x0 + 3) + 63 * (x1 + 2)) by (unfold S_sub; lia).
        exact (GoodKS_add_last (y :: ys) _ 3 Hgks_rest). }
      set (R_tail := S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> prepend11_01 d R0).
      destruct (IH (fst sub) (snd sub) S_sub R_tail Hsub_len HS_sub Hsub_nil Hsub_cons Hsub_gks)
        as [y0 [ys [Hstep_sub [Hval_ys [Hys_emp [Hgks_sub _]]]]]].
      set (py := bump_enc_twice y0 ys).
      set (ks_mid := (fst py + 1) :: snd py).
      assert (Hne_mid : ks_mid <> []) by discriminate.
      assert (Hval_mid : ValidKS ks_mid) by (apply (GoodKS_succ_valid S_sub (fst py) (snd py)); exact Hgks_sub).
      exists (d - 1), (add_last ks_mid (3 * (d - 1))).
      split; [|split; [exact (ValidKS_add_last ks_mid (3 * (d - 1)) Hval_mid) |
               split; [intros Hemp; exfalso; exact (add_last_ne_nil ks_mid (3 * (d - 1)) Hne_mid Hemp) | split]]].
      * rewrite Hd_split.
        pose proof (e0_loop_drain_pairs d 1 (x1 :: xs_rest) R0) as H1.
        assert (Hx1_eq : x1 = (x1 - 1) + 1) by lia.
        pose proof (step_modeE0_loop_b10_b011_10_b10_encL (x1 - 1) xs_rest (prepend11_01 d R0)) as H2.
        rewrite <- Hx1_eq in H2.
        fold R_tail in H2.
        pose proof (modeE1_to_modeC xs_rest (x1 - 1)
          (S0 >> S1 >> S0 >> S0 >> S0 >> R_tail) Hval_rest) as H3.
        fold sub in H3.
        pose proof (step_modeC_b01_b000 (encL (fst sub) (snd sub)) R_tail) as H4.
        pose proof (unwrap_11_01_1011101_step y0 ys (prepend11_01 d R0) Hval_ys) as H5.
        fold py in H5; fold ks_mid in H5.
        pose proof (modeC_consume_11_01_nonempty (d - 1) 0 ks_mid
          (S1 >> S1 >> S0 >> S1 >> R0) Hne_mid Hval_mid) as H6.
        rewrite <- (prepend11_01_split_last d R0 Hd) in H6.
        replace (0 + (d - 1)) with (d - 1) in H6 by lia.
        exact (stepStar_stepPlus_stepPlus H1
          (stepPlus_stepPlus_stepPlus H2
            (stepPlus_stepPlus_stepPlus H3
              (stepPlus_stepPlus_stepPlus H4
                (stepPlus_stepPlus_stepPlus Hstep_sub
                  (stepPlus_stepStar_stepPlus H5 H6)))))).
      * cbv zeta.
        rewrite (bump_enc_twice_nonempty (d - 1) (add_last ks_mid (3 * (d - 1)))
          (add_last_ne_nil ks_mid (3 * (d - 1)) Hne_mid)).
        rewrite add_last_add; cbn [fst snd].
        replace (d - 1 + 1) with d by lia.
        cbn [GoodKS].
        split; [unfold S_sub; lia |].
        replace (S0_val + 63 * (d + 2)) with S_sub by reflexivity.
        exact (GoodKS_add_last ks_mid S_sub (3 * (d - 1) + 6) Hgks_sub).
      * intros _ HS81; subst S0_val. cbv zeta.
        rewrite (bump_enc_nonempty (d - 1) (add_last ks_mid (3 * (d - 1)))
          (add_last_ne_nil ks_mid (3 * (d - 1)) Hne_mid)).
        rewrite add_last_add; cbn [fst snd].
        replace (d - 1 + 1) with d by lia.
        cbn [GoodKS].
        split; [unfold S_sub; lia |].
        replace (81 + 63 * (d + 2)) with S_sub by reflexivity.
        exact (GoodKS_add_last ks_mid S_sub (3 * (d - 1) + 3) Hgks_sub).
Qed.

Lemma step_k0_pos (k0 : nat) (ks : list nat) :
  k0 >= 1 ->
  InvNil k0 ks ->
  exists k0' ks',
    (cfg_modeC (encL k0 ks) (const S0) -[ holdout_0311_tm ]->+ cfg_modeC (encL k0' ks') (const S0)) /\
    InvNil k0' ks'.
Proof.
  intros Hk0 Hinv.
  set (x0 := k0 - 1).
  assert (Hk0_eq : k0 = x0 + 1) by lia.
  assert (Hto_e0 : cfg_modeC (encL k0 ks) (const S0) -[ holdout_0311_tm ]->+ cfg_modeE0_loop (encL x0 ks) (const S0)).
  { rewrite Hk0_eq.
    exact (stepPlus_stepPlus_stepPlus (step_modeC_nil (encL (x0 + 1) ks)) (step_modeE0_first_b10_encL x0 ks)). }
  set (d := x0 / 2).
  set (rem := x0 mod 2).
  assert (Hdiv : rem + 2 * d = x0) by (unfold d, rem; lia).
  assert (Hrem : rem = 0 \/ rem = 1) by (unfold rem; lia).
  destruct Hinv as [[-> Hk5] | [Hne Hgks]].
  - destruct Hrem as [Heven | Hodd].
    + assert (Hd : d >= 2) by lia.
      assert (Hx_split : x0 = 0 + 2 * d) by lia.
      exists (d + 1), [3 * d].
      split.
      * rewrite Hx_split in Hto_e0.
        pose proof (e0_loop_drain_pairs d 0 [] (const S0)) as H1.
        pose proof (step_modeE0_loop_base (prepend11_01 d (const S0))) as H2.
        change (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0)) with (encL 0 [0]) in H2.
        pose proof (step_modeC_b01_encL 0 [0] (prepend11_01 d (const S0))) as H3; simpl in H3.
        pose proof (modeC_consume_11_01_nonempty d 1 [0] (const S0) ltac:(discriminate) I) as H4.
        cbn [add_last] in H4.
        replace (1 + d) with (d + 1) in H4 by lia.
        replace (0 + 3 * d) with (3 * d) in H4 by lia.
        exact (stepPlus_stepPlus_stepPlus Hto_e0
          (stepStar_stepPlus_stepPlus H1
            (stepPlus_stepPlus_stepPlus H2
              (stepPlus_stepStar_stepPlus H3 H4)))).
      * right; split; [discriminate |].
        destruct (Nat.eqb_spec (d + 1) 1); [lia |].
        cbn [GoodKS]; split; [lia | exact I].
    + assert (Hd : d >= 2) by lia.
      assert (Hx_split : x0 = 1 + 2 * d) by lia.
      exists (4 * d + 7), (@nil nat).
      split; [|left; split; [reflexivity | lia]].
      rewrite Hx_split in Hto_e0.
      pose proof (e0_loop_drain_pairs d 1 [] (const S0)) as H1.
      pose proof (step_modeE0_loop_b10_base (prepend11_01 d (const S0))) as H2.
      change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S1 >> S1 >> (S0 >> S1 >> prepend11_01 d (const S0))))))
        with (prepend01 3 (prepend11_01 (S d) (const S0))) in H2.
      pose proof (modeC_prepend01_star 3 0 [] (prepend11_01 (S d) (const S0))) as H3; simpl in H3.
      pose proof (modeC_consume_11_01_nil (S d) 3 (const S0)) as H4.
      replace (3 + 4 * S d) with (4 * d + 7) in H4 by lia.
      exact (stepPlus_stepPlus_stepPlus Hto_e0
        (stepStar_stepPlus_stepPlus H1
          (stepPlus_stepStar_stepPlus H2 (stepStar_trans H3 H4)))).
  - destruct ks as [|k1 ks_rest]; [congruence |].
    set (S_in := if Nat.eqb k0 1 then 81 else 36 * (k0 + 2)).
    fold S_in in Hgks.
    assert (HS_in_ge : S_in >= 81).
    { unfold S_in; destruct (Nat.eqb_spec k0 1); lia. }
    cbn [GoodKS] in Hgks; destruct Hgks as [Hk1_bound Hgks_rest].
    assert (Hk1_ge : k1 >= 1) by lia.
    pose proof (GoodKS_valid ks_rest (S_in + 63 * (k1 + 2)) ltac:(lia) Hgks_rest) as Hval_rest.
    destruct Hrem as [Heven | Hodd].
    + assert (Hx_split : x0 = 0 + 2 * d) by lia.
      destruct ks_rest as [|k2 rest'].
      * exists (k1 + 4 * d + 7), (@nil nat).
        split; [|left; split; [reflexivity | lia]].
        rewrite Hx_split in Hto_e0.
        pose proof (e0_loop_drain_pairs d 0 [k1] (const S0)) as H1.
        pose proof (step_modeE0_loop_b011_10 (encL k1 []) (prepend11_01 d (const S0))) as H2.
        change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> prepend11_01 d (const S0)))))
          with (prepend01 4 (prepend11_01 d (const S0))) in H2.
        pose proof (modeE1_to_modeC [] k1 (prepend01 4 (prepend11_01 d (const S0))) I) as H3; simpl in H3.
        pose proof (modeC_prepend01_star 4 (k1 + 3) [] (prepend11_01 d (const S0))) as H4.
        pose proof (modeC_consume_11_01_nil d (k1 + 3 + 4) (const S0)) as H5.
        replace (k1 + 3 + 4 + 4 * d) with (k1 + 4 * d + 7) in H5 by lia.
        exact (stepPlus_stepPlus_stepPlus Hto_e0
          (stepStar_stepPlus_stepPlus H1
            (stepPlus_stepPlus_stepPlus H2
              (stepPlus_stepStar_stepPlus H3 (stepStar_trans H4 H5))))).
      * assert (Hne_rest : k2 :: rest' <> []) by discriminate.
        exists (k1 + d + 4), (add_last (k2 :: rest') (3 * d + 3)).
        split.
        -- rewrite Hx_split in Hto_e0.
           pose proof (e0_loop_drain_pairs d 0 (k1 :: k2 :: rest') (const S0)) as H1.
           pose proof (step_modeE0_loop_b011_10 (encL k1 (k2 :: rest')) (prepend11_01 d (const S0))) as H2.
           change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> prepend11_01 d (const S0)))))
             with (prepend01 4 (prepend11_01 d (const S0))) in H2.
           pose proof (modeE1_to_modeC (k2 :: rest') k1 (prepend01 4 (prepend11_01 d (const S0))) Hval_rest) as H3.
           rewrite (bump_enc_nonempty k1 (k2 :: rest') Hne_rest) in H3; simpl in H3.
           pose proof (modeC_prepend01_star 4 k1 (add_last (k2 :: rest') 3) (prepend11_01 d (const S0))) as H4.
           pose proof (modeC_consume_11_01_nonempty d (k1 + 4) (add_last (k2 :: rest') 3) (const S0)
             (add_last_ne_nil (k2 :: rest') 3 Hne_rest)
             (ValidKS_add_last (k2 :: rest') 3 Hval_rest)) as H5.
           rewrite add_last_add in H5.
           replace (k1 + 4 + d) with (k1 + d + 4) in H5 by lia.
           replace (3 + 3 * d) with (3 * d + 3) in H5 by lia.
           exact (stepPlus_stepPlus_stepPlus Hto_e0
             (stepStar_stepPlus_stepPlus H1
               (stepPlus_stepPlus_stepPlus H2
                 (stepPlus_stepStar_stepPlus H3 (stepStar_trans H4 H5))))).
        -- right; split; [exact (add_last_ne_nil (k2 :: rest') (3 * d + 3) Hne_rest) |].
           destruct (Nat.eqb_spec (k1 + d + 4) 1); [lia |].
           apply GoodKS_add_last.
           eapply GoodKS_mono; [|exact Hgks_rest].
           unfold S_in; destruct (Nat.eqb_spec k0 1); lia.
    + assert (Hx_split : x0 = 1 + 2 * d) by lia.
      assert (Hk0_ne1 : k0 <> 1) by lia.
      assert (HS_in_eq : S_in = 72 * (d + 2)).
      { unfold S_in; destruct (Nat.eqb_spec k0 1); lia. }
      set (S_sub := 36 * (d + 2)).
      assert (HS_sub : S_sub >= 36) by (unfold S_sub; lia).
      assert (Hk1_ge3 : k1 >= 3) by lia.
      set (sub := bump_enc (k1 - 1) ks_rest).
      assert (Hsub_nil : snd sub = [] -> 2 * S_sub <= 35 * fst sub).
      { unfold sub, bump_enc; destruct ks_rest as [|y ys]; cbn [fst snd]; [intros _; unfold S_sub; lia |].
        intros Hemp; exfalso; exact (add_last_ne_nil (y :: ys) 3 ltac:(discriminate) Hemp). }
      assert (Hsub_cons : snd sub <> [] -> fst sub >= 2 /\ 2 * S_sub <= 35 * (fst sub + 3)).
      { unfold sub, bump_enc; destruct ks_rest as [|y ys]; cbn [fst snd]; [congruence | intros _; unfold S_sub; lia]. }
      assert (Hsub_gks : GoodKS (2 * S_sub + 63 * (fst sub + 3)) (snd sub)).
      { unfold sub, bump_enc; destruct ks_rest as [|y ys]; cbn [fst snd]; [exact I |].
        replace (2 * S_sub + 63 * (k1 - 1 + 3)) with (S_in + 63 * (k1 + 2)) by (unfold S_sub; lia).
        exact (GoodKS_add_last (y :: ys) _ 3 Hgks_rest). }
      set (R_tail := S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> prepend11_01 d (const S0)).
      destruct (e0_loop_leave1_goodks (List.length (snd sub)) (fst sub) (snd sub) S_sub R_tail
        eq_refl HS_sub Hsub_nil Hsub_cons Hsub_gks)
        as [y0 [ys [Hstep_sub [Hval_ys [_ [Hgks_sub _]]]]]].
      set (py := bump_enc_twice y0 ys).
      set (ks_mid := (fst py + 1) :: snd py).
      assert (Hne_mid : ks_mid <> []) by discriminate.
      assert (Hval_mid : ValidKS ks_mid) by (apply (GoodKS_succ_valid S_sub (fst py) (snd py)); exact Hgks_sub).
      exists d, (add_last ks_mid (3 * d)).
      split.
      * rewrite Hx_split in Hto_e0.
        pose proof (e0_loop_drain_pairs d 1 (k1 :: ks_rest) (const S0)) as H1.
        assert (Hk1_eq : k1 = (k1 - 1) + 1) by lia.
        pose proof (step_modeE0_loop_b10_b011_10_b10_encL (k1 - 1) ks_rest (prepend11_01 d (const S0))) as H2.
        rewrite <- Hk1_eq in H2.
        fold R_tail in H2.
        pose proof (modeE1_to_modeC ks_rest (k1 - 1)
          (S0 >> S1 >> S0 >> S0 >> S0 >> R_tail) Hval_rest) as H3.
        fold sub in H3.
        pose proof (step_modeC_b01_b000 (encL (fst sub) (snd sub)) R_tail) as H4.
        pose proof (unwrap_11_01_1011101_step y0 ys (prepend11_01 d (const S0)) Hval_ys) as H5.
        fold py in H5; fold ks_mid in H5.
        pose proof (modeC_consume_11_01_nonempty d 0 ks_mid (const S0) Hne_mid Hval_mid) as H6.
        replace (0 + d) with d in H6 by lia.
        exact (stepPlus_stepPlus_stepPlus Hto_e0
          (stepStar_stepPlus_stepPlus H1
            (stepPlus_stepPlus_stepPlus H2
              (stepPlus_stepPlus_stepPlus H3
                (stepPlus_stepPlus_stepPlus H4
                  (stepPlus_stepPlus_stepPlus Hstep_sub
                    (stepPlus_stepStar_stepPlus H5 H6))))))).
      * right; split; [exact (add_last_ne_nil ks_mid (3 * d) Hne_mid) |].
        apply GoodKS_add_last.
        eapply GoodKS_mono; [|exact Hgks_sub].
        unfold S_sub; destruct (Nat.eqb_spec d 1); lia.
Qed.

Lemma e0_loop_drain_plus2 (w0 : nat) (ws : list nat) (S_w : nat) :
  (ws = [] -> w0 >= 4) ->
  36 <= S_w + 54 * (w0 / 2) ->
  GoodKS (S_w + 63 * (w0 + 3)) ws ->
  exists k0' ks',
    (cfg_modeE0_loop (encL w0 ws) (S0 >> S1 >> S0 >> S1 >> const S0)
      -[ holdout_0311_tm ]->+ cfg_modeC (encL k0' ks') (const S0)) /\
    InvNil k0' ks'.
Proof.
  intros Hempty Hsw Hgks.
  set (R0 := S0 >> S1 >> S0 >> S1 >> const S0).
  assert (HR0 : R0 = prepend01 2 (const S0)) by reflexivity.
  set (d := w0 / 2).
  set (rem := w0 mod 2).
  assert (Hdiv : rem + 2 * d = w0) by (unfold d, rem; lia).
  assert (Hrem : rem = 0 \/ rem = 1) by (unfold rem; lia).
  destruct ws as [|w1 ws_rest].
  - pose proof (Hempty eq_refl) as Hw4.
    destruct Hrem as [Heven | Hodd].
    + assert (Hd : d >= 2) by lia.
      assert (Hw_split : w0 = 0 + 2 * d) by lia.
      exists (d + 3), [3 * d].
      split.
      * rewrite Hw_split.
        pose proof (e0_loop_drain_pairs d 0 [] R0) as H1.
        pose proof (step_modeE0_loop_base (prepend11_01 d R0)) as H2.
        change (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0)) with (encL 0 [0]) in H2.
        pose proof (step_modeC_b01_encL 0 [0] (prepend11_01 d R0)) as H3; simpl in H3.
        pose proof (modeC_consume_11_01_nonempty d 1 [0] R0 ltac:(discriminate) I) as H4.
        cbn [add_last] in H4.
        replace (0 + 3 * d) with (3 * d) in H4 by lia.
        rewrite HR0 in H4.
        pose proof (modeC_prepend01_star 2 (1 + d) [3 * d] (const S0)) as H5.
        replace (1 + d + 2) with (d + 3) in H5 by lia.
        exact (stepStar_stepPlus_stepPlus H1
          (stepPlus_stepPlus_stepPlus H2
            (stepPlus_stepStar_stepPlus H3 (stepStar_trans H4 H5)))).
      * right; split; [discriminate |].
        destruct (Nat.eqb_spec (d + 3) 1); [lia |].
        cbn [GoodKS]; split; [lia | exact I].
    + assert (Hd : d >= 1) by lia.
      assert (Hw_split : w0 = 1 + 2 * d) by lia.
      exists (4 * d + 9), (@nil nat).
      split; [|left; split; [reflexivity | lia]].
      rewrite Hw_split.
      pose proof (e0_loop_drain_pairs d 1 [] R0) as H1.
      pose proof (step_modeE0_loop_b10_base (prepend11_01 d R0)) as H2.
      change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S1 >> S1 >> (S0 >> S1 >> prepend11_01 d R0)))))
        with (prepend01 3 (prepend11_01 (S d) R0)) in H2.
      pose proof (modeC_prepend01_star 3 0 [] (prepend11_01 (S d) R0)) as H3; simpl in H3.
      pose proof (modeC_consume_11_01_nil (S d) 3 R0) as H4.
      rewrite HR0 in H4.
      pose proof (modeC_prepend01_star 2 (3 + 4 * S d) [] (const S0)) as H5.
      replace (3 + 4 * S d + 2) with (4 * d + 9) in H5 by lia.
      exact (stepStar_stepPlus_stepPlus H1
        (stepPlus_stepStar_stepPlus H2 (stepStar_trans H3 (stepStar_trans H4 H5)))).
  - cbn [GoodKS] in Hgks; destruct Hgks as [Hw1_bound Hgks_rest].
    assert (Hw1_ge : w1 >= 4) by (unfold d in Hsw; lia).
    pose proof (GoodKS_valid ws_rest (S_w + 63 * (w0 + 3) + 63 * (w1 + 2)) ltac:(lia) Hgks_rest) as Hval_rest.
    destruct Hrem as [Heven | Hodd].
    + assert (Hw_split : w0 = 0 + 2 * d) by lia.
      destruct ws_rest as [|w2 rest'].
      * exists (w1 + 4 * d + 9), (@nil nat).
        split; [|left; split; [reflexivity | lia]].
        rewrite Hw_split.
        pose proof (e0_loop_drain_pairs d 0 [w1] R0) as H1.
        pose proof (step_modeE0_loop_b011_10 (encL w1 []) (prepend11_01 d R0)) as H2.
        change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> prepend11_01 d R0))))
          with (prepend01 4 (prepend11_01 d R0)) in H2.
        pose proof (modeE1_to_modeC [] w1 (prepend01 4 (prepend11_01 d R0)) I) as H3; simpl in H3.
        pose proof (modeC_prepend01_star 4 (w1 + 3) [] (prepend11_01 d R0)) as H4.
        pose proof (modeC_consume_11_01_nil d (w1 + 3 + 4) R0) as H5.
        rewrite HR0 in H5.
        pose proof (modeC_prepend01_star 2 (w1 + 3 + 4 + 4 * d) [] (const S0)) as H6.
        replace (w1 + 3 + 4 + 4 * d + 2) with (w1 + 4 * d + 9) in H6 by lia.
        exact (stepStar_stepPlus_stepPlus H1
          (stepPlus_stepPlus_stepPlus H2
            (stepPlus_stepStar_stepPlus H3 (stepStar_trans H4 (stepStar_trans H5 H6))))).
      * assert (Hne_rest : w2 :: rest' <> []) by discriminate.
        exists (w1 + d + 6), (add_last (w2 :: rest') (3 * d + 3)).
        split.
        -- rewrite Hw_split.
           pose proof (e0_loop_drain_pairs d 0 (w1 :: w2 :: rest') R0) as H1.
           pose proof (step_modeE0_loop_b011_10 (encL w1 (w2 :: rest')) (prepend11_01 d R0)) as H2.
           change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> prepend11_01 d R0))))
             with (prepend01 4 (prepend11_01 d R0)) in H2.
           pose proof (modeE1_to_modeC (w2 :: rest') w1 (prepend01 4 (prepend11_01 d R0)) Hval_rest) as H3.
           rewrite (bump_enc_nonempty w1 (w2 :: rest') Hne_rest) in H3; simpl in H3.
           pose proof (modeC_prepend01_star 4 w1 (add_last (w2 :: rest') 3) (prepend11_01 d R0)) as H4.
           pose proof (modeC_consume_11_01_nonempty d (w1 + 4) (add_last (w2 :: rest') 3) R0
             (add_last_ne_nil (w2 :: rest') 3 Hne_rest)
             (ValidKS_add_last (w2 :: rest') 3 Hval_rest)) as H5.
           rewrite add_last_add in H5.
           replace (3 + 3 * d) with (3 * d + 3) in H5 by lia.
           rewrite HR0 in H5.
           pose proof (modeC_prepend01_star 2 (w1 + 4 + d) (add_last (w2 :: rest') (3 * d + 3)) (const S0)) as H6.
           replace (w1 + 4 + d + 2) with (w1 + d + 6) in H6 by lia.
           exact (stepStar_stepPlus_stepPlus H1
             (stepPlus_stepPlus_stepPlus H2
               (stepPlus_stepStar_stepPlus H3 (stepStar_trans H4 (stepStar_trans H5 H6))))).
        -- right; split; [exact (add_last_ne_nil (w2 :: rest') (3 * d + 3) Hne_rest) |].
           destruct (Nat.eqb_spec (w1 + d + 6) 1); [lia |].
           apply GoodKS_add_last.
           eapply GoodKS_mono; [|exact Hgks_rest].
           unfold d in Hsw; lia.
    + assert (Hw_split : w0 = 1 + 2 * d) by lia.
      set (S_sub := 36 * (d + 4)).
      assert (HS_sub : S_sub >= 36) by (unfold S_sub; lia).
      assert (H2S_le : 2 * S_sub <= S_w + 63 * (w0 + 3)) by (unfold S_sub; unfold d in Hsw; lia).
      set (sub := bump_enc (w1 - 1) ws_rest).
      assert (Hsub_nil : snd sub = [] -> 2 * S_sub <= 35 * fst sub).
      { unfold sub, bump_enc; destruct ws_rest as [|y ys]; cbn [fst snd]; [intros _; unfold S_sub; lia |].
        intros Hemp; exfalso; exact (add_last_ne_nil (y :: ys) 3 ltac:(discriminate) Hemp). }
      assert (Hsub_cons : snd sub <> [] -> fst sub >= 2 /\ 2 * S_sub <= 35 * (fst sub + 3)).
      { unfold sub, bump_enc; destruct ws_rest as [|y ys]; cbn [fst snd]; [congruence | intros _; unfold S_sub; lia]. }
      assert (Hsub_gks : GoodKS (2 * S_sub + 63 * (fst sub + 3)) (snd sub)).
      { unfold sub, bump_enc; destruct ws_rest as [|y ys]; cbn [fst snd]; [exact I |].
        apply GoodKS_add_last.
        eapply GoodKS_mono; [|exact Hgks_rest]; lia. }
      set (R_tail := S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> prepend11_01 d R0).
      destruct (e0_loop_leave1_goodks (List.length (snd sub)) (fst sub) (snd sub) S_sub R_tail
        eq_refl HS_sub Hsub_nil Hsub_cons Hsub_gks)
        as [y0 [ys [Hstep_sub [Hval_ys [_ [Hgks_sub _]]]]]].
      set (py := bump_enc_twice y0 ys).
      set (ks_mid := (fst py + 1) :: snd py).
      assert (Hne_mid : ks_mid <> []) by discriminate.
      assert (Hval_mid : ValidKS ks_mid) by (apply (GoodKS_succ_valid S_sub (fst py) (snd py)); exact Hgks_sub).
      exists (d + 2), (add_last ks_mid (3 * d)).
      split.
      * rewrite Hw_split.
        pose proof (e0_loop_drain_pairs d 1 (w1 :: ws_rest) R0) as H1.
        assert (Hw1_eq : w1 = (w1 - 1) + 1) by lia.
        pose proof (step_modeE0_loop_b10_b011_10_b10_encL (w1 - 1) ws_rest (prepend11_01 d R0)) as H2.
        rewrite <- Hw1_eq in H2.
        fold R_tail in H2.
        pose proof (modeE1_to_modeC ws_rest (w1 - 1)
          (S0 >> S1 >> S0 >> S0 >> S0 >> R_tail) Hval_rest) as H3.
        fold sub in H3.
        pose proof (step_modeC_b01_b000 (encL (fst sub) (snd sub)) R_tail) as H4.
        pose proof (unwrap_11_01_1011101_step y0 ys (prepend11_01 d R0) Hval_ys) as H5.
        fold py in H5; fold ks_mid in H5.
        pose proof (modeC_consume_11_01_nonempty d 0 ks_mid R0 Hne_mid Hval_mid) as H6.
        replace (0 + d) with d in H6 by lia.
        rewrite HR0 in H6.
        pose proof (modeC_prepend01_star 2 d (add_last ks_mid (3 * d)) (const S0)) as H7.
        exact (stepStar_stepPlus_stepPlus H1
          (stepPlus_stepPlus_stepPlus H2
            (stepPlus_stepPlus_stepPlus H3
              (stepPlus_stepPlus_stepPlus H4
                (stepPlus_stepPlus_stepPlus Hstep_sub
                  (stepPlus_stepStar_stepPlus H5 (stepStar_trans H6 H7))))))).
      * right; split; [exact (add_last_ne_nil ks_mid (3 * d) Hne_mid) |].
        destruct (Nat.eqb_spec (d + 2) 1); [lia |].
        replace (36 * (d + 2 + 2)) with S_sub by (unfold S_sub; lia).
        exact (GoodKS_add_last ks_mid S_sub (3 * d) Hgks_sub).
Qed.

Lemma step_b01_b101_nil_to_e0_loop (p0 : nat) (ps : list nat) :
  ValidKS ps ->
  let w := bump_enc p0 ps in
  cfg_modeC (encL p0 ps) (S0 >> S1 >> S1 >> S0 >> S1 >> const S0)
    -[ holdout_0311_tm ]->+
    cfg_modeE0_loop (encL (fst w) (snd w)) (S0 >> S1 >> S0 >> S1 >> const S0).
Proof.
  intros Hval; cbv zeta.
  set (w := bump_enc p0 ps).
  pose proof (step_modeC_b01_b101_nil (encL p0 ps)) as H1.
  pose proof (modeE1_to_modeC ps p0
    (S0 >> S1 >> S0 >> S0 >> S0 >> (S0 >> S1 >> (S0 >> S1 >> const S0))) Hval) as H2.
  fold w in H2.
  pose proof (step_modeC_b01_b000 (encL (fst w) (snd w)) (S0 >> S1 >> S0 >> S1 >> const S0)) as H3.
  exact (stepPlus_stepPlus_stepPlus H1 (stepPlus_stepPlus_stepPlus H2 H3)).
Qed.

Lemma step_k0_zero (ks : list nat) :
  InvNil 0 ks ->
  exists k0' ks',
    (cfg_modeC (encL 0 ks) (const S0) -[ holdout_0311_tm ]->+ cfg_modeC (encL k0' ks') (const S0)) /\
    InvNil k0' ks'.
Proof.
  intros [[_ Hk5] | [Hne Hgks]]; [lia |].
  cbn [Nat.eqb] in Hgks.
  destruct ks as [|k1 ks_rest]; [congruence |].
  cbn [GoodKS] in Hgks; destruct Hgks as [Hk1_bound Hgks_rest].
  assert (Hk1_ge : k1 >= 1) by lia.
  replace (36 * (0 + 2)) with 72 in Hgks_rest by lia.
  pose proof (GoodKS_valid ks_rest (72 + 63 * (k1 + 2)) ltac:(lia) Hgks_rest) as Hval_rest.
  set (sub := bump_enc (k1 - 1) ks_rest).
  assert (Hto_sub : cfg_modeC (encL 0 (k1 :: ks_rest)) (const S0) -[ holdout_0311_tm ]->+
    cfg_modeE0_loop (encL (fst sub) (snd sub)) (S1 >> S0 >> S1 >> const S0)).
  { assert (Hk1_eq : k1 = (k1 - 1) + 1) by lia.
    pose proof (step_modeC_nil (encL 0 (k1 :: ks_rest))) as H1.
    pose proof (step_modeE0_first_b011_10_b10_encL (k1 - 1) ks_rest) as H2.
    rewrite <- Hk1_eq in H2.
    pose proof (modeE1_to_modeC ks_rest (k1 - 1)
      (S0 >> S1 >> S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> const S0)) Hval_rest) as H3.
    fold sub in H3.
    pose proof (step_modeC_b01_b000 (encL (fst sub) (snd sub)) (S1 >> S0 >> S1 >> const S0)) as H4.
    exact (stepPlus_stepPlus_stepPlus H1 (stepPlus_stepPlus_stepPlus H2 (stepPlus_stepPlus_stepPlus H3 H4))). }
  assert (H0a_dec : (ks_rest = [] \/ k1 >= 3) \/ (ks_rest <> [] /\ k1 < 3)).
  { destruct ks_rest as [|y ys]; [left; left; reflexivity |].
    destruct (Nat.leb_spec 3 k1); [left; right; lia | right; split; [discriminate | lia]]. }
  destruct H0a_dec as [H0a | [Hne_rest Hk1_lt3]].
  -  
    assert (Hsub_nil : snd sub = [] -> 2 * 36 <= 35 * fst sub).
    { unfold sub, bump_enc; destruct ks_rest as [|y ys]; cbn [fst snd]; [intros _; lia |].
      intros Hemp; exfalso; exact (add_last_ne_nil (y :: ys) 3 ltac:(discriminate) Hemp). }
    assert (Hsub_cons : snd sub <> [] -> fst sub >= 2 /\ 2 * 36 <= 35 * (fst sub + 3)).
    { unfold sub, bump_enc; destruct ks_rest as [|y ys]; cbn [fst snd]; [congruence |].
      destruct H0a as [Hemp | Hk3]; [congruence | intros _; lia]. }
    assert (Hsub_gks : GoodKS (2 * 36 + 63 * (fst sub + 3)) (snd sub)).
    { unfold sub, bump_enc; destruct ks_rest as [|y ys]; cbn [fst snd]; [exact I |].
      replace (2 * 36 + 63 * (k1 - 1 + 3)) with (72 + 63 * (k1 + 2)) by lia.
      exact (GoodKS_add_last (y :: ys) _ 3 Hgks_rest). }
    destruct (e0_loop_leave1_goodks (List.length (snd sub)) (fst sub) (snd sub) 36
      (S1 >> S0 >> S1 >> const S0) eq_refl ltac:(lia) Hsub_nil Hsub_cons Hsub_gks)
      as [m0 [ms [Hstep_l1 [Hval_ms [Hms_emp [Hgks_w _]]]]]].
    set (p1 := bump_enc m0 ms).
    set (w := bump_enc_twice m0 ms).
    assert (Hw_eq : w = bump_enc (fst p1) (snd p1)) by reflexivity.
    assert (Hc11 : cfg_modeC (encL m0 ms)
      (S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> S1 >> const S0)
      -[ holdout_0311_tm ]->+
      cfg_modeC (encL (fst p1) (snd p1)) (S0 >> S1 >> S1 >> S0 >> S1 >> const S0)).
    { exact (stepPlus_stepPlus_stepPlus
        (step_modeC_b11 (encL m0 ms) (S0 >> S1 >> S1 >> S0 >> S1 >> const S0))
        (modeE1_to_modeC ms m0 (S0 >> S1 >> S1 >> S0 >> S1 >> const S0) Hval_ms)). }
    pose proof (step_b01_b101_nil_to_e0_loop (fst p1) (snd p1) (ValidKS_bump_enc m0 ms Hval_ms)) as Hto_w.
    cbv zeta in Hto_w; rewrite <- Hw_eq in Hto_w.
    assert (Hw_empty : snd w = [] -> fst w >= 4).
    { destruct ms as [|u us].
      - intros _; unfold w, bump_enc_twice, bump_enc; cbn [fst snd]; lia.
      - intros Hemp; unfold w in Hemp;
        rewrite (bump_enc_twice_nonempty m0 (u :: us) ltac:(discriminate)) in Hemp; cbn [snd] in Hemp;
        exfalso; exact (add_last_ne_nil (u :: us) 6 ltac:(discriminate) Hemp). }
    assert (Hgks_ws : GoodKS (36 + 63 * (fst w + 3)) (snd w)).
    { cbv zeta in Hgks_w; fold w in Hgks_w; cbn [GoodKS] in Hgks_w.
      destruct Hgks_w as [_ H2].
      replace (36 + 63 * (fst w + 3)) with (36 + 63 * (fst w + 1 + 2)) by lia.
      exact H2. }
    destruct (e0_loop_drain_plus2 (fst w) (snd w) 36 Hw_empty ltac:(lia) Hgks_ws)
      as [k0' [ks' [Hdrain Hinv']]].
    exists k0', ks'; split; [|exact Hinv'].
    exact (stepPlus_stepPlus_stepPlus Hto_sub
      (stepPlus_stepPlus_stepPlus Hstep_l1
        (stepPlus_stepPlus_stepPlus Hc11
          (stepPlus_stepPlus_stepPlus Hto_w Hdrain)))).
  - destruct ks_rest as [|k2 ks_tail]; [congruence |].
    assert (Hk1_cases : k1 = 1 \/ k1 = 2) by lia.
    destruct Hk1_cases as [-> | ->].
    +  
      assert (Hsub_eq : sub = (0, add_last (k2 :: ks_tail) 3)) by reflexivity.
      replace (72 + 63 * (1 + 2)) with 261 in Hgks_rest by lia.
      pose proof (GoodKS_add_last (k2 :: ks_tail) 261 3 Hgks_rest) as Hgks_sub.
      destruct (add_last (k2 :: ks_tail) 3) as [|x1 xs_rest] eqn:Hal;
        [exfalso; exact (add_last_ne_nil (k2 :: ks_tail) 3 ltac:(discriminate) Hal) |].
      cbn [GoodKS] in Hgks_sub; destruct Hgks_sub as [Hx1_bound Hgks_xs].
      assert (Hx1_ge6 : x1 >= 6) by lia.
      pose proof (GoodKS_valid xs_rest (261 + 63 * (x1 + 2)) ltac:(lia) Hgks_xs) as Hval_xs.
      set (xb := bump_enc x1 xs_rest).
      set (p1 := (fst xb + 3, snd xb)).
      set (w := bump_enc (fst p1) (snd p1)).
      assert (Hstep_0b : cfg_modeE0_loop (encL 0 (x1 :: xs_rest)) (S1 >> S0 >> S1 >> const S0)
        -[ holdout_0311_tm ]->+
        cfg_modeC (encL (fst p1) (snd p1)) (S0 >> S1 >> S1 >> S0 >> S1 >> const S0)).
      { pose proof (step_modeE0_loop_b011_10 (encL x1 xs_rest) (S1 >> S0 >> S1 >> const S0)) as H1.
        change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S1 >> S0 >> S1 >> const S0)))))
          with (prepend01 3 (S0 >> S1 >> S1 >> S0 >> S1 >> const S0)) in H1.
        pose proof (modeE1_to_modeC xs_rest x1
          (prepend01 3 (S0 >> S1 >> S1 >> S0 >> S1 >> const S0)) Hval_xs) as H2.
        fold xb in H2.
        pose proof (modeC_prepend01_star 3 (fst xb) (snd xb) (S0 >> S1 >> S1 >> S0 >> S1 >> const S0)) as H3.
        exact (stepPlus_stepPlus_stepPlus H1 (stepPlus_stepStar_stepPlus H2 H3)). }
      assert (Hval_p1 : ValidKS (snd p1)) by (unfold p1; exact (ValidKS_bump_enc x1 xs_rest Hval_xs)).
      pose proof (step_b01_b101_nil_to_e0_loop (fst p1) (snd p1) Hval_p1) as Hto_w.
      cbv zeta in Hto_w; fold w in Hto_w.
      assert (Hw1_ge9 : fst w >= 9).
      { destruct xs_rest as [|y ys].
        - unfold w, p1, xb, bump_enc; cbn [fst snd]; lia.
        - assert (Hw_cons : w = (x1 + 3, add_last (y :: ys) 6)).
          { unfold w, p1, xb; cbn [fst snd bump_enc].
            rewrite (bump_enc_nonempty (x1 + 3) (add_last (y :: ys) 3)
              (add_last_ne_nil (y :: ys) 3 ltac:(discriminate))).
            rewrite add_last_add; reflexivity. }
          rewrite Hw_cons; cbn [fst]; lia. }
      assert (Hw_empty : snd w = [] -> fst w >= 4) by (intros _; lia).
      assert (Hsw9 : 36 <= 9 + 54 * (fst w / 2)) by lia.
      assert (Hgks_ws : GoodKS (9 + 63 * (fst w + 3)) (snd w)).
      { destruct xs_rest as [|y ys].
        - unfold w, p1, xb, bump_enc; cbn [fst snd GoodKS]; exact I.
        - assert (Hw_cons : w = (x1 + 3, add_last (y :: ys) 6)).
          { unfold w, p1, xb; cbn [fst snd bump_enc].
            rewrite (bump_enc_nonempty (x1 + 3) (add_last (y :: ys) 3)
              (add_last_ne_nil (y :: ys) 3 ltac:(discriminate))).
            rewrite add_last_add; reflexivity. }
          rewrite Hw_cons; cbn [fst snd].
          replace (9 + 63 * (x1 + 3 + 3)) with (261 + 63 * (x1 + 2)) by lia.
          exact (GoodKS_add_last (y :: ys) _ 6 Hgks_xs). }
      destruct (e0_loop_drain_plus2 (fst w) (snd w) 9 Hw_empty Hsw9 Hgks_ws)
        as [k0' [ks' [Hdrain Hinv']]].
      rewrite Hsub_eq in Hto_sub; cbn [fst snd] in Hto_sub.
      exists k0', ks'; split; [|exact Hinv'].
      exact (stepPlus_stepPlus_stepPlus Hto_sub
        (stepPlus_stepPlus_stepPlus Hstep_0b
          (stepPlus_stepPlus_stepPlus Hto_w Hdrain))).
    +  
      assert (Hsub_eq : sub = (1, add_last (k2 :: ks_tail) 3)) by reflexivity.
      replace (72 + 63 * (2 + 2)) with 324 in Hgks_rest by lia.
      pose proof (GoodKS_add_last (k2 :: ks_tail) 324 3 Hgks_rest) as Hgks_sub.
      destruct (add_last (k2 :: ks_tail) 3) as [|x1 xs_rest] eqn:Hal;
        [exfalso; exact (add_last_ne_nil (k2 :: ks_tail) 3 ltac:(discriminate) Hal) |].
      cbn [GoodKS] in Hgks_sub; destruct Hgks_sub as [Hx1_bound Hgks_xs].
      assert (Hx1_ge8 : x1 >= 8) by lia.
      pose proof (GoodKS_valid xs_rest (324 + 63 * (x1 + 2)) ltac:(lia) Hgks_xs) as Hval_xs.
      set (sub2 := bump_enc (x1 - 1) xs_rest).
      set (R_101 := S1 >> S0 >> S1 >> const S0).
      set (R_1011101_101 := S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> R_101).
      assert (Hstep1 : cfg_modeE0_loop (encL 1 (x1 :: xs_rest)) R_101 -[ holdout_0311_tm ]->+
        cfg_modeE0_loop (encL (fst sub2) (snd sub2)) R_1011101_101).
      { assert (Hx1_eq : x1 = (x1 - 1) + 1) by lia.
        pose proof (step_modeE0_loop_b10_b011_10_b10_encL (x1 - 1) xs_rest R_101) as H1.
        rewrite <- Hx1_eq in H1.
        fold R_1011101_101 in H1.
        pose proof (modeE1_to_modeC xs_rest (x1 - 1)
          (S0 >> S1 >> S0 >> S0 >> S0 >> R_1011101_101) Hval_xs) as H2.
        fold sub2 in H2.
        pose proof (step_modeC_b01_b000 (encL (fst sub2) (snd sub2)) R_1011101_101) as H3.
        exact (stepPlus_stepPlus_stepPlus H1 (stepPlus_stepPlus_stepPlus H2 H3)). }
      assert (Hsub2_nil : snd sub2 = [] -> 2 * 162 <= 35 * fst sub2).
      { unfold sub2, bump_enc; destruct xs_rest as [|y ys]; cbn [fst snd]; [intros _; lia |].
        intros Hemp; exfalso; exact (add_last_ne_nil (y :: ys) 3 ltac:(discriminate) Hemp). }
      assert (Hsub2_cons : snd sub2 <> [] -> fst sub2 >= 2 /\ 2 * 162 <= 35 * (fst sub2 + 3)).
      { unfold sub2, bump_enc; destruct xs_rest as [|y ys]; cbn [fst snd]; [congruence | intros _; lia]. }
      assert (Hsub2_gks : GoodKS (2 * 162 + 63 * (fst sub2 + 3)) (snd sub2)).
      { unfold sub2, bump_enc; destruct xs_rest as [|y ys]; cbn [fst snd]; [exact I |].
        replace (2 * 162 + 63 * (x1 - 1 + 3)) with (324 + 63 * (x1 + 2)) by lia.
        exact (GoodKS_add_last (y :: ys) _ 3 Hgks_xs). }
      destruct (e0_loop_leave1_goodks (List.length (snd sub2)) (fst sub2) (snd sub2) 162 R_1011101_101
        eq_refl ltac:(lia) Hsub2_nil Hsub2_cons Hsub2_gks)
        as [y0 [ys [Hstep_l2 [Hval_ys [Hys_emp [Hgks_z _]]]]]].
      pose proof (unwrap_11_01_1011101_step y0 ys R_101 Hval_ys) as Hunwrap2.
      cbv zeta in Hunwrap2, Hgks_z.
      set (pz := bump_enc_twice y0 ys) in *.
      set (z1 := fst pz + 1) in *.
      set (zs := snd pz) in *.
      cbn [GoodKS] in Hgks_z; destruct Hgks_z as [Hz1_bound Hgks_zs].
      assert (Hz1_ge3 : z1 >= 3) by lia.
      assert (Hzs_emp_z1 : zs = [] -> z1 >= 14).
      { destruct ys as [|u us].
        - pose proof (Hys_emp eq_refl) as Hy7.
          intros _; unfold z1, pz, bump_enc_twice, bump_enc; cbn [fst snd]; lia.
        - intros Hemp; unfold zs, pz in Hemp.
          rewrite (bump_enc_twice_nonempty y0 (u :: us) ltac:(discriminate)) in Hemp; cbn [snd] in Hemp.
          exfalso; exact (add_last_ne_nil (u :: us) 6 ltac:(discriminate) Hemp). }
      pose proof (GoodKS_valid zs (162 + 63 * (z1 + 2)) ltac:(lia) Hgks_zs) as Hval_zs.
      set (zb := bump_enc (z1 - 1) zs).
      set (w := bump_enc (fst zb) (snd zb)).
      set (R_0000101 := S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> const S0).
      set (R_101_01_01 := S1 >> S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> const S0))).
      assert (Hstep34 : cfg_modeC (encL 0 (z1 :: zs)) R_101 -[ holdout_0311_tm ]->+
        cfg_modeE0_loop (encL (fst w) (snd w)) R_101_01_01).
      { assert (Hz1_eq : z1 = (z1 - 1) + 1) by lia.
        pose proof (step_modeC_b01110_b10_b101_nil_encL (z1 - 1) zs) as HA.
        rewrite <- Hz1_eq in HA.
        fold R_101 in HA; fold R_0000101 in HA.
        pose proof (modeE1_to_modeC zs (z1 - 1)
          (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> R_0000101) Hval_zs) as HA2.
        fold zb in HA2.
        pose proof (step_modeC_b01_b10101_encL (fst zb) (snd zb) R_0000101) as HA3.
        pose proof (step_modeC_b01110_b10_b0000101_encL (fst zb) (snd zb) (const S0)) as HB.
        fold R_0000101 in HB; fold R_101_01_01 in HB.
        pose proof (modeE1_to_modeC (snd zb) (fst zb)
          (S0 >> S1 >> S0 >> S0 >> S0 >> R_101_01_01)
          (ValidKS_bump_enc (z1 - 1) zs Hval_zs)) as HB2.
        fold w in HB2.
        pose proof (step_modeC_b01_b000 (encL (fst w) (snd w)) R_101_01_01) as HB3.
        exact (stepPlus_stepPlus_stepPlus HA
          (stepPlus_stepPlus_stepPlus HA2
            (stepPlus_stepPlus_stepPlus HA3
              (stepPlus_stepPlus_stepPlus HB
                (stepPlus_stepPlus_stepPlus HB2 HB3))))). }
      assert (Hw_def : w = bump_enc_twice (z1 - 1) zs) by reflexivity.
      assert (Hw_nil : snd w = [] -> 2 * 81 <= 35 * fst w).
      { destruct zs as [|y ys'] eqn:Hzs.
        - pose proof (Hzs_emp_z1 eq_refl) as Hz14.
          assert (Hw_nil_eq : w = (z1 - 1 + 3 + 3, (@nil nat))) by (rewrite Hw_def; reflexivity).
          rewrite Hw_nil_eq; cbn [fst snd]; intros _; lia.
        - assert (Hw_cons_eq : w = (z1 - 1, add_last (y :: ys') 6))
            by (rewrite Hw_def; exact (bump_enc_twice_nonempty (z1 - 1) (y :: ys') ltac:(discriminate))).
          rewrite Hw_cons_eq; cbn [snd]; intros Hemp;
          exfalso; exact (add_last_ne_nil (y :: ys') 6 ltac:(discriminate) Hemp). }
      assert (Hw_ge10 : snd w = [] -> fst w >= 10).
      { destruct zs as [|y ys'] eqn:Hzs.
        - pose proof (Hzs_emp_z1 eq_refl) as Hz14.
          assert (Hw_nil_eq : w = (z1 - 1 + 3 + 3, (@nil nat))) by (rewrite Hw_def; reflexivity).
          rewrite Hw_nil_eq; cbn [fst snd]; intros _; lia.
        - assert (Hw_cons_eq : w = (z1 - 1, add_last (y :: ys') 6))
            by (rewrite Hw_def; exact (bump_enc_twice_nonempty (z1 - 1) (y :: ys') ltac:(discriminate))).
          rewrite Hw_cons_eq; cbn [snd]; intros Hemp;
          exfalso; exact (add_last_ne_nil (y :: ys') 6 ltac:(discriminate) Hemp). }
      assert (Hw_cons : snd w <> [] -> fst w >= 2 /\ 2 * 81 <= 35 * (fst w + 3)).
      { destruct zs as [|y ys'] eqn:Hzs.
        - assert (Hw_nil_eq : w = (z1 - 1 + 3 + 3, (@nil nat))) by (rewrite Hw_def; reflexivity).
          rewrite Hw_nil_eq; cbn [snd]; congruence.
        - assert (Hw_cons_eq : w = (z1 - 1, add_last (y :: ys') 6))
            by (rewrite Hw_def; exact (bump_enc_twice_nonempty (z1 - 1) (y :: ys') ltac:(discriminate))).
          rewrite Hw_cons_eq; cbn [fst snd]; intros _; lia. }
      assert (Hw_gks : GoodKS (2 * 81 + 63 * (fst w + 3)) (snd w)).
      { destruct zs as [|y ys'] eqn:Hzs.
        - assert (Hw_nil_eq : w = (z1 - 1 + 3 + 3, (@nil nat))) by (rewrite Hw_def; reflexivity).
          rewrite Hw_nil_eq; cbn [snd GoodKS]; exact I.
        - assert (Hw_cons_eq : w = (z1 - 1, add_last (y :: ys') 6))
            by (rewrite Hw_def; exact (bump_enc_twice_nonempty (z1 - 1) (y :: ys') ltac:(discriminate))).
          rewrite Hw_cons_eq; cbn [fst snd].
          replace (2 * 81 + 63 * (z1 - 1 + 3)) with (162 + 63 * (z1 + 2)) by lia.
          exact (GoodKS_add_last (y :: ys') _ 6 Hgks_zs). }
      destruct (e0_loop_leave1_goodks (List.length (snd w)) (fst w) (snd w) 81 R_101_01_01
        eq_refl ltac:(lia) Hw_nil Hw_cons Hw_gks)
        as [m0 [ms [Hstep_l5 [Hval_ms [_ [_ Hgks_81_fn]]]]]].
      pose proof (Hgks_81_fn Hw_ge10 eq_refl) as Hgks_b1.
      cbv zeta in Hgks_b1.
      set (b1 := bump_enc m0 ms) in *.
      assert (Hstep6 : cfg_modeC (encL m0 ms)
        (S1 >> S1 >> S0 >> S1 >> R_101_01_01) -[ holdout_0311_tm ]->+
        cfg_modeC (encL 1 ((fst b1 + 1) :: snd b1)) (const S0)).
      { pose proof (step_modeC_b11 (encL m0 ms) (S0 >> S1 >> R_101_01_01)) as H1.
        pose proof (modeE1_to_modeC ms m0 (S0 >> S1 >> R_101_01_01) Hval_ms) as H2.
        fold b1 in H2.
        pose proof (step_modeC_b01_b10101_encL (fst b1) (snd b1)
          (S0 >> S1 >> const S0)) as H3.
        pose proof (step_modeC_b01_encL 0 ((fst b1 + 1) :: snd b1) (const S0)) as H4; simpl in H4.
        exact (stepPlus_stepPlus_stepPlus H1
          (stepPlus_stepPlus_stepPlus H2
            (stepPlus_stepPlus_stepPlus H3 H4))). }
      rewrite Hsub_eq in Hto_sub; cbn [fst snd] in Hto_sub.
      fold R_101 in Hto_sub.
      exists 1, ((fst b1 + 1) :: snd b1).
      split.
      * exact (stepPlus_stepPlus_stepPlus Hto_sub
          (stepPlus_stepPlus_stepPlus Hstep1
            (stepPlus_stepPlus_stepPlus Hstep_l2
              (stepPlus_stepPlus_stepPlus Hunwrap2
                (stepPlus_stepPlus_stepPlus Hstep34
                  (stepPlus_stepPlus_stepPlus Hstep_l5 Hstep6)))))).
      * right; split; [discriminate | exact Hgks_b1].
Qed.

Definition Inv (c : Q * tape) : Prop :=
  exists k0 ks, c = cfg_modeC (encL k0 ks) (const S0) /\ InvNil k0 ks.

Lemma init_reaches_inv :
  exists c, (c0 -[ holdout_0311_tm ]->+ c) /\ Inv c.
Proof.
  pose proof init_reaches_modeC as H0.
  change (S0 >> S1 >> const S0) with (encL 0 []) in H0.
  assert (H1 : cfg_modeC (encL 0 []) (const S0) -[ holdout_0311_tm ]->+ cfg_modeC (encL 3 []) (const S0)).
  { pose proof (step_modeC_nil (encL 0 [])) as Ha.
    pose proof step_modeE0_first_base as Hb.
    change (S0 >> S1 >> const S0) with (encL 0 []) in Hb.
    change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> const S0))) with (prepend01 3 (const S0)) in Hb.
    pose proof (modeC_prepend01_star 3 0 [] (const S0)) as Hc; simpl in Hc.
    exact (stepPlus_stepPlus_stepPlus Ha (stepPlus_stepStar_stepPlus Hb Hc)). }
  assert (H2 : cfg_modeC (encL 3 []) (const S0) -[ holdout_0311_tm ]->+ cfg_modeC (encL 2 [3]) (const S0)).
  { pose proof (step_modeC_nil (encL 3 [])) as Ha.
    pose proof (step_modeE0_first_b10 (encL 2 [])) as Hb.
    pose proof (step_modeE0_loop_b10_b10 (encL 0 []) (const S0)) as Hc.
    change (S1 >> S1 >> (S0 >> S1 >> const S0)) with (prepend11_01 1 (const S0)) in Hc.
    pose proof (step_modeE0_loop_base (prepend11_01 1 (const S0))) as Hd.
    change (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0)) with (encL 0 [0]) in Hd.
    pose proof (step_modeC_b01_encL 0 [0] (prepend11_01 1 (const S0))) as He; simpl in He.
    pose proof (modeC_consume_11_01_nonempty 1 1 [0] (const S0) ltac:(discriminate) I) as Hf.
    cbn [add_last] in Hf; simpl in Hf.
    exact (stepPlus_stepPlus_stepPlus Ha
      (stepPlus_stepPlus_stepPlus Hb
        (stepPlus_stepPlus_stepPlus Hc
          (stepPlus_stepPlus_stepPlus Hd
            (stepPlus_stepStar_stepPlus He Hf))))). }
  assert (Hinv : InvNil 2 [3]).
  { right; split; [discriminate | cbn [Nat.eqb GoodKS]; split; [lia | exact I]]. }
  exists (cfg_modeC (encL 2 [3]) (const S0)).
  split.
  - exact (stepPlus_stepPlus_stepPlus H0 (stepPlus_stepPlus_stepPlus H1 H2)).
  - exists 2, [3]; exact (conj eq_refl Hinv).
Qed.

Lemma inv_step :
  forall c, Inv c -> exists c', Inv c' /\ (c -[ holdout_0311_tm ]->+ c').
Proof.
  intros c [k0 [ks [-> Hinv]]].
  destruct k0 as [|k0'].
  - destruct (step_k0_zero ks Hinv) as [k0' [ks' [Hstep Hinv']]].
    exists (cfg_modeC (encL k0' ks') (const S0)).
    split; [exists k0', ks'; exact (conj eq_refl Hinv') | exact Hstep].
  - destruct (step_k0_pos (S k0') ks ltac:(lia) Hinv) as [k0'' [ks'' [Hstep Hinv']]].
    exists (cfg_modeC (encL k0'' ks'') (const S0)).
    split; [exists k0'', ks''; exact (conj eq_refl Hinv') | exact Hstep].
Qed.

Theorem nonhalt: ~ halts tm c0.
Proof.
  destruct init_reaches_inv as [c [Hinit Hinv]].
  eapply multistep_nonhalt; [exact (stepPlus_stepStar Hinit) |].
  eapply progress_nonhalt; [exact inv_step | exact Hinv].
Qed.

End TM3.
Print Assumptions TM3.nonhalt.



Module TM4.
Import BusyCoq.Individual62.

Import Lia ZifyNat PeanoNat String List.

Import ListNotations.

Open Scope list_scope.

Open Scope nat_scope.

Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC1RF_---0LD_0LE1LB_1LF1LD_1RD0RA").

Notation holdout_0311_tm := TM3.tm.

Notation stepPlus_stepStar := TM3.stepPlus_stepStar.

Notation stepPlus_stepPlus_stepPlus := TM3.stepPlus_stepPlus_stepPlus.

Notation stepPlus_stepStar_stepPlus := TM3.stepPlus_stepStar_stepPlus.

Notation stepStar_stepPlus_stepPlus := TM3.stepStar_stepPlus_stepPlus.

Notation stepStar_trans := TM3.stepStar_trans.

Notation cfg_of := TM3.cfg_of.

Notation LocalState := TM3.LocalState.

Notation mkLocalState := TM3.mkLocalState.

Notation ls_l := TM3.ls_l.

Notation ls_r := TM3.ls_r.

Notation ls_q := TM3.ls_q.

Notation ls_d := TM3.ls_d.

Notation step_local := TM3.step_local.

Notation step_local_spec := TM3.step_local_spec.

Notation run_local := TM3.run_local.

Notation run_local_spec := TM3.run_local_spec.

Notation run_local_plus_eq := TM3.run_local_plus_eq.

Notation cfg_modeC := TM3.cfg_modeC.

Notation cfg_modeE1 := TM3.cfg_modeE1.

Notation cfg_modeE0_first := TM3.cfg_modeE0_first.

Notation cfg_modeE0_loop := TM3.cfg_modeE0_loop.

Notation cfg_b101_mid := TM3.cfg_b101_mid.

Notation cfg_e0f_mid := TM3.cfg_e0f_mid.

Notation cfg_e0l_mid := TM3.cfg_e0l_mid.

Notation cfg_transA_mid := TM3.cfg_transA_mid.

Notation cfg_transB_mid := TM3.cfg_transB_mid.

Ltac norm_cfg :=
  unfold cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop,
         cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, cfg_transA_mid, cfg_transB_mid,
         cfg_of, c0, tape0, q0, s0;
  cbn [ls_q ls_d ls_l ls_r Str_app hd tl];
  repeat rewrite <- const_unfold;
  reflexivity.

Ltac solve_local m n s1 L0 R0 :=
  eapply (run_local_plus_eq m n s1 _ _ _ L0 R0);
  [ cbv; reflexivity | norm_cfg | norm_cfg ].

Lemma init_reaches_modeC :
  c0 -[ holdout_0311_tm ]->+ cfg_modeC (S0 >> S1 >> const S0) (const S0).
Proof.
  solve_local holdout_0311_tm 9 (mkLocalState [S0; S0] [S0; S0] A R) (const S0) (const S0).
Qed.

Lemma step_modeC_nil (l : side) :
  cfg_modeC l (const S0) -[ holdout_0311_tm ]->+ cfg_modeE0_first l.
Proof.
  solve_local holdout_0311_tm 5 (mkLocalState [S1; S0] [S0; S0; S0] C R) l (const S0).
Qed.

Lemma step_modeC_b01 (l r : side) :
  cfg_modeC l (S0 >> S1 >> r) -[ holdout_0311_tm ]->+ cfg_modeC (S1 >> S0 >> l) r.
Proof.
  solve_local holdout_0311_tm 1 (mkLocalState [S1; S0] [S0; S1] C R) l r.
Qed.

Lemma step_modeC_b01_b10101 (l r : side) :
  cfg_modeC l (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> r) -[ holdout_0311_tm ]->+
    cfg_modeC (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l)) r.
Proof.
  solve_local holdout_0311_tm 6 (mkLocalState [S1; S0] [S0; S1; S1; S0; S1; S0; S1] C R) l r.
Qed.

Lemma step_modeC_b11 (l r : side) :
  cfg_modeC l (S1 >> S1 >> r) -[ holdout_0311_tm ]->+ cfg_modeE1 l r.
Proof.
  solve_local holdout_0311_tm 2 (mkLocalState [S1; S0] [S1; S1] C R) l r.
Qed.

Lemma step_modeC_b01_b000 (l r : side) :
  cfg_modeC l (S0 >> S1 >> S0 >> S0 >> S0 >> r) -[ holdout_0311_tm ]->+ cfg_modeE0_loop l r.
Proof.
  solve_local holdout_0311_tm 13 (mkLocalState [S1; S0] [S0; S1; S0; S0; S0] C R) l r.
Qed.

Lemma step_modeC_b01_b101_nil_1 (l : side) :
  cfg_modeC (S1 >> S0 >> l) (S1 >> S0 >> S1 >> const S0) -[ holdout_0311_tm ]->+ cfg_b101_mid l.
Proof.
  solve_local holdout_0311_tm 33
    (mkLocalState [S1; S0; S1; S0] [S1; S0; S1; S0; S0; S0; S0; S0; S0] C R) l (const S0).
Qed.

Lemma step_modeC_b01_b101_nil_2 (l : side) :
  cfg_b101_mid l -[ holdout_0311_tm ]->+
    cfg_modeE1 (S1 >> S0 >> l) (S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> const S0).
Proof.
  solve_local holdout_0311_tm 32
    (mkLocalState [S1; S1; S1; S1; S0; S1; S0] [S0; S1; S0; S1; S0; S1] E L) l (const S0).
Qed.

Lemma step_modeC_b01_b1011101 (l r : side) :
  cfg_modeC l (S0 >> S1 >> S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> r) -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> r).
Proof.
  solve_local holdout_0311_tm 16
    (mkLocalState [S1; S0] [S0; S1; S1; S0; S1; S1; S1; S0; S1] C R) l r.
Qed.

Lemma step_modeE1_base (r : side) :
  cfg_modeE1 (S0 >> S1 >> const S0) r -[ holdout_0311_tm ]->+
    cfg_modeC (S0 >> S1 >> const S0) (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> r))).
Proof.
  solve_local holdout_0311_tm 24
    (mkLocalState [S1; S0; S0; S1; S0; S0; S0; S0] [S0; S1] E L) (const S0) r.
Qed.

Lemma step_modeE1_b10 (l r : side) :
  cfg_modeE1 (S1 >> S0 >> l) r -[ holdout_0311_tm ]->+ cfg_modeE1 l (S0 >> S1 >> r).
Proof.
  solve_local holdout_0311_tm 5 (mkLocalState [S1; S0; S1; S0] [S0; S1] E L) l r.
Qed.

Lemma step_modeC_b01_b101_nil (l : side) :
  cfg_modeC l (S0 >> S1 >> S1 >> S0 >> S1 >> const S0) -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S0 >> S0 >> S0 >> (S0 >> S1 >> (S0 >> S1 >> const S0))).
Proof.
  exact (stepPlus_stepPlus_stepPlus (step_modeC_b01 l _)
    (stepPlus_stepPlus_stepPlus (step_modeC_b01_b101_nil_1 l)
      (stepPlus_stepPlus_stepPlus (step_modeC_b01_b101_nil_2 l) (step_modeE1_b10 l _)))).
Qed.

Lemma step_modeE1_b011_10_base (r : side) :
  cfg_modeE1 (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0)) r -[ holdout_0311_tm ]->+
    cfg_modeC (S0 >> S1 >> const S0)
      (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> r))).
Proof.
  solve_local holdout_0311_tm 33
    (mkLocalState [S1; S0; S0; S1; S1; S1; S0; S0; S1; S0; S0; S0; S0] [S0; S1] E L) (const S0) r.
Qed.

Lemma step_modeE1_b011_10_b10 (l r : side) :
  cfg_modeE1 (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l)) r -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> r).
Proof.
  solve_local holdout_0311_tm 14
    (mkLocalState [S1; S0; S0; S1; S1; S1; S0; S1; S0] [S0; S1] E L) l r.
Qed.

Lemma step_modeE0_first_base :
  cfg_modeE0_first (S0 >> S1 >> const S0) -[ holdout_0311_tm ]->+
    cfg_modeC (S0 >> S1 >> const S0)
      (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> const S0))).
Proof.
  solve_local holdout_0311_tm 24
    (mkLocalState [S0; S1; S0; S0; S1; S0; S0; S0] [S0; S1] E L) (const S0) (const S0).
Qed.

Lemma step_modeE0_first_b10 (l : side) :
  cfg_modeE0_first (S1 >> S0 >> l) -[ holdout_0311_tm ]->+ cfg_modeE0_loop l (const S0).
Proof.
  solve_local holdout_0311_tm 5 (mkLocalState [S0; S1; S0; S1; S0] [S0; S1] E L) l (const S0).
Qed.

Lemma step_modeE0_first_b011_10_base_1 :
  cfg_modeE0_first (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0)) -[ holdout_0311_tm ]->+
    cfg_modeE1 (S0 >> S1 >> const S0) (S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> const S0)).
Proof.
  solve_local holdout_0311_tm 35
    (mkLocalState [S0; S1; S0; S0; S1; S1; S1; S0; S0; S1] [S0; S1] E L) (const S0) (const S0).
Qed.

Lemma step_modeE0_first_b011_10_base :
  cfg_modeE0_first (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0)) -[ holdout_0311_tm ]->+
    cfg_modeC (S0 >> S1 >> const S0)
      (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> const S0)))).
Proof.
  exact (stepPlus_stepPlus_stepPlus step_modeE0_first_b011_10_base_1 (step_modeE1_base _)).
Qed.

Lemma step_modeE0_first_b011_10_b10_1 (l : side) :
  cfg_modeE0_first (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l)) -[ holdout_0311_tm ]->+ cfg_e0f_mid l.
Proof.
  solve_local holdout_0311_tm 20
    (mkLocalState [S0; S1; S0; S0; S1; S1; S1; S0; S1; S0] [S0; S1] E L) l (const S0).
Qed.

Lemma step_modeE0_first_b011_10_b10_2 (l : side) :
  cfg_e0f_mid l -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> const S0)).
Proof.
  solve_local holdout_0311_tm 20
    (mkLocalState [S1; S1; S1; S0; S1; S0] [S0; S0; S0; S1; S0; S1] B R) l (const S0).
Qed.

Lemma step_modeE0_first_b011_10_b10 (l : side) :
  cfg_modeE0_first (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l)) -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> const S0)).
Proof.
  exact (stepPlus_stepPlus_stepPlus (step_modeE0_first_b011_10_b10_1 l) (step_modeE0_first_b011_10_b10_2 l)).
Qed.

Lemma step_modeE0_loop_base (r : side) :
  cfg_modeE0_loop (S0 >> S1 >> const S0) r -[ holdout_0311_tm ]->+
    cfg_modeC (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0)) (S0 >> S1 >> r).
Proof.
  solve_local holdout_0311_tm 26
    (mkLocalState [S0; S0; S1; S0; S0] [S0; S1; S1; S1; S0; S1] E L) (const S0) r.
Qed.

Lemma step_modeE0_loop_b10_base (r : side) :
  cfg_modeE0_loop (S1 >> S0 >> (S0 >> S1 >> const S0)) r -[ holdout_0311_tm ]->+
    cfg_modeC (S0 >> S1 >> const S0)
      (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S1 >> S1 >> (S0 >> S1 >> r))))).
Proof.
  solve_local holdout_0311_tm 24
    (mkLocalState [S0; S1; S0; S0; S1; S0; S0; S0] [S0; S1; S1; S1; S0; S1] E L) (const S0) r.
Qed.

Lemma step_modeE0_loop_b10_b10 (l r : side) :
  cfg_modeE0_loop (S1 >> S0 >> (S1 >> S0 >> l)) r -[ holdout_0311_tm ]->+
    cfg_modeE0_loop l (S1 >> S1 >> (S0 >> S1 >> r)).
Proof.
  solve_local holdout_0311_tm 5
    (mkLocalState [S0; S1; S0; S1; S0] [S0; S1; S1; S1; S0; S1] E L) l r.
Qed.

Lemma step_modeE0_loop_b10_b011_10_base_1 (r : side) :
  cfg_modeE0_loop (S1 >> S0 >> (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0))) r -[ holdout_0311_tm ]->+
    cfg_modeE1 (S0 >> S1 >> const S0)
      (S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> r)).
Proof.
  solve_local holdout_0311_tm 35
    (mkLocalState [S0; S1; S0; S0; S1; S1; S1; S0; S0; S1] [S0; S1; S1; S1; S0; S1] E L) (const S0) r.
Qed.

Lemma step_modeE0_loop_b10_b011_10_base (r : side) :
  cfg_modeE0_loop (S1 >> S0 >> (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0))) r -[ holdout_0311_tm ]->+
    cfg_modeC (S0 >> S1 >> const S0)
      (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> r)))).
Proof.
  exact (stepPlus_stepPlus_stepPlus (step_modeE0_loop_b10_b011_10_base_1 r) (step_modeE1_base _)).
Qed.

Lemma step_modeE0_loop_b10_b011_10_b10_1 (l r : side) :
  cfg_modeE0_loop (S1 >> S0 >> (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l))) r -[ holdout_0311_tm ]->+
    cfg_e0l_mid l r.
Proof.
  solve_local holdout_0311_tm 20
    (mkLocalState [S0; S1; S0; S0; S1; S1; S1; S0; S1; S0] [S0; S1; S1; S1; S0; S1] E L) l r.
Qed.

Lemma step_modeE0_loop_b10_b011_10_b10_2 (l r : side) :
  cfg_e0l_mid l r -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> r)).
Proof.
  solve_local holdout_0311_tm 20
    (mkLocalState [S1; S1; S1; S0; S1; S0] [S0; S0; S0; S1; S0; S1; S1; S1; S0; S1] B R) l r.
Qed.

Lemma step_modeE0_loop_b10_b011_10_b10 (l r : side) :
  cfg_modeE0_loop (S1 >> S0 >> (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l))) r -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> r)).
Proof.
  exact (stepPlus_stepPlus_stepPlus (step_modeE0_loop_b10_b011_10_b10_1 l r) (step_modeE0_loop_b10_b011_10_b10_2 l r)).
Qed.

Lemma step_modeE0_loop_b011_10 (l r : side) :
  cfg_modeE0_loop (S0 >> S1 >> S1 >> S1 >> S0 >> l) r -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> r)))).
Proof.
  solve_local holdout_0311_tm 27
    (mkLocalState [S0; S0; S1; S1; S1; S0] [S0; S1; S1; S1; S0; S1] E L) l r.
Qed.

Lemma step_modeC_b01110_b10_b101_nil_1 (l : side) :
  cfg_modeC (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l))
    (S1 >> S0 >> S1 >> const S0) -[ holdout_0311_tm ]->+ cfg_transA_mid l.
Proof.
  solve_local holdout_0311_tm 40
    (mkLocalState [S1; S0; S0; S1; S1; S1; S0; S1; S0] [S1; S0; S1; S0; S0; S0; S0; S0; S0] C R) l (const S0).
Qed.

Lemma step_modeC_b01110_b10_b101_nil_2 (l : side) :
  cfg_transA_mid l -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >>
      (S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> const S0)).
Proof.
  solve_local holdout_0311_tm 40
    (mkLocalState [S1; S1; S1; S1; S0; S0; S1; S1; S1; S0; S1; S0] [S0; S0; S0; S1; S0; S1] B R) l (const S0).
Qed.

Lemma step_modeC_b01110_b10_b101_nil (l : side) :
  cfg_modeC (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l))
    (S1 >> S0 >> S1 >> const S0) -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >>
      (S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> const S0)).
Proof.
  exact (stepPlus_stepPlus_stepPlus (step_modeC_b01110_b10_b101_nil_1 l) (step_modeC_b01110_b10_b101_nil_2 l)).
Qed.

Lemma step_modeC_b01110_b10_b0000101_1 (l r : side) :
  cfg_modeC (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l))
    (S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> r) -[ holdout_0311_tm ]->+ cfg_transB_mid l r.
Proof.
  solve_local holdout_0311_tm 23
    (mkLocalState [S1; S0; S0; S1; S1; S1; S0; S1; S0] [S0; S0; S0; S0; S1; S0; S1] C R) l r.
Qed.

Lemma step_modeC_b01110_b10_b0000101_2 (l r : side) :
  cfg_transB_mid l r -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S0 >> S0 >> S0 >>
      (S1 >> S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> r)))).
Proof.
  solve_local holdout_0311_tm 23
    (mkLocalState [S1; S0; S1; S1; S0; S1; S0] [S1; S0; S1; S0; S1; S0; S1; S0; S1] B R) l r.
Qed.

Lemma step_modeC_b01110_b10_b0000101 (l r : side) :
  cfg_modeC (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l))
    (S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> r) -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S0 >> S0 >> S0 >>
      (S1 >> S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> r)))).
Proof.
  exact (stepPlus_stepPlus_stepPlus (step_modeC_b01110_b10_b0000101_1 l r) (step_modeC_b01110_b10_b0000101_2 l r)).
Qed.

Notation prepend10 := TM3.prepend10.

Notation encL_tail := TM3.encL_tail.

Notation encL := TM3.encL.

Notation encL_zero_nil := TM3.encL_zero_nil.

Notation encL_S := TM3.encL_S.

Notation encL_succ := TM3.encL_succ.

Notation encL_zero_cons := TM3.encL_zero_cons.

Lemma step_modeC_b01_encL (k0 : nat) (ks : list nat) (r : side) :
  cfg_modeC (encL k0 ks) (S0 >> S1 >> r) -[ holdout_0311_tm ]->+
    cfg_modeC (encL (k0 + 1) ks) r.
Proof. rewrite Nat.add_1_r. exact (step_modeC_b01 (encL k0 ks) r). Qed.

Lemma step_modeC_b01_b10101_encL (k0 : nat) (ks : list nat) (r : side) :
  cfg_modeC (encL k0 ks) (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> r) -[ holdout_0311_tm ]->+
    cfg_modeC (encL 0 ((k0 + 1) :: ks)) r.
Proof. rewrite Nat.add_1_r. exact (step_modeC_b01_b10101 (encL k0 ks) r). Qed.

Lemma step_modeE1_b10_encL (k0 : nat) (ks : list nat) (r : side) :
  cfg_modeE1 (encL (k0 + 1) ks) r -[ holdout_0311_tm ]->+
    cfg_modeE1 (encL k0 ks) (S0 >> S1 >> r).
Proof. rewrite Nat.add_1_r. exact (step_modeE1_b10 (encL k0 ks) r). Qed.

Lemma step_modeE1_b011_10_b10_encL (k1 : nat) (ks : list nat) (r : side) :
  cfg_modeE1 (encL 0 ((k1 + 1) :: ks)) r -[ holdout_0311_tm ]->+
    cfg_modeE1 (encL k1 ks) (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> r).
Proof. rewrite Nat.add_1_r. exact (step_modeE1_b011_10_b10 (encL k1 ks) r). Qed.

Lemma step_modeE0_first_b10_encL (x0 : nat) (ks : list nat) :
  cfg_modeE0_first (encL (x0 + 1) ks) -[ holdout_0311_tm ]->+
    cfg_modeE0_loop (encL x0 ks) (const S0).
Proof. rewrite Nat.add_1_r. exact (step_modeE0_first_b10 (encL x0 ks)). Qed.

Lemma step_modeE0_first_b011_10_b10_encL (x1 : nat) (ks : list nat) :
  cfg_modeE0_first (encL 0 ((x1 + 1) :: ks)) -[ holdout_0311_tm ]->+
    cfg_modeE1 (encL x1 ks) (S0 >> S1 >> S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> const S0)).
Proof. rewrite Nat.add_1_r. exact (step_modeE0_first_b011_10_b10 (encL x1 ks)). Qed.

Lemma step_modeE0_loop_b10_b011_10_b10_encL (x1 : nat) (ks : list nat) (r : side) :
  cfg_modeE0_loop (encL 1 ((x1 + 1) :: ks)) r -[ holdout_0311_tm ]->+
    cfg_modeE1 (encL x1 ks) (S0 >> S1 >> S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> r)).
Proof. rewrite Nat.add_1_r. exact (step_modeE0_loop_b10_b011_10_b10 (encL x1 ks) r). Qed.

Lemma step_modeC_b01110_b10_b101_nil_encL (z1 : nat) (zs : list nat) :
  cfg_modeC (encL 0 ((z1 + 1) :: zs)) (S1 >> S0 >> S1 >> const S0) -[ holdout_0311_tm ]->+
    cfg_modeE1 (encL z1 zs) (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >>
      (S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> const S0)).
Proof. rewrite Nat.add_1_r. exact (step_modeC_b01110_b10_b101_nil (encL z1 zs)). Qed.

Lemma step_modeC_b01110_b10_b0000101_encL (z1 : nat) (zs : list nat) (r : side) :
  cfg_modeC (encL 0 ((z1 + 1) :: zs)) (S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> r) -[ holdout_0311_tm ]->+
    cfg_modeE1 (encL z1 zs) (S0 >> S1 >> S0 >> S0 >> S0 >>
      (S1 >> S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> r)))).
Proof. rewrite Nat.add_1_r. exact (step_modeC_b01110_b10_b0000101 (encL z1 zs) r). Qed.

Notation prepend01 := TM3.prepend01.

Notation prepend01_add := TM3.prepend01_add.

Notation prepend11_01 := TM3.prepend11_01.

Notation prepend11_01_add := TM3.prepend11_01_add.

Notation add_last := TM3.add_last.

Notation add_last_cons := TM3.add_last_cons.

Notation add_last_length := TM3.add_last_length.

Notation add_last_ne_nil := TM3.add_last_ne_nil.

Notation add_last_zero := TM3.add_last_zero.

Notation add_last_add := TM3.add_last_add.

Notation bump_enc := TM3.bump_enc.

Notation bump_enc_twice := TM3.bump_enc_twice.

Notation bump_enc_nonempty := TM3.bump_enc_nonempty.

Notation bump_enc_twice_nonempty := TM3.bump_enc_twice_nonempty.

Notation ValidKS := TM3.ValidKS.

Notation ValidKS_add_last := TM3.ValidKS_add_last.

Notation GoodKS := TM3.GoodKS.

Notation GoodKS_mono := TM3.GoodKS_mono.

Notation GoodKS_add_last := TM3.GoodKS_add_last.

Notation GoodKS_valid := TM3.GoodKS_valid.

Notation GoodKS_succ_valid := TM3.GoodKS_succ_valid.

Notation InvNil := TM3.InvNil.

Lemma modeC_prepend01_star (n : nat) :
  forall (k0 : nat) (ks : list nat) (r : side),
    cfg_modeC (encL k0 ks) (prepend01 n r) -[ holdout_0311_tm ]->*
      cfg_modeC (encL (k0 + n) ks) r.
Proof.
  induction n as [|n IH]; intros k0 ks r; cbn [prepend01].
  - replace (k0 + 0) with k0 by lia. apply evstep_refl.
  - pose proof (step_modeC_b01_encL k0 ks (prepend01 n r)) as H1.
    pose proof (IH (k0 + 1) ks r) as H2.
    replace (k0 + 1 + n) with (k0 + S n) in H2 by lia.
    exact (stepPlus_stepStar (stepPlus_stepStar_stepPlus H1 H2)).
Qed.

Lemma e0_loop_drain_pairs (d : nat) :
  forall (rem : nat) (xs : list nat) (r : side),
    cfg_modeE0_loop (encL (rem + 2 * d) xs) r -[ holdout_0311_tm ]->*
      cfg_modeE0_loop (encL rem xs) (prepend11_01 d r).
Proof.
  induction d as [|d IH]; intros rem xs r; cbn [prepend11_01].
  - replace (rem + 2 * 0) with rem by lia. apply evstep_refl.
  - replace (rem + 2 * S d) with (S (S (rem + 2 * d))) by lia.
    pose proof (step_modeE0_loop_b10_b10 (encL (rem + 2 * d) xs) r) as H1.
    change (S1 >> S1 >> (S0 >> S1 >> r)) with (prepend11_01 1 r) in H1.
    pose proof (IH rem xs (prepend11_01 1 r)) as H2.
    rewrite <- prepend11_01_add in H2.
    replace (d + 1) with (S d) in H2 by lia.
    exact (stepPlus_stepStar (stepPlus_stepStar_stepPlus H1 H2)).
Qed.

Lemma modeE1_drain_k0 (k0 : nat) :
  forall (ks : list nat) (r : side),
    cfg_modeE1 (encL k0 ks) r -[ holdout_0311_tm ]->*
      cfg_modeE1 (encL 0 ks) (prepend01 k0 r).
Proof.
  induction k0 as [|k0 IH]; intros ks r.
  - apply evstep_refl.
  - pose proof (step_modeE1_b10 (encL k0 ks) r) as H1.
    change (S0 >> S1 >> r) with (prepend01 1 r) in H1.
    pose proof (IH ks (prepend01 1 r)) as H2.
    rewrite <- prepend01_add in H2.
    replace (k0 + 1) with (S k0) in H2 by lia.
    exact (stepPlus_stepStar (stepPlus_stepStar_stepPlus H1 H2)).
Qed.

Lemma modeE1_to_modeC (ks : list nat) :
  forall (k0 : nat) (r : side),
    ValidKS ks ->
    let b := bump_enc k0 ks in
    cfg_modeE1 (encL k0 ks) r -[ holdout_0311_tm ]->+ cfg_modeC (encL (fst b) (snd b)) r.
Proof.
  induction ks as [|k1 ks' IH]; intros k0 r Hval; simpl.
  - pose proof (modeE1_drain_k0 k0 [] r) as H1.
    pose proof (step_modeE1_base (prepend01 k0 r)) as H2.
    change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> prepend01 k0 r)))
      with (prepend01 3 (prepend01 k0 r)) in H2.
    rewrite <- prepend01_add in H2.
    replace (3 + k0) with (k0 + 3) in H2 by lia.
    pose proof (modeC_prepend01_star (k0 + 3) 0 [] r) as H3; simpl in H3.
    exact (stepStar_stepPlus_stepPlus H1 (stepPlus_stepStar_stepPlus H2 H3)).
  - destruct ks' as [|k2 ks''].
    + simpl.
      pose proof (modeE1_drain_k0 k0 [k1] r) as H1.
      destruct k1 as [|k1'].
      * pose proof (step_modeE1_b011_10_base (prepend01 k0 r)) as H2.
        pose proof (step_modeC_b01 (encL 0 [])
          (S0 >> S1 >> (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> prepend01 k0 r))) as H3.
        pose proof (step_modeC_b01 (encL 1 [])
          (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> prepend01 k0 r)) as H4.
        pose proof (step_modeC_b01_b10101_encL 2 [] (prepend01 k0 r)) as H5; simpl in H5.
        pose proof (modeC_prepend01_star k0 0 [3] r) as H6; simpl in H6.
        exact (stepStar_stepPlus_stepPlus H1
          (stepPlus_stepPlus_stepPlus H2
            (stepPlus_stepPlus_stepPlus H3
              (stepPlus_stepPlus_stepPlus H4
                (stepPlus_stepStar_stepPlus H5 H6))))).
      * pose proof (step_modeE1_b011_10_b10 (encL k1' []) (prepend01 k0 r)) as H2.
        pose proof (IH k1' (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> prepend01 k0 r) I) as H3.
        simpl in H3.
        pose proof (step_modeC_b01_b10101_encL (k1' + 3) [] (prepend01 k0 r)) as H4.
        replace (k1' + 3 + 1) with (S k1' + 3) in H4 by lia.
        pose proof (modeC_prepend01_star k0 0 [S k1' + 3] r) as H5; simpl in H5.
        exact (stepStar_stepPlus_stepPlus H1
          (stepPlus_stepPlus_stepPlus H2
            (stepPlus_stepPlus_stepPlus H3
              (stepPlus_stepStar_stepPlus H4 H5)))).
    + simpl in Hval. destruct Hval as [Hk1 Hval'].
      destruct k1 as [|k1']; [lia|].
      simpl.
      pose proof (modeE1_drain_k0 k0 (S k1' :: k2 :: ks'') r) as H1.
      pose proof (step_modeE1_b011_10_b10 (encL k1' (k2 :: ks'')) (prepend01 k0 r)) as H2.
      pose proof (IH k1' (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> prepend01 k0 r) Hval') as H3.
      simpl in H3.
      pose proof (step_modeC_b01_b10101 (encL k1' (add_last (k2 :: ks'') 3)) (prepend01 k0 r)) as H4.
      pose proof (modeC_prepend01_star k0 0 (S k1' :: add_last (k2 :: ks'') 3) r) as H5; simpl in H5.
      exact (stepStar_stepPlus_stepPlus H1
        (stepPlus_stepPlus_stepPlus H2
          (stepPlus_stepPlus_stepPlus H3
            (stepPlus_stepStar_stepPlus H4 H5)))).
Qed.

Lemma modeC_consume_11_01_nil (n : nat) :
  forall (k0 : nat) (r : side),
    cfg_modeC (encL k0 []) (prepend11_01 n r) -[ holdout_0311_tm ]->*
      cfg_modeC (encL (k0 + 4 * n) []) r.
Proof.
  induction n as [|n IH]; intros k0 r; cbn [prepend11_01].
  - replace (k0 + 4 * 0) with k0 by lia. apply evstep_refl.
  - pose proof (step_modeC_b11 (encL k0 []) (S0 >> S1 >> prepend11_01 n r)) as H1.
    pose proof (modeE1_to_modeC [] k0 (S0 >> S1 >> prepend11_01 n r) I) as H2; simpl in H2.
    pose proof (step_modeC_b01_encL (k0 + 3) [] (prepend11_01 n r)) as H3.
    replace (k0 + 3 + 1) with (k0 + 4) in H3 by lia.
    pose proof (IH (k0 + 4) r) as H4.
    replace (k0 + 4 + 4 * n) with (k0 + 4 * S n) in H4 by lia.
    exact (stepPlus_stepStar
      (stepPlus_stepPlus_stepPlus H1
        (stepPlus_stepPlus_stepPlus H2
          (stepPlus_stepStar_stepPlus H3 H4)))).
Qed.

Lemma modeC_consume_11_01_nonempty (n : nat) :
  forall (k0 : nat) (ks : list nat) (r : side),
    ks <> [] -> ValidKS ks ->
    cfg_modeC (encL k0 ks) (prepend11_01 n r) -[ holdout_0311_tm ]->*
      cfg_modeC (encL (k0 + n) (add_last ks (3 * n))) r.
Proof.
  induction n as [|n IH]; intros k0 ks r Hne Hval; cbn [prepend11_01].
  - replace (k0 + 0) with k0 by lia. replace (3 * 0) with 0 by lia.
    rewrite add_last_zero. apply evstep_refl.
  - pose proof (step_modeC_b11 (encL k0 ks) (S0 >> S1 >> prepend11_01 n r)) as H1.
    pose proof (modeE1_to_modeC ks k0 (S0 >> S1 >> prepend11_01 n r) Hval) as H2; simpl in H2.
    rewrite (bump_enc_nonempty k0 ks Hne) in H2; simpl in H2.
    pose proof (step_modeC_b01_encL k0 (add_last ks 3) (prepend11_01 n r)) as H3.
    pose proof (IH (k0 + 1) (add_last ks 3) r
      (add_last_ne_nil ks 3 Hne) (ValidKS_add_last ks 3 Hval)) as H4.
    rewrite add_last_add in H4.
    replace (k0 + 1 + n) with (k0 + S n) in H4 by lia.
    replace (3 + 3 * n) with (3 * S n) in H4 by lia.
    exact (stepPlus_stepStar
      (stepPlus_stepPlus_stepPlus H1
        (stepPlus_stepPlus_stepPlus H2
          (stepPlus_stepStar_stepPlus H3 H4)))).
Qed.

Notation ValidKS_bump_enc := TM3.ValidKS_bump_enc.

Lemma unwrap_11_01_1011101_step (m0 : nat) (ms : list nat) (R0 : side) :
  ValidKS ms ->
  let p := bump_enc_twice m0 ms in
  cfg_modeC (encL m0 ms)
    (S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> R0)
    -[ holdout_0311_tm ]->+
    cfg_modeC (encL 0 ((fst p + 1) :: snd p)) R0.
Proof.
  intros Hval. simpl.
  set (p1 := bump_enc m0 ms).
  set (p2 := bump_enc (fst p1) (snd p1)).
  pose proof (step_modeC_b11 (encL m0 ms)
    (S0 >> S1 >> S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> R0)) as H1.
  pose proof (modeE1_to_modeC ms m0
    (S0 >> S1 >> S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> R0) Hval) as H2.
  fold p1 in H2.
  pose proof (step_modeC_b01_b1011101 (encL (fst p1) (snd p1)) R0) as H3.
  pose proof (modeE1_to_modeC (snd p1) (fst p1)
    (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> R0)
    (ValidKS_bump_enc m0 ms Hval)) as H4.
  fold p2 in H4.
  pose proof (step_modeC_b01_b10101_encL (fst p2) (snd p2) R0) as H5.
  exact (stepPlus_stepPlus_stepPlus H1
    (stepPlus_stepPlus_stepPlus H2
      (stepPlus_stepPlus_stepPlus H3
        (stepPlus_stepPlus_stepPlus H4 H5)))).
Qed.

Notation prepend11_01_split_last := TM3.prepend11_01_split_last.

Notation prepend11_01_S_split := TM3.prepend11_01_S_split.

Lemma e0_loop_leave1_goodks (n : nat) :
  forall (x0 : nat) (xs : list nat) (S0_val : nat) (R0 : side),
    List.length xs = n ->
    S0_val >= 36 ->
    (xs = [] -> 2 * S0_val <= 35 * x0) ->
    (xs <> [] -> x0 >= 2 /\ 2 * S0_val <= 35 * (x0 + 3)) ->
    GoodKS (2 * S0_val + 63 * (x0 + 3)) xs ->
    exists m0 ms,
      (cfg_modeE0_loop (encL x0 xs) R0 -[ holdout_0311_tm ]->+
        cfg_modeC (encL m0 ms) (S1 >> S1 >> S0 >> S1 >> R0)) /\
      ValidKS ms /\
      (ms = [] -> m0 >= 7) /\
      (let p := bump_enc_twice m0 ms in GoodKS S0_val ((fst p + 1) :: snd p)) /\
      ((xs = [] -> x0 >= 10) -> S0_val = 81 ->
        let p1 := bump_enc m0 ms in GoodKS 81 ((fst p1 + 1) :: snd p1)).
Proof.
  induction n as [|n' IH]; intros x0 xs S0_val R0 Hlen HS Hnil Hcons Hgks.
  - destruct xs as [|x1 xs_rest]; [|simpl in Hlen; lia].
    pose proof (Hnil eq_refl) as Hx0.
    assert (Hx0_ge : x0 >= 3) by lia.
    set (d := x0 / 2).
    set (rem := x0 mod 2).
    assert (Hdiv : rem + 2 * d = x0) by (unfold d, rem; lia).
    assert (Hrem : rem = 0 \/ rem = 1) by (unfold rem; lia).
    destruct Hrem as [Heven | Hodd].
    + assert (Hd : d >= 2) by lia.
      exists d, [3 * d - 3].
      split; [|split; [exact I | split; [discriminate | split]]].
      * assert (Hd_split : x0 = 0 + 2 * d) by lia.
        rewrite Hd_split.
        pose proof (e0_loop_drain_pairs d 0 [] R0) as H1.
        pose proof (step_modeE0_loop_base (prepend11_01 d R0)) as H2.
        change (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0)) with (encL 0 [0]) in H2.
        pose proof (step_modeC_b01_encL 0 [0] (prepend11_01 d R0)) as H3; simpl in H3.
        pose proof (modeC_consume_11_01_nonempty (d - 1) 1 [0]
          (S1 >> S1 >> S0 >> S1 >> R0) ltac:(discriminate) I) as H4.
        cbn [add_last] in H4.
        rewrite <- (prepend11_01_split_last d R0 ltac:(lia)) in H4.
        replace (1 + (d - 1)) with d in H4 by lia.
        replace (0 + 3 * (d - 1)) with (3 * d - 3) in H4 by lia.
        exact (stepStar_stepPlus_stepPlus H1 (stepPlus_stepPlus_stepPlus H2 (stepPlus_stepStar_stepPlus H3 H4))).
      * unfold bump_enc_twice, bump_enc; cbn [fst snd add_last GoodKS].
        split; [lia | split; [lia | exact I]].
      * intros Hx10 HS81.
        pose proof (Hx10 eq_refl) as Hx10'.
        assert (Hd5 : d >= 5) by lia.
        unfold bump_enc; cbn [fst snd add_last GoodKS].
        split; [lia | split; [lia | exact I]].
    + assert (Hd : d >= 1) by lia.
      exists (4 * d + 3), (@nil nat).
      split; [|split; [exact I | split; [intros _; lia | split]]].
      * assert (Hd_split : x0 = 1 + 2 * d) by lia.
        rewrite Hd_split.
        pose proof (e0_loop_drain_pairs d 1 [] R0) as H1.
        pose proof (step_modeE0_loop_b10_base (prepend11_01 d R0)) as H2.
        change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S1 >> S1 >> (S0 >> S1 >> prepend11_01 d R0)))))
          with (prepend01 3 (prepend11_01 (S d) R0)) in H2.
        pose proof (modeC_prepend01_star 3 0 [] (prepend11_01 (S d) R0)) as H3; simpl in H3.
        pose proof (modeC_consume_11_01_nil d 3 (S1 >> S1 >> S0 >> S1 >> R0)) as H4.
        rewrite <- (prepend11_01_S_split d R0) in H4.
        replace (3 + 4 * d) with (4 * d + 3) in H4 by lia.
        exact (stepStar_stepPlus_stepPlus H1 (stepPlus_stepStar_stepPlus H2 (stepStar_trans H3 H4))).
      * unfold bump_enc_twice, bump_enc; cbn [fst snd GoodKS].
        split; [lia | exact I].
      * intros _ _.
        unfold bump_enc; cbn [fst snd GoodKS].
        split; [lia | exact I].
  - destruct xs as [|x1 xs_rest]; [simpl in Hlen; lia|].
    assert (Hlen' : List.length xs_rest = n') by (simpl in Hlen; lia).
    destruct (Hcons ltac:(discriminate)) as [Hx0_ge Hx0_bound].
    cbn [GoodKS] in Hgks; destruct Hgks as [Hx1_bound Hgks_rest].
    assert (Hx1_ge : x1 >= 1) by lia.
    pose proof (GoodKS_valid xs_rest (2 * S0_val + 63 * (x0 + 3) + 63 * (x1 + 2)) ltac:(lia) Hgks_rest) as Hval_rest.
    set (d := x0 / 2).
    set (rem := x0 mod 2).
    assert (Hd : d >= 1) by (unfold d; lia).
    assert (Hdiv : rem + 2 * d = x0) by (unfold d, rem; lia).
    assert (Hrem : rem = 0 \/ rem = 1) by (unfold rem; lia).
    destruct Hrem as [Heven | Hodd].
    + assert (Hd_split : x0 = 0 + 2 * d) by lia.
      destruct xs_rest as [|x2 rest'].
      * exists (x1 + 4 * d + 3), (@nil nat).
        split; [|split; [exact I | split; [intros _; lia | split]]].
        -- rewrite Hd_split.
           pose proof (e0_loop_drain_pairs d 0 [x1] R0) as H1.
           pose proof (step_modeE0_loop_b011_10 (encL x1 []) (prepend11_01 d R0)) as H2.
           change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> prepend11_01 d R0))))
             with (prepend01 4 (prepend11_01 d R0)) in H2.
           pose proof (modeE1_to_modeC [] x1 (prepend01 4 (prepend11_01 d R0)) I) as H3; simpl in H3.
           pose proof (modeC_prepend01_star 4 (x1 + 3) [] (prepend11_01 d R0)) as H4.
           pose proof (modeC_consume_11_01_nil (d - 1) (x1 + 3 + 4) (S1 >> S1 >> S0 >> S1 >> R0)) as H5.
           rewrite <- (prepend11_01_split_last d R0 Hd) in H5.
           replace (x1 + 3 + 4 + 4 * (d - 1)) with (x1 + 4 * d + 3) in H5 by lia.
           exact (stepStar_stepPlus_stepPlus H1
             (stepPlus_stepPlus_stepPlus H2
               (stepPlus_stepStar_stepPlus H3 (stepStar_trans H4 H5)))).
        -- unfold bump_enc_twice, bump_enc; cbn [fst snd GoodKS].
           split; [lia | exact I].
        -- intros _ _.
           unfold bump_enc; cbn [fst snd GoodKS].
           split; [lia | exact I].
      * assert (Hne_rest : x2 :: rest' <> []) by discriminate.
        exists (x1 + d + 3), (add_last (x2 :: rest') (3 * d)).
        split; [|split; [exact (ValidKS_add_last (x2 :: rest') (3 * d) Hval_rest) |
                 split; [intros Hemp; exfalso; exact (add_last_ne_nil (x2 :: rest') (3 * d) Hne_rest Hemp) | split]]].
        -- rewrite Hd_split.
           pose proof (e0_loop_drain_pairs d 0 (x1 :: x2 :: rest') R0) as H1.
           pose proof (step_modeE0_loop_b011_10 (encL x1 (x2 :: rest')) (prepend11_01 d R0)) as H2.
           change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> prepend11_01 d R0))))
             with (prepend01 4 (prepend11_01 d R0)) in H2.
           pose proof (modeE1_to_modeC (x2 :: rest') x1 (prepend01 4 (prepend11_01 d R0)) Hval_rest) as H3.
           rewrite (bump_enc_nonempty x1 (x2 :: rest') Hne_rest) in H3; simpl in H3.
           pose proof (modeC_prepend01_star 4 x1 (add_last (x2 :: rest') 3) (prepend11_01 d R0)) as H4.
           pose proof (modeC_consume_11_01_nonempty (d - 1) (x1 + 4) (add_last (x2 :: rest') 3)
             (S1 >> S1 >> S0 >> S1 >> R0)
             (add_last_ne_nil (x2 :: rest') 3 Hne_rest)
             (ValidKS_add_last (x2 :: rest') 3 Hval_rest)) as H5.
           rewrite add_last_add in H5.
           rewrite <- (prepend11_01_split_last d R0 Hd) in H5.
           replace (x1 + 4 + (d - 1)) with (x1 + d + 3) in H5 by lia.
           replace (3 + 3 * (d - 1)) with (3 * d) in H5 by lia.
           exact (stepStar_stepPlus_stepPlus H1
             (stepPlus_stepPlus_stepPlus H2
               (stepPlus_stepStar_stepPlus H3 (stepStar_trans H4 H5)))).
        -- cbv zeta.
           rewrite (bump_enc_twice_nonempty (x1 + d + 3) (add_last (x2 :: rest') (3 * d))
             (add_last_ne_nil (x2 :: rest') (3 * d) Hne_rest)).
           rewrite add_last_add; cbn [fst snd GoodKS].
           split; [lia |].
           apply GoodKS_add_last.
           eapply GoodKS_mono; [|exact Hgks_rest]; lia.
        -- intros _ HS81; subst S0_val. cbv zeta.
           rewrite (bump_enc_nonempty (x1 + d + 3) (add_last (x2 :: rest') (3 * d))
             (add_last_ne_nil (x2 :: rest') (3 * d) Hne_rest)).
           rewrite add_last_add; cbn [fst snd GoodKS].
           split; [lia |].
           apply GoodKS_add_last.
           eapply GoodKS_mono; [|exact Hgks_rest]; lia.
    + assert (Hd_split : x0 = 1 + 2 * d) by lia.
      set (S_sub := S0_val + 63 * (d + 2)).
      assert (HS_sub : S_sub >= 36) by (unfold S_sub; lia).
      assert (Hx1_ge10 : x1 >= 10) by lia.
      set (sub := bump_enc (x1 - 1) xs_rest).
      assert (Hsub_len : List.length (snd sub) = n').
      { unfold sub, bump_enc; destruct xs_rest; cbn [fst snd]; [exact Hlen' | rewrite add_last_length; exact Hlen']. }
      assert (Hsub_nil : snd sub = [] -> 2 * S_sub <= 35 * fst sub).
      { unfold sub, bump_enc; destruct xs_rest as [|y ys]; cbn [fst snd]; [intros _; unfold S_sub; lia |].
        intros Hemp; exfalso; exact (add_last_ne_nil (y :: ys) 3 ltac:(discriminate) Hemp). }
      assert (Hsub_cons : snd sub <> [] -> fst sub >= 2 /\ 2 * S_sub <= 35 * (fst sub + 3)).
      { unfold sub, bump_enc; destruct xs_rest as [|y ys]; cbn [fst snd]; [congruence | intros _; unfold S_sub; lia]. }
      assert (Hsub_gks : GoodKS (2 * S_sub + 63 * (fst sub + 3)) (snd sub)).
      { unfold sub, bump_enc; destruct xs_rest as [|y ys]; cbn [fst snd]; [exact I |].
        replace (2 * S_sub + 63 * (x1 - 1 + 3)) with (2 * S0_val + 63 * (x0 + 3) + 63 * (x1 + 2)) by (unfold S_sub; lia).
        exact (GoodKS_add_last (y :: ys) _ 3 Hgks_rest). }
      set (R_tail := S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> prepend11_01 d R0).
      destruct (IH (fst sub) (snd sub) S_sub R_tail Hsub_len HS_sub Hsub_nil Hsub_cons Hsub_gks)
        as [y0 [ys [Hstep_sub [Hval_ys [Hys_emp [Hgks_sub _]]]]]].
      set (py := bump_enc_twice y0 ys).
      set (ks_mid := (fst py + 1) :: snd py).
      assert (Hne_mid : ks_mid <> []) by discriminate.
      assert (Hval_mid : ValidKS ks_mid) by (apply (GoodKS_succ_valid S_sub (fst py) (snd py)); exact Hgks_sub).
      exists (d - 1), (add_last ks_mid (3 * (d - 1))).
      split; [|split; [exact (ValidKS_add_last ks_mid (3 * (d - 1)) Hval_mid) |
               split; [intros Hemp; exfalso; exact (add_last_ne_nil ks_mid (3 * (d - 1)) Hne_mid Hemp) | split]]].
      * rewrite Hd_split.
        pose proof (e0_loop_drain_pairs d 1 (x1 :: xs_rest) R0) as H1.
        assert (Hx1_eq : x1 = (x1 - 1) + 1) by lia.
        pose proof (step_modeE0_loop_b10_b011_10_b10_encL (x1 - 1) xs_rest (prepend11_01 d R0)) as H2.
        rewrite <- Hx1_eq in H2.
        fold R_tail in H2.
        pose proof (modeE1_to_modeC xs_rest (x1 - 1)
          (S0 >> S1 >> S0 >> S0 >> S0 >> R_tail) Hval_rest) as H3.
        fold sub in H3.
        pose proof (step_modeC_b01_b000 (encL (fst sub) (snd sub)) R_tail) as H4.
        pose proof (unwrap_11_01_1011101_step y0 ys (prepend11_01 d R0) Hval_ys) as H5.
        fold py in H5; fold ks_mid in H5.
        pose proof (modeC_consume_11_01_nonempty (d - 1) 0 ks_mid
          (S1 >> S1 >> S0 >> S1 >> R0) Hne_mid Hval_mid) as H6.
        rewrite <- (prepend11_01_split_last d R0 Hd) in H6.
        replace (0 + (d - 1)) with (d - 1) in H6 by lia.
        exact (stepStar_stepPlus_stepPlus H1
          (stepPlus_stepPlus_stepPlus H2
            (stepPlus_stepPlus_stepPlus H3
              (stepPlus_stepPlus_stepPlus H4
                (stepPlus_stepPlus_stepPlus Hstep_sub
                  (stepPlus_stepStar_stepPlus H5 H6)))))).
      * cbv zeta.
        rewrite (bump_enc_twice_nonempty (d - 1) (add_last ks_mid (3 * (d - 1)))
          (add_last_ne_nil ks_mid (3 * (d - 1)) Hne_mid)).
        rewrite add_last_add; cbn [fst snd].
        replace (d - 1 + 1) with d by lia.
        cbn [GoodKS].
        split; [unfold S_sub; lia |].
        replace (S0_val + 63 * (d + 2)) with S_sub by reflexivity.
        exact (GoodKS_add_last ks_mid S_sub (3 * (d - 1) + 6) Hgks_sub).
      * intros _ HS81; subst S0_val. cbv zeta.
        rewrite (bump_enc_nonempty (d - 1) (add_last ks_mid (3 * (d - 1)))
          (add_last_ne_nil ks_mid (3 * (d - 1)) Hne_mid)).
        rewrite add_last_add; cbn [fst snd].
        replace (d - 1 + 1) with d by lia.
        cbn [GoodKS].
        split; [unfold S_sub; lia |].
        replace (81 + 63 * (d + 2)) with S_sub by reflexivity.
        exact (GoodKS_add_last ks_mid S_sub (3 * (d - 1) + 3) Hgks_sub).
Qed.

Lemma step_k0_pos (k0 : nat) (ks : list nat) :
  k0 >= 1 ->
  InvNil k0 ks ->
  exists k0' ks',
    (cfg_modeC (encL k0 ks) (const S0) -[ holdout_0311_tm ]->+ cfg_modeC (encL k0' ks') (const S0)) /\
    InvNil k0' ks'.
Proof.
  intros Hk0 Hinv.
  set (x0 := k0 - 1).
  assert (Hk0_eq : k0 = x0 + 1) by lia.
  assert (Hto_e0 : cfg_modeC (encL k0 ks) (const S0) -[ holdout_0311_tm ]->+ cfg_modeE0_loop (encL x0 ks) (const S0)).
  { rewrite Hk0_eq.
    exact (stepPlus_stepPlus_stepPlus (step_modeC_nil (encL (x0 + 1) ks)) (step_modeE0_first_b10_encL x0 ks)). }
  set (d := x0 / 2).
  set (rem := x0 mod 2).
  assert (Hdiv : rem + 2 * d = x0) by (unfold d, rem; lia).
  assert (Hrem : rem = 0 \/ rem = 1) by (unfold rem; lia).
  destruct Hinv as [[-> Hk5] | [Hne Hgks]].
  - destruct Hrem as [Heven | Hodd].
    + assert (Hd : d >= 2) by lia.
      assert (Hx_split : x0 = 0 + 2 * d) by lia.
      exists (d + 1), [3 * d].
      split.
      * rewrite Hx_split in Hto_e0.
        pose proof (e0_loop_drain_pairs d 0 [] (const S0)) as H1.
        pose proof (step_modeE0_loop_base (prepend11_01 d (const S0))) as H2.
        change (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0)) with (encL 0 [0]) in H2.
        pose proof (step_modeC_b01_encL 0 [0] (prepend11_01 d (const S0))) as H3; simpl in H3.
        pose proof (modeC_consume_11_01_nonempty d 1 [0] (const S0) ltac:(discriminate) I) as H4.
        cbn [add_last] in H4.
        replace (1 + d) with (d + 1) in H4 by lia.
        replace (0 + 3 * d) with (3 * d) in H4 by lia.
        exact (stepPlus_stepPlus_stepPlus Hto_e0
          (stepStar_stepPlus_stepPlus H1
            (stepPlus_stepPlus_stepPlus H2
              (stepPlus_stepStar_stepPlus H3 H4)))).
      * right; split; [discriminate |].
        destruct (Nat.eqb_spec (d + 1) 1); [lia |].
        cbn [GoodKS]; split; [lia | exact I].
    + assert (Hd : d >= 2) by lia.
      assert (Hx_split : x0 = 1 + 2 * d) by lia.
      exists (4 * d + 7), (@nil nat).
      split; [|left; split; [reflexivity | lia]].
      rewrite Hx_split in Hto_e0.
      pose proof (e0_loop_drain_pairs d 1 [] (const S0)) as H1.
      pose proof (step_modeE0_loop_b10_base (prepend11_01 d (const S0))) as H2.
      change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S1 >> S1 >> (S0 >> S1 >> prepend11_01 d (const S0))))))
        with (prepend01 3 (prepend11_01 (S d) (const S0))) in H2.
      pose proof (modeC_prepend01_star 3 0 [] (prepend11_01 (S d) (const S0))) as H3; simpl in H3.
      pose proof (modeC_consume_11_01_nil (S d) 3 (const S0)) as H4.
      replace (3 + 4 * S d) with (4 * d + 7) in H4 by lia.
      exact (stepPlus_stepPlus_stepPlus Hto_e0
        (stepStar_stepPlus_stepPlus H1
          (stepPlus_stepStar_stepPlus H2 (stepStar_trans H3 H4)))).
  - destruct ks as [|k1 ks_rest]; [congruence |].
    set (S_in := if Nat.eqb k0 1 then 81 else 36 * (k0 + 2)).
    fold S_in in Hgks.
    assert (HS_in_ge : S_in >= 81).
    { unfold S_in; destruct (Nat.eqb_spec k0 1); lia. }
    cbn [GoodKS] in Hgks; destruct Hgks as [Hk1_bound Hgks_rest].
    assert (Hk1_ge : k1 >= 1) by lia.
    pose proof (GoodKS_valid ks_rest (S_in + 63 * (k1 + 2)) ltac:(lia) Hgks_rest) as Hval_rest.
    destruct Hrem as [Heven | Hodd].
    + assert (Hx_split : x0 = 0 + 2 * d) by lia.
      destruct ks_rest as [|k2 rest'].
      * exists (k1 + 4 * d + 7), (@nil nat).
        split; [|left; split; [reflexivity | lia]].
        rewrite Hx_split in Hto_e0.
        pose proof (e0_loop_drain_pairs d 0 [k1] (const S0)) as H1.
        pose proof (step_modeE0_loop_b011_10 (encL k1 []) (prepend11_01 d (const S0))) as H2.
        change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> prepend11_01 d (const S0)))))
          with (prepend01 4 (prepend11_01 d (const S0))) in H2.
        pose proof (modeE1_to_modeC [] k1 (prepend01 4 (prepend11_01 d (const S0))) I) as H3; simpl in H3.
        pose proof (modeC_prepend01_star 4 (k1 + 3) [] (prepend11_01 d (const S0))) as H4.
        pose proof (modeC_consume_11_01_nil d (k1 + 3 + 4) (const S0)) as H5.
        replace (k1 + 3 + 4 + 4 * d) with (k1 + 4 * d + 7) in H5 by lia.
        exact (stepPlus_stepPlus_stepPlus Hto_e0
          (stepStar_stepPlus_stepPlus H1
            (stepPlus_stepPlus_stepPlus H2
              (stepPlus_stepStar_stepPlus H3 (stepStar_trans H4 H5))))).
      * assert (Hne_rest : k2 :: rest' <> []) by discriminate.
        exists (k1 + d + 4), (add_last (k2 :: rest') (3 * d + 3)).
        split.
        -- rewrite Hx_split in Hto_e0.
           pose proof (e0_loop_drain_pairs d 0 (k1 :: k2 :: rest') (const S0)) as H1.
           pose proof (step_modeE0_loop_b011_10 (encL k1 (k2 :: rest')) (prepend11_01 d (const S0))) as H2.
           change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> prepend11_01 d (const S0)))))
             with (prepend01 4 (prepend11_01 d (const S0))) in H2.
           pose proof (modeE1_to_modeC (k2 :: rest') k1 (prepend01 4 (prepend11_01 d (const S0))) Hval_rest) as H3.
           rewrite (bump_enc_nonempty k1 (k2 :: rest') Hne_rest) in H3; simpl in H3.
           pose proof (modeC_prepend01_star 4 k1 (add_last (k2 :: rest') 3) (prepend11_01 d (const S0))) as H4.
           pose proof (modeC_consume_11_01_nonempty d (k1 + 4) (add_last (k2 :: rest') 3) (const S0)
             (add_last_ne_nil (k2 :: rest') 3 Hne_rest)
             (ValidKS_add_last (k2 :: rest') 3 Hval_rest)) as H5.
           rewrite add_last_add in H5.
           replace (k1 + 4 + d) with (k1 + d + 4) in H5 by lia.
           replace (3 + 3 * d) with (3 * d + 3) in H5 by lia.
           exact (stepPlus_stepPlus_stepPlus Hto_e0
             (stepStar_stepPlus_stepPlus H1
               (stepPlus_stepPlus_stepPlus H2
                 (stepPlus_stepStar_stepPlus H3 (stepStar_trans H4 H5))))).
        -- right; split; [exact (add_last_ne_nil (k2 :: rest') (3 * d + 3) Hne_rest) |].
           destruct (Nat.eqb_spec (k1 + d + 4) 1); [lia |].
           apply GoodKS_add_last.
           eapply GoodKS_mono; [|exact Hgks_rest].
           unfold S_in; destruct (Nat.eqb_spec k0 1); lia.
    + assert (Hx_split : x0 = 1 + 2 * d) by lia.
      assert (Hk0_ne1 : k0 <> 1) by lia.
      assert (HS_in_eq : S_in = 72 * (d + 2)).
      { unfold S_in; destruct (Nat.eqb_spec k0 1); lia. }
      set (S_sub := 36 * (d + 2)).
      assert (HS_sub : S_sub >= 36) by (unfold S_sub; lia).
      assert (Hk1_ge3 : k1 >= 3) by lia.
      set (sub := bump_enc (k1 - 1) ks_rest).
      assert (Hsub_nil : snd sub = [] -> 2 * S_sub <= 35 * fst sub).
      { unfold sub, bump_enc; destruct ks_rest as [|y ys]; cbn [fst snd]; [intros _; unfold S_sub; lia |].
        intros Hemp; exfalso; exact (add_last_ne_nil (y :: ys) 3 ltac:(discriminate) Hemp). }
      assert (Hsub_cons : snd sub <> [] -> fst sub >= 2 /\ 2 * S_sub <= 35 * (fst sub + 3)).
      { unfold sub, bump_enc; destruct ks_rest as [|y ys]; cbn [fst snd]; [congruence | intros _; unfold S_sub; lia]. }
      assert (Hsub_gks : GoodKS (2 * S_sub + 63 * (fst sub + 3)) (snd sub)).
      { unfold sub, bump_enc; destruct ks_rest as [|y ys]; cbn [fst snd]; [exact I |].
        replace (2 * S_sub + 63 * (k1 - 1 + 3)) with (S_in + 63 * (k1 + 2)) by (unfold S_sub; lia).
        exact (GoodKS_add_last (y :: ys) _ 3 Hgks_rest). }
      set (R_tail := S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> prepend11_01 d (const S0)).
      destruct (e0_loop_leave1_goodks (List.length (snd sub)) (fst sub) (snd sub) S_sub R_tail
        eq_refl HS_sub Hsub_nil Hsub_cons Hsub_gks)
        as [y0 [ys [Hstep_sub [Hval_ys [_ [Hgks_sub _]]]]]].
      set (py := bump_enc_twice y0 ys).
      set (ks_mid := (fst py + 1) :: snd py).
      assert (Hne_mid : ks_mid <> []) by discriminate.
      assert (Hval_mid : ValidKS ks_mid) by (apply (GoodKS_succ_valid S_sub (fst py) (snd py)); exact Hgks_sub).
      exists d, (add_last ks_mid (3 * d)).
      split.
      * rewrite Hx_split in Hto_e0.
        pose proof (e0_loop_drain_pairs d 1 (k1 :: ks_rest) (const S0)) as H1.
        assert (Hk1_eq : k1 = (k1 - 1) + 1) by lia.
        pose proof (step_modeE0_loop_b10_b011_10_b10_encL (k1 - 1) ks_rest (prepend11_01 d (const S0))) as H2.
        rewrite <- Hk1_eq in H2.
        fold R_tail in H2.
        pose proof (modeE1_to_modeC ks_rest (k1 - 1)
          (S0 >> S1 >> S0 >> S0 >> S0 >> R_tail) Hval_rest) as H3.
        fold sub in H3.
        pose proof (step_modeC_b01_b000 (encL (fst sub) (snd sub)) R_tail) as H4.
        pose proof (unwrap_11_01_1011101_step y0 ys (prepend11_01 d (const S0)) Hval_ys) as H5.
        fold py in H5; fold ks_mid in H5.
        pose proof (modeC_consume_11_01_nonempty d 0 ks_mid (const S0) Hne_mid Hval_mid) as H6.
        replace (0 + d) with d in H6 by lia.
        exact (stepPlus_stepPlus_stepPlus Hto_e0
          (stepStar_stepPlus_stepPlus H1
            (stepPlus_stepPlus_stepPlus H2
              (stepPlus_stepPlus_stepPlus H3
                (stepPlus_stepPlus_stepPlus H4
                  (stepPlus_stepPlus_stepPlus Hstep_sub
                    (stepPlus_stepStar_stepPlus H5 H6))))))).
      * right; split; [exact (add_last_ne_nil ks_mid (3 * d) Hne_mid) |].
        apply GoodKS_add_last.
        eapply GoodKS_mono; [|exact Hgks_sub].
        unfold S_sub; destruct (Nat.eqb_spec d 1); lia.
Qed.

Lemma e0_loop_drain_plus2 (w0 : nat) (ws : list nat) (S_w : nat) :
  (ws = [] -> w0 >= 4) ->
  36 <= S_w + 54 * (w0 / 2) ->
  GoodKS (S_w + 63 * (w0 + 3)) ws ->
  exists k0' ks',
    (cfg_modeE0_loop (encL w0 ws) (S0 >> S1 >> S0 >> S1 >> const S0)
      -[ holdout_0311_tm ]->+ cfg_modeC (encL k0' ks') (const S0)) /\
    InvNil k0' ks'.
Proof.
  intros Hempty Hsw Hgks.
  set (R0 := S0 >> S1 >> S0 >> S1 >> const S0).
  assert (HR0 : R0 = prepend01 2 (const S0)) by reflexivity.
  set (d := w0 / 2).
  set (rem := w0 mod 2).
  assert (Hdiv : rem + 2 * d = w0) by (unfold d, rem; lia).
  assert (Hrem : rem = 0 \/ rem = 1) by (unfold rem; lia).
  destruct ws as [|w1 ws_rest].
  - pose proof (Hempty eq_refl) as Hw4.
    destruct Hrem as [Heven | Hodd].
    + assert (Hd : d >= 2) by lia.
      assert (Hw_split : w0 = 0 + 2 * d) by lia.
      exists (d + 3), [3 * d].
      split.
      * rewrite Hw_split.
        pose proof (e0_loop_drain_pairs d 0 [] R0) as H1.
        pose proof (step_modeE0_loop_base (prepend11_01 d R0)) as H2.
        change (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0)) with (encL 0 [0]) in H2.
        pose proof (step_modeC_b01_encL 0 [0] (prepend11_01 d R0)) as H3; simpl in H3.
        pose proof (modeC_consume_11_01_nonempty d 1 [0] R0 ltac:(discriminate) I) as H4.
        cbn [add_last] in H4.
        replace (0 + 3 * d) with (3 * d) in H4 by lia.
        rewrite HR0 in H4.
        pose proof (modeC_prepend01_star 2 (1 + d) [3 * d] (const S0)) as H5.
        replace (1 + d + 2) with (d + 3) in H5 by lia.
        exact (stepStar_stepPlus_stepPlus H1
          (stepPlus_stepPlus_stepPlus H2
            (stepPlus_stepStar_stepPlus H3 (stepStar_trans H4 H5)))).
      * right; split; [discriminate |].
        destruct (Nat.eqb_spec (d + 3) 1); [lia |].
        cbn [GoodKS]; split; [lia | exact I].
    + assert (Hd : d >= 1) by lia.
      assert (Hw_split : w0 = 1 + 2 * d) by lia.
      exists (4 * d + 9), (@nil nat).
      split; [|left; split; [reflexivity | lia]].
      rewrite Hw_split.
      pose proof (e0_loop_drain_pairs d 1 [] R0) as H1.
      pose proof (step_modeE0_loop_b10_base (prepend11_01 d R0)) as H2.
      change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S1 >> S1 >> (S0 >> S1 >> prepend11_01 d R0)))))
        with (prepend01 3 (prepend11_01 (S d) R0)) in H2.
      pose proof (modeC_prepend01_star 3 0 [] (prepend11_01 (S d) R0)) as H3; simpl in H3.
      pose proof (modeC_consume_11_01_nil (S d) 3 R0) as H4.
      rewrite HR0 in H4.
      pose proof (modeC_prepend01_star 2 (3 + 4 * S d) [] (const S0)) as H5.
      replace (3 + 4 * S d + 2) with (4 * d + 9) in H5 by lia.
      exact (stepStar_stepPlus_stepPlus H1
        (stepPlus_stepStar_stepPlus H2 (stepStar_trans H3 (stepStar_trans H4 H5)))).
  - cbn [GoodKS] in Hgks; destruct Hgks as [Hw1_bound Hgks_rest].
    assert (Hw1_ge : w1 >= 4) by (unfold d in Hsw; lia).
    pose proof (GoodKS_valid ws_rest (S_w + 63 * (w0 + 3) + 63 * (w1 + 2)) ltac:(lia) Hgks_rest) as Hval_rest.
    destruct Hrem as [Heven | Hodd].
    + assert (Hw_split : w0 = 0 + 2 * d) by lia.
      destruct ws_rest as [|w2 rest'].
      * exists (w1 + 4 * d + 9), (@nil nat).
        split; [|left; split; [reflexivity | lia]].
        rewrite Hw_split.
        pose proof (e0_loop_drain_pairs d 0 [w1] R0) as H1.
        pose proof (step_modeE0_loop_b011_10 (encL w1 []) (prepend11_01 d R0)) as H2.
        change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> prepend11_01 d R0))))
          with (prepend01 4 (prepend11_01 d R0)) in H2.
        pose proof (modeE1_to_modeC [] w1 (prepend01 4 (prepend11_01 d R0)) I) as H3; simpl in H3.
        pose proof (modeC_prepend01_star 4 (w1 + 3) [] (prepend11_01 d R0)) as H4.
        pose proof (modeC_consume_11_01_nil d (w1 + 3 + 4) R0) as H5.
        rewrite HR0 in H5.
        pose proof (modeC_prepend01_star 2 (w1 + 3 + 4 + 4 * d) [] (const S0)) as H6.
        replace (w1 + 3 + 4 + 4 * d + 2) with (w1 + 4 * d + 9) in H6 by lia.
        exact (stepStar_stepPlus_stepPlus H1
          (stepPlus_stepPlus_stepPlus H2
            (stepPlus_stepStar_stepPlus H3 (stepStar_trans H4 (stepStar_trans H5 H6))))).
      * assert (Hne_rest : w2 :: rest' <> []) by discriminate.
        exists (w1 + d + 6), (add_last (w2 :: rest') (3 * d + 3)).
        split.
        -- rewrite Hw_split.
           pose proof (e0_loop_drain_pairs d 0 (w1 :: w2 :: rest') R0) as H1.
           pose proof (step_modeE0_loop_b011_10 (encL w1 (w2 :: rest')) (prepend11_01 d R0)) as H2.
           change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> prepend11_01 d R0))))
             with (prepend01 4 (prepend11_01 d R0)) in H2.
           pose proof (modeE1_to_modeC (w2 :: rest') w1 (prepend01 4 (prepend11_01 d R0)) Hval_rest) as H3.
           rewrite (bump_enc_nonempty w1 (w2 :: rest') Hne_rest) in H3; simpl in H3.
           pose proof (modeC_prepend01_star 4 w1 (add_last (w2 :: rest') 3) (prepend11_01 d R0)) as H4.
           pose proof (modeC_consume_11_01_nonempty d (w1 + 4) (add_last (w2 :: rest') 3) R0
             (add_last_ne_nil (w2 :: rest') 3 Hne_rest)
             (ValidKS_add_last (w2 :: rest') 3 Hval_rest)) as H5.
           rewrite add_last_add in H5.
           replace (3 + 3 * d) with (3 * d + 3) in H5 by lia.
           rewrite HR0 in H5.
           pose proof (modeC_prepend01_star 2 (w1 + 4 + d) (add_last (w2 :: rest') (3 * d + 3)) (const S0)) as H6.
           replace (w1 + 4 + d + 2) with (w1 + d + 6) in H6 by lia.
           exact (stepStar_stepPlus_stepPlus H1
             (stepPlus_stepPlus_stepPlus H2
               (stepPlus_stepStar_stepPlus H3 (stepStar_trans H4 (stepStar_trans H5 H6))))).
        -- right; split; [exact (add_last_ne_nil (w2 :: rest') (3 * d + 3) Hne_rest) |].
           destruct (Nat.eqb_spec (w1 + d + 6) 1); [lia |].
           apply GoodKS_add_last.
           eapply GoodKS_mono; [|exact Hgks_rest].
           unfold d in Hsw; lia.
    + assert (Hw_split : w0 = 1 + 2 * d) by lia.
      set (S_sub := 36 * (d + 4)).
      assert (HS_sub : S_sub >= 36) by (unfold S_sub; lia).
      assert (H2S_le : 2 * S_sub <= S_w + 63 * (w0 + 3)) by (unfold S_sub; unfold d in Hsw; lia).
      set (sub := bump_enc (w1 - 1) ws_rest).
      assert (Hsub_nil : snd sub = [] -> 2 * S_sub <= 35 * fst sub).
      { unfold sub, bump_enc; destruct ws_rest as [|y ys]; cbn [fst snd]; [intros _; unfold S_sub; lia |].
        intros Hemp; exfalso; exact (add_last_ne_nil (y :: ys) 3 ltac:(discriminate) Hemp). }
      assert (Hsub_cons : snd sub <> [] -> fst sub >= 2 /\ 2 * S_sub <= 35 * (fst sub + 3)).
      { unfold sub, bump_enc; destruct ws_rest as [|y ys]; cbn [fst snd]; [congruence | intros _; unfold S_sub; lia]. }
      assert (Hsub_gks : GoodKS (2 * S_sub + 63 * (fst sub + 3)) (snd sub)).
      { unfold sub, bump_enc; destruct ws_rest as [|y ys]; cbn [fst snd]; [exact I |].
        apply GoodKS_add_last.
        eapply GoodKS_mono; [|exact Hgks_rest]; lia. }
      set (R_tail := S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> prepend11_01 d R0).
      destruct (e0_loop_leave1_goodks (List.length (snd sub)) (fst sub) (snd sub) S_sub R_tail
        eq_refl HS_sub Hsub_nil Hsub_cons Hsub_gks)
        as [y0 [ys [Hstep_sub [Hval_ys [_ [Hgks_sub _]]]]]].
      set (py := bump_enc_twice y0 ys).
      set (ks_mid := (fst py + 1) :: snd py).
      assert (Hne_mid : ks_mid <> []) by discriminate.
      assert (Hval_mid : ValidKS ks_mid) by (apply (GoodKS_succ_valid S_sub (fst py) (snd py)); exact Hgks_sub).
      exists (d + 2), (add_last ks_mid (3 * d)).
      split.
      * rewrite Hw_split.
        pose proof (e0_loop_drain_pairs d 1 (w1 :: ws_rest) R0) as H1.
        assert (Hw1_eq : w1 = (w1 - 1) + 1) by lia.
        pose proof (step_modeE0_loop_b10_b011_10_b10_encL (w1 - 1) ws_rest (prepend11_01 d R0)) as H2.
        rewrite <- Hw1_eq in H2.
        fold R_tail in H2.
        pose proof (modeE1_to_modeC ws_rest (w1 - 1)
          (S0 >> S1 >> S0 >> S0 >> S0 >> R_tail) Hval_rest) as H3.
        fold sub in H3.
        pose proof (step_modeC_b01_b000 (encL (fst sub) (snd sub)) R_tail) as H4.
        pose proof (unwrap_11_01_1011101_step y0 ys (prepend11_01 d R0) Hval_ys) as H5.
        fold py in H5; fold ks_mid in H5.
        pose proof (modeC_consume_11_01_nonempty d 0 ks_mid R0 Hne_mid Hval_mid) as H6.
        replace (0 + d) with d in H6 by lia.
        rewrite HR0 in H6.
        pose proof (modeC_prepend01_star 2 d (add_last ks_mid (3 * d)) (const S0)) as H7.
        exact (stepStar_stepPlus_stepPlus H1
          (stepPlus_stepPlus_stepPlus H2
            (stepPlus_stepPlus_stepPlus H3
              (stepPlus_stepPlus_stepPlus H4
                (stepPlus_stepPlus_stepPlus Hstep_sub
                  (stepPlus_stepStar_stepPlus H5 (stepStar_trans H6 H7))))))).
      * right; split; [exact (add_last_ne_nil ks_mid (3 * d) Hne_mid) |].
        destruct (Nat.eqb_spec (d + 2) 1); [lia |].
        replace (36 * (d + 2 + 2)) with S_sub by (unfold S_sub; lia).
        exact (GoodKS_add_last ks_mid S_sub (3 * d) Hgks_sub).
Qed.

Lemma step_b01_b101_nil_to_e0_loop (p0 : nat) (ps : list nat) :
  ValidKS ps ->
  let w := bump_enc p0 ps in
  cfg_modeC (encL p0 ps) (S0 >> S1 >> S1 >> S0 >> S1 >> const S0)
    -[ holdout_0311_tm ]->+
    cfg_modeE0_loop (encL (fst w) (snd w)) (S0 >> S1 >> S0 >> S1 >> const S0).
Proof.
  intros Hval; cbv zeta.
  set (w := bump_enc p0 ps).
  pose proof (step_modeC_b01_b101_nil (encL p0 ps)) as H1.
  pose proof (modeE1_to_modeC ps p0
    (S0 >> S1 >> S0 >> S0 >> S0 >> (S0 >> S1 >> (S0 >> S1 >> const S0))) Hval) as H2.
  fold w in H2.
  pose proof (step_modeC_b01_b000 (encL (fst w) (snd w)) (S0 >> S1 >> S0 >> S1 >> const S0)) as H3.
  exact (stepPlus_stepPlus_stepPlus H1 (stepPlus_stepPlus_stepPlus H2 H3)).
Qed.

Lemma step_k0_zero (ks : list nat) :
  InvNil 0 ks ->
  exists k0' ks',
    (cfg_modeC (encL 0 ks) (const S0) -[ holdout_0311_tm ]->+ cfg_modeC (encL k0' ks') (const S0)) /\
    InvNil k0' ks'.
Proof.
  intros [[_ Hk5] | [Hne Hgks]]; [lia |].
  cbn [Nat.eqb] in Hgks.
  destruct ks as [|k1 ks_rest]; [congruence |].
  cbn [GoodKS] in Hgks; destruct Hgks as [Hk1_bound Hgks_rest].
  assert (Hk1_ge : k1 >= 1) by lia.
  replace (36 * (0 + 2)) with 72 in Hgks_rest by lia.
  pose proof (GoodKS_valid ks_rest (72 + 63 * (k1 + 2)) ltac:(lia) Hgks_rest) as Hval_rest.
  set (sub := bump_enc (k1 - 1) ks_rest).
  assert (Hto_sub : cfg_modeC (encL 0 (k1 :: ks_rest)) (const S0) -[ holdout_0311_tm ]->+
    cfg_modeE0_loop (encL (fst sub) (snd sub)) (S1 >> S0 >> S1 >> const S0)).
  { assert (Hk1_eq : k1 = (k1 - 1) + 1) by lia.
    pose proof (step_modeC_nil (encL 0 (k1 :: ks_rest))) as H1.
    pose proof (step_modeE0_first_b011_10_b10_encL (k1 - 1) ks_rest) as H2.
    rewrite <- Hk1_eq in H2.
    pose proof (modeE1_to_modeC ks_rest (k1 - 1)
      (S0 >> S1 >> S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> const S0)) Hval_rest) as H3.
    fold sub in H3.
    pose proof (step_modeC_b01_b000 (encL (fst sub) (snd sub)) (S1 >> S0 >> S1 >> const S0)) as H4.
    exact (stepPlus_stepPlus_stepPlus H1 (stepPlus_stepPlus_stepPlus H2 (stepPlus_stepPlus_stepPlus H3 H4))). }
  assert (H0a_dec : (ks_rest = [] \/ k1 >= 3) \/ (ks_rest <> [] /\ k1 < 3)).
  { destruct ks_rest as [|y ys]; [left; left; reflexivity |].
    destruct (Nat.leb_spec 3 k1); [left; right; lia | right; split; [discriminate | lia]]. }
  destruct H0a_dec as [H0a | [Hne_rest Hk1_lt3]].
  -  
    assert (Hsub_nil : snd sub = [] -> 2 * 36 <= 35 * fst sub).
    { unfold sub, bump_enc; destruct ks_rest as [|y ys]; cbn [fst snd]; [intros _; lia |].
      intros Hemp; exfalso; exact (add_last_ne_nil (y :: ys) 3 ltac:(discriminate) Hemp). }
    assert (Hsub_cons : snd sub <> [] -> fst sub >= 2 /\ 2 * 36 <= 35 * (fst sub + 3)).
    { unfold sub, bump_enc; destruct ks_rest as [|y ys]; cbn [fst snd]; [congruence |].
      destruct H0a as [Hemp | Hk3]; [congruence | intros _; lia]. }
    assert (Hsub_gks : GoodKS (2 * 36 + 63 * (fst sub + 3)) (snd sub)).
    { unfold sub, bump_enc; destruct ks_rest as [|y ys]; cbn [fst snd]; [exact I |].
      replace (2 * 36 + 63 * (k1 - 1 + 3)) with (72 + 63 * (k1 + 2)) by lia.
      exact (GoodKS_add_last (y :: ys) _ 3 Hgks_rest). }
    destruct (e0_loop_leave1_goodks (List.length (snd sub)) (fst sub) (snd sub) 36
      (S1 >> S0 >> S1 >> const S0) eq_refl ltac:(lia) Hsub_nil Hsub_cons Hsub_gks)
      as [m0 [ms [Hstep_l1 [Hval_ms [Hms_emp [Hgks_w _]]]]]].
    set (p1 := bump_enc m0 ms).
    set (w := bump_enc_twice m0 ms).
    assert (Hw_eq : w = bump_enc (fst p1) (snd p1)) by reflexivity.
    assert (Hc11 : cfg_modeC (encL m0 ms)
      (S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> S1 >> const S0)
      -[ holdout_0311_tm ]->+
      cfg_modeC (encL (fst p1) (snd p1)) (S0 >> S1 >> S1 >> S0 >> S1 >> const S0)).
    { exact (stepPlus_stepPlus_stepPlus
        (step_modeC_b11 (encL m0 ms) (S0 >> S1 >> S1 >> S0 >> S1 >> const S0))
        (modeE1_to_modeC ms m0 (S0 >> S1 >> S1 >> S0 >> S1 >> const S0) Hval_ms)). }
    pose proof (step_b01_b101_nil_to_e0_loop (fst p1) (snd p1) (ValidKS_bump_enc m0 ms Hval_ms)) as Hto_w.
    cbv zeta in Hto_w; rewrite <- Hw_eq in Hto_w.
    assert (Hw_empty : snd w = [] -> fst w >= 4).
    { destruct ms as [|u us].
      - intros _; unfold w, bump_enc_twice, bump_enc; cbn [fst snd]; lia.
      - intros Hemp; unfold w in Hemp;
        rewrite (bump_enc_twice_nonempty m0 (u :: us) ltac:(discriminate)) in Hemp; cbn [snd] in Hemp;
        exfalso; exact (add_last_ne_nil (u :: us) 6 ltac:(discriminate) Hemp). }
    assert (Hgks_ws : GoodKS (36 + 63 * (fst w + 3)) (snd w)).
    { cbv zeta in Hgks_w; fold w in Hgks_w; cbn [GoodKS] in Hgks_w.
      destruct Hgks_w as [_ H2].
      replace (36 + 63 * (fst w + 3)) with (36 + 63 * (fst w + 1 + 2)) by lia.
      exact H2. }
    destruct (e0_loop_drain_plus2 (fst w) (snd w) 36 Hw_empty ltac:(lia) Hgks_ws)
      as [k0' [ks' [Hdrain Hinv']]].
    exists k0', ks'; split; [|exact Hinv'].
    exact (stepPlus_stepPlus_stepPlus Hto_sub
      (stepPlus_stepPlus_stepPlus Hstep_l1
        (stepPlus_stepPlus_stepPlus Hc11
          (stepPlus_stepPlus_stepPlus Hto_w Hdrain)))).
  - destruct ks_rest as [|k2 ks_tail]; [congruence |].
    assert (Hk1_cases : k1 = 1 \/ k1 = 2) by lia.
    destruct Hk1_cases as [-> | ->].
    +  
      assert (Hsub_eq : sub = (0, add_last (k2 :: ks_tail) 3)) by reflexivity.
      replace (72 + 63 * (1 + 2)) with 261 in Hgks_rest by lia.
      pose proof (GoodKS_add_last (k2 :: ks_tail) 261 3 Hgks_rest) as Hgks_sub.
      destruct (add_last (k2 :: ks_tail) 3) as [|x1 xs_rest] eqn:Hal;
        [exfalso; exact (add_last_ne_nil (k2 :: ks_tail) 3 ltac:(discriminate) Hal) |].
      cbn [GoodKS] in Hgks_sub; destruct Hgks_sub as [Hx1_bound Hgks_xs].
      assert (Hx1_ge6 : x1 >= 6) by lia.
      pose proof (GoodKS_valid xs_rest (261 + 63 * (x1 + 2)) ltac:(lia) Hgks_xs) as Hval_xs.
      set (xb := bump_enc x1 xs_rest).
      set (p1 := (fst xb + 3, snd xb)).
      set (w := bump_enc (fst p1) (snd p1)).
      assert (Hstep_0b : cfg_modeE0_loop (encL 0 (x1 :: xs_rest)) (S1 >> S0 >> S1 >> const S0)
        -[ holdout_0311_tm ]->+
        cfg_modeC (encL (fst p1) (snd p1)) (S0 >> S1 >> S1 >> S0 >> S1 >> const S0)).
      { pose proof (step_modeE0_loop_b011_10 (encL x1 xs_rest) (S1 >> S0 >> S1 >> const S0)) as H1.
        change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S1 >> S0 >> S1 >> const S0)))))
          with (prepend01 3 (S0 >> S1 >> S1 >> S0 >> S1 >> const S0)) in H1.
        pose proof (modeE1_to_modeC xs_rest x1
          (prepend01 3 (S0 >> S1 >> S1 >> S0 >> S1 >> const S0)) Hval_xs) as H2.
        fold xb in H2.
        pose proof (modeC_prepend01_star 3 (fst xb) (snd xb) (S0 >> S1 >> S1 >> S0 >> S1 >> const S0)) as H3.
        exact (stepPlus_stepPlus_stepPlus H1 (stepPlus_stepStar_stepPlus H2 H3)). }
      assert (Hval_p1 : ValidKS (snd p1)) by (unfold p1; exact (ValidKS_bump_enc x1 xs_rest Hval_xs)).
      pose proof (step_b01_b101_nil_to_e0_loop (fst p1) (snd p1) Hval_p1) as Hto_w.
      cbv zeta in Hto_w; fold w in Hto_w.
      assert (Hw1_ge9 : fst w >= 9).
      { destruct xs_rest as [|y ys].
        - unfold w, p1, xb, bump_enc; cbn [fst snd]; lia.
        - assert (Hw_cons : w = (x1 + 3, add_last (y :: ys) 6)).
          { unfold w, p1, xb; cbn [fst snd bump_enc].
            rewrite (bump_enc_nonempty (x1 + 3) (add_last (y :: ys) 3)
              (add_last_ne_nil (y :: ys) 3 ltac:(discriminate))).
            rewrite add_last_add; reflexivity. }
          rewrite Hw_cons; cbn [fst]; lia. }
      assert (Hw_empty : snd w = [] -> fst w >= 4) by (intros _; lia).
      assert (Hsw9 : 36 <= 9 + 54 * (fst w / 2)) by lia.
      assert (Hgks_ws : GoodKS (9 + 63 * (fst w + 3)) (snd w)).
      { destruct xs_rest as [|y ys].
        - unfold w, p1, xb, bump_enc; cbn [fst snd GoodKS]; exact I.
        - assert (Hw_cons : w = (x1 + 3, add_last (y :: ys) 6)).
          { unfold w, p1, xb; cbn [fst snd bump_enc].
            rewrite (bump_enc_nonempty (x1 + 3) (add_last (y :: ys) 3)
              (add_last_ne_nil (y :: ys) 3 ltac:(discriminate))).
            rewrite add_last_add; reflexivity. }
          rewrite Hw_cons; cbn [fst snd].
          replace (9 + 63 * (x1 + 3 + 3)) with (261 + 63 * (x1 + 2)) by lia.
          exact (GoodKS_add_last (y :: ys) _ 6 Hgks_xs). }
      destruct (e0_loop_drain_plus2 (fst w) (snd w) 9 Hw_empty Hsw9 Hgks_ws)
        as [k0' [ks' [Hdrain Hinv']]].
      rewrite Hsub_eq in Hto_sub; cbn [fst snd] in Hto_sub.
      exists k0', ks'; split; [|exact Hinv'].
      exact (stepPlus_stepPlus_stepPlus Hto_sub
        (stepPlus_stepPlus_stepPlus Hstep_0b
          (stepPlus_stepPlus_stepPlus Hto_w Hdrain))).
    +  
      assert (Hsub_eq : sub = (1, add_last (k2 :: ks_tail) 3)) by reflexivity.
      replace (72 + 63 * (2 + 2)) with 324 in Hgks_rest by lia.
      pose proof (GoodKS_add_last (k2 :: ks_tail) 324 3 Hgks_rest) as Hgks_sub.
      destruct (add_last (k2 :: ks_tail) 3) as [|x1 xs_rest] eqn:Hal;
        [exfalso; exact (add_last_ne_nil (k2 :: ks_tail) 3 ltac:(discriminate) Hal) |].
      cbn [GoodKS] in Hgks_sub; destruct Hgks_sub as [Hx1_bound Hgks_xs].
      assert (Hx1_ge8 : x1 >= 8) by lia.
      pose proof (GoodKS_valid xs_rest (324 + 63 * (x1 + 2)) ltac:(lia) Hgks_xs) as Hval_xs.
      set (sub2 := bump_enc (x1 - 1) xs_rest).
      set (R_101 := S1 >> S0 >> S1 >> const S0).
      set (R_1011101_101 := S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> R_101).
      assert (Hstep1 : cfg_modeE0_loop (encL 1 (x1 :: xs_rest)) R_101 -[ holdout_0311_tm ]->+
        cfg_modeE0_loop (encL (fst sub2) (snd sub2)) R_1011101_101).
      { assert (Hx1_eq : x1 = (x1 - 1) + 1) by lia.
        pose proof (step_modeE0_loop_b10_b011_10_b10_encL (x1 - 1) xs_rest R_101) as H1.
        rewrite <- Hx1_eq in H1.
        fold R_1011101_101 in H1.
        pose proof (modeE1_to_modeC xs_rest (x1 - 1)
          (S0 >> S1 >> S0 >> S0 >> S0 >> R_1011101_101) Hval_xs) as H2.
        fold sub2 in H2.
        pose proof (step_modeC_b01_b000 (encL (fst sub2) (snd sub2)) R_1011101_101) as H3.
        exact (stepPlus_stepPlus_stepPlus H1 (stepPlus_stepPlus_stepPlus H2 H3)). }
      assert (Hsub2_nil : snd sub2 = [] -> 2 * 162 <= 35 * fst sub2).
      { unfold sub2, bump_enc; destruct xs_rest as [|y ys]; cbn [fst snd]; [intros _; lia |].
        intros Hemp; exfalso; exact (add_last_ne_nil (y :: ys) 3 ltac:(discriminate) Hemp). }
      assert (Hsub2_cons : snd sub2 <> [] -> fst sub2 >= 2 /\ 2 * 162 <= 35 * (fst sub2 + 3)).
      { unfold sub2, bump_enc; destruct xs_rest as [|y ys]; cbn [fst snd]; [congruence | intros _; lia]. }
      assert (Hsub2_gks : GoodKS (2 * 162 + 63 * (fst sub2 + 3)) (snd sub2)).
      { unfold sub2, bump_enc; destruct xs_rest as [|y ys]; cbn [fst snd]; [exact I |].
        replace (2 * 162 + 63 * (x1 - 1 + 3)) with (324 + 63 * (x1 + 2)) by lia.
        exact (GoodKS_add_last (y :: ys) _ 3 Hgks_xs). }
      destruct (e0_loop_leave1_goodks (List.length (snd sub2)) (fst sub2) (snd sub2) 162 R_1011101_101
        eq_refl ltac:(lia) Hsub2_nil Hsub2_cons Hsub2_gks)
        as [y0 [ys [Hstep_l2 [Hval_ys [Hys_emp [Hgks_z _]]]]]].
      pose proof (unwrap_11_01_1011101_step y0 ys R_101 Hval_ys) as Hunwrap2.
      cbv zeta in Hunwrap2, Hgks_z.
      set (pz := bump_enc_twice y0 ys) in *.
      set (z1 := fst pz + 1) in *.
      set (zs := snd pz) in *.
      cbn [GoodKS] in Hgks_z; destruct Hgks_z as [Hz1_bound Hgks_zs].
      assert (Hz1_ge3 : z1 >= 3) by lia.
      assert (Hzs_emp_z1 : zs = [] -> z1 >= 14).
      { destruct ys as [|u us].
        - pose proof (Hys_emp eq_refl) as Hy7.
          intros _; unfold z1, pz, bump_enc_twice, bump_enc; cbn [fst snd]; lia.
        - intros Hemp; unfold zs, pz in Hemp.
          rewrite (bump_enc_twice_nonempty y0 (u :: us) ltac:(discriminate)) in Hemp; cbn [snd] in Hemp.
          exfalso; exact (add_last_ne_nil (u :: us) 6 ltac:(discriminate) Hemp). }
      pose proof (GoodKS_valid zs (162 + 63 * (z1 + 2)) ltac:(lia) Hgks_zs) as Hval_zs.
      set (zb := bump_enc (z1 - 1) zs).
      set (w := bump_enc (fst zb) (snd zb)).
      set (R_0000101 := S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> const S0).
      set (R_101_01_01 := S1 >> S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> const S0))).
      assert (Hstep34 : cfg_modeC (encL 0 (z1 :: zs)) R_101 -[ holdout_0311_tm ]->+
        cfg_modeE0_loop (encL (fst w) (snd w)) R_101_01_01).
      { assert (Hz1_eq : z1 = (z1 - 1) + 1) by lia.
        pose proof (step_modeC_b01110_b10_b101_nil_encL (z1 - 1) zs) as HA.
        rewrite <- Hz1_eq in HA.
        fold R_101 in HA; fold R_0000101 in HA.
        pose proof (modeE1_to_modeC zs (z1 - 1)
          (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> R_0000101) Hval_zs) as HA2.
        fold zb in HA2.
        pose proof (step_modeC_b01_b10101_encL (fst zb) (snd zb) R_0000101) as HA3.
        pose proof (step_modeC_b01110_b10_b0000101_encL (fst zb) (snd zb) (const S0)) as HB.
        fold R_0000101 in HB; fold R_101_01_01 in HB.
        pose proof (modeE1_to_modeC (snd zb) (fst zb)
          (S0 >> S1 >> S0 >> S0 >> S0 >> R_101_01_01)
          (ValidKS_bump_enc (z1 - 1) zs Hval_zs)) as HB2.
        fold w in HB2.
        pose proof (step_modeC_b01_b000 (encL (fst w) (snd w)) R_101_01_01) as HB3.
        exact (stepPlus_stepPlus_stepPlus HA
          (stepPlus_stepPlus_stepPlus HA2
            (stepPlus_stepPlus_stepPlus HA3
              (stepPlus_stepPlus_stepPlus HB
                (stepPlus_stepPlus_stepPlus HB2 HB3))))). }
      assert (Hw_def : w = bump_enc_twice (z1 - 1) zs) by reflexivity.
      assert (Hw_nil : snd w = [] -> 2 * 81 <= 35 * fst w).
      { destruct zs as [|y ys'] eqn:Hzs.
        - pose proof (Hzs_emp_z1 eq_refl) as Hz14.
          assert (Hw_nil_eq : w = (z1 - 1 + 3 + 3, (@nil nat))) by (rewrite Hw_def; reflexivity).
          rewrite Hw_nil_eq; cbn [fst snd]; intros _; lia.
        - assert (Hw_cons_eq : w = (z1 - 1, add_last (y :: ys') 6))
            by (rewrite Hw_def; exact (bump_enc_twice_nonempty (z1 - 1) (y :: ys') ltac:(discriminate))).
          rewrite Hw_cons_eq; cbn [snd]; intros Hemp;
          exfalso; exact (add_last_ne_nil (y :: ys') 6 ltac:(discriminate) Hemp). }
      assert (Hw_ge10 : snd w = [] -> fst w >= 10).
      { destruct zs as [|y ys'] eqn:Hzs.
        - pose proof (Hzs_emp_z1 eq_refl) as Hz14.
          assert (Hw_nil_eq : w = (z1 - 1 + 3 + 3, (@nil nat))) by (rewrite Hw_def; reflexivity).
          rewrite Hw_nil_eq; cbn [fst snd]; intros _; lia.
        - assert (Hw_cons_eq : w = (z1 - 1, add_last (y :: ys') 6))
            by (rewrite Hw_def; exact (bump_enc_twice_nonempty (z1 - 1) (y :: ys') ltac:(discriminate))).
          rewrite Hw_cons_eq; cbn [snd]; intros Hemp;
          exfalso; exact (add_last_ne_nil (y :: ys') 6 ltac:(discriminate) Hemp). }
      assert (Hw_cons : snd w <> [] -> fst w >= 2 /\ 2 * 81 <= 35 * (fst w + 3)).
      { destruct zs as [|y ys'] eqn:Hzs.
        - assert (Hw_nil_eq : w = (z1 - 1 + 3 + 3, (@nil nat))) by (rewrite Hw_def; reflexivity).
          rewrite Hw_nil_eq; cbn [snd]; congruence.
        - assert (Hw_cons_eq : w = (z1 - 1, add_last (y :: ys') 6))
            by (rewrite Hw_def; exact (bump_enc_twice_nonempty (z1 - 1) (y :: ys') ltac:(discriminate))).
          rewrite Hw_cons_eq; cbn [fst snd]; intros _; lia. }
      assert (Hw_gks : GoodKS (2 * 81 + 63 * (fst w + 3)) (snd w)).
      { destruct zs as [|y ys'] eqn:Hzs.
        - assert (Hw_nil_eq : w = (z1 - 1 + 3 + 3, (@nil nat))) by (rewrite Hw_def; reflexivity).
          rewrite Hw_nil_eq; cbn [snd GoodKS]; exact I.
        - assert (Hw_cons_eq : w = (z1 - 1, add_last (y :: ys') 6))
            by (rewrite Hw_def; exact (bump_enc_twice_nonempty (z1 - 1) (y :: ys') ltac:(discriminate))).
          rewrite Hw_cons_eq; cbn [fst snd].
          replace (2 * 81 + 63 * (z1 - 1 + 3)) with (162 + 63 * (z1 + 2)) by lia.
          exact (GoodKS_add_last (y :: ys') _ 6 Hgks_zs). }
      destruct (e0_loop_leave1_goodks (List.length (snd w)) (fst w) (snd w) 81 R_101_01_01
        eq_refl ltac:(lia) Hw_nil Hw_cons Hw_gks)
        as [m0 [ms [Hstep_l5 [Hval_ms [_ [_ Hgks_81_fn]]]]]].
      pose proof (Hgks_81_fn Hw_ge10 eq_refl) as Hgks_b1.
      cbv zeta in Hgks_b1.
      set (b1 := bump_enc m0 ms) in *.
      assert (Hstep6 : cfg_modeC (encL m0 ms)
        (S1 >> S1 >> S0 >> S1 >> R_101_01_01) -[ holdout_0311_tm ]->+
        cfg_modeC (encL 1 ((fst b1 + 1) :: snd b1)) (const S0)).
      { pose proof (step_modeC_b11 (encL m0 ms) (S0 >> S1 >> R_101_01_01)) as H1.
        pose proof (modeE1_to_modeC ms m0 (S0 >> S1 >> R_101_01_01) Hval_ms) as H2.
        fold b1 in H2.
        pose proof (step_modeC_b01_b10101_encL (fst b1) (snd b1)
          (S0 >> S1 >> const S0)) as H3.
        pose proof (step_modeC_b01_encL 0 ((fst b1 + 1) :: snd b1) (const S0)) as H4; simpl in H4.
        exact (stepPlus_stepPlus_stepPlus H1
          (stepPlus_stepPlus_stepPlus H2
            (stepPlus_stepPlus_stepPlus H3 H4))). }
      rewrite Hsub_eq in Hto_sub; cbn [fst snd] in Hto_sub.
      fold R_101 in Hto_sub.
      exists 1, ((fst b1 + 1) :: snd b1).
      split.
      * exact (stepPlus_stepPlus_stepPlus Hto_sub
          (stepPlus_stepPlus_stepPlus Hstep1
            (stepPlus_stepPlus_stepPlus Hstep_l2
              (stepPlus_stepPlus_stepPlus Hunwrap2
                (stepPlus_stepPlus_stepPlus Hstep34
                  (stepPlus_stepPlus_stepPlus Hstep_l5 Hstep6)))))).
      * right; split; [discriminate | exact Hgks_b1].
Qed.

Notation Inv := TM3.Inv.

Lemma init_reaches_inv :
  exists c, (c0 -[ holdout_0311_tm ]->+ c) /\ Inv c.
Proof.
  pose proof init_reaches_modeC as H0.
  change (S0 >> S1 >> const S0) with (encL 0 []) in H0.
  assert (H1 : cfg_modeC (encL 0 []) (const S0) -[ holdout_0311_tm ]->+ cfg_modeC (encL 3 []) (const S0)).
  { pose proof (step_modeC_nil (encL 0 [])) as Ha.
    pose proof step_modeE0_first_base as Hb.
    change (S0 >> S1 >> const S0) with (encL 0 []) in Hb.
    change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> const S0))) with (prepend01 3 (const S0)) in Hb.
    pose proof (modeC_prepend01_star 3 0 [] (const S0)) as Hc; simpl in Hc.
    exact (stepPlus_stepPlus_stepPlus Ha (stepPlus_stepStar_stepPlus Hb Hc)). }
  assert (H2 : cfg_modeC (encL 3 []) (const S0) -[ holdout_0311_tm ]->+ cfg_modeC (encL 2 [3]) (const S0)).
  { pose proof (step_modeC_nil (encL 3 [])) as Ha.
    pose proof (step_modeE0_first_b10 (encL 2 [])) as Hb.
    pose proof (step_modeE0_loop_b10_b10 (encL 0 []) (const S0)) as Hc.
    change (S1 >> S1 >> (S0 >> S1 >> const S0)) with (prepend11_01 1 (const S0)) in Hc.
    pose proof (step_modeE0_loop_base (prepend11_01 1 (const S0))) as Hd.
    change (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0)) with (encL 0 [0]) in Hd.
    pose proof (step_modeC_b01_encL 0 [0] (prepend11_01 1 (const S0))) as He; simpl in He.
    pose proof (modeC_consume_11_01_nonempty 1 1 [0] (const S0) ltac:(discriminate) I) as Hf.
    cbn [add_last] in Hf; simpl in Hf.
    exact (stepPlus_stepPlus_stepPlus Ha
      (stepPlus_stepPlus_stepPlus Hb
        (stepPlus_stepPlus_stepPlus Hc
          (stepPlus_stepPlus_stepPlus Hd
            (stepPlus_stepStar_stepPlus He Hf))))). }
  assert (Hinv : InvNil 2 [3]).
  { right; split; [discriminate | cbn [Nat.eqb GoodKS]; split; [lia | exact I]]. }
  exists (cfg_modeC (encL 2 [3]) (const S0)).
  split.
  - exact (stepPlus_stepPlus_stepPlus H0 (stepPlus_stepPlus_stepPlus H1 H2)).
  - exists 2, [3]; exact (conj eq_refl Hinv).
Qed.

Lemma inv_step :
  forall c, Inv c -> exists c', Inv c' /\ (c -[ holdout_0311_tm ]->+ c').
Proof.
  intros c [k0 [ks [-> Hinv]]].
  destruct k0 as [|k0'].
  - destruct (step_k0_zero ks Hinv) as [k0' [ks' [Hstep Hinv']]].
    exists (cfg_modeC (encL k0' ks') (const S0)).
    split; [exists k0', ks'; exact (conj eq_refl Hinv') | exact Hstep].
  - destruct (step_k0_pos (S k0') ks ltac:(lia) Hinv) as [k0'' [ks'' [Hstep Hinv']]].
    exists (cfg_modeC (encL k0'' ks'') (const S0)).
    split; [exists k0'', ks''; exact (conj eq_refl Hinv') | exact Hstep].
Qed.

Definition sigma_EFDBAC (q : Q) : Q :=
  match q with
  | A => E | B => F | C => D | D => B | E => A | F => C
  end.

Lemma perm_311_128 : Perm holdout_0311_tm (flip tm) sigma_EFDBAC.
Proof.
  split.
  - intros [] [] H; vm_compute in H; try discriminate; vm_compute; reflexivity.
  - intros [] [] s' d q' H; vm_compute in H; inversion H; subst; vm_compute; reflexivity.
Qed.

Lemma init_reaches_conj_inv_128 :
  c0 -[ tm ]->+ (D;; (const S0) {{S0}} (encL 8 [])).
Proof.
  eapply (run_local_plus_eq tm 177
    (mkLocalState [S0; S0; S0; S0; S0; S0; S0]
                  [S0; S0; S0; S0; S0; S0; S0; S0; S0; S0; S0; S0; S0] A R)
    _ _ _ (const S0) (const S0));
  [ cbv; reflexivity | norm_cfg | unfold encL, encL_tail, prepend10; norm_cfg ].
Qed.

Theorem nonhalt: ~ halts tm c0.
Proof.
  eapply multistep_nonhalt; [exact (stepPlus_stepStar init_reaches_conj_inv_128) |].
  intros Hhalt; apply flip_halts in Hhalt; revert Hhalt.
  change (flip_conf (D;; (const S0) {{S0}} (encL 8 [])))
    with (sigma_EFDBAC C;; (encL 8 []) {{S0}} (const S0)).
  eapply (perm_nonhalt' holdout_0311_tm (flip tm) sigma_EFDBAC C ((encL 8 []) {{S0}} (const S0)) perm_311_128).
  change (C;; (encL 8 []) {{S0}} (const S0)) with (cfg_modeC (encL 7 []) (const S0)).
  eapply progress_nonhalt; [exact inv_step |].
  exists 7, (@nil nat); split; [reflexivity | left; split; [reflexivity | lia]].
Qed.

End TM4.
Print Assumptions TM4.nonhalt.
