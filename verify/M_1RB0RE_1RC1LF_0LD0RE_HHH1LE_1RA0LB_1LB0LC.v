(* 1RB0RE_1RC1LF_0LD0RE_---1LE_1RA0LB_1LB0LC never halts. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Lia ZifyNat ZifyN PeanoNat NArith String List.
Import ListNotations.

Open Scope list.
Open Scope sym.

Definition tm := Eval compute in
  (TM_from_str "1RB0RE_1RC1LF_0LD0RE_---1LE_1RA0LB_1LB0LC").

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

(* ---------- Section 1: Tape power conversion lemmas ---------- *)

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

(* ---------- Section 2: Core shift lemmas ---------- *)

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

(* ---------- Section 3: Bounce lemmas & Rule 1 ---------- *)

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

(* ---------- Section 4: Initial sweep & local half-steps ---------- *)

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

(* ---------- Section 5: Rule 2 & c = 2 transitions ---------- *)

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

(* ---------- Section 6: c = 1 even & odd transitions ---------- *)

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

(* ---------- Section 7: Stem (c0 -> P a0 81) & full macro-cycle ---------- *)

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

(* ---------- Section 8: Top-level non-halting theorem ---------- *)

Definition Hub (s : nat * nat) : Q * tape :=
  let '(a, j) := s in P a j.

Lemma nonhalt : ~ halts tm c0.
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

Print Assumptions nonhalt.
