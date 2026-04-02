Require Import Arith Lia PeanoNat Bool FunInd Recdef.

Function v2 (n : nat) {measure id n} : nat :=
  match n with
  | 0 => 0
  | _ => if Nat.even n then S (v2 (Nat.div2 n)) else 0
  end.
Proof.
  intros n n0 -> _.
  unfold id.
  apply Nat.lt_div2.
  lia.
Qed.

Fixpoint T (m : nat) : nat :=
  match m with
  | 0 => 0
  | S k => T k + 2 ^ v2 (S k)
  end.

Section BMO3.

Variable a : nat -> nat.
Hypothesis a_ini : a 0 = 2.
Hypothesis a_rec : forall n, a (S n) = a n + 2 ^ (v2 (a n) + 2) - 1.

Lemma v2_0 : v2 0 = 0.
Proof.
  rewrite v2_equation.
  reflexivity.
Qed.

Lemma v2_odd (n : nat) : v2 (S (2 * n)) = 0.
Proof.
  rewrite v2_equation.
  replace (S (2 * n)) with (2 * n + 1) by lia.
  rewrite Nat.even_odd.
  reflexivity.
Qed.

Lemma v2_even_double (n : nat) : v2 (2 * S n) = S (v2 (S n)).
Proof.
  rewrite v2_equation.
  rewrite Nat.even_even, Nat.div2_double.
  reflexivity.
Qed.

Lemma problem3_lower_bound : forall n, 3 * n + 2 <= a n.
Proof.
  intro n.
  induction n as [|n ihn].
  - rewrite a_ini.
    lia.
  - rewrite a_rec.
    assert (4 <= 2 ^ (v2 (a n) + 2)).
    { replace 4 with (2 ^ 2) by reflexivity.
      apply Nat.pow_le_mono_r.
      - lia.
      - lia. }
    lia.
Qed.

Lemma problem3_even_iff : forall n, Nat.Even (a n) <-> Nat.Even n.
Proof.
  intro n.
  assert (forall m, Nat.even (a m) = Nat.even m) as hbool.
  { intro m.
    induction m as [|m ihm].
    - rewrite a_ini.
      reflexivity.
    - rewrite a_rec.
      rewrite Nat.even_sub.
      + rewrite Nat.even_add.
        rewrite Nat.even_pow by lia.
        rewrite Nat.even_2.
        rewrite Nat.even_1.
        rewrite Nat.even_succ.
        rewrite <- Nat.negb_even.
        rewrite ihm.
        destruct (Nat.even m); reflexivity.
      + assert (1 <= 2 ^ (v2 (a m) + 2)).
        { apply Nat.pow_lower_bound. lia. }
        lia. }
  rewrite <- Nat.even_spec.
  rewrite <- Nat.even_spec.
  rewrite hbool.
  reflexivity.
Qed.

Lemma even_double_div2 (n : nat) : Nat.Even n -> n = 2 * Nat.div2 n.
Proof.
  intro hn.
  apply Nat.Even_double in hn.
  rewrite Nat.double_twice in hn.
  exact hn.
Qed.

Lemma v2_even_pos (n : nat) (hn : n <> 0) :
  Nat.Even n -> v2 n = S (v2 (Nat.div2 n)).
Proof.
  intro he.
  destruct n as [|n].
  - contradiction.
  - rewrite v2_equation.
    apply Nat.even_spec in he.
    rewrite he.
    reflexivity.
Qed.

Lemma v2_odd_nonzero (n : nat) (hn : n <> 0) :
  Nat.Odd n -> v2 n = 0.
Proof.
  intro ho.
  destruct n as [|n].
  - contradiction.
  - rewrite v2_equation.
    destruct (Nat.even (S n)) eqn:he.
    + exfalso.
      apply Nat.even_spec in he.
      apply Nat.Even_Odd_False with (x := S n); assumption.
    + reflexivity.
Qed.

Lemma v2_eq0_odd (n : nat) (hn : n <> 0) :
  v2 n = 0 -> Nat.Odd n.
Proof.
  intro hv.
  destruct (Nat.Even_Odd_dec n) as [he|ho].
  - rewrite (v2_even_pos n hn he) in hv.
    discriminate.
  - exact ho.
Qed.

Lemma v2_pos_even (n r : nat) (hn : n <> 0) :
  v2 n = S r -> Nat.Even n.
Proof.
  intro hv.
  destruct (Nat.Even_Odd_dec n) as [he|ho].
  - exact he.
  - rewrite v2_odd_nonzero in hv by assumption.
    discriminate.
Qed.

Lemma div2_nonzero_of_v2_pos (n r : nat) (hn : n <> 0) :
  v2 n = S r -> Nat.div2 n <> 0.
Proof.
  intro hv.
  assert (he : Nat.Even n) by (apply v2_pos_even with (r := r); assumption).
  intro hdiv.
  pose proof (even_double_div2 n he) as hn'.
  rewrite hdiv in hn'.
  lia.
Qed.

Lemma v2_div2_eq (n r : nat) (hn : n <> 0) :
  v2 n = S r -> v2 (Nat.div2 n) = r.
Proof.
  intro hv.
  assert (he : Nat.Even n) by (apply v2_pos_even with (r := r); assumption).
  rewrite (v2_even_pos n hn he) in hv.
  inversion hv.
  reflexivity.
Qed.

Lemma v2_double_pos (n : nat) (hn : n <> 0) : v2 (2 * n) = S (v2 n).
Proof.
  destruct n as [|n].
  - contradiction.
  - rewrite v2_equation.
    rewrite Nat.even_even, Nat.div2_double.
    reflexivity.
Qed.

Lemma v2_lower_bound_pos : forall m, m <> 0 -> 2 ^ v2 m <= m.
Proof.
  intro m.
  pattern m.
  apply lt_wf_ind.
  intros n ih hm.
  destruct n as [|n].
  - contradiction.
  - rewrite v2_equation.
    destruct (Nat.even (S n)) eqn:he.
    + replace (2 ^ S (v2 (Nat.div2 (S n)))) with
        (2 * 2 ^ v2 (Nat.div2 (S n))) by (simpl; lia).
      assert (hdiv : Nat.div2 (S n) <> 0).
      { intro h0.
        apply Nat.even_spec in he.
        pose proof (even_double_div2 (S n) he) as hn'.
        rewrite h0 in hn'.
        lia. }
      specialize (ih (Nat.div2 (S n))).
      assert (hlt : Nat.div2 (S n) < S n).
      { apply Nat.lt_div2. lia. }
      specialize (ih hlt hdiv).
      apply Nat.even_spec in he.
      rewrite (even_double_div2 (S n) he).
      rewrite Nat.div2_double.
      apply Nat.mul_le_mono_l.
      exact ih.
    + simpl.
      lia.
Qed.

Lemma v2_pow2 : forall k, v2 (2 ^ k) = k.
Proof.
  induction k as [|k ih].
  - simpl.
    apply v2_odd_nonzero; [lia|].
    exists 0.
    reflexivity.
  - rewrite Nat.pow_succ_r' by lia.
    rewrite v2_double_pos.
    + rewrite ih.
      reflexivity.
    + apply Nat.pow_nonzero.
      lia.
Qed.

Lemma T_double (m : nat) : T (2 * m) = m + 2 * T m.
Proof.
  induction m as [|m ihm].
  - reflexivity.
  - replace (2 * S m) with (S (S (2 * m))) by lia.
    simpl.
    replace (m + (m + 0)) with (2 * m) by lia.
    replace (S (S (m + (m + 0)))) with (2 * S m) by lia.
    assert (hvodd : v2 (S (2 * m)) = 0) by apply v2_odd.
    rewrite hvodd, Nat.pow_0_r.
    replace (T (S (2 * m))) with (T (2 * m) + 1).
    2:{ simpl.
        replace (m + (m + 0)) with (2 * m) by lia.
        rewrite hvodd, Nat.pow_0_r.
        lia. }
    rewrite ihm.
    simpl.
    replace (S (S (m + (m + 0)))) with (2 * S m) by lia.
    replace (v2 (2 * S m)) with (S (v2 (S m))).
    2:{ symmetry.
        apply v2_double_pos.
        lia. }
    replace (2 ^ S (v2 (S m))) with (2 * 2 ^ v2 (S m)) by (simpl; lia).
    ring_simplify.
    reflexivity.
Qed.

Definition F (m : nat) : nat := m + 1 + 4 * T m.

Lemma F_pos (m : nat) : F m <> 0.
Proof.
  unfold F.
  lia.
Qed.

Lemma F_succ (m : nat) : F (S m) = F m + 2 ^ (v2 (S m) + 2) + 1.
Proof.
  unfold F.
  simpl.
  replace (2 ^ (v2 (S m) + 2)) with (4 * 2 ^ v2 (S m)).
  2:{ replace (v2 (S m) + 2) with (S (S (v2 (S m)))) by lia.
      simpl.
      lia. }
  ring_simplify.
  reflexivity.
Qed.

Lemma F_even_shape (m : nat) : F (2 * m) = 2 * (3 * m + 4 * T m) + 1.
Proof.
  unfold F.
  rewrite T_double.
  lia.
Qed.

Lemma F_odd_shape (m : nat) : F (S (2 * m)) = 2 * (2 * (S m) + F m).
Proof.
  unfold F.
  simpl.
  replace (m + (m + 0)) with (2 * m) by lia.
  rewrite v2_odd, Nat.pow_0_r, T_double.
  lia.
Qed.

Lemma v2_same_plus_double :
  forall r x y,
    x <> 0 ->
    y <> 0 ->
    v2 x = r ->
    v2 y = r ->
    v2 (2 * x + y) = r.
Proof.
  induction r as [|r ihr]; intros x y hx hy hvx hvy.
  - apply v2_eq0_odd in hvx as hox; [|exact hx].
    apply v2_eq0_odd in hvy as hoy; [|exact hy].
    apply v2_odd_nonzero.
    + lia.
    + apply Nat.Odd_add_r.
      * exists x.
        reflexivity.
      * exact hoy.
  - assert (hex : Nat.Even x) by (apply v2_pos_even with (r := r); assumption).
    assert (hey : Nat.Even y) by (apply v2_pos_even with (r := r); assumption).
    assert (hxdiv : v2 (Nat.div2 x) = r).
    { apply v2_div2_eq with (n := x); assumption. }
    assert (hydiv : v2 (Nat.div2 y) = r).
    { apply v2_div2_eq with (n := y); assumption. }
    assert (hx0 : Nat.div2 x <> 0).
    { apply div2_nonzero_of_v2_pos with (n := x) (r := r); assumption. }
    assert (hy0 : Nat.div2 y <> 0).
    { apply div2_nonzero_of_v2_pos with (n := y) (r := r); assumption. }
    replace (2 * x + y) with (2 * (2 * Nat.div2 x + Nat.div2 y)).
    2:{ set (dx := Nat.div2 x).
        set (dy := Nat.div2 y).
        assert (hxeq : x = 2 * dx).
        { subst dx. apply even_double_div2. exact hex. }
        assert (hyeq : y = 2 * dy).
        { subst dy. apply even_double_div2. exact hey. }
        rewrite hxeq, hyeq.
        ring_simplify.
        reflexivity. }
    assert (hinner : 2 * Nat.div2 x + Nat.div2 y <> 0).
    { intro h.
      destruct (Nat.div2 y) as [|k] eqn:hyv.
      - exfalso.
        apply hy0.
        reflexivity.
      - exfalso.
        replace (2 * Nat.div2 x + S k) with (S (2 * Nat.div2 x + k)) in h by lia.
        discriminate. }
    rewrite (v2_double_pos _ hinner).
    apply f_equal.
    apply ihr; assumption.
Qed.

Lemma F_v2 : forall m, v2 (F m) = v2 (m + 1).
Proof.
  intro m.
  pattern m.
  apply lt_wf_ind.
  intros n ih.
  destruct (Nat.Even_Odd_dec n) as [he|ho].
  - destruct he as [q hq].
    subst n.
    rewrite F_even_shape.
    replace (2 * (3 * q + 4 * T q) + 1) with (S (2 * (3 * q + 4 * T q))) by lia.
    rewrite v2_odd.
    replace (2 * q + 1) with (S (2 * q)) by lia.
    symmetry.
    apply v2_odd.
  - destruct ho as [q hq].
    subst n.
    replace (2 * q + 1) with (S (2 * q)) by lia.
    rewrite F_odd_shape.
    rewrite v2_double_pos by (unfold F; lia).
    assert (hq_lt : q < 2 * q + 1) by lia.
    specialize (ih q hq_lt).
    replace (S (2 * q) + 1) with (2 * (S q)) by lia.
    rewrite v2_double_pos by lia.
    apply f_equal.
    apply v2_same_plus_double with (x := S q) (y := F q).
    + lia.
    + apply F_pos.
    + reflexivity.
    + replace (q + 1) with (S q) in ih by lia.
      exact ih.
Qed.

Lemma a_odd_double (m : nat) : Nat.Odd (a (S (2 * m))).
Proof.
  destruct (Nat.Even_Odd_dec (a (S (2 * m)))) as [he|ho].
  - exfalso.
    apply (proj1 (problem3_even_iff (S (2 * m)))) in he.
    apply Nat.Even_succ in he.
    apply Nat.Even_Odd_False with (x := 2 * m).
    + exists m.
      reflexivity.
    + exact he.
  - exact ho.
Qed.

Lemma a_even_formula : forall m, a (2 * m) = 2 * F m.
Proof.
  intro m.
  induction m as [|m ihm].
  - unfold F.
    simpl.
    rewrite a_ini.
    reflexivity.
  - assert (hval_even : v2 (a (2 * m)) = S (v2 (S m))).
    { rewrite ihm.
      rewrite v2_double_pos by apply F_pos.
      rewrite F_v2.
      replace (m + 1) with (S m) by lia.
      reflexivity. }
    assert (hstep : a (S (2 * m)) = 2 * F m + 2 ^ (S (v2 (S m)) + 2) - 1).
    { rewrite a_rec.
      rewrite hval_even.
      rewrite ihm.
      reflexivity. }
    replace (2 * S m) with (S (S (2 * m))) by lia.
    rewrite a_rec.
    rewrite hstep.
    replace (v2 (2 * F m + 2 ^ (S (v2 (S m)) + 2) - 1)) with 0.
    2:{ rewrite <- hstep.
        symmetry.
        apply v2_odd_nonzero.
        - pose proof (problem3_lower_bound (S (2 * m))).
          lia.
        - apply a_odd_double. }
    simpl.
    replace (2 ^ (S (v2 (S m)) + 2)) with (2 * 2 ^ (v2 (S m) + 2)).
    2:{ replace (S (v2 (S m)) + 2) with (S (v2 (S m) + 2)) by lia.
        simpl.
        lia. }
    set (p := 2 ^ (v2 (S m) + 2)).
    assert (hf : 1 <= F m).
    { destruct (F m) eqn:hfm.
      - exfalso.
        apply (F_pos m).
        exact hfm.
      - lia. }
    assert (hp : 1 <= p).
    { subst p.
      apply Nat.pow_lower_bound.
      lia. }
    replace
      (F m + (F m + 0) + (p + (p + 0)) - 1 + 4 - 1)
      with (F m + (F m + 0) + (p + (p + 0)) + 2) by lia.
    replace
      (F m + (F m + 0) + (p + (p + 0)) + 2)
      with (2 * F m + 2 * p + 2) by nia.
    replace (2 * F m + 2 * p + 2) with (2 * F (S m)).
    2:{ subst p.
        rewrite F_succ.
        nia. }
    reflexivity.
Qed.

Lemma problem3_v2_eq :
  forall n, Nat.Even n -> v2 (a n) = v2 (n + 2).
Proof.
  intros n hn.
  destruct hn as [m hm].
  subst n.
  rewrite a_even_formula.
  rewrite v2_double_pos by apply F_pos.
  rewrite F_v2.
  replace (2 * m + 2) with (2 * (m + 1)) by lia.
  rewrite v2_double_pos by lia.
  reflexivity.
Qed.

Lemma v2_pow4 (k : nat) : v2 (4 ^ k) = 2 * k.
Proof.
  replace 4 with (2 ^ 2) by reflexivity.
  rewrite <- Nat.pow_mul_r.
  simpl.
  apply v2_pow2.
Qed.

Theorem beaver_math_olympiad_problem_3 :
  ~ exists n k, a n = 4 ^ k.
Proof.
  intros [n [k hk]].
  destruct k as [|k].
  - rewrite Nat.pow_0_r in hk.
    assert (2 <= a n).
    { apply Nat.le_trans with (m := 3 * n + 2).
      - lia.
      - apply problem3_lower_bound. }
    rewrite hk in H.
    lia.
  - destruct k as [|k].
    + destruct n as [|n].
      * rewrite a_ini in hk.
        discriminate.
      * assert (5 <= a (S n)).
        { apply Nat.le_trans with (m := 3 * S n + 2).
          - lia.
          - apply problem3_lower_bound. }
        rewrite hk in H.
        simpl in H.
        lia.
    + assert (Nat.Even (a n)) as h_even_an.
      { rewrite hk.
        rewrite <- Nat.even_spec.
        rewrite Nat.even_pow by lia.
        reflexivity. }
      assert (Nat.Even n) as h_even_n.
      { apply (proj1 (problem3_even_iff n)).
        exact h_even_an. }
      assert (v2 (a n) = 2 * S (S k)) as hv2_an.
      { rewrite hk.
        apply v2_pow4.
      }
      pose proof (problem3_v2_eq n h_even_n) as hv2_eq.
      assert (v2 (n + 2) = 2 * S (S k)) as hv2_n.
      { rewrite <- hv2_eq.
        exact hv2_an. }
      assert (2 ^ (2 * S (S k)) <= n + 2) as hn2.
      { pose proof (v2_lower_bound_pos (n + 2)) as hbound.
        specialize (hbound ltac:(lia)).
        rewrite hv2_n in hbound.
        exact hbound. }
      replace (2 ^ (2 * S (S k))) with (4 ^ S (S k)) in hn2.
      2:{ rewrite Nat.pow_mul_r.
          simpl.
          reflexivity. }
      assert (4 ^ S (S k) - 2 <= n) by lia.
      assert (3 * (4 ^ S (S k) - 2) + 2 <= a n).
      { apply Nat.le_trans with (m := 3 * n + 2).
        - nia.
        - apply problem3_lower_bound. }
      set (m := 4 ^ S (S k)) in *.
      assert (4 <= m) as hm_ge4.
      { subst m.
        rewrite Nat.pow_succ_r'.
        apply Nat.le_mul_r.
        apply Nat.pow_nonzero.
        lia. }
      rewrite hk in H0.
      lia.
Qed.

End BMO3.



Require Import Arith Lia PeanoNat Bool Relations.

Fixpoint bmo3 (n : nat) : nat :=
  match n with
  | 0 => 2
  | S k => bmo3 k + 2 ^ (v2 (bmo3 k) + 2) - 1
  end.

Lemma bmo3_ini : bmo3 0 = 2.
Proof.
  reflexivity.
Qed.

Lemma bmo3_rec : forall n, bmo3 (S n) = bmo3 n + 2 ^ (v2 (bmo3 n) + 2) - 1.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem bmo3_no_pow4 :
  ~ exists n k, bmo3 n = 4 ^ k.
Proof.
  apply beaver_math_olympiad_problem_3.
  - exact bmo3_ini.
  - exact bmo3_rec.
Qed.

Definition state := (bool * nat * nat)%type.

Inductive rev_step : state -> state -> Prop :=
| Inc tp len n m :
    m + 2 < 2 ^ (len + 1) ->
    rev_step
      (tp, len + 2 + n, ((m + 2) * 2 + 1) * 2 ^ n)
      (negb tp, len + 2 + n, (m * 2 + 1) * 2 ^ n + 1)
| Ov1 tp len n :
    rev_step
      (tp, len + 2 + n, (0 * 2 + 1) * 2 ^ n)
      (negb tp, len + 4 + n, (12 * 2 ^ len - 3) * 2 ^ n + 1)
| Ov2 tp len n :
    rev_step
      (tp, len + 3 + n, (1 * 2 + 1) * 2 ^ (S n))
      (negb tp, len + 5 + n, (12 * 2 ^ len - 1) * 2 ^ (S n) + 1).

Inductive steps : nat -> state -> state -> Prop :=
| steps_0 s : steps 0 s s
| steps_S n s t u :
    rev_step s t ->
    steps n t u ->
    steps (S n) s u.

Fixpoint counter_len (k : nat) : nat :=
  match k with
  | 0 => 4
  | S j =>
      let l := counter_len j in
      if Nat.ltb (bmo3 (S (S j))) (2 ^ l) then l else l + 2
  end.

Definition counter_state (k : nat) : state :=
  (Nat.even (S k), counter_len k, 2 ^ counter_len k - bmo3 (S k)).

Lemma counter_len_even : forall k, Nat.Even (counter_len k).
Proof.
  induction k as [|k ih].
  - exists 2.
    reflexivity.
  - unfold counter_len at 1.
    fold counter_len.
    destruct (Nat.ltb (bmo3 (S (S k))) (2 ^ counter_len k)) eqn:hlt.
    + exact ih.
    + destruct ih as [q hq].
      exists (S q).
      lia.
Qed.

Lemma bmo3_pos : forall n, bmo3 n <> 0.
Proof.
  intro n.
  destruct n as [|n].
  - rewrite bmo3_ini.
    discriminate.
  - intro h0.
    pose proof (problem3_lower_bound bmo3 bmo3_ini bmo3_rec (S n)) as h.
    rewrite h0 in h.
    lia.
Qed.

Lemma bmo3_not_pow2_succ :
  forall k p, bmo3 (S k) <> 2 ^ p.
Proof.
  intros k p hp.
  destruct (Nat.even p) eqn:hp_even.
  - apply Nat.even_spec in hp_even.
    destruct hp_even as [q hq].
    apply bmo3_no_pow4.
    exists (S k), q.
    rewrite hp.
    rewrite hq.
    replace (2 ^ (2 * q)) with (4 ^ q).
    2:{ rewrite Nat.pow_mul_r.
        simpl.
        reflexivity. }
    reflexivity.
  - assert (Nat.Even (bmo3 (S k))) as hb_even.
    { rewrite hp.
      rewrite <- Nat.even_spec.
      destruct p as [|p].
      - discriminate.
      - rewrite Nat.pow_succ_r' by lia.
        rewrite Nat.even_mul.
        rewrite Nat.even_2.
        simpl.
        reflexivity. }
    pose proof (proj1 (problem3_even_iff bmo3 bmo3_ini bmo3_rec (S k)) hb_even) as hk_even.
    assert (hv2a : v2 (bmo3 (S k)) = p).
    { rewrite hp.
      exact (v2_pow2 bmo3 bmo3_ini p). }
    assert (hv2n : v2 (S k + 2) = p).
    { pose proof (problem3_v2_eq bmo3 bmo3_ini bmo3_rec (S k) hk_even) as h.
      rewrite hv2a in h.
      symmetry.
      exact h. }
    assert (2 ^ p <= S k + 2).
    { pose proof (v2_lower_bound_pos bmo3 bmo3_ini (S k + 2)) as h.
      specialize (h ltac:(lia)).
      rewrite hv2n in h.
      exact h. }
    pose proof (problem3_lower_bound bmo3 bmo3_ini bmo3_rec (S k)) as hlow.
    rewrite hp in hlow.
    lia.
Qed.

Lemma v2_factor_odd :
  forall n, n <> 0 -> exists q, Nat.Odd q /\ n = q * 2 ^ v2 n.
Proof.
  intro m.
  pattern m.
  apply lt_wf_ind.
  intros n ih hn.
  destruct (v2 n) eqn:hv.
  - exists n.
    split.
    + apply v2_eq0_odd; assumption.
    + simpl.
      lia.
  - set (d := Nat.div2 n).
    assert (hd0 : d <> 0).
    { subst d.
      apply (div2_nonzero_of_v2_pos bmo3 bmo3_ini) with (r := n0) (n := n);
        assumption. }
    assert (hvd : v2 d = n0).
    { subst d.
      apply v2_div2_eq with (n := n); assumption. }
    assert (hdlt : d < n).
    { subst d.
      apply Nat.lt_div2.
      lia. }
    specialize (ih d hdlt hd0).
    destruct ih as [q [hq hqeq]].
    exists q.
    split.
    + exact hq.
    + assert (he : Nat.Even n).
      { apply v2_pos_even with (r := n0); assumption. }
      subst d.
      pose proof (even_double_div2 n he) as hn2.
      rewrite hqeq in hn2.
      rewrite hvd in hn2.
      simpl.
      nia.
Qed.

Lemma odd_nonzero (q : nat) : Nat.Odd q -> q <> 0.
Proof.
  intros [r hr].
  lia.
Qed.

Lemma v2_odd_mul_pow2 :
  forall q n, Nat.Odd q -> v2 (q * 2 ^ n) = n.
Proof.
  intros q n hq.
  induction n as [|n ihn].
  - simpl.
    rewrite Nat.mul_1_r.
    apply v2_odd_nonzero.
    + apply odd_nonzero.
      exact hq.
    + exact hq.
  - rewrite Nat.pow_succ_r' by lia.
    replace (q * (2 * 2 ^ n)) with (2 * (q * 2 ^ n)) by lia.
    rewrite v2_double_pos.
    + rewrite ihn.
      reflexivity.
    + assert (q <> 0) by (apply odd_nonzero; exact hq).
      assert (q * 2 ^ n <> 0).
      { intro h0.
        apply Nat.eq_mul_0 in h0.
        destruct h0 as [h0|h0].
        - contradiction.
        - pose proof (Nat.pow_nonzero 2 n ltac:(lia)) as hpow.
          contradiction. }
      exact H0.
Qed.

Lemma counter_bound :
  forall k, bmo3 (S k) < 2 ^ counter_len k.
Proof.
  induction k as [|k ih].
  - simpl.
    change (bmo3 1 < 2 ^ 4).
    rewrite bmo3_rec, bmo3_ini.
    replace (v2 2) with 1.
    2:{ symmetry.
        change 2 with (2 ^ 1).
        exact (v2_pow2 bmo3 bmo3_ini 1). }
    simpl.
    lia.
  - unfold counter_len at 1.
    fold counter_len.
    assert (hbound : bmo3 (S k) < 2 ^ counter_len k) by exact ih.
    destruct (Nat.ltb (bmo3 (S (S k))) (2 ^ counter_len k)) eqn:hlt.
    + apply Nat.ltb_lt in hlt.
      exact hlt.
    + assert (2 ^ counter_len k < bmo3 (S (S k))).
      { apply Nat.ltb_ge in hlt.
        assert (bmo3 (S (S k)) <> 2 ^ counter_len k).
        { intro heq.
          apply (bmo3_not_pow2_succ (S k) (counter_len k)).
          exact heq. }
        lia. }
      replace (2 ^ (counter_len k + 2)) with (4 * 2 ^ counter_len k).
      2:{ rewrite Nat.pow_add_r by lia.
          simpl.
          lia. }
      rewrite bmo3_rec.
      assert (2 ^ (v2 (bmo3 (S k)) + 2) <= 2 ^ counter_len k).
      { apply Nat.pow_le_mono_r.
        - lia.
        - assert (S (v2 (bmo3 (S k))) < counter_len k).
          { destruct (Nat.lt_ge_cases (S (v2 (bmo3 (S k)))) (counter_len k)) as [hsmall|hlarge].
            - exact hsmall.
            - assert (hv2lt : v2 (bmo3 (S k)) < counter_len k).
              { destruct (Nat.lt_ge_cases (v2 (bmo3 (S k))) (counter_len k)) as [hsmall'|hlarge'].
                - exact hsmall'.
                - exfalso.
                  pose proof (v2_lower_bound_pos bmo3 bmo3_ini (bmo3 (S k))) as h.
                  specialize (h (bmo3_pos (S k))).
                  assert (2 ^ counter_len k <= bmo3 (S k)).
                  { apply Nat.le_trans with (m := 2 ^ v2 (bmo3 (S k))).
                    - apply Nat.pow_le_mono_r; lia.
                    - exact h. }
                  lia. }
              assert (heq_len : counter_len k = S (v2 (bmo3 (S k)))) by lia.
              destruct (v2_factor_odd (bmo3 (S k)) (bmo3_pos (S k))) as [q [hq hqeq]].
              assert (hq1 : q = 1).
              { destruct hq as [r hr].
                rewrite hr in hqeq.
                rewrite hqeq in hbound.
                rewrite heq_len in hbound.
                simpl in hbound.
                assert (hpow : 0 < 2 ^ v2 (bmo3 (S k))).
                { apply Nat.pow_lower_bound.
                  lia. }
                pose proof
                  (proj2
                     (Nat.mul_lt_mono_pos_r
                        (2 ^ v2 (bmo3 (S k))) (2 * r + 1) 2 hpow)) as hmul.
                specialize (hmul hbound).
                nia. }
              exfalso.
              apply (bmo3_not_pow2_succ k (v2 (bmo3 (S k)))).
              transitivity (q * 2 ^ v2 (bmo3 (S k))).
              { exact hqeq. }
              { rewrite hq1.
                simpl.
                lia. } }
          lia. }
      lia.
Qed.

Lemma counter_state_start :
  counter_state 0 = (false, 4, 7).
Proof.
  unfold counter_state.
  simpl.
  change ((false, 4, 2 ^ 4 - bmo3 1) = (false, 4, 7)).
  repeat f_equal.
  rewrite bmo3_rec, bmo3_ini.
  replace (v2 2) with 1.
  2:{ symmetry.
      change 2 with (2 ^ 1).
      exact (v2_pow2 bmo3 bmo3_ini 1). }
  simpl.
  lia.
Qed.

Lemma pow2_odd_false :
  forall n, 0 < n -> Nat.odd (2 ^ n) = false.
Proof.
  intros [|n] hn.
  - lia.
  - rewrite Nat.pow_succ_r' by lia.
    rewrite Nat.odd_mul.
    simpl.
    reflexivity.
Qed.

Lemma odd_sub_pow2 :
  forall n q, 0 < n -> Nat.Odd q -> q < 2 ^ n -> Nat.Odd (2 ^ n - q).
Proof.
  intros n q hn hq hlt.
  apply Nat.odd_spec.
  rewrite Nat.odd_sub by lia.
  rewrite pow2_odd_false by exact hn.
  apply Nat.odd_spec in hq.
  rewrite hq.
  reflexivity.
Qed.

Definition abs_step (s t : state) : Prop :=
  let '(tp, l, x) := s in
  let a := 2 ^ l - x in
  let a' := a + 2 ^ (v2 a + 2) - 1 in
  let l' := if Nat.ltb a' (2 ^ l) then l else l + 2 in
  t = (negb tp, l', 2 ^ l' - a').

Lemma abs_step_deterministic :
  forall s t u, abs_step s t -> abs_step s u -> t = u.
Proof.
  intros [[tp l] x] t u ht hu.
  unfold abs_step in *.
  simpl in *.
  congruence.
Qed.

Lemma rev_step_implies_abs_step :
  forall s t, rev_step s t -> abs_step s t.
Proof.
  intros s t hstep.
  inversion hstep; subst; clear hstep; unfold abs_step; simpl.
  - set (q := 2 ^ (len + 2) - ((m + 2) * 2 + 1)).
    assert (hq_lt : ((m + 2) * 2 + 1) < 2 ^ (len + 2)).
    { replace (2 ^ (len + 2)) with (2 ^ (len + 1) * 2).
      2:{ replace (len + 2) with (S (len + 1)) by lia.
          rewrite Nat.pow_succ_r' by lia.
          rewrite Nat.mul_comm.
          reflexivity. }
      nia. }
    assert (hq_odd : Nat.Odd q).
    { unfold q.
      apply odd_sub_pow2.
      - lia.
      - exists (m + 2).
        lia.
      - exact hq_lt. }
    assert (hv2a :
      v2 (2 ^ (len + 2 + n) - (((m + 2) * 2 + 1) * 2 ^ n)) = n).
    { rewrite Nat.pow_add_r by lia.
      replace (2 ^ (len + 2) * 2 ^ n - (((m + 2) * 2 + 1) * 2 ^ n))
        with (q * 2 ^ n) by (unfold q; nia).
      apply v2_odd_mul_pow2.
      exact hq_odd. }
    rewrite hv2a.
    assert (ha' :
      2 ^ (len + 2 + n) - (((m + 2) * 2 + 1) * 2 ^ n) + 2 ^ (n + 2) - 1 =
      2 ^ (len + 2 + n) - ((m * 2 + 1) * 2 ^ n + 1)).
    { pose proof (Nat.pow_nonzero 2 n ltac:(lia)) as hpow.
      assert (hsrc_le : (((m + 2) * 2 + 1) * 2 ^ n) <= 2 ^ (len + 2 + n)).
      { rewrite Nat.pow_add_r by lia.
        apply Nat.lt_le_incl.
        apply (proj1 (Nat.mul_lt_mono_pos_r (2 ^ n) (((m + 2) * 2 + 1)) (2 ^ (len + 2)) ltac:(lia))).
        exact hq_lt. }
      replace (2 ^ (n + 2)) with (2 ^ n * 4).
      2:{ replace (n + 2) with (S (S n)) by lia.
          rewrite Nat.pow_succ_r' by lia.
          rewrite Nat.pow_succ_r' by lia.
          simpl.
          nia. }
      nia. }
    rewrite ha'.
    assert (hlt :
      (2 ^ (len + 2 + n) - ((m * 2 + 1) * 2 ^ n + 1) <? 2 ^ (len + 2 + n)) = true).
    { apply Nat.ltb_lt.
      apply Nat.sub_lt.
      - pose proof (Nat.pow_nonzero 2 n ltac:(lia)) as hpow.
        rewrite Nat.pow_add_r by lia.
        assert (hsrc_lt :
          (((m + 2) * 2 + 1) * 2 ^ n) < 2 ^ (len + 2) * 2 ^ n).
        { apply (proj1 (Nat.mul_lt_mono_pos_r (2 ^ n) (((m + 2) * 2 + 1)) (2 ^ (len + 2)) ltac:(lia))).
          exact hq_lt. }
        nia.
      - pose proof (Nat.pow_nonzero 2 n ltac:(lia)) as hpow.
        nia. }
    rewrite hlt.
    assert (htgt_le : (m * 2 + 1) * 2 ^ n + 1 <= 2 ^ (len + 2 + n)).
    { pose proof (Nat.pow_nonzero 2 n ltac:(lia)) as hpow.
      rewrite Nat.pow_add_r by lia.
      assert (hsrc_lt :
        (((m + 2) * 2 + 1) * 2 ^ n) < 2 ^ (len + 2) * 2 ^ n).
      { apply (proj1 (Nat.mul_lt_mono_pos_r (2 ^ n) (((m + 2) * 2 + 1)) (2 ^ (len + 2)) ltac:(lia))).
        exact hq_lt. }
      nia. }
    replace
      (2 ^ (len + 2 + n) - (2 ^ (len + 2 + n) - ((m * 2 + 1) * 2 ^ n + 1)))
      with ((m * 2 + 1) * 2 ^ n + 1) by lia.
    reflexivity.
  - assert (hq_odd : Nat.Odd (2 ^ (len + 2) - 1)).
    { apply odd_sub_pow2.
      - lia.
      - exists 0.
        reflexivity.
      - change 1 with (2 ^ 0).
        apply (proj1 (Nat.pow_lt_mono_r_iff 2 0 (len + 2) ltac:(lia))).
        lia. }
    assert (hv2a : v2 (2 ^ (len + 2 + n) - 1 * 2 ^ n) = n).
    { rewrite Nat.pow_add_r by lia.
      replace (2 ^ (len + 2) * 2 ^ n - 1 * 2 ^ n) with ((2 ^ (len + 2) - 1) * 2 ^ n)
        by nia.
      apply v2_odd_mul_pow2.
      exact hq_odd. }
    replace (2 ^ n + 0) with (1 * 2 ^ n) by nia.
    rewrite hv2a.
    assert (ha' :
      2 ^ (len + 2 + n) - 1 * 2 ^ n + 2 ^ (n + 2) - 1 =
      2 ^ (len + 2 + n) + 3 * 2 ^ n - 1).
    { pose proof (Nat.pow_nonzero 2 n ltac:(lia)) as hpow.
      assert (hsrc_le : 2 ^ n <= 2 ^ (len + 2 + n)).
      { rewrite Nat.pow_add_r by lia.
        assert (hbase : 1 <= 2 ^ (len + 2)).
        { replace 1 with (2 ^ 0) by reflexivity.
          apply Nat.pow_le_mono_r; lia. }
        nia. }
      replace (2 ^ (n + 2)) with (2 ^ n * 4).
      2:{ replace (n + 2) with (S (S n)) by lia.
          rewrite Nat.pow_succ_r' by lia.
          rewrite Nat.pow_succ_r' by lia.
          simpl.
          nia. }
      nia. }
    rewrite ha'.
    assert (hlt :
      (2 ^ (len + 2 + n) + 3 * 2 ^ n - 1 <? 2 ^ (len + 2 + n)) = false).
    { apply Nat.ltb_ge.
      pose proof (Nat.pow_nonzero 2 n ltac:(lia)) as hpow.
      nia. }
    rewrite hlt.
    replace (len + 2 + n + 2) with (len + 4 + n) by lia.
    assert (hpow4 : 2 ^ (len + 4 + n) = 16 * 2 ^ len * 2 ^ n).
    { rewrite Nat.pow_add_r by lia.
      rewrite Nat.pow_add_r by lia.
      simpl.
      nia. }
    assert (hpow2 : 2 ^ (len + 2 + n) = 4 * 2 ^ len * 2 ^ n).
    { rewrite Nat.pow_add_r by lia.
      rewrite Nat.pow_add_r by lia.
      simpl.
      nia. }
    replace
      (2 ^ (len + 4 + n) - (2 ^ (len + 2 + n) + 3 * 2 ^ n - 1))
      with ((12 * 2 ^ len - 3) * 2 ^ n + 1).
    2:{ rewrite hpow4, hpow2.
        pose proof (Nat.pow_nonzero 2 len ltac:(lia)) as hlen.
        pose proof (Nat.pow_nonzero 2 n ltac:(lia)) as hn.
        nia. }
    reflexivity.
  - assert (h3_lt : 3 < 2 ^ (len + 2)).
    { replace (2 ^ (len + 2)) with (2 ^ len * 4).
      2:{ replace (len + 2) with (S (S len)) by lia.
          rewrite Nat.pow_succ_r' by lia.
          rewrite Nat.pow_succ_r' by lia.
          simpl.
          nia. }
      pose proof (Nat.pow_nonzero 2 len ltac:(lia)) as hpow.
      nia. }
    assert (hq_odd : Nat.Odd (2 ^ (len + 2) - 3)).
    { apply odd_sub_pow2.
      - lia.
      - exists 1.
        reflexivity.
      - exact h3_lt. }
    assert (hv2a : v2 (2 ^ (len + 3 + n) - 3 * 2 ^ S n) = S n).
    { replace (len + 3 + n) with (len + 2 + S n) by lia.
      rewrite Nat.pow_add_r by lia.
      replace (2 ^ (len + 2) * 2 ^ S n - 3 * 2 ^ S n) with ((2 ^ (len + 2) - 3) * 2 ^ S n)
        by nia.
      apply v2_odd_mul_pow2.
      exact hq_odd. }
    replace
      (2 ^ n + (2 ^ n + 0) + (2 ^ n + (2 ^ n + 0) + (2 ^ n + (2 ^ n + 0) + 0)))
      with (3 * 2 ^ S n).
    2:{ replace (2 ^ S n) with (2 ^ n + (2 ^ n + 0)).
        2:{ rewrite Nat.pow_succ_r' by lia.
            simpl.
            nia. }
        nia. }
    rewrite hv2a.
    assert (ha' :
      2 ^ (len + 3 + n) - 3 * 2 ^ S n + 2 ^ (S n + 2) - 1 =
      2 ^ (len + 3 + n) + 2 ^ S n - 1).
    { pose proof (Nat.pow_nonzero 2 (S n) ltac:(lia)) as hpow.
      assert (hsrc_le : 3 * 2 ^ S n <= 2 ^ (len + 3 + n)).
      { replace (len + 3 + n) with (len + 2 + S n) by lia.
        rewrite Nat.pow_add_r by lia.
        apply Nat.lt_le_incl.
        apply (proj1 (Nat.mul_lt_mono_pos_r (2 ^ S n) 3 (2 ^ (len + 2)) ltac:(lia))).
        exact h3_lt. }
      replace (2 ^ (S n + 2)) with (2 ^ S n * 4).
      2:{ replace (S n + 2) with (S (S (S n))) by lia.
          rewrite Nat.pow_succ_r' by lia.
          rewrite Nat.pow_succ_r' by lia.
          simpl.
          nia. }
      nia. }
    rewrite ha'.
    assert (hlt :
      (2 ^ (len + 3 + n) + 2 ^ S n - 1 <? 2 ^ (len + 3 + n)) = false).
    { apply Nat.ltb_ge.
      pose proof (Nat.pow_nonzero 2 (S n) ltac:(lia)) as hpow.
      nia. }
    rewrite hlt.
    replace (len + 3 + n + 2) with (len + 5 + n) by lia.
    assert (hpow4 : 2 ^ (len + 5 + n) = 16 * 2 ^ len * 2 ^ S n).
    { replace (len + 5 + n) with (len + 4 + S n) by lia.
      rewrite Nat.pow_add_r by lia.
      rewrite Nat.pow_add_r by lia.
      simpl.
      nia. }
    assert (hpow2 : 2 ^ (len + 3 + n) = 4 * 2 ^ len * 2 ^ S n).
    { replace (len + 3 + n) with (len + 2 + S n) by lia.
      rewrite Nat.pow_add_r by lia.
      rewrite Nat.pow_add_r by lia.
      simpl.
      nia. }
    replace
      (2 ^ (len + 5 + n) - (2 ^ (len + 3 + n) + 2 ^ S n - 1))
      with ((12 * 2 ^ len - 1) * 2 ^ S n + 1).
    2:{ rewrite hpow4, hpow2.
        pose proof (Nat.pow_nonzero 2 len ltac:(lia)) as hlen.
        pose proof (Nat.pow_nonzero 2 (S n) ltac:(lia)) as hn.
        nia. }
    reflexivity.
Qed.

Inductive abs_steps : nat -> state -> state -> Prop :=
| abs_steps_0 s : abs_steps 0 s s
| abs_steps_S n s t u :
    abs_step s t ->
    abs_steps n t u ->
    abs_steps (S n) s u.

Lemma counter_state_abs_step :
  forall k, abs_step (counter_state k) (counter_state (S k)).
Proof.
  intro k.
  unfold abs_step, counter_state.
  set (l := counter_len k).
  set (a := bmo3 (S k)).
  assert (ha : a < 2 ^ l).
  { subst a l.
    apply counter_bound. }
  assert (hsub : 2 ^ l - (2 ^ l - a) = a) by lia.
  rewrite hsub.
  unfold a.
  rewrite bmo3_rec.
  unfold l.
  simpl.
  replace (Nat.even k) with (negb (Nat.even (S k))).
  2:{ rewrite Nat.even_succ.
      rewrite <- Nat.negb_even.
      destruct (Nat.even k);
      reflexivity. }
  reflexivity.
Qed.

Lemma counter_state_rev_step :
  forall k, rev_step (counter_state k) (counter_state (S k)).
Proof.
  intro k.
  set (l := counter_len k).
  set (a := bmo3 (S k)).
  set (r := v2 a).
  assert (ha_pos : a <> 0).
  { subst a.
    apply bmo3_pos. }
  assert (ha_bound : a < 2 ^ l).
  { subst a l.
    apply counter_bound. }
  destruct (v2_factor_odd a ha_pos) as [q [hq hqeq]].
  assert (hr_lt_l : r < l).
  { assert (hlow : 2 ^ r <= a).
    { subst r a.
      apply (v2_lower_bound_pos bmo3 bmo3_ini).
      exact ha_pos. }
    destruct (Nat.lt_ge_cases r l) as [hlt|hge].
    - exact hlt.
    - assert (2 ^ l <= 2 ^ r).
      { apply Nat.pow_le_mono_r.
        - lia.
        - lia. }
      lia. }
  assert (hpowr_pos : 0 < 2 ^ r).
  { apply Nat.pow_lower_bound.
    lia. }
  assert (hl_split : 2 ^ l = 2 ^ (l - r) * 2 ^ r).
  { replace (2 ^ l) with (2 ^ ((l - r) + r)).
    2:{ f_equal.
        lia. }
    rewrite Nat.pow_add_r by lia.
    reflexivity. }
  assert (hq_lt : q < 2 ^ (l - r)).
  { apply (proj2 (Nat.mul_lt_mono_pos_r (2 ^ r) q (2 ^ (l - r)) hpowr_pos)).
    rewrite <- hl_split.
    unfold r.
    rewrite <- hqeq.
    exact ha_bound. }
  set (span := l - r).
  assert (hspan_ge2 : 2 <= span).
  { unfold span.
    destruct (l - r) as [|[|u]] eqn:hspan.
    - lia.
    - exfalso.
      assert (q = 1).
      { destruct hq as [v hv].
        change (2 ^ 1) with 2 in hq_lt.
        lia. }
      apply (bmo3_not_pow2_succ k r).
      subst a.
      subst r.
      transitivity (q * 2 ^ v2 (bmo3 (S k))); [exact hqeq|].
      rewrite H.
      rewrite Nat.mul_1_l.
      reflexivity.
    - lia. }
  set (len0 := span - 2).
  assert (hl_repr : l = len0 + 2 + r).
  { unfold len0, span.
    lia. }
  set (p := 2 ^ span - q).
  assert (hp_odd : Nat.Odd p).
  { unfold p.
    apply odd_sub_pow2.
    - unfold span.
      lia.
    - exact hq.
    - exact hq_lt. }
  assert (hq_pos : 0 < q).
  { destruct hq as [u hu].
    lia. }
  assert (hp_lt : p < 2 ^ span).
  { unfold p.
    apply Nat.sub_lt.
    - apply Nat.lt_le_incl.
      exact hq_lt.
    - exact hq_pos. }
  assert (hx : 2 ^ l - a = p * 2 ^ r).
  { unfold p.
    rewrite hqeq.
    rewrite hl_split.
    rewrite <- Nat.mul_sub_distr_r.
    reflexivity. }
  destruct hp_odd as [u hu].
  destruct u as [|u].
  - set (src := (Nat.even (S k), len0 + 2 + r, (0 * 2 + 1) * 2 ^ r)).
    set (tgt := (negb (Nat.even (S k)), len0 + 4 + r, (12 * 2 ^ len0 - 3) * 2 ^ r + 1)).
    assert (hsrc : counter_state k = src).
    { unfold counter_state, src.
      assert (hlen_eq : counter_len k = len0 + 2 + r).
      { unfold l.
        exact hl_repr. }
      assert (hx_eq : 2 ^ (len0 + 2 + r) - bmo3 (S k) = (0 * 2 + 1) * 2 ^ r).
      { replace (2 ^ (len0 + 2 + r) - bmo3 (S k)) with (2 ^ l - a).
        2:{ unfold a.
            rewrite <- hl_repr.
            reflexivity. }
        rewrite hx, hu.
        reflexivity. }
      rewrite hlen_eq, hx_eq.
      reflexivity. }
    assert (hraw : rev_step src tgt).
    { unfold src, tgt.
      apply Ov1. }
    assert (habs_tgt : abs_step src tgt).
    { apply rev_step_implies_abs_step.
      exact hraw. }
    assert (habs_counter : abs_step src (counter_state (S k))).
    { rewrite <- hsrc.
      apply counter_state_abs_step. }
    pose proof (abs_step_deterministic src tgt (counter_state (S k)) habs_tgt habs_counter) as htgt.
    rewrite hsrc.
    rewrite <- htgt.
    exact hraw.
  - destruct u as [|m].
    + assert (hr_pos : 0 < r).
      { destruct r as [|n].
        - exfalso.
          apply (bmo3_not_pow2_succ (S k) l).
          assert (ha3 : a = 2 ^ l - 3).
          { rewrite hu in hx.
            change (2 ^ 0) with 1 in hx.
            simpl.
            nia. }
          rewrite bmo3_rec.
          change (bmo3 (S k)) with a.
          rewrite ha3.
          assert (hv20 : v2 (2 ^ l - 3) = 0).
          { apply v2_odd_nonzero.
            - assert (h4 : 4 <= 2 ^ l).
              { replace 4 with (2 ^ 2) by reflexivity.
                apply Nat.pow_le_mono_r; lia. }
              lia.
            - apply odd_sub_pow2.
              + lia.
              + exists 1.
                reflexivity.
              + assert (h4 : 4 <= 2 ^ l).
                { replace 4 with (2 ^ 2) by reflexivity.
                  apply Nat.pow_le_mono_r; lia. }
                lia. }
          rewrite hv20.
          simpl.
          nia.
        - lia. }
      destruct r as [|n].
      { lia. }
      set (src := (Nat.even (S k), len0 + 3 + n, (1 * 2 + 1) * 2 ^ S n)).
      set (tgt := (negb (Nat.even (S k)), len0 + 5 + n, (12 * 2 ^ len0 - 1) * 2 ^ S n + 1)).
      assert (hsrc : counter_state k = src).
      { unfold counter_state, src.
        assert (hlen_eq : counter_len k = len0 + 3 + n).
        { unfold l, len0, span in hl_repr.
          lia. }
        assert (hx_eq : 2 ^ (len0 + 3 + n) - bmo3 (S k) = (1 * 2 + 1) * 2 ^ S n).
        { replace (2 ^ (len0 + 3 + n) - bmo3 (S k)) with (2 ^ l - a).
          2:{ unfold a, l.
              rewrite hlen_eq.
              reflexivity. }
          rewrite hx, hu.
          reflexivity. }
        rewrite hlen_eq, hx_eq.
        reflexivity. }
      assert (hraw : rev_step src tgt).
      { unfold src, tgt.
        apply Ov2. }
      assert (habs_tgt : abs_step src tgt).
      { apply rev_step_implies_abs_step.
        exact hraw. }
      assert (habs_counter : abs_step src (counter_state (S k))).
      { rewrite <- hsrc.
        apply counter_state_abs_step. }
      pose proof (abs_step_deterministic src tgt (counter_state (S k)) habs_tgt habs_counter) as htgt.
      rewrite hsrc.
      rewrite <- htgt.
      exact hraw.
    + set (src := (Nat.even (S k), len0 + 2 + r, ((m + 2) * 2 + 1) * 2 ^ r)).
      set (tgt := (negb (Nat.even (S k)), len0 + 2 + r, (m * 2 + 1) * 2 ^ r + 1)).
      assert (hm_lt : m + 2 < 2 ^ (len0 + 1)).
      { assert (hpm : ((m + 2) * 2 + 1) < 2 ^ span).
        { replace (((m + 2) * 2 + 1)) with p.
          2:{ rewrite hu.
              nia. }
          exact hp_lt. }
        replace (2 ^ span) with (2 * 2 ^ (len0 + 1)) in hpm.
        2:{ unfold len0.
            replace (span - 2 + 1) with (span - 1) by lia.
            replace span with (S (span - 1)) by lia.
            rewrite Nat.pow_succ_r' by lia.
            replace (S (span - 1) - 1) with (span - 1) by lia.
            rewrite Nat.mul_comm.
            reflexivity. }
        assert (hdouble : 2 * (m + 2) < 2 * 2 ^ (len0 + 1)) by nia.
        apply (proj2 (Nat.mul_lt_mono_pos_l 2 (m + 2) (2 ^ (len0 + 1)) ltac:(lia))).
        exact hdouble. }
      assert (hsrc : counter_state k = src).
      { unfold counter_state, src.
        assert (hlen_eq : counter_len k = len0 + 2 + r).
        { unfold l.
          exact hl_repr. }
        assert (hx_eq : 2 ^ (len0 + 2 + r) - bmo3 (S k) = ((m + 2) * 2 + 1) * 2 ^ r).
        { replace (2 ^ (len0 + 2 + r) - bmo3 (S k)) with (2 ^ l - a).
          2:{ unfold a.
              rewrite <- hl_repr.
              reflexivity. }
          rewrite hx, hu.
          nia. }
        rewrite hlen_eq, hx_eq.
        reflexivity. }
      assert (hraw : rev_step src tgt).
      { unfold src, tgt.
        apply Inc.
        exact hm_lt. }
      assert (habs_tgt : abs_step src tgt).
      { apply rev_step_implies_abs_step.
        exact hraw. }
      assert (habs_counter : abs_step src (counter_state (S k))).
      { rewrite <- hsrc.
        apply counter_state_abs_step. }
      pose proof (abs_step_deterministic src tgt (counter_state (S k)) habs_tgt habs_counter) as htgt.
      rewrite hsrc.
      rewrite <- htgt.
      exact hraw.
Qed.


From BusyCoq Require Import Individual25.
From BusyCoq Require Import BinaryCounter25_v2.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Open Scope list.

Lemma lt_mul2add1_mul2 a b:
  a<b ->
  a*2+1<b*2.
Proof.
  lia.
Qed.

Lemma lt_mul1 a b:
  1*a<b*a ->
  a<b*a.
Proof.
  lia.
Qed.

Ltac rw_Bin' :=
rw_Bin;
repeat rewrite Nat.pow_add_r; change (2^1) with 2%nat; try lia;
repeat rewrite Nat.add_0_r;
repeat
match goal with
| |- _+1<_ => apply lt_mul2add1_mul2; try lia
| |- _*?a < _*?a => rewrite <-Nat.mul_lt_mono_pos_r; try lia
| |- ?a < _*?a => apply lt_mul1; try lia
| _ => try lia
end.


Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB1RB3LA4LA2RA_2LB3RA---3RA4RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition RC r len n := BinDec [3] [4] len n (r*>0inf).

Lemma RC_Inc l r len n:
  n+1<2^len ->
  l {{A}}> RC r len (n+1) -->*
  l <{{A}} RC r len n.
Proof.
  rewrite (Nat.add_comm n 1).
  intros H.
  eapply progress_evstep.
  apply RBinDec_spec with (qL:=[]) (qR:=[]); try assumption.
  es.
Qed.

Notation "l |> r" := (l {{B}}> r) (at level 30).
Notation "l <| r" := (l <{{A}} r) (at level 30).

Lemma Inc1_S l r len n m:
  m+1<2^len ->
  l |> RC r (len+1+1+n+1) (((m+1)*2*2+1)*2^n*2) -->*
  l <| RC r (len+1+1+n+1) ((m*2*2+1)*2^n*2+1).
Proof.
  intros H.
  unfold RC.
  rw_Bin'.
  es; er.
  follow RC_Inc.
  es.
Qed.

Lemma Inc2_S l r len n m:
  m+1<2^len ->
  l |> RC r (len+1+1+n+1) ((((m+1)*2+1)*2+1)*2^n*2) -->*
  l <| RC r (len+1+1+n+1) (((m*2+1)*2+1)*2^n*2+1).
Proof.
  intros H.
  unfold RC.
  rw_Bin'.
  es; er.
  follow RC_Inc.
  es.
Qed.

Lemma Inc1_O l r len m:
  m+1<2^len ->
  l |> RC r (len+1+1) ((m+1)*2*2+1) -->*
  l <| RC r (len+1+1) ((m*2+1)*2).
Proof.
  intros H.
  unfold RC.
  rw_Bin'.
  es; er.
  follow RC_Inc.
  es.
Qed.

Lemma Inc2_O l r len m:
  m<2^len ->
  l |> RC r (len+1+1) ((m*2+1)*2+1) -->*
  l <| RC r (len+1+1) (m*2*2).
Proof.
  intros H.
  unfold RC.
  rw_Bin'.
  er.
Qed.

Lemma Inc l r len n m:
  m+2<2^len*2 ->
  l |> RC r (len+1+1+n) (((m+2)*2+1)*2^n) -->*
  l <| RC r (len+1+1+n) ((m*2+1)*2^n+1).
Proof.
  intros H.
  pose proof (Nat.Div0.div_mod m 2).
  remember (m/2) as m0.
  destruct (m mod 2) as [|[|]]. 3: lia.
  - subst m.
    destruct n as [|n].
    + applys_eq (Inc1_O l r len m0); cbn; flia.
    + applys_eq (Inc1_S l r len n m0); cbn; flia.
  - subst m.
    destruct n as [|n].
    + applys_eq (Inc2_O l r len (m0+1)); cbn; flia.
    + applys_eq (Inc2_S l r len n m0); cbn; flia.
Qed.

Lemma Ov1_S l len n:
  l |> RC [] (len+1+1+n+1) ((0*2*2+1)*2^n*2) -->*
  l <| RC [] (1+1+len+1+1+n+1) ((((1*2+1)*2^len-1)*2*2+1)*2^n*2+1).
Proof.
  unfold RC.
  rw_Bin'.
  es.
Qed.

Lemma Ov2_S l len n:
  l |> RC [] (len+1+1+n+1) (((0*2+1)*2+1)*2^n*2) -->*
  l <| RC [] (1+1+len+1+1+n+1) (((((1*2+1)*2^len-1)*2+1)*2+1)*2^n*2+1).
Proof.
  unfold RC.
  rw_Bin'.
  es.
Qed.

Lemma Ov1_O l len:
  l |> RC [] (len+1+1) (0*2*2+1) -->*
  l <| RC [] (1+1+len+1+1) ((((1*2+1)*2^len-1)*2+1)*2).
Proof.
  unfold RC.
  rw_Bin'.
  es.
Qed.

Lemma Ov1 l len n:
  l |> RC [] (len+1+1+n) ((0*2+1)*2^n) -->*
  l <| RC [] (1+1+len+1+1+n) ((((1*2+1)*2^len-1)*2*2+1)*2^n+1).
Proof.
  destruct n.
  - applys_eq (Ov1_O l len); cbn; flia.
  - applys_eq (Ov1_S l len n); cbn; flia.
Qed.

Definition LH (tp:bool) := 0inf <* (if tp then [1] else [1]).

Lemma LR r tp:
  LH tp <| r -->+
  LH (negb tp) |> r.
Proof.
  destruct tp;
  er.
Qed.

Definition S0 '(tp,len,n) :=
  LH tp |> RC [] len n.

Lemma Inc' tp len n m:
  m+2<2^len*2 ->
  S0 (tp, (len+1+1+n), (((m+2)*2+1)*2^n)) -->+
  S0 (negb tp, (len+1+1+n), ((m*2+1)*2^n+1)).
Proof.
  intros.
  unfold S0.
  follow Inc.
  apply LR.
Qed.

Lemma Ov1' tp len n:
  S0 (tp, (len+1+1+n), ((0*2+1)*2^n)) -->+
  S0 (negb tp, (1+1+len+1+1+n), ((((1*2+1)*2^len-1)*2*2+1)*2^n+1)).
Proof.
  intros.
  unfold S0.
  follow Ov1.
  apply LR.
Qed.

Lemma Ov2' tp len n:
  S0 (tp, (len+1+1+n+1), (((0*2+1)*2+1)*2^n*2)) -->+
  S0 (negb tp, (1+1+len+1+1+n+1), (((((1*2+1)*2^len-1)*2+1)*2+1)*2^n*2+1)).
Proof.
  intros.
  unfold S0.
  follow Ov2_S.
  apply LR.
Qed.

Definition S1 k := S0 (counter_state k).

Lemma init:
  c0 -->*
  S1 0.
Proof.
  unfold S1.
  rewrite counter_state_start.
  er.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intro k.
  exists (S k).
  unfold S1.
  epose proof (counter_state_rev_step k) as I1.
  remember (counter_state k) as v1.
  remember (counter_state (S k)) as v2.
  clear Heqv1 Heqv2.
  inverts I1.
  - rewrite Nat.pow_add_r in H.
    applys_eq (Inc' tp len n m); flia.
  - applys_eq (Ov1' tp len n); flia.
  - cbn[Nat.pow].
    applys_eq (Ov2' tp len n); flia.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB0RB3LA4LA2RA_2LB3RA---3RA4RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition RC r len n := BinDec [3] [4] len n (r*>0inf).

Lemma RC_Inc l r len n:
  n+1<2^len ->
  l {{A}}> RC r len (n+1) -->*
  l <{{A}} RC r len n.
Proof.
  rewrite (Nat.add_comm n 1).
  intros H.
  eapply progress_evstep.
  apply RBinDec_spec with (qL:=[]) (qR:=[]); try assumption.
  es.
Qed.

Notation "l |> r" := (l {{B}}> r) (at level 30).
Notation "l <| r" := (l <{{A}} r) (at level 30).

Lemma Inc1_S l r len n m:
  m+1<2^len ->
  l |> RC r (len+1+1+n+1) (((m+1)*2*2+1)*2^n*2) -->*
  l <| RC r (len+1+1+n+1) ((m*2*2+1)*2^n*2+1).
Proof.
  intros H.
  unfold RC.
  rw_Bin'.
  es; er.
  follow RC_Inc.
  es.
Qed.

Lemma Inc2_S l r len n m:
  m+1<2^len ->
  l |> RC r (len+1+1+n+1) ((((m+1)*2+1)*2+1)*2^n*2) -->*
  l <| RC r (len+1+1+n+1) (((m*2+1)*2+1)*2^n*2+1).
Proof.
  intros H.
  unfold RC.
  rw_Bin'.
  es; er.
  follow RC_Inc.
  es.
Qed.

Lemma Inc1_O l r len m:
  m+1<2^len ->
  l |> RC r (len+1+1) ((m+1)*2*2+1) -->*
  l <| RC r (len+1+1) ((m*2+1)*2).
Proof.
  intros H.
  unfold RC.
  rw_Bin'.
  es; er.
  follow RC_Inc.
  es.
Qed.

Lemma Inc2_O l r len m:
  m<2^len ->
  l |> RC r (len+1+1) ((m*2+1)*2+1) -->*
  l <| RC r (len+1+1) (m*2*2).
Proof.
  intros H.
  unfold RC.
  rw_Bin'.
  er.
Qed.

Lemma Inc l r len n m:
  m+2<2^len*2 ->
  l |> RC r (len+1+1+n) (((m+2)*2+1)*2^n) -->*
  l <| RC r (len+1+1+n) ((m*2+1)*2^n+1).
Proof.
  intros H.
  pose proof (Nat.Div0.div_mod m 2).
  remember (m/2) as m0.
  destruct (m mod 2) as [|[|]]. 3: lia.
  - subst m.
    destruct n as [|n].
    + applys_eq (Inc1_O l r len m0); cbn; flia.
    + applys_eq (Inc1_S l r len n m0); cbn; flia.
  - subst m.
    destruct n as [|n].
    + applys_eq (Inc2_O l r len (m0+1)); cbn; flia.
    + applys_eq (Inc2_S l r len n m0); cbn; flia.
Qed.

Lemma Ov1_S l len n:
  l |> RC [] (len+1+1+n+1) ((0*2*2+1)*2^n*2) -->*
  l <| RC [] (1+1+len+1+1+n+1) ((((1*2+1)*2^len-1)*2*2+1)*2^n*2+1).
Proof.
  unfold RC.
  rw_Bin'.
  es.
Qed.

Lemma Ov2_S l len n:
  l |> RC [] (len+1+1+n+1) (((0*2+1)*2+1)*2^n*2) -->*
  l <| RC [] (1+1+len+1+1+n+1) (((((1*2+1)*2^len-1)*2+1)*2+1)*2^n*2+1).
Proof.
  unfold RC.
  rw_Bin'.
  es.
Qed.

Lemma Ov1_O l len:
  l |> RC [] (len+1+1) (0*2*2+1) -->*
  l <| RC [] (1+1+len+1+1) ((((1*2+1)*2^len-1)*2+1)*2).
Proof.
  unfold RC.
  rw_Bin'.
  es.
Qed.

Lemma Ov1 l len n:
  l |> RC [] (len+1+1+n) ((0*2+1)*2^n) -->*
  l <| RC [] (1+1+len+1+1+n) ((((1*2+1)*2^len-1)*2*2+1)*2^n+1).
Proof.
  destruct n.
  - applys_eq (Ov1_O l len); cbn; flia.
  - applys_eq (Ov1_S l len n); cbn; flia.
Qed.

Definition LH (tp:bool) := 0inf <* (if tp then [1] else []).

Lemma LR r tp:
  LH tp <| r -->+
  LH (negb tp) |> r.
Proof.
  destruct tp;
  er.
Qed.

Definition S0 '(tp,len,n) :=
  LH tp |> RC [] len n.

Lemma Inc' tp len n m:
  m+2<2^len*2 ->
  S0 (tp, (len+1+1+n), (((m+2)*2+1)*2^n)) -->+
  S0 (negb tp, (len+1+1+n), ((m*2+1)*2^n+1)).
Proof.
  intros.
  unfold S0.
  follow Inc.
  apply LR.
Qed.

Lemma Ov1' tp len n:
  S0 (tp, (len+1+1+n), ((0*2+1)*2^n)) -->+
  S0 (negb tp, (1+1+len+1+1+n), ((((1*2+1)*2^len-1)*2*2+1)*2^n+1)).
Proof.
  intros.
  unfold S0.
  follow Ov1.
  apply LR.
Qed.

Lemma Ov2' tp len n:
  S0 (tp, (len+1+1+n+1), (((0*2+1)*2+1)*2^n*2)) -->+
  S0 (negb tp, (1+1+len+1+1+n+1), (((((1*2+1)*2^len-1)*2+1)*2+1)*2^n*2+1)).
Proof.
  intros.
  unfold S0.
  follow Ov2_S.
  apply LR.
Qed.

Definition S1 k := S0 (counter_state k).

Lemma init:
  c0 -->*
  S1 0.
Proof.
  unfold S1.
  rewrite counter_state_start.
  er.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intro k.
  exists (S k).
  unfold S1.
  epose proof (counter_state_rev_step k) as I1.
  remember (counter_state k) as v1.
  remember (counter_state (S k)) as v2.
  clear Heqv1 Heqv2.
  inverts I1.
  - rewrite Nat.pow_add_r in H.
    applys_eq (Inc' tp len n m); flia.
  - applys_eq (Ov1' tp len n); flia.
  - cbn[Nat.pow].
    applys_eq (Ov2' tp len n); flia.
Qed.

End TM2.

Close Scope sym.

Module BMO3VariantMinus.
Require Import Arith Lia PeanoNat.

Definition state := (nat * nat)%type.

Inductive variant_step : state -> state -> Prop :=
| Inc len n m :
    m + 2 < 2 ^ (len + 1) ->
    variant_step
      (len + 2 + n, ((m + 2) * 2 + 1) * 2 ^ n)
      (len + 2 + n, (m * 2 + 1) * 2 ^ n - 1)
| Ov1 len n :
    variant_step
      (len + 2 + n, (0 * 2 + 1) * 2 ^ n)
      (len + 3 + n, ((((2 ^ (len + 1) - 1) * 2) * 2 + 1) * 2 ^ n) - 1)
| Ov2 len n :
    variant_step
      (len + 2 + n, ((0 * 2 + 1) * 2 + 1) * 2 ^ n)
      (len + 3 + n, ((((2 ^ (len + 1) - 1) * 2 + 1) * 2 + 1) * 2 ^ n) - 1).

Definition variant_closed : Prop :=
  forall s t, variant_step s t -> exists u, variant_step t u.

Definition start : state := (3, 1).

Definition complement (s : state) : nat :=
  let '(l, x) := s in
  2 ^ l - x - 1.

Lemma start_steps_to_12 :
  variant_step start (4, 12).
Proof.
  unfold start.
  change (variant_step
            (1 + 2 + 0, (0 * 2 + 1) * 2 ^ 0)
            (1 + 3 + 0, ((((2 ^ (1 + 1) - 1) * 2) * 2 + 1) * 2 ^ 0) - 1)).
  apply Ov1.
Qed.

Lemma zero_stuck :
  forall l t, ~ variant_step (l, 0) t.
Proof.
  intros l t h.
  inversion h; subst.
  - pose proof (Nat.pow_nonzero 2 n ltac:(lia)) as hpow.
    lia.
  - pose proof (Nat.pow_nonzero 2 n ltac:(lia)) as hpow.
    lia.
  - pose proof (Nat.pow_nonzero 2 n ltac:(lia)) as hpow.
    lia.
Qed.

Lemma nonclosure_witness :
  variant_step (3, 5) (3, 0).
Proof.
  change (variant_step
            (1 + 2 + 0, ((0 + 2) * 2 + 1) * 2 ^ 0)
            (1 + 2 + 0, ((0 * 2 + 1) * 2 ^ 0) - 1)).
  apply Inc.
  simpl.
  lia.
Qed.

Theorem variant_not_closed :
  ~ variant_closed.
Proof.
  intro hclosed.
  unfold variant_closed in hclosed.
  destruct (hclosed _ _ nonclosure_witness) as [u hu].
  exact (zero_stuck 3 u hu).
Qed.

Lemma complement_start :
  complement start = 6.
Proof.
  reflexivity.
Qed.

Lemma complement_inc_formula :
  forall len n m,
    m + 2 < 2 ^ (len + 1) ->
    complement (len + 2 + n, ((m + 2) * 2 + 1) * 2 ^ n) + 2 ^ (n + 2) + 1 =
    complement (len + 2 + n, (m * 2 + 1) * 2 ^ n - 1).
Proof.
  intros len n m hm.
  unfold complement.
  set (p := 2 ^ (len + 2 + n)).
  set (r := 2 ^ n).
  set (t := (m * 2 + 1) * r).
  assert (hodd_lt : ((m + 2) * 2 + 1) < 2 ^ (len + 2)).
  { replace (2 ^ (len + 2)) with (2 ^ (len + 1) * 2).
    2:{ replace (len + 2) with (S (len + 1)) by lia.
        rewrite Nat.pow_succ_r' by lia.
        rewrite Nat.mul_comm.
        reflexivity. }
    nia. }
  assert (hsrc_lt : ((m + 2) * 2 + 1) * r < p).
  { unfold p, r.
    rewrite Nat.pow_add_r by lia.
    assert (hpow_pos : 0 < 2 ^ n).
    { apply Nat.pow_lower_bound.
      lia. }
    apply (proj1 (Nat.mul_lt_mono_pos_r (2 ^ n) (((m + 2) * 2 + 1)) (2 ^ (len + 2)) hpow_pos)).
    exact hodd_lt. }
  assert (hsrc_le : ((m + 2) * 2 + 1) * r <= p) by lia.
  assert (ht_le : t <= p) by (unfold t; nia).
  assert (ht_pos : 0 < t).
  { unfold t, r.
    pose proof (Nat.pow_nonzero 2 n ltac:(lia)) as hpow.
    nia. }
  assert (hpow4 : 2 ^ (n + 2) = 4 * r).
  { unfold r.
    replace (n + 2) with (S (S n)) by lia.
    rewrite Nat.pow_succ_r' by lia.
    rewrite Nat.pow_succ_r' by lia.
    simpl.
    nia. }
  rewrite hpow4.
  replace (((m + 2) * 2 + 1) * r) with (t + 4 * r) in hsrc_lt by (unfold t; nia).
  replace (((m + 2) * 2 + 1) * r) with (t + 4 * r) in hsrc_le by (unfold t; nia).
  replace (p - (t - 1) - 1) with (p - t).
  2:{ rewrite <- Nat.sub_add_distr.
      replace (t - 1 + 1) with t by lia.
      reflexivity. }
  replace (p - (t + 4 * r) - 1 + 4 * r + 1) with (((p - (t + 4 * r)) - 1 + 1) + 4 * r).
  2:{ assert (0 < p - (t + 4 * r)) by lia.
      lia. }
  replace (((p - (t + 4 * r)) - 1 + 1) + 4 * r) with ((p - (t + 4 * r)) + 4 * r).
  2:{ rewrite Nat.sub_add by lia.
      reflexivity. }
  replace (p - (t + 4 * r)) with (p - t - 4 * r).
  2:{ symmetry.
      apply Nat.sub_add_distr. }
  lia.
Qed.

Lemma complement_ov1_formula :
  forall len n,
    complement (len + 3 + n, ((((2 ^ (len + 1) - 1) * 2) * 2 + 1) * 2 ^ n) - 1) = 3 * 2 ^ n.
Proof.
  intros len n.
  unfold complement.
  rewrite Nat.pow_add_r by lia.
  replace ((((2 ^ (len + 1) - 1) * 2) * 2 + 1) * 2 ^ n - 1)
    with ((2 ^ (len + 3) - 3) * 2 ^ n - 1).
  2:{ assert (hpow : 2 ^ (len + 3) = 4 * 2 ^ (len + 1)).
      { replace (len + 3) with ((len + 1) + 2) by lia.
        rewrite Nat.pow_add_r by lia.
        simpl.
        nia. }
      rewrite hpow.
      pose proof (Nat.pow_nonzero 2 (len + 1) ltac:(lia)) as hpow1.
      nia. }
  replace
    (2 ^ (len + 3) * 2 ^ n - ((2 ^ (len + 3) - 3) * 2 ^ n - 1) - 1)
    with (2 ^ (len + 3) * 2 ^ n - ((2 ^ (len + 3) - 3) * 2 ^ n)).
  2:{ assert (0 < (2 ^ (len + 3) - 3) * 2 ^ n).
      { apply Nat.mul_pos_pos.
        - assert (4 <= 2 ^ (len + 3)).
          { replace 4 with (2 ^ 2) by reflexivity.
            apply Nat.pow_le_mono_r; lia. }
          lia.
        - apply Nat.pow_lower_bound.
          lia. }
      rewrite <- Nat.sub_add_distr.
      replace (((2 ^ (len + 3) - 3) * 2 ^ n - 1) + 1) with ((2 ^ (len + 3) - 3) * 2 ^ n) by lia.
      reflexivity. }
  assert (3 <= 2 ^ (len + 3)).
  { assert (4 <= 2 ^ (len + 3)).
    { replace 4 with (2 ^ 2) by reflexivity.
      apply Nat.pow_le_mono_r; lia. }
    eapply Nat.le_trans.
    - exact (Nat.le_succ_diag_r 3).
    - exact H. }
  replace (2 ^ (len + 3) * 2 ^ n) with ((((2 ^ (len + 3) - 3) + 3) * 2 ^ n)).
  2:{ f_equal.
      lia. }
  rewrite Nat.mul_add_distr_r.
  rewrite Nat.add_comm.
  rewrite Nat.add_sub.
  reflexivity.
Qed.

Lemma complement_ov2_formula :
  forall len n,
    complement (len + 3 + n, ((((2 ^ (len + 1) - 1) * 2 + 1) * 2 + 1) * 2 ^ n) - 1) = 2 ^ n.
Proof.
  intros len n.
  unfold complement.
  rewrite Nat.pow_add_r by lia.
  replace ((((2 ^ (len + 1) - 1) * 2 + 1) * 2 + 1) * 2 ^ n - 1)
    with ((2 ^ (len + 3) - 1) * 2 ^ n - 1).
  2:{ assert (hpow : 2 ^ (len + 3) = 4 * 2 ^ (len + 1)).
      { replace (len + 3) with ((len + 1) + 2) by lia.
        rewrite Nat.pow_add_r by lia.
        simpl.
        nia. }
      rewrite hpow.
      pose proof (Nat.pow_nonzero 2 (len + 1) ltac:(lia)) as hpow1.
      nia. }
  replace
    (2 ^ (len + 3) * 2 ^ n - ((2 ^ (len + 3) - 1) * 2 ^ n - 1) - 1)
    with (2 ^ (len + 3) * 2 ^ n - ((2 ^ (len + 3) - 1) * 2 ^ n)).
  2:{ assert (0 < (2 ^ (len + 3) - 1) * 2 ^ n).
      { apply Nat.mul_pos_pos.
        - assert (1 < 2 ^ (len + 3)).
          { replace 1 with (2 ^ 0) by reflexivity.
            apply (proj1 (Nat.pow_lt_mono_r_iff 2 0 (len + 3) ltac:(lia))).
            lia. }
          lia.
        - apply Nat.pow_lower_bound.
          lia. }
      rewrite <- Nat.sub_add_distr.
      replace (((2 ^ (len + 3) - 1) * 2 ^ n - 1) + 1) with ((2 ^ (len + 3) - 1) * 2 ^ n) by lia.
      reflexivity. }
  assert (1 <= 2 ^ (len + 3)).
  { apply Nat.pow_lower_bound.
    lia. }
  replace (2 ^ (len + 3) * 2 ^ n) with ((((2 ^ (len + 3) - 1) + 1) * 2 ^ n)).
  2:{ f_equal.
      lia. }
  rewrite Nat.mul_add_distr_r.
  rewrite Nat.add_comm.
  rewrite Nat.add_sub.
  rewrite Nat.mul_1_l.
  reflexivity.
Qed.


Require Import Arith Lia PeanoNat.

Definition step := variant_step.

Definition seed (_ : nat) : nat := 2.

Lemma seed_0 : seed 0 = 2.
Proof.
  reflexivity.
Qed.

Lemma F_pos' : forall m, BMO3.F m <> 0.
Proof.
  exact (BMO3.F_pos seed seed_0).
Qed.

Lemma F_succ' : forall m,
  BMO3.F (S m) = BMO3.F m + 2 ^ (BMO3.v2 (S m) + 2) + 1.
Proof.
  exact (BMO3.F_succ seed seed_0).
Qed.

Lemma F_v2' : forall m, BMO3.v2 (BMO3.F m) = BMO3.v2 (m + 1).
Proof.
  exact (BMO3.F_v2 seed seed_0).
Qed.

Lemma v2_lower_bound_pos' :
  forall m, m <> 0 -> 2 ^ BMO3.v2 m <= m.
Proof.
  exact (BMO3.v2_lower_bound_pos seed seed_0).
Qed.

Lemma v2_pow2' : forall k, BMO3.v2 (2 ^ k) = k.
Proof.
  exact (BMO3.v2_pow2 seed seed_0).
Qed.

Lemma v2_odd' : forall n, BMO3.v2 (S (2 * n)) = 0.
Proof.
  exact (BMO3.v2_odd seed seed_0).
Qed.

Lemma T_ge : forall m, m <= BMO3.T m.
Proof.
  intro m.
  induction m as [|m ihm].
  - reflexivity.
  - simpl.
    assert (1 <= 2 ^ BMO3.v2 (S m)).
    { apply Nat.pow_lower_bound.
      lia. }
    lia.
Qed.

Lemma F_ge_5m1 : forall m, 5 * m + 1 <= BMO3.F m.
Proof.
  intro m.
  unfold BMO3.F.
  pose proof (T_ge m) as ht.
  nia.
Qed.

Lemma F_not_pow2 :
  forall m p, 2 <= m -> BMO3.F m <> 2 ^ p.
Proof.
  intros m p hm hpow.
  assert (hbound : 2 ^ BMO3.v2 (BMO3.F m) <= m + 1).
  { rewrite F_v2'.
    apply v2_lower_bound_pos'.
    lia. }
  rewrite hpow in hbound.
  rewrite v2_pow2' in hbound.
  pose proof (F_ge_5m1 m) as hlarge.
  lia.
Qed.

Lemma F_not_three_pow2 :
  forall m p, 2 <= m -> BMO3.F m <> 3 * 2 ^ p.
Proof.
  intros m p hm hpow.
  assert (hv : BMO3.v2 (BMO3.F m) = p).
  { rewrite hpow.
    apply v2_odd_mul_pow2.
    exists 1.
    reflexivity. }
  rewrite F_v2' in hv.
  assert (hbound : 2 ^ p <= m + 1).
  { rewrite <- hv.
    apply v2_lower_bound_pos'.
    lia. }
  pose proof (F_ge_5m1 m) as hlarge.
  lia.
Qed.

Lemma odd_nonzero (q : nat) : Nat.Odd q -> q <> 0.
Proof.
  intros [u hu].
  lia.
Qed.

Lemma odd_ge_5_of_F_factor :
  forall m q,
    2 <= m ->
    Nat.Odd q ->
    BMO3.F m = q * 2 ^ BMO3.v2 (BMO3.F m) ->
    5 <= q.
Proof.
  intros m q hm hq hqeq.
  destruct hq as [u hu].
  subst q.
  destruct u as [|[|u]].
  - exfalso.
    apply (F_not_pow2 m (BMO3.v2 (BMO3.F m))); [exact hm|].
    simpl in hqeq.
    rewrite Nat.add_0_r in hqeq.
    exact hqeq.
  - exfalso.
    apply (F_not_three_pow2 m (BMO3.v2 (BMO3.F m))); [exact hm|].
    simpl in hqeq.
    rewrite Nat.add_0_r in hqeq.
    replace (3 * 2 ^ BMO3.v2 (BMO3.F m))
      with (2 ^ BMO3.v2 (BMO3.F m) + (2 ^ BMO3.v2 (BMO3.F m) + 2 ^ BMO3.v2 (BMO3.F m))) by lia.
    exact hqeq.
  - lia.
Qed.

Definition counter_len (k : nat) : nat :=
  Nat.log2 (BMO3.F (k + 2)).

Definition counter_state (k : nat) : state :=
  (counter_len k, 2 ^ (counter_len k + 1) - BMO3.F (k + 2)).

Lemma counter_len_spec :
  forall k, 2 ^ counter_len k <= BMO3.F (k + 2) < 2 ^ (counter_len k + 1).
Proof.
  intro k.
  unfold counter_len.
  replace (Nat.log2 (BMO3.F (k + 2)) + 1) with (S (Nat.log2 (BMO3.F (k + 2)))) by lia.
  apply Nat.log2_spec.
  apply Nat.neq_0_lt_0.
  apply F_pos'.
Qed.

Lemma counter_state_start :
  counter_state 0 = start.
Proof.
  unfold counter_state, counter_len, start.
  change ((Nat.log2 (BMO3.F 2), 2 ^ (Nat.log2 (BMO3.F 2) + 1) - BMO3.F 2) = (3, 1)).
  assert (hf : BMO3.F 2 = 15).
  { unfold BMO3.F.
    simpl.
    change 2 with (2 ^ 1).
    rewrite v2_pow2'.
    change 1 with (S (2 * 0)).
    rewrite v2_odd'.
    simpl.
    reflexivity. }
  rewrite hf.
  vm_compute.
  reflexivity.
Qed.

Lemma odd_factor_log2_ge2 :
  forall m q,
    2 <= m ->
    Nat.Odd q ->
    BMO3.F m = q * 2 ^ BMO3.v2 (BMO3.F m) ->
    2 <= Nat.log2 q.
Proof.
  intros m q hm hq hqeq.
  pose proof (odd_ge_5_of_F_factor m q hm hq hqeq) as hq5.
  replace 2 with (Nat.log2 4).
  2:{ change 4 with (2 ^ 2).
      rewrite Nat.log2_pow2 by lia.
      reflexivity. }
  apply Nat.log2_le_mono.
  lia.
Qed.

Lemma counter_len_from_factor :
  forall k q,
    Nat.Odd q ->
    BMO3.F (k + 2) = q * 2 ^ BMO3.v2 (BMO3.F (k + 2)) ->
    counter_len k = BMO3.v2 (BMO3.F (k + 2)) + Nat.log2 q.
Proof.
  intros k q hq hqeq.
  unfold counter_len.
  rewrite hqeq at 1.
  replace (Nat.log2 (q * 2 ^ BMO3.v2 (BMO3.F (k + 2))))
    with (BMO3.v2 (BMO3.F (k + 2)) + Nat.log2 q).
  2:{ rewrite Nat.log2_mul_pow2.
      - reflexivity.
      - apply Nat.neq_0_lt_0.
        apply odd_nonzero.
        exact hq.
      - lia. }
  rewrite Nat.add_comm.
  reflexivity.
Qed.

Lemma odd_complement_of_factor :
  forall m q,
    2 <= m ->
    Nat.Odd q ->
    BMO3.F m = q * 2 ^ BMO3.v2 (BMO3.F m) ->
    let d := Nat.log2 q in
    let p := 2 ^ (d + 1) - q in
    Nat.Odd p /\ 1 <= p < 2 ^ d.
Proof.
  intros m q hm hq hqeq d p.
  assert (hd_ge2 : 2 <= d).
  { unfold d.
    apply odd_factor_log2_ge2 with (m := m); assumption. }
  assert (hq_pos : 0 < q).
  { apply Nat.neq_0_lt_0.
    apply odd_nonzero.
    exact hq. }
  assert (hqspec : 2 ^ d <= q < 2 ^ (d + 1)).
  { unfold d.
    replace (Nat.log2 q + 1) with (S (Nat.log2 q)) by lia.
    apply Nat.log2_spec.
    exact hq_pos. }
  assert (hq_gt : 2 ^ d < q).
  { destruct hqspec as [hlo _].
    destruct (Nat.eq_dec q (2 ^ d)) as [heq|hneq].
    - exfalso.
      apply Nat.odd_spec in hq.
      rewrite heq in hq.
      rewrite pow2_odd_false in hq by lia.
      discriminate.
    - lia. }
  split.
  - unfold p.
    apply odd_sub_pow2.
    + lia.
    + exact hq.
    + exact (proj2 hqspec).
  - unfold p.
    split.
    + lia.
    + replace (2 ^ (d + 1)) with (2 ^ d + 2 ^ d).
      2:{ replace (d + 1) with (S d) by lia.
          rewrite Nat.pow_succ_r' by lia.
          simpl.
          lia. }
      assert (2 ^ d + 1 <= q) as hgt1 by lia.
      assert (exists t, q = 2 ^ d + S t) as [t ht].
      { exists (q - 2 ^ d - 1).
        lia. }
      rewrite ht.
      replace (2 ^ d + 2 ^ d - (2 ^ d + S t)) with (2 ^ d - S t) by lia.
      apply Nat.sub_lt.
      * replace (2 ^ (d + 1)) with (2 ^ d + 2 ^ d) in hqspec.
        2:{ replace (d + 1) with (S d) by lia.
            rewrite Nat.pow_succ_r' by lia.
            simpl.
            lia. }
        lia.
      * lia.
Qed.

Lemma ov1_target_arith :
  forall x y,
    1 <= x ->
    1 <= y ->
    8 * x * y - (((4 * x - 1) * y) + 4 * y + 1) = (4 * x - 3) * y - 1.
Proof.
  intros x y hx hy.
  nia.
Qed.

Lemma ov2_target_arith :
  forall x y,
    1 <= x ->
    1 <= y ->
    8 * x * y - (((4 * x - 3) * y) + 4 * y + 1) = (4 * x - 1) * y - 1.
Proof.
  intros x y hx hy.
  nia.
Qed.

Lemma inc_target_arith :
  forall a p r,
    p <= a ->
    2 <= (p - 4) * 2 ^ r ->
    a * 2 ^ r - (((a - p) * 2 ^ r) + 4 * 2 ^ r + 1) = (p - 4) * 2 ^ r - 1.
Proof.
  intros a p r hpa hgap.
  nia.
Qed.

Lemma counter_state_step :
  forall k, step (counter_state k) (counter_state (S k)).
Proof.
  intro k.
  set (a := BMO3.F (k + 2)).
  set (r := BMO3.v2 a).
  assert (ha_pos : a <> 0).
  { unfold a.
    apply F_pos'. }
  destruct (v2_factor_odd a ha_pos) as [q [hq hqeq]].
  set (d := Nat.log2 q).
  set (p := 2 ^ (d + 1) - q).
  assert (hd_ge2 : 2 <= d).
  { unfold d.
    apply odd_factor_log2_ge2 with (m := k + 2); try assumption.
    lia. }
  assert (hlen : counter_len k = r + d).
  { unfold r, d, a.
    exact (counter_len_from_factor k q hq hqeq). }
  assert (hp : Nat.Odd p /\ 1 <= p < 2 ^ d).
  { unfold p, d, a.
    apply odd_complement_of_factor with (m := k + 2); auto.
    lia. }
  assert (ha_repr : a = q * 2 ^ r).
  { unfold r in hqeq.
    exact hqeq. }
  assert (hx :
    2 ^ (counter_len k + 1) - BMO3.F (k + 2) = p * 2 ^ r).
  { rewrite hlen.
    unfold a in ha_repr.
    rewrite ha_repr.
    unfold p, d.
    replace (r + Nat.log2 q + 1) with (Nat.log2 q + 1 + r) by lia.
    rewrite Nat.pow_add_r by lia.
    nia. }
  assert (ha_next :
    BMO3.F (k + 3) = a + 2 ^ (r + 2) + 1).
  { unfold a, r.
    replace (k + 3) with (S (k + 2)) by lia.
    rewrite F_succ'.
    replace (S (k + 2)) with (k + 2 + 1) by lia.
    rewrite <- F_v2' with (m := k + 2).
    reflexivity. }
  assert (hr_pos : 1 <= 2 ^ r).
  { apply Nat.pow_lower_bound.
    lia. }
  assert (hr2 : 2 ^ (r + 2) = 4 * 2 ^ r).
  { replace (r + 2) with (2 + r) by lia.
    rewrite Nat.pow_add_r by lia.
    simpl.
    nia. }
  assert (hd_pow : 4 <= 2 ^ d).
  { replace 4 with (2 ^ 2) by reflexivity.
    apply Nat.pow_le_mono_r.
    lia.
    exact hd_ge2. }
  set (len0 := d - 2).
  assert (hlen0 : counter_len k = len0 + 2 + r).
  { unfold len0.
    rewrite hlen.
    lia. }
  destruct hp as [hp_odd [hp_lo hp_hi]].
  destruct hp_odd as [u hu].
  destruct u as [|u].
  - assert (hq1 : q = 2 ^ (d + 1) - 1).
    { unfold p in hu.
      lia. }
    assert (hsrc :
      counter_state k = (len0 + 2 + r, (0 * 2 + 1) * 2 ^ r)).
    { unfold counter_state.
      rewrite hx, hlen0, hu.
      reflexivity. }
    assert (hlen_next : counter_len (S k) = len0 + 3 + r).
    { unfold counter_len.
      apply Nat.log2_unique.
      - lia.
      - replace (S k + 2) with (k + 3) by lia.
        rewrite ha_next, ha_repr, hq1.
        rewrite hr2.
        split.
        + replace (len0 + 3 + r) with (d + 1 + r) by (unfold len0; lia).
          replace (d + 1 + r) with ((d + 1) + r) by lia.
          rewrite !Nat.pow_add_r by lia.
          nia.
        + replace (S (len0 + 3 + r)) with (d + 2 + r) by (unfold len0; lia).
          replace (d + 2 + r) with ((d + 2) + r) by lia.
          rewrite !Nat.pow_add_r by lia.
          replace (2 ^ (d + 2)) with (4 * 2 ^ d).
          2:{ replace (d + 2) with (S (S d)) by lia.
              rewrite Nat.pow_succ_r' by lia.
              rewrite Nat.pow_succ_r' by lia.
              simpl.
              nia. }
          replace (2 ^ (d + 1)) with (2 * 2 ^ d).
          2:{ replace (d + 1) with (S d) by lia.
              rewrite Nat.pow_succ_r' by lia.
              nia. }
          replace (2 ^ 1) with 2 by reflexivity.
          replace (2 ^ d * 2) with (2 * 2 ^ d) by nia.
          assert (hgap : 1 < (2 * 2 ^ d - 3) * 2 ^ r) by nia.
          change (2 ^ d * 2 ^ 2 * 2 ^ r) with (2 ^ d * 4 * 2 ^ r).
          assert (hdiff :
            2 ^ d * 4 * 2 ^ r =
            ((2 * 2 ^ d - 1) * 2 ^ r + 4 * 2 ^ r + 1) +
            (((2 * 2 ^ d - 3) * 2 ^ r) - 1)).
          { nia. }
          rewrite hdiff.
          apply Nat.lt_add_pos_r.
          lia. }
    assert (htgt :
      counter_state (S k) =
      (len0 + 3 + r,
       ((((2 ^ (len0 + 1) - 1) * 2) * 2 + 1) * 2 ^ r) - 1)).
    { unfold counter_state.
      rewrite hlen_next.
      replace (S k + 2) with (k + 3) by lia.
      rewrite ha_next, ha_repr, hq1.
      rewrite hr2.
      replace (len0 + 3 + r + 1) with ((d + 2) + r) by (unfold len0; lia).
      rewrite Nat.pow_add_r by lia.
      replace (len0 + 1) with (d - 1) by (unfold len0; lia).
      assert (hd1 : 1 <= d - 1) by lia.
      replace (2 ^ (d + 2)) with (8 * 2 ^ (d - 1)).
      2:{ replace (d + 2) with ((d - 1) + 3) by lia.
          rewrite Nat.pow_add_r by lia.
          simpl.
          nia. }
      replace (2 ^ (d + 1)) with (4 * 2 ^ (d - 1)).
      2:{ replace (d + 1) with ((d - 1) + 2) by lia.
          rewrite Nat.pow_add_r by lia.
          simpl.
          nia. }
      assert (hpow_dm1 : 1 <= 2 ^ (d - 1)).
      { apply Nat.pow_lower_bound.
        lia. }
      replace ((((2 ^ (d - 1) - 1) * 2) * 2 + 1))
        with (4 * 2 ^ (d - 1) - 3) by nia.
      rewrite (ov1_target_arith (2 ^ (d - 1)) (2 ^ r) hpow_dm1 hr_pos).
      reflexivity. }
    rewrite hsrc, htgt.
    apply BMO3VariantMinus.Ov1.
  - destruct u as [|m].
    + assert (hq3 : q = 2 ^ (d + 1) - 3).
      { unfold p in hu.
        lia. }
      assert (hsrc :
        counter_state k = (len0 + 2 + r, ((0 * 2 + 1) * 2 + 1) * 2 ^ r)).
      { unfold counter_state.
        rewrite hx, hlen0, hu.
        reflexivity. }
      assert (hlen_next : counter_len (S k) = len0 + 3 + r).
      { unfold counter_len.
        apply Nat.log2_unique.
        - lia.
        - replace (S k + 2) with (k + 3) by lia.
          rewrite ha_next, ha_repr, hq3.
          rewrite hr2.
          split.
          + replace (len0 + 3 + r) with (d + 1 + r) by (unfold len0; lia).
            replace (d + 1 + r) with ((d + 1) + r) by lia.
            rewrite !Nat.pow_add_r by lia.
            nia.
          + replace (S (len0 + 3 + r)) with (d + 2 + r) by (unfold len0; lia).
            replace (d + 2 + r) with ((d + 2) + r) by lia.
            rewrite !Nat.pow_add_r by lia.
            replace (2 ^ (d + 2)) with (4 * 2 ^ d).
            2:{ replace (d + 2) with (S (S d)) by lia.
                rewrite Nat.pow_succ_r' by lia.
                rewrite Nat.pow_succ_r' by lia.
                simpl.
                nia. }
            replace (2 ^ (d + 1)) with (2 * 2 ^ d).
            2:{ replace (d + 1) with (S d) by lia.
                rewrite Nat.pow_succ_r' by lia.
                nia. }
            replace (2 ^ 1) with 2 by reflexivity.
            replace (2 ^ d * 2) with (2 * 2 ^ d) by nia.
            assert (hgap : 1 < (2 * 2 ^ d - 1) * 2 ^ r) by nia.
            change (2 ^ d * 2 ^ 2 * 2 ^ r) with (2 ^ d * 4 * 2 ^ r).
            assert (hdiff :
              2 ^ d * 4 * 2 ^ r =
              ((2 * 2 ^ d - 3) * 2 ^ r + 4 * 2 ^ r + 1) +
              (((2 * 2 ^ d - 1) * 2 ^ r) - 1)).
            { nia. }
            rewrite hdiff.
            apply Nat.lt_add_pos_r.
            lia. }
      assert (htgt :
        counter_state (S k) =
        (len0 + 3 + r,
         ((((2 ^ (len0 + 1) - 1) * 2 + 1) * 2 + 1) * 2 ^ r) - 1)).
      { unfold counter_state.
        rewrite hlen_next.
        replace (S k + 2) with (k + 3) by lia.
        rewrite ha_next, ha_repr, hq3.
        rewrite hr2.
        replace (len0 + 3 + r + 1) with ((d + 2) + r) by (unfold len0; lia).
        rewrite Nat.pow_add_r by lia.
        replace (len0 + 1) with (d - 1) by (unfold len0; lia).
        assert (hd1 : 1 <= d - 1) by lia.
        replace (2 ^ (d + 2)) with (8 * 2 ^ (d - 1)).
        2:{ replace (d + 2) with ((d - 1) + 3) by lia.
            rewrite Nat.pow_add_r by lia.
            simpl.
            nia. }
        replace (2 ^ (d + 1)) with (4 * 2 ^ (d - 1)).
        2:{ replace (d + 1) with ((d - 1) + 2) by lia.
            rewrite Nat.pow_add_r by lia.
            simpl.
            nia. }
        assert (hpow_dm1 : 1 <= 2 ^ (d - 1)).
        { apply Nat.pow_lower_bound.
          lia. }
        replace ((((2 ^ (d - 1) - 1) * 2 + 1) * 2 + 1))
          with (4 * 2 ^ (d - 1) - 1) by nia.
        rewrite (ov2_target_arith (2 ^ (d - 1)) (2 ^ r) hpow_dm1 hr_pos).
        reflexivity. }
      rewrite hsrc, htgt.
      apply BMO3VariantMinus.Ov2.
    + assert (hpm : p = ((m + 2) * 2 + 1)).
      { rewrite hu.
        nia. }
      assert (hm_lt : m + 2 < 2 ^ (len0 + 1)).
      { assert (hpm_lt : ((m + 2) * 2 + 1) < 2 ^ d).
        { rewrite <- hpm.
          exact hp_hi. }
        replace (len0 + 1) with (d - 1) by (unfold len0; lia).
        assert (hdouble : 2 * (m + 2) < 2 ^ d) by nia.
        replace (2 ^ d) with (2 * 2 ^ (d - 1)) in hdouble.
        2:{ replace d with (S (d - 1)) by lia.
            rewrite Nat.pow_succ_r' by lia.
            replace (S (d - 1) - 1) with (d - 1) by lia.
            rewrite Nat.mul_comm.
            reflexivity. }
        apply (proj2 (Nat.mul_lt_mono_pos_l 2 (m + 2) (2 ^ (d - 1)) ltac:(lia))).
        exact hdouble. }
      assert (hgap : 2 <= (p - 4) * 2 ^ r).
      { destruct (Nat.lt_ge_cases ((p - 4) * 2 ^ r) 2) as [hsmall|hge].
        - assert (hprod : (p - 4) * 2 ^ r = 1) by lia.
          assert (hr0 : r = 0).
          { destruct r as [|r'].
            - reflexivity.
            - pose proof (Nat.pow_nonzero 2 (S r') ltac:(lia)) as hpow.
              simpl in hprod.
              nia. }
          assert (hp5 : p = 5).
          { rewrite hr0 in hprod.
            simpl in hprod.
            nia. }
          assert (hq5 : q = 2 ^ (d + 1) - 5).
          { unfold p in hp5.
            lia. }
          assert (hpow2 : BMO3.F (k + 3) = 2 ^ (d + r + 1)).
          { rewrite hr0 in *.
            rewrite ha_next, ha_repr, hq5.
            replace (d + 0 + 1) with (d + 1) by lia.
            simpl.
            nia. }
          exfalso.
          apply (F_not_pow2 (k + 3) (d + r + 1)).
          + lia.
          + exact hpow2.
        - exact hge. }
      assert (hsrc :
        counter_state k = (len0 + 2 + r, ((m + 2) * 2 + 1) * 2 ^ r)).
      { unfold counter_state.
        rewrite hx, hlen0, hpm.
        reflexivity. }
      assert (hlen_next : counter_len (S k) = len0 + 2 + r).
      { unfold counter_len.
        apply Nat.log2_unique.
        - lia.
        - replace (S k + 2) with (k + 3) by lia.
          rewrite ha_next, ha_repr.
          rewrite hr2.
          split.
          + replace (len0 + 2 + r) with (d + r) by (unfold len0; lia).
            assert (hbase : 2 ^ (d + r) <= q * 2 ^ r).
            { pose proof (counter_len_spec k) as hspec.
              rewrite hlen in hspec.
              change (BMO3.F (k + 2)) with a in hspec.
              rewrite ha_repr in hspec.
              replace (d + r) with (r + d) by lia.
              exact (proj1 hspec). }
            nia.
          + replace (S (len0 + 2 + r)) with (d + 1 + r) by (unfold len0; lia).
            replace (d + 1 + r) with ((d + 1) + r) by lia.
            rewrite Nat.pow_add_r by lia.
            assert (hupper :
              q * 2 ^ r + 2 ^ (r + 2) + 1 <= 2 ^ (d + 1) * 2 ^ r - 1).
            { unfold p in hgap.
              assert (hqeq' : q = 2 ^ (d + 1) - p) by lia.
              rewrite hqeq'.
              rewrite hr2.
              repeat rewrite Nat.pow_add_r in *.
              lia. }
            repeat rewrite Nat.pow_add_r in *.
            lia. }
      assert (htgt :
        counter_state (S k) =
        (len0 + 2 + r, ((m * 2 + 1) * 2 ^ r) - 1)).
      { unfold counter_state.
        rewrite hlen_next.
        replace (S k + 2) with (k + 3) by lia.
        rewrite ha_next, ha_repr.
        rewrite hr2.
        replace (len0 + 2 + r + 1) with ((d + 1) + r) by (unfold len0; lia).
        rewrite Nat.pow_add_r by lia.
        replace q with (2 ^ (d + 1) - p) by (unfold p; lia).
        assert (hp_le : p <= 2 ^ (d + 1)).
        { apply Nat.lt_le_incl.
          eapply Nat.lt_trans.
          - exact hp_hi.
          - replace (2 ^ (d + 1)) with (2 * 2 ^ d).
            2:{ replace (d + 1) with (S d) by lia.
                rewrite Nat.pow_succ_r' by lia.
                nia. }
            nia. }
        rewrite (inc_target_arith (2 ^ (d + 1)) p r hp_le hgap).
        rewrite hpm.
        replace ((m + 2) * 2 + 1 - 4) with (m * 2 + 1) by (clear; lia).
        reflexivity. }
      rewrite hsrc, htgt.
      apply BMO3VariantMinus.Inc.
      exact hm_lt.
Qed.


End BMO3VariantMinus.

From BusyCoq Require Import Individual25.
From BusyCoq Require Import BinaryCounter25_v2 DivModCases.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Open Scope list.

Module TM3.
Import BMO3VariantMinus.

Definition tm := Eval compute in (TM_from_str "1RB0RA3LA4LA2RA_2LB3LA---4RA3RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition RC (tp:bool) len n := BinDec [3] [4] len n ((if tp then [2] else [])*>0inf).

Lemma RC_Inc l r len n:
  n+1<2^len ->
  l {{A}}> RC r len (n+1) -->*
  l <{{A}} RC r len n.
Proof.
  rewrite (Nat.add_comm n 1).
  intros H.
  eapply progress_evstep.
  apply RBinDec_spec with (qL:=[]) (qR:=[]); try assumption.
  es.
Qed.

Notation "l |> r" := (l {{B}}> r) (at level 30).


Definition S0 '(tp,len,n) :=
  0inf<*<[1] |> RC tp len n.

Lemma Inc tp len n m:
  m+2<2^len*2 ->
  S0 (tp, (len+1+1+n), (((m+2)*2+1)*2^n)) -->+
  S0 (tp, (len+1+1+n), ((m*2+1)*2^n-1)).
Proof.
  intros H.
  unfold S0.
  destruct (mod2 m); subst.
  - replace (a*2+2) with ((a+1)*2) by lia.
    unfold RC.
    rw_Bin'.
    2: nia.
    es; er.
    follow RC_Inc.
    1: lia.
    es.
  - replace (1+a*2) with (a*2+1) by lia.
    replace (a*2+1+2) with ((a+1)*2+1) by lia.
    unfold RC.
    rw_Bin'.
    2: nia.
    es; er.
    follow RC_Inc.
    1: lia.
    es.
Qed.

Lemma Ov1 tp len n:
  S0 (tp, (len+1+1+n), ((0*2+1)*2^n)) -->+
  S0 (negb tp, (len+1+1+1+n), ((((2^(len+1)-1)*2)*2+1)*2^n-1)).
Proof.
  unfold S0,RC.
  rw_Bin'.
  destruct tp;
  es.
Qed.

Lemma Ov2 tp len n:
  S0 (tp, (len+1+1+n), (((0*2+1)*2+1)*2^n)) -->+
  S0 (negb tp, (len+1+1+1+n), ((((2^(len+1)-1)*2+1)*2+1)*2^n-1)).
Proof.
  unfold S0,RC.
  rw_Bin'.
  destruct tp;
  es.
Qed.

Local Transparent BinDec.

Lemma init:
  c0 -->*
  S0 (false,3,1)%nat.
Proof.
  unfold S0,RC.
  er.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(tp,len,n) => exists k, (len,n) = counter_state k).
  2: exists O; rewrite counter_state_start; reflexivity.
  intros [[tp len] n] [k I0].
  epose proof (counter_state_step k) as I1.
  remember (counter_state k) as v1.
  remember (counter_state (S k)) as v2.
  clear Heqv1.
  subst v1.
  destruct v2 as [len' n'].
  inverts I1.
  - rewrite Nat.pow_add_r in H0.
    eexists (_,_,_); split.
    2: eexists; apply Heqv2.
    applys_eq (Inc tp len0 n0 m); flia.
  - eexists (_,_,_); split.
    2: eexists; apply Heqv2.
    applys_eq (Ov1 tp len0 n0); flia.
  - eexists (_,_,_); split.
    2: eexists; apply Heqv2.
    applys_eq (Ov2 tp len0 n0); flia.
Qed.

End TM3.


