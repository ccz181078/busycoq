From BusyCoq Require Import Individual62.
From BusyCoq Require Import Longitudinal.
Require Import ZifyNat Lia PeanoNat String List.

Open Scope list.

Definition tm := Eval compute in (TM_from_str "1LB1RD_0LC0LB_1RD1RA_0RE---_1RF0RD_1RA0RB").

Notation hR := (E,<[0]).
Notation hL := (C,[0;0]).
Notation hRp := (F,<[0;1]).
Notation z := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation zP := [(hRp,hL)].

Notation Sx := ([1;0]:list Sym).
Notation P := ([0]:list Sym).
Notation X := ([0;1;0]:list Sym).
Notation M := ([0;0;1;0]:list Sym).
Notation N := ([0;1;1;0]:list Sym).

Definition tm' := flip tm.

Definition LC n := 0inf <* <[1;0;1]^^n <* <[1].

Lemma LIncs k n:
  sideRLs tm' (hLR^^k) (LC n) (LC (k+n)).
Proof.
  gen n.
  induction k; intros.
  - esx.
  - cbn[lpow].
    eapply sideRLs_trans.
    2: applys_eq (IHk (S n)); flia.
    esx.
Qed.

Open Scope nat_scope.

Fixpoint a (n:nat) :=
match n with
| 0 => 1
| S n => 3 * a n + 2^n + 2
end.

Definition b n := 2^n.
Definition g n := 3^(S n).
Definition x n := 2^(S n)-1.

Lemma a_g n:
  a n + b n + 1 = g n.
Proof.
  unfold b,g.
  induction n.
  - cbn. lia.
  - cbn [a Nat.pow].
    cbn [Nat.pow] in IHn.
    lia.
Qed.

Lemma b_pos n: b n > 0.
Proof.
  unfold b.
  pose proof (Nat.pow_nonzero 2 n ltac:(lia)).
  lia.
Qed.

Lemma b_le_a1 n:
  b n <= a n + 1.
Proof.
  unfold b.
  induction n.
  - cbn. lia.
  - cbn [a Nat.pow].
    lia.
Qed.

Lemma xS n:
  S (x n) = 2^(S n).
Proof.
  unfold x.
  pose proof (Nat.pow_nonzero 2 (S n)).
  lia.
Qed.

Lemma x_b n:
  x n = 2 * b n - 1.
Proof.
  unfold x,b.
  cbn [Nat.pow].
  reflexivity.
Qed.

Lemma bx n:
  b n - 1 + b n = x n.
Proof.
  rewrite x_b.
  pose proof (b_pos n).
  lia.
Qed.

Lemma x_step n:
  x (S n) = x n + 2^(S n).
Proof.
  unfold x.
  pose proof (Nat.pow_nonzero 2 (S n)).
  cbn [Nat.pow].
  lia.
Qed.

Lemma g_step n:
  g (S n) = g n + 2 * g n.
Proof.
  unfold g.
  cbn [Nat.pow].
  lia.
Qed.

Lemma a_step n:
  a (S n) = 3 * a n + b n + 2.
Proof.
  unfold b.
  cbn [a].
  reflexivity.
Qed.

Lemma z_g_step n:
  z^^(g (S n)) = z^^(g n) ++ z^^(2 * g n).
Proof.
  rewrite <-lpow_add.
  rewrite g_step.
  reflexivity.
Qed.

Lemma z_a_tail_step n c:
  z^^(a (S n) + c) ++ zP ++ z^^(b (S n) - 1) =
  z^^(a n + b n + c) ++ (z^^(2 * a n + 2) ++ zP ++ z^^(2^(S n)-1)).
Proof.
  repeat rewrite <-app_assoc.
  rewrite (app_assoc (z^^(a n + b n + c)) (z^^(2 * a n + 2))
    (zP ++ z^^(2^(S n)-1))).
  rewrite <-lpow_add.
  replace (a n + b n + c + (2 * a n + 2)) with (a (S n) + c) by
    (rewrite a_step; lia).
  unfold b.
  cbn [Nat.pow].
  reflexivity.
Qed.

Lemma R_X : segRLs tm z z X X.
Proof. esx. Qed.

Lemma R_M : segRLs tm z z M M.
Proof. esx. Qed.

Lemma R_PX : segRLs tm zP z X M.
Proof. esx. Qed.

Lemma R_PS : segRLs tm zP z Sx X.
Proof. esx. Qed.

Lemma Z_X_one m:
  segRLs tm z z (X^^m) (X^^m).
Proof.
  induction m.
  - cbn. apply segRLs_nil.
  - cbn [lpow].
    eapply segRLs_concat.
    + apply R_X.
    + apply IHm.
Qed.

Lemma Z_Xs n m:
  segRLs tm (z^^n) (z^^n) (X^^m) (X^^m).
Proof.
  apply segRLs_wall''.
  apply Z_X_one.
Qed.

Lemma Z_MX_one m:
  segRLs tm z z (M++X^^m) (M++X^^m).
Proof.
  eapply segRLs_concat.
  - apply R_M.
  - apply Z_X_one.
Qed.

Lemma Z_MXs n m:
  segRLs tm (z^^n) (z^^n) (M++X^^m) (M++X^^m).
Proof.
  apply segRLs_wall''.
  apply Z_MX_one.
Qed.

Lemma ZP_X a0:
  segRLs tm (z^^a0++zP) (z^^(a0+1)) X M.
Proof.
  induction a0.
  - cbn. apply R_PX.
  - cbn [lpow].
    change (S a0 + 1) with (S (a0+1)).
    cbn [lpow].
    eapply (@segRLs_trans tm z z (z^^a0++zP) (z^^(a0+1)) X X M).
    + apply R_X.
    + apply IHa0.
Qed.

Lemma ZP_X_suf a0 b0:
  segRLs tm (z^^a0 ++ zP ++ z^^b0) (z^^(a0+1+b0)) X M.
Proof.
  replace (z^^a0 ++ zP ++ z^^b0) with ((z^^a0++zP)++z^^b0) by
    (rewrite app_assoc; reflexivity).
  replace (z^^(a0+1+b0)) with (z^^(a0+1)++z^^b0) by
    (rewrite <-lpow_add; f_equal; lia).
  eapply segRLs_trans.
  - apply ZP_X.
  - replace M with (M++X^^0) at 1 by reflexivity.
    replace M with (M++X^^0) at 2 by reflexivity.
    apply Z_MXs.
Qed.

Lemma PX_to_M a0 b0 m:
  segRLs tm (z^^a0 ++ zP ++ z^^b0) (z^^(a0+1+b0))
    (X^^(S m)) (M++X^^m).
Proof.
  cbn [lpow].
  eapply segRLs_concat.
  - apply ZP_X_suf.
  - apply Z_Xs.
Qed.

Lemma ZP_S_suf b0:
  segRLs tm (zP++z^^b0) (z^^(S b0)) Sx X.
Proof.
  change (z^^(S b0)) with (z++z^^b0).
  eapply segRLs_trans.
  - apply R_PS.
  - change X with (X^^1) at 1.
    change X with (X^^1) at 2.
    apply Z_Xs.
Qed.

Lemma PS_to_X b0 m:
  segRLs tm (zP++z^^b0) (z^^(S b0)) (Sx++X^^m) (X^^(S m)).
Proof.
  cbn [lpow].
  eapply segRLs_concat.
  - apply ZP_S_suf.
  - apply Z_Xs.
Qed.

Lemma Z_X_side_one m:
  sideRLs tm z (X^^m *> 0inf) (X^^(S m) *> 0inf).
Proof.
  induction m.
  - cbn. esx.
  - cbn [lpow].
    eapply (@segRLs_sideRLs_concat tm z z X X
      (X^^m *> 0inf) (X^^(S m) *> 0inf)).
    + apply R_X.
    + apply IHm.
Qed.

Lemma Z_prefix_X_side p:
  segRLs tm z z p p ->
  forall k m, sideRLs tm (z^^k)
    ((p++X^^m) *> 0inf) ((p++X^^(k+m)) *> 0inf).
Proof.
  intros Hp k.
  induction k.
  all: intro m.
  - cbn. replace (0 + m) with m by lia. constructor.
  - cbn [lpow].
    eapply (@sideRLs_trans tm z (z^^k)
      ((p++X^^m) *> 0inf)
      ((p++X^^(S m)) *> 0inf)
      ((p++X^^(S k + m)) *> 0inf)).
    + repeat rewrite Str_app_assoc.
      eapply (@segRLs_sideRLs_concat tm z z p p
        (X^^m *> 0inf) (X^^(S m) *> 0inf)).
      * apply Hp.
      * apply Z_X_side_one.
    + replace (S k + m) with (k + S m) by lia.
      apply IHk.
Qed.

Lemma Z_X_side k m:
  sideRLs tm (z^^k) (X^^m *> 0inf) (X^^(k+m) *> 0inf).
Proof.
  applys_eq (Z_prefix_X_side [] segRLs_nil k m).
Qed.

Lemma ZP_X_side m:
  sideRLs tm zP (X^^(S m) *> 0inf) ((M++X^^(S m)) *> 0inf).
Proof.
  cbn [lpow].
  eapply (@segRLs_sideRLs_concat tm zP z X M
    (X^^m *> 0inf) (X^^(S m) *> 0inf)).
  - apply R_PX.
  - apply Z_X_side_one.
Qed.

Lemma Z_suffix_side a0 b0 m:
  a0 > 0 ->
  sideRLs tm (z^^a0 ++ zP ++ z^^b0)
    (X^^m *> 0inf)
    ((M++X^^(b0 + (a0 + m))) *> 0inf).
Proof.
  intro Ha0.
  eapply (@sideRLs_trans tm (z^^a0) (zP++z^^b0)
    (X^^m *> 0inf)
    (X^^(a0+m) *> 0inf)
    ((M++X^^(b0 + (a0 + m))) *> 0inf)).
  - apply Z_X_side.
  - replace (X^^(a0+m)) with (X^^(S (a0+m-1))) by flia.
    eapply (@sideRLs_trans tm zP (z^^b0)
      (X^^(S (a0+m-1)) *> 0inf)
      ((M++X^^(S (a0+m-1))) *> 0inf)
      ((M++X^^(b0 + (a0 + m))) *> 0inf)).
    + apply ZP_X_side.
    + replace (b0 + (a0 + m)) with (b0 + S (a0+m-1)) by lia.
      apply Z_prefix_X_side.
      apply R_M.
Qed.

Definition P1 n :=
  segRLs tm (z^^(g n))
    (z^^(a n + 2) ++ zP ++ z^^(b n - 1))
    (Sx ++ X^^(x n))
    (Sx ++ X^^(x n)).

Definition P2 n :=
  segRLs tm (zP ++ z^^(g n))
    (z^^(a n) ++ zP ++ z^^(b n - 1))
    (M ++ X^^(x n))
    (Sx ++ X^^(x n)).

Definition P3 n :=
  segRLs tm (z^^(2 * g n))
    (z^^(2 * a n + 2) ++ zP ++ z^^(2^(S n)-1))
    (Sx ++ X^^(x n) ++ M ++ X^^(x n))
    (Sx ++ X^^(x (S n))).

Lemma P1_0: P1 0.
Proof.
  unfold P1.
  cbn [a b g x Nat.pow].
  esx.
Qed.

Lemma P2_0: P2 0.
Proof.
  unfold P2.
  cbn [a b g x Nat.pow].
  esx.
Qed.

Lemma Pre_P1 n:
  P1 n ->
  segRLs tm (z^^(g n)) (z^^(a n + b n + 2))
    (Sx ++ X^^(x n) ++ X^^(2^(S n)))
    (Sx ++ X^^(x n) ++ M ++ X^^(x n)).
Proof.
  unfold P1.
  intro HP1.
  rewrite app_assoc.
  applys_eq (segRLs_concat HP1 (PX_to_M (a n + 2) (b n - 1) (x n))).
  - pose proof (b_pos n). flia.
  - rewrite xS. reflexivity.
Qed.

Lemma P3_suffix_in n:
  ((z^^(a n + 2) ++ zP ++ z^^(b n - 1)) ++
   (z^^(a n + 2) ++ zP ++ z^^(b n - 1))) =
  (z^^(a n + 2) ++ (zP ++ z^^(g n)) ++ (zP ++ z^^(b n - 1))).
Proof.
  repeat rewrite <- app_assoc.
  rewrite (app_assoc (z^^(b n - 1)) (z^^(a n + 2))
    (zP ++ z^^(b n - 1))).
  rewrite <-lpow_add, <-a_g.
  pose proof (b_pos n).
  flia.
Qed.

Lemma P3_suffix_out n:
  z^^(2 * a n + 2) ++ zP ++ z^^(2^(S n)-1) =
  z^^(a n + 2) ++ (z^^(a n) ++ zP ++ z^^(b n - 1)) ++ z^^(b n).
Proof.
  repeat rewrite <- app_assoc.
  rewrite (app_assoc (z^^(a n + 2)) (z^^(a n))
    (zP ++ z^^(b n - 1) ++ z^^(b n))).
  repeat rewrite <-lpow_add.
  unfold b.
  cbn [Nat.pow].
  pose proof (b_pos n).
  flia.
Qed.

Lemma P3_suffix n:
  P2 n ->
  segRLs tm
    ((z^^(a n + 2) ++ zP ++ z^^(b n - 1)) ++
     (z^^(a n + 2) ++ zP ++ z^^(b n - 1)))
    (z^^(2 * a n + 2) ++ zP ++ z^^(2^(S n)-1))
    (M ++ X^^(x n))
    (X^^(2^(S n))).
Proof.
  unfold P2.
  intro HP2.
  rewrite P3_suffix_in, P3_suffix_out.
  eapply segRLs_trans.
  - apply Z_MXs.
  - eapply segRLs_trans.
    + apply HP2.
    + applys_eq (PS_to_X (b n - 1) (x n)).
      * pose proof (b_pos n). flia.
      * rewrite xS. reflexivity.
Qed.

Lemma P1_twice n:
  P1 n ->
  segRLs tm (z^^(2 * g n))
    ((z^^(a n + 2) ++ zP ++ z^^(b n - 1)) ++
     (z^^(a n + 2) ++ zP ++ z^^(b n - 1)))
    (Sx ++ X^^(x n))
    (Sx ++ X^^(x n)).
Proof.
  unfold P1.
  intro HP1.
  replace (2 * g n) with (g n + g n) by lia.
  rewrite lpow_add.
  eapply segRLs_trans; apply HP1.
Qed.

Lemma P3_of_P1_P2 n:
  P1 n -> P2 n -> P3 n.
Proof.
  unfold P3.
  intros HP1 HP2.
  rewrite x_step.
  rewrite (@lpow_add Sym (x n) (2^(S n)) X).
  rewrite (app_assoc Sx (X^^(x n)) (M ++ X^^(x n))).
  rewrite (app_assoc Sx (X^^(x n)) (X^^(2^(S n)))).
  eapply segRLs_concat.
  - apply P1_twice, HP1.
  - apply P3_suffix, HP2.
Qed.

Lemma P1_S n:
  P1 n -> P2 n -> P1 (S n).
Proof.
  intros HP1 HP2.
  unfold P1.
  rewrite z_g_step, z_a_tail_step.
  eapply segRLs_trans.
  - applys_eq (Pre_P1 n HP1); try reflexivity.
    rewrite x_step.
    rewrite (@lpow_add Sym (x n) (2^(S n)) X).
    reflexivity.
  - applys_eq (P3_of_P1_P2 n HP1 HP2); try reflexivity.
Qed.

Lemma P2_prefix n:
  P2 n ->
  segRLs tm (zP ++ z^^(g n)) (z^^(a n + b n))
    (M ++ X^^(x (S n)))
    (Sx ++ X^^(x n) ++ M ++ X^^(x n)).
Proof.
  unfold P2.
  intro HP2.
  rewrite x_step.
  rewrite (@lpow_add Sym (x n) (2^(S n)) X).
  rewrite (app_assoc M (X^^(x n)) (X^^(2^(S n)))).
  rewrite (app_assoc Sx (X^^(x n)) (M ++ X^^(x n))).
  applys_eq (segRLs_concat HP2 (PX_to_M (a n) (b n - 1) (x n))).
  - pose proof (b_pos n). flia.
  - rewrite xS. reflexivity.
Qed.

Lemma P2_S n:
  P1 n -> P2 n -> P2 (S n).
Proof.
  intros HP1 HP2.
  unfold P2.
  rewrite z_g_step, app_assoc.
  replace (z^^(a (S n)) ++ zP ++ z^^(b (S n) - 1)) with
    (z^^(a (S n) + 0) ++ zP ++ z^^(b (S n) - 1)) by flia.
  rewrite z_a_tail_step.
  replace (z^^(a n + b n + 0)) with (z^^(a n + b n)) by flia.
  eapply segRLs_trans.
  - apply P2_prefix.
    apply HP2.
  - applys_eq (P3_of_P1_P2 n HP1 HP2); try reflexivity.
Qed.

Lemma P12 n: P1 n /\ P2 n.
Proof.
  induction n.
  - split; [apply P1_0|apply P2_0].
  - destruct IHn as [HP1 HP2].
    split.
    + apply P1_S; assumption.
    + apply P2_S; assumption.
Qed.

Theorem P1_all n: P1 n.
Proof. apply P12. Qed.

Theorem P2_all n: P2 n.
Proof. apply P12. Qed.

Theorem P3_all n: P3 n.
Proof.
  destruct (P12 n) as [HP1 HP2].
  apply P3_of_P1_P2; assumption.
Qed.

Definition step_m n m := m + 2 * (g n - 2^(S n)).

Definition Aconf n m :=
  (Sx ++ X^^(x n) ++ M ++ X^^(x n) ++ X^^m) *> 0inf.

Theorem BigStep_side n m:
  sideRLs tm (z^^(2 * g n)) (Aconf n m) (Aconf (S n) (step_m n m)).
Proof.
  unfold Aconf, step_m.
  applys_eq (segRLs_sideRLs_concat (P3_all n)
    (Z_suffix_side (2 * a n + 2) (2^(S n)-1) m ltac:(lia))).
  - repeat rewrite Str_app_assoc.
    reflexivity.
  - repeat rewrite Str_app_assoc.
    rewrite lpow_add'.
    replace (x (S n) + (m + 2 * (g n - 2 ^ S n)))
      with (2 ^ S n - 1 + (2 * a n + 2 + m)).
    + reflexivity.
    + rewrite x_b.
      rewrite <- a_g.
      pose proof (b_le_a1 n).
      unfold b in *.
      cbn [Nat.pow] in *.
      pose proof (Nat.pow_nonzero 2 n ltac:(lia)).
      pose proof (Nat.pow_nonzero 2 (S n) ltac:(lia)).
      lia.
Qed.

Definition S0 '(a,n,m) :=
  LC a {{{ (hR,R) }}} Aconf n m.

Lemma BigStep a n m:
  S0 (a,n,m) -[ tm ]->*
  S0 (2*g n+a,S n,step_m n m).
Proof.
  unfold S0.
  eapply sideRLs_concat_1.
  1: apply BigStep_side.
  apply LIncs.
Qed.

Lemma BigStep' n:
  exists a m,
  c0 -[ tm ]->* S0 (a,n,m).
Proof.
  induction n.
  - exists 3,1.
    esx.
  - destruct IHn as [a [m I1]].
    eexists _,_.
    follow I1.
    apply BigStep.
Qed.

Lemma pow2_gt n:
  n<2^n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros.
  epose proof (BigStep' n) as [a [m I1]].
  eexists _,_; split.
  1: apply I1.
  split.
  - unfold S0,LC,Aconf.
    repeat rewrite Str_app_assoc.
    solve_sigma_score.
  - unfold x; cbn[Nat.pow].
    pose proof (pow2_gt n).
    lia.
Qed.
