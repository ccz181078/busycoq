(** * Explicit lower bounds on the halting time and the number of ones
      of the BB(6) champion

  The BB(6) champion (found by mxdys, June 2025) is listed as
    1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE.
  [SOBCv5.TM63] proves that the machine
    1RB---_1LC0RF_1RE0LD_0LC1RB_1RA1RE_1RE0RD
  halts; it is the same transition table with the states renamed, started
  in the champion's state B, and the two runs merge after 15 and 9 steps
  ([Eqv_v2.TM872]).  [SOBCv5.TM62] is the same table started in the
  champion's state D.

  This file adds lower bounds on the number of steps and on the number of
  non-blank cells at the halt.  The halting proof in [SOBCv5] passes
  through a configuration whose right half holds [1 + b3] blocks [1 1 1],
  where [b3] is the nested tower defined below, and these blocks are still
  on the tape when the machine halts.  A machine started on the blank tape
  writes at most one non-blank cell per step
  ([sigma_score_bounded_fromc0]), so the halting time exceeds [3 * b3]
  too.  The rules, the tower function [t2] and the residue tactics are
  those of [SOBCv5]; nothing there is changed.

  Main statements, with [s] the number of non-blank cells of the halting
  configuration [c] and [n] the number of steps:
  - [TM63_bound.halting_config_score]:
      exists n c s, c0 -[ tm ]->> n / c /\ halted tm c /\
        sigma_score c s /\ s <= n /\ 3 * b3 < s
  - [TM63_bound.halting_config_score_tower]: the same with
      10^^(10^^(10^^8)) < s,  2^^(2^^(2^^10)) < s  and  2^^^5 < s
  - [TM63_bound.halts_with_bound], [TM63_bound.halts_with_tower_bound]:
      exists n, halts_in tm c0 n /\ n > 3 * b3, and the three towers
  - [Champion.halting_config_score], [Champion.halts_with_bound]: the
    same for the listed champion string.  Its halting time is exactly 6
    more than that of [TM63.tm], and its halting tape is the same.
  - [TM62_bound]: the same four statements for [SOBCv5.TM62].

  [halts_in] and [halted] do not perform the halting transition, so the
  usual step count is [n + 1]; the halting transition reads a 1, so it
  cannot lower the number of ones.

  AI assistance: this file was produced with the help of Claude (Anthropic).
*)

From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import BinaryCounter.
From BusyCoq Require Import BinaryCounter_v2.
From BusyCoq Require Import NatMod.
From BusyCoq Require Import SimplTape.
From BusyCoq Require Import SOBCv5.

Open Scope list.

(** ** Generic part: the halting time is at least the number of non-blank
    cells of any configuration on the run. *)

Lemma halting_time_ge_sigma_score tm c s n:
  c0 -[ tm ]->* c ->
  sigma_score c s ->
  halts_in tm c0 n ->
  s <= n.
Proof.
  intros He Hs Hn.
  destruct (evstep_multistep _ _ _ He) as [k Hk].
  pose proof (sigma_score_bounded_fromc0 _ _ _ _ Hk Hs) as H1.
  pose proof (within_halt _ _ _ _ _ Hn Hk) as H2.
  lia.
Qed.

Lemma halts_in_unique tm c n m:
  halts_in tm c n ->
  halts_in tm c m ->
  n = m.
Proof.
  intros Hn Hm.
  destruct (Nat.lt_trichotomy n m) as [H|[H|H]].
  2: exact H.
  - destruct Hm as [ch [Hrun _]].
    exfalso. eapply exceeds_halt; [apply Hn | | apply Hrun]. lia.
  - destruct Hn as [ch [Hrun _]].
    exfalso. eapply exceeds_halt; [apply Hm | | apply Hrun]. lia.
Qed.

Lemma multistep_halts_in tm c c' k m:
  c -[ tm ]->> k / c' ->
  halts_in tm c' m ->
  halts_in tm c (k + m).
Proof.
  intros Hk [ch [Hm Hh]].
  exists ch. split.
  2: exact Hh.
  eapply multistep_trans; eauto.
Qed.

Definition has_score (l : side) := exists s, sigma_score_side l s.

Lemma has_score_const0: has_score (const s0).
Proof.
  exists O. constructor.
Qed.

Lemma has_score_app xs l:
  has_score l -> has_score (xs *> l).
Proof.
  intros [s Hs].
  eexists.
  apply sigma_score_Str_app.
  - reflexivity.
  - exact Hs.
Qed.

Lemma has_score_BinaryCounter d0 d1 l p:
  has_score l -> has_score (BinaryCounter d0 d1 l p).
Proof.
  intros Hl.
  induction p; cbn [BinaryCounter].
  - apply has_score_app, IHp.
  - apply has_score_app, IHp.
  - exact Hl.
Qed.

Lemma has_score_BinDec d0 d1 len n l:
  has_score l -> has_score (BinDec d0 d1 len n l).
Proof.
  unfold BinDec.
  apply has_score_BinaryCounter.
Qed.

(** ** Power towers *)

(** [tet k] is 2^^k, a tower of [k] twos. *)
Fixpoint tet (k : nat) : nat :=
match k with
| O => 1
| S k0 => 2 ^ tet k0
end.

Lemma tet_S k: tet (S k) = 2 ^ tet k.
Proof. reflexivity. Qed.

Lemma tet_ge1 k: 1 <= tet k.
Proof.
  destruct k.
  - apply Nat.le_refl.
  - rewrite tet_S.
    pose proof (Nat.pow_nonzero 2 (tet k)).
    lia.
Qed.

Lemma tet_le_S k: tet k <= tet (S k).
Proof.
  induction k.
  - rewrite tet_S. pose proof (Nat.pow_nonzero 2 (tet 0)). change (tet 0) with 1%nat in *. lia.
  - rewrite (tet_S (S k)), (tet_S k).
    apply Nat.pow_le_mono_r.
    + lia.
    + exact IHk.
Qed.

Lemma tet_mono i j: i <= j -> tet i <= tet j.
Proof.
  intros H.
  induction H.
  - apply Nat.le_refl.
  - eapply Nat.le_trans.
    + exact IHle.
    + apply tet_le_S.
Qed.

(** [pent k] is 2^^^k. *)
Fixpoint pent (k : nat) : nat :=
match k with
| O => 1
| S k0 => tet (pent k0)
end.

Lemma pent_S k: pent (S k) = tet (pent k).
Proof. reflexivity. Qed.

Lemma pow2_tet x h:
  tet h <= x ->
  tet (S h) <= 2 ^ x.
Proof.
  intros H.
  rewrite tet_S.
  apply Nat.pow_le_mono_r.
  - lia.
  - exact H.
Qed.

Lemma mul_pow2_tet c x h:
  2 <= c ->
  tet h <= x ->
  tet (S h) <= c * 2 ^ x - 1.
Proof.
  intros Hc Hx.
  pose proof (pow2_tet x h Hx) as H.
  pose proof (tet_ge1 (S h)) as H1.
  generalize dependent (tet (S h)).
  generalize (2 ^ x).
  intros y t Ht Ht1.
  assert (2 * y <= c * y) by (apply Nat.mul_le_mono_r; exact Hc).
  lia.
Qed.

(** [tet10 k] is 10^^k, a tower of [k] tens. *)
Fixpoint tet10 (k : nat) : nat :=
match k with
| O => 1
| S k0 => 10 ^ tet10 k0
end.

Lemma tet10_S k: tet10 (S k) = 10 ^ tet10 k.
Proof. reflexivity. Qed.

Lemma tet10_ge1 k: 1 <= tet10 k.
Proof.
  destruct k.
  - apply Nat.le_refl.
  - rewrite tet10_S.
    pose proof (Nat.pow_nonzero 10 (tet10 k)).
    lia.
Qed.

Lemma tet10_le_S k: tet10 k <= tet10 (S k).
Proof.
  induction k.
  - rewrite tet10_S. pose proof (Nat.pow_nonzero 10 (tet10 0)). change (tet10 0) with 1%nat in *. lia.
  - rewrite (tet10_S (S k)), (tet10_S k).
    apply Nat.pow_le_mono_r.
    + lia.
    + exact IHk.
Qed.

Lemma tet10_mono i j: i <= j -> tet10 i <= tet10 j.
Proof.
  intros H.
  induction H.
  - apply Nat.le_refl.
  - eapply Nat.le_trans.
    + exact IHle.
    + apply tet10_le_S.
Qed.

(** Base 2 against base 10: [2 ^ (4 * T) = 16 ^ T >= 10 ^ T + 1]. *)
Lemma pow16_ge T: 1 <= T -> 10 ^ T + 1 <= 16 ^ T.
Proof.
  intros H.
  destruct T as [|T].
  1: lia.
  rewrite !Nat.pow_succ_r'.
  pose proof (Nat.pow_le_mono_l 10 16 T ltac:(lia)) as H1.
  pose proof (Nat.pow_nonzero 10 T ltac:(lia)) as H2.
  generalize dependent (16 ^ T).
  generalize dependent (10 ^ T).
  intros. lia.
Qed.

Lemma pow2_4mul T: 2 ^ (4 * T) = 16 ^ T.
Proof.
  rewrite Nat.pow_mul_r.
  reflexivity.
Qed.

Lemma pow2_step10 x T:
  1 <= T ->
  4 * T + 2 <= x ->
  4 * 10 ^ T + 2 <= 2 ^ x - 1.
Proof.
  intros HT Hx.
  pose proof (Nat.pow_le_mono_r 2 (4 * T + 2) x ltac:(lia) Hx) as H.
  rewrite Nat.pow_add_r, pow2_4mul in H.
  change (2 ^ 2)%nat with 4%nat in H.
  pose proof (pow16_ge T HT) as H1.
  generalize dependent (2 ^ x).
  generalize dependent (16 ^ T).
  generalize dependent (10 ^ T).
  intros. lia.
Qed.

Lemma mul_pow2_tet10 c x h:
  2 <= c ->
  4 * tet10 h <= x ->
  tet10 (S h) <= c * 2 ^ x - 1.
Proof.
  intros Hc Hx.
  rewrite tet10_S.
  pose proof (Nat.pow_le_mono_r 2 (4 * tet10 h) x ltac:(lia) Hx) as H.
  rewrite pow2_4mul in H.
  pose proof (Nat.pow_le_mono_l 10 16 (tet10 h) ltac:(lia)) as H1.
  pose proof (Nat.pow_nonzero 10 (tet10 h) ltac:(lia)) as H2.
  assert (Hm: 2 * 2 ^ x <= c * 2 ^ x) by (apply Nat.mul_le_mono_r; exact Hc).
  generalize dependent (2 ^ x).
  generalize dependent (16 ^ tet10 h).
  generalize dependent (10 ^ tet10 h).
  intros. lia.
Qed.

(** ** Counting non-blank cells *)

Lemma sigma_score_state q q' t s:
  sigma_score (q;; t) s ->
  sigma_score (q';; t) s.
Proof.
  intros H.
  inverts H.
  constructor; auto.
Qed.

Ltac score_side :=
  repeat match goal with
  | |- sigma_score_side (const _) _ => apply sigma_score_side_O
  | |- sigma_score_side (_ >> _) _ =>
    eapply sigma_score_side_S; [ reflexivity | ]
  | |- sigma_score_side ((_ ^^ _) *> _) _ =>
    eapply sigma_score_Str_app; [ apply sigma_score_lpow; reflexivity | ]
  | |- sigma_score_side (_ *> _) _ =>
    eapply sigma_score_Str_app; [ reflexivity | ]
  end.

Module TM63_bound.
Import TM63.

(** ** [t2] and [st2] against power towers *)

Lemma t2_tet a b k:
  tet k + 1 <= b ->
  tet (a + k) + 1 <= t2 a b.
Proof.
  intros Hb.
  induction a.
  - exact Hb.
  - rewrite t2_S.
    change (S a + k) with (S (a + k)).
    assert (H: 2 * tet (S (a + k)) <= 2 ^ t2 a b).
    { rewrite tet_S, <- Nat.pow_succ_r'.
      apply Nat.pow_le_mono_r.
      - lia.
      - lia. }
    pose proof (Nat.pow_le_mono_r 2 1 (tet (a + k)) ltac:(lia) (tet_ge1 (a + k))) as H2.
    change (2 ^ 1)%nat with 2%nat in H2.
    rewrite <- tet_S in H2.
    generalize dependent (tet (S (a + k))).
    generalize (2 ^ t2 a b).
    intros. lia.
Qed.

Lemma st2_ge_t2 a b:
  t2 a b <= st2 a b.
Proof.
  destruct a.
  - rewrite st2_O, t2_O. apply Nat.le_refl.
  - rewrite st2_S. apply Nat.le_add_l.
Qed.

(** ** The parameters of the run *)

Definition a1 := st2 7 6 + 12.
Definition n1 := 31 * 2 ^ a1 - 1.
Definition b1 := t2 8 6.
Definition len1 := 5 + a1.
Definition a2 := st2 n1 b1 + (n1 / 3 * 5 + 2).
Definition b2 := t2 (n1 + 1) b1.
Definition len2 := len1 + 1 + 1 + a2.
Definition n2 := (((2 ^ len1 - 1) * 2 + 1) * 2 + 1) * 2 ^ a2 - 1.
Definition a3 := st2 n2 b2 + (n2 / 3 * 5 + 4).
Definition b3 := t2 (n2 + 1) b2.

(** The last configuration of the run before the final (halting) rule:
    the right part of the tape holds [1 + b3] blocks [1 1 1]. *)
Definition last_config := S1 len2 0 m0 a3 0 b3.

Lemma Rsts2_v2 n len0 b:
  n<2^len0 ->
  n mod 3 = 2 ->
  S1 len0 n m2 b 0 (2^b-1) -->*
  S1 len0 0 m0 (st2 n b + (n/3*5+4)) 0 (t2 (n+1) b).
Proof.
  intros.
  epose proof (div_mod' n 3 2 H0) as Hn.
  rewrite Hn.
  follow Rsts2.
  1: lia.
  finish.
Qed.

(** The same numbers in a shorter form. *)
Lemma n1_eq: n1 = (2 ^ 5 - 1) * 2 ^ a1 - 1.
Proof. reflexivity. Qed.

Lemma n2_eq: n2 = (2 ^ (a1 + 7) - 1) * 2 ^ a2 - 1.
Proof.
  unfold n2, len1.
  replace (a1 + 7) with (2 + (5 + a1)) by lia.
  rewrite (Nat.pow_add_r 2 2 (5 + a1)).
  change (2 ^ 2)%nat with 4%nat.
  pose proof (Nat.pow_nonzero 2 (5 + a1)) as H.
  generalize dependent (2 ^ (5 + a1)).
  intros x Hx.
  replace (((x - 1) * 2 + 1) * 2 + 1) with (4 * x - 1) by lia.
  reflexivity.
Qed.

Lemma n1_lt: n1 < 2 ^ len1.
Proof.
  exact (Rst1'_WF 3 a1).
Qed.

Lemma n2_lt: n2 < 2 ^ len2.
Proof.
  exact (Rst1'_WF len1 a2).
Qed.

Lemma n1_mod3: n1 mod 3 = 1%nat.
Proof.
  unfold n1, a1.
  rw_mod; reflexivity.
  Unshelve.
  all: solve_ge.
Qed.

Lemma n2_mod3: n2 mod 3 = 2%nat.
Proof.
  unfold n2, a2, len1, b1, n1, a1.
  rw_mod; reflexivity.
  Unshelve.
  all: solve_ge.
  all: repeat
       match goal with
       | |- t2 _ _ >= _ => apply t2_ge1; solve_ge
       end.
Qed.

Lemma reach_last_config: c0 -->* last_config.
Proof.
  follow init.
  mid (S1 3 0 m1 a1 0 b1).
  1: exact (Rsts1 2 3 6 ltac:(cbn; lia)).
  mid (S1 len1 n1 m2 b1 0 (2 ^ b1 - 1)).
  1: exact (Rst1' 3 a1 b1).
  mid (S1 len1 0 m1 a2 0 b2).
  1: exact (Rsts1_v2 n1 len1 b1 n1_lt n1_mod3).
  mid (S1 len2 n2 m2 b2 0 (2 ^ b2 - 1)).
  1: exact (Rst1' len1 a2 b2).
  exact (Rsts2_v2 n2 len2 b2 n2_lt n2_mod3).
Qed.

Lemma last_config_halts: halts tm last_config.
Proof.
  apply Rst0'.
Qed.

Lemma S1_m0_score len0 a b:
  exists s, sigma_score (S1 len0 0 m0 a 0 b) s /\ 3 * b < s.
Proof.
  assert (Hl: has_score (LC (LC lh len0 0 <* d0 <* m0) a 0)).
  { unfold LC.
    apply has_score_BinDec.
    do 2 apply has_score_app.
    apply has_score_BinDec.
    apply has_score_app.
    apply has_score_const0. }
  destruct Hl as [sl Hl].
  exists (sl + (0 + (3 + (3 * (1 + b) + 0)))).
  split.
  2: lia.
  unfold S1, S0, RC.
  apply sigma_score_headL.
  1: exact Hl.
  apply sigma_score_Str_app.
  1: reflexivity.
  apply sigma_score_Str_app.
  1: reflexivity.
  apply sigma_score_Str_app.
  2: constructor.
  apply sigma_score_lpow.
  reflexivity.
Qed.

(** The last rule, [Rst0'], as a run to an explicit halting configuration.
    The blocks [1 1 1] on the right are still there at the halt. *)
Lemma Rst0'_run a0 a b:
  exists c s,
  S1 a0 0 m0 a 0 b -->* c /\
  halted tm c /\
  sigma_score c s /\
  3 * b < s.
Proof.
  do 2 eexists.
  split.
  { unfold S1,S0,LC,RC.
    rw_Bin.
    all: try solve_pow2_lt.
    repeat (rewrite lpow_add || rewrite lpow_mul || simpl_tape || simpl_rotate).
    repeat (step1 || sr || simpl_rotate).
    finish. }
  split.
  { constructor. }
  split.
  { apply sigma_score_intro.
    - score_side.
    - reflexivity.
    - score_side. }
  cbn. lia.
Qed.

Lemma halting_config:
  exists c s,
  c0 -->* c /\ halted tm c /\ sigma_score c s /\ 3 * b3 < s.
Proof.
  destruct (Rst0'_run len2 a3 b3) as [c [s [H1 [H2 [H3 H4]]]]].
  exists c, s.
  refine (conj _ (conj H2 (conj H3 H4))).
  eapply evstep_trans.
  - exact reach_last_config.
  - exact H1.
Qed.

(** ** The bound *)

(** The machine halts after [n] steps in a configuration [c] with [s]
    non-blank cells, and [3 * b3 < s <= n]. *)
Theorem halting_config_score:
  exists n c s,
  c0 -[ tm ]->> n / c /\ halted tm c /\ sigma_score c s /\
  s <= n /\ 3 * b3 < s.
Proof.
  destruct halting_config as [c [s [H1 [H2 [H3 H4]]]]].
  destruct (evstep_multistep _ _ _ H1) as [n Hn].
  exists n, c, s.
  pose proof (sigma_score_bounded_fromc0 _ _ _ _ Hn H3) as H5.
  exact (conj Hn (conj H2 (conj H3 (conj H5 H4)))).
Qed.

Theorem halting_time_gt n:
  halts_in tm c0 n ->
  3 * b3 < n.
Proof.
  intros Hn.
  destruct (S1_m0_score len2 a3 b3) as [s [Hs Hlt]].
  pose proof (halting_time_ge_sigma_score _ _ _ _ reach_last_config Hs Hn).
  lia.
Qed.

Theorem halts_with_bound:
  exists n, halts_in tm c0 n /\ n > 3 * b3.
Proof.
  destruct halt as [n Hn].
  exists n. split.
  - exact Hn.
  - apply halting_time_gt, Hn.
Qed.

(** ** The bound as a power tower *)

Lemma b1_ge: tet (8 + 2) + 1 <= b1.
Proof.
  apply t2_tet. cbn. lia.
Qed.

Lemma a1_ge: tet (7 + 2) <= a1.
Proof.
  unfold a1.
  pose proof (t2_tet 7 6 2 ltac:(cbn; lia)) as H.
  pose proof (st2_ge_t2 7 6) as H1.
  generalize dependent (tet (7 + 2)).
  generalize dependent (t2 7 6).
  generalize (st2 7 6).
  intros. lia.
Qed.

Lemma n1_ge: tet 10 <= n1.
Proof.
  unfold n1.
  apply (mul_pow2_tet 31 a1 (7 + 2)).
  - lia.
  - exact a1_ge.
Qed.

Lemma b2_ge: tet (n1 + 1 + (8 + 2)) + 1 <= b2.
Proof.
  apply t2_tet, b1_ge.
Qed.

Lemma a2_ge: tet (n1 + (8 + 2)) <= a2.
Proof.
  unfold a2.
  pose proof (t2_tet n1 b1 (8 + 2) b1_ge) as H.
  pose proof (st2_ge_t2 n1 b1) as H1.
  generalize dependent (tet (n1 + (8 + 2))).
  generalize dependent (t2 n1 b1).
  generalize (st2 n1 b1) (n1 / 3 * 5 + 2).
  intros. lia.
Qed.

Lemma n2_ge: tet (S (n1 + (8 + 2))) <= n2.
Proof.
  unfold n2.
  apply mul_pow2_tet.
  - generalize (2 ^ len1). intros. lia.
  - exact a2_ge.
Qed.

Lemma b3_ge: tet (n2 + 1 + (n1 + 1 + (8 + 2))) + 1 <= b3.
Proof.
  apply t2_tet, b2_ge.
Qed.

Lemma b3_ge_tower: tet (tet (tet 10)) < b3.
Proof.
  pose proof b3_ge as H3.
  pose proof n2_ge as H2.
  pose proof n1_ge as H1.
  assert (Ha: tet (tet 10) <= n2).
  { eapply Nat.le_trans.
    2: exact H2.
    apply tet_mono.
    eapply Nat.le_trans.
    1: exact H1.
    apply Nat.le_trans with (m := n1 + (8 + 2)).
    - apply Nat.le_add_r.
    - apply Nat.le_succ_diag_r. }
  assert (Hb: tet (tet (tet 10)) <= tet (n2 + 1 + (n1 + 1 + (8 + 2)))).
  { apply tet_mono.
    eapply Nat.le_trans.
    1: exact Ha.
    rewrite <- Nat.add_assoc.
    apply Nat.le_add_r. }
  eapply Nat.le_lt_trans.
  1: exact Hb.
  unfold lt.
  rewrite <- Nat.add_1_r.
  exact H3.
Qed.

Lemma pent5_le: pent 5 <= tet (tet (tet 10)).
Proof.
  rewrite (pent_S 4), (pent_S 3), (pent_S 2).
  change (pent 2) with 4%nat.
  do 3 apply tet_mono.
  repeat constructor.
Qed.

(** The same in base 10. *)

Lemma t2_tet10 a b k:
  4 * tet10 k + 2 <= b ->
  4 * tet10 (a + k) + 2 <= t2 a b.
Proof.
  intros Hb.
  induction a.
  - exact Hb.
  - rewrite t2_S.
    change (S a + k) with (S (a + k)).
    rewrite tet10_S.
    apply pow2_step10.
    + apply tet10_ge1.
    + exact IHa.
Qed.

Lemma t2_6_tet10 a: 4 * tet10 a + 2 <= t2 a 6.
Proof.
  pose proof (t2_tet10 a 6 0 ltac:(cbn; lia)) as H.
  rewrite Nat.add_0_r in H.
  exact H.
Qed.

Lemma a1_ge10: 4 * tet10 7 <= a1.
Proof.
  unfold a1.
  pose proof (t2_6_tet10 7) as H.
  pose proof (st2_ge_t2 7 6) as H1.
  generalize dependent (tet10 7).
  generalize dependent (t2 7 6).
  generalize (st2 7 6).
  intros. lia.
Qed.

Lemma n1_ge10: tet10 8 <= n1.
Proof.
  unfold n1.
  apply (mul_pow2_tet10 31 a1 7).
  - lia.
  - exact a1_ge10.
Qed.

Lemma b1_ge10: 4 * tet10 8 + 2 <= b1.
Proof.
  exact (t2_6_tet10 8).
Qed.

Lemma b2_ge10: 4 * tet10 (n1 + 1 + 8) + 2 <= b2.
Proof.
  apply t2_tet10, b1_ge10.
Qed.

Lemma a2_ge10: 4 * tet10 (n1 + 8) <= a2.
Proof.
  unfold a2.
  pose proof (t2_tet10 n1 b1 8 b1_ge10) as H.
  pose proof (st2_ge_t2 n1 b1) as H1.
  generalize dependent (tet10 (n1 + 8)).
  generalize dependent (t2 n1 b1).
  generalize (st2 n1 b1) (n1 / 3 * 5 + 2).
  intros. lia.
Qed.

Lemma n2_ge10: tet10 (S (n1 + 8)) <= n2.
Proof.
  unfold n2.
  apply mul_pow2_tet10.
  - generalize (2 ^ len1). intros. lia.
  - exact a2_ge10.
Qed.

Lemma b3_ge10: 4 * tet10 (n2 + 1 + (n1 + 1 + 8)) + 2 <= b3.
Proof.
  apply t2_tet10, b2_ge10.
Qed.

Lemma b3_ge_tower10: tet10 (tet10 (tet10 8)) < b3.
Proof.
  pose proof b3_ge10 as H3.
  assert (Ha: tet10 (tet10 8) <= n2).
  { eapply Nat.le_trans.
    2: exact n2_ge10.
    apply tet10_mono.
    eapply Nat.le_trans.
    1: exact n1_ge10.
    apply Nat.le_trans with (m := n1 + 8).
    - apply Nat.le_add_r.
    - apply Nat.le_succ_diag_r. }
  assert (Hb: tet10 (tet10 (tet10 8)) <= tet10 (n2 + 1 + (n1 + 1 + 8))).
  { apply tet10_mono.
    eapply Nat.le_trans.
    1: exact Ha.
    rewrite <- Nat.add_assoc.
    apply Nat.le_add_r. }
  generalize dependent (tet10 (n2 + 1 + (n1 + 1 + 8))).
  generalize (tet10 (tet10 (tet10 8))).
  generalize b3.
  intros. lia.
Qed.

(** [b3] exceeds 10^^(10^^(10^^8)), 2^^(2^^(2^^10)) and 2^^^5. *)
Lemma b3_towers:
  tet10 (tet10 (tet10 8)) < b3 /\
  tet (tet (tet 10)) < b3 /\
  pent 5 < b3.
Proof.
  exact (conj b3_ge_tower10
           (conj b3_ge_tower (Nat.le_lt_trans _ _ _ pent5_le b3_ge_tower))).
Qed.

Theorem halting_time_gt_tower n:
  halts_in tm c0 n ->
  tet10 (tet10 (tet10 8)) < n /\
  tet (tet (tet 10)) < n /\
  pent 5 < n.
Proof.
  intros Hn.
  pose proof (halting_time_gt n Hn) as H.
  assert (Hb: b3 < n).
  { generalize dependent b3. intros. lia. }
  destruct b3_towers as [T1 [T2 T3]].
  exact (conj (Nat.lt_trans _ _ _ T1 Hb)
           (conj (Nat.lt_trans _ _ _ T2 Hb) (Nat.lt_trans _ _ _ T3 Hb))).
Qed.

Theorem halts_with_tower_bound:
  exists n,
  halts_in tm c0 n /\
  n > tet10 (tet10 (tet10 8)) /\
  n > tet (tet (tet 10)) /\
  n > pent 5.
Proof.
  destruct halt as [n Hn].
  exists n.
  split.
  1: exact Hn.
  exact (halting_time_gt_tower n Hn).
Qed.

(** The number of non-blank cells at the halt satisfies the same bounds. *)
Theorem halting_config_score_tower:
  exists n c s,
  c0 -[ tm ]->> n / c /\ halted tm c /\ sigma_score c s /\
  s <= n /\
  tet10 (tet10 (tet10 8)) < s /\
  tet (tet (tet 10)) < s /\
  pent 5 < s.
Proof.
  destruct halting_config_score as [n [c [s [H1 [H2 [H3 [H4 H5]]]]]]].
  exists n, c, s.
  assert (Hb: b3 < s).
  { generalize dependent b3. intros. lia. }
  destruct b3_towers as [T1 [T2 T3]].
  exact (conj H1 (conj H2 (conj H3 (conj H4
           (conj (Nat.lt_trans _ _ _ T1 Hb)
              (conj (Nat.lt_trans _ _ _ T2 Hb) (Nat.lt_trans _ _ _ T3 Hb))))))).
Qed.

End TM63_bound.

(** ** The same bound for the champion in the form listed on the wiki *)

Module Champion.

Definition tm := Eval compute in (TM_from_str "1RB1RA_1RC---_1LD0RF_1RA0LE_0LD1RC_1RA0RE").

(** Renaming of the states that turns [tm] into [TM63.tm]. *)
Definition f (q : Q) : Q :=
match q with
| A => E
| B => A
| C => B
| D => C
| E => D
| F => F
end.

Lemma perm: Perm tm TM63.tm f.
Proof.
  split.
  - intros q s; destruct q,s; cbn; congruence.
  - intros q s s' d q'; destruct q,s; cbn; intros H; inverts H; reflexivity.
Qed.

(** After 15 steps of [tm] and 9 steps of [TM63.tm] the two runs are in the
    same configuration (up to the renaming [f], which sends [A] to [E]). *)
Lemma merge:
  exists t,
  c0 -[ tm ]->> 15 / (A;; t) /\
  c0 -[ TM63.tm ]->> 9 / (E;; t).
Proof.
  eexists.
  split.
  - apply multistep_c_spec. vm_compute. simpl_tape. reflexivity.
  - apply multistep_c_spec. vm_compute. simpl_tape. reflexivity.
Qed.

Lemma halts_in_from_TM63 m:
  halts_in TM63.tm c0 m ->
  halts_in tm c0 (m + 6).
Proof.
  intros Hm.
  destruct merge as [t [H1 H2]].
  pose proof (within_halt _ _ _ _ _ Hm H2) as Hle.
  pose proof (preceeds_halt _ _ _ _ _ Hm H2 Hle) as H3.
  change (E;; t) with (f A;; t) in H3.
  apply (perm_halts_in' _ _ _ _ _ _ perm) in H3.
  pose proof (multistep_halts_in _ _ _ _ _ H1 H3) as H4.
  replace (m + 6) with (15 + (m - 9)) by lia.
  exact H4.
Qed.

Lemma halts_in_to_TM63 n:
  halts_in tm c0 n ->
  6 <= n /\ halts_in TM63.tm c0 (n - 6).
Proof.
  intros Hn.
  destruct TM63.halt as [m Hm].
  pose proof (halts_in_from_TM63 m Hm) as H.
  pose proof (halts_in_unique _ _ _ _ Hn H) as E.
  subst n.
  split.
  1: lia.
  replace (m + 6 - 6) with m by lia.
  exact Hm.
Qed.

(** The halting configurations have the same tape. *)
Lemma halting_config_from_TM63 n c:
  c0 -[ TM63.tm ]->> n / c ->
  halted TM63.tm c ->
  exists q, c0 -[ tm ]->> (n + 6) / (q;; snd c) /\ halted tm (q;; snd c).
Proof.
  intros Hn Hh.
  destruct merge as [t [H1 H2]].
  assert (Hin: halts_in TM63.tm c0 n) by (exists c; split; assumption).
  pose proof (within_halt _ _ _ _ _ Hin H2) as Hle.
  destruct (rewind_split' 9 (n - 9) _ _ _ _ Hn ltac:(lia)) as [c1 [Ha Hb]].
  pose proof (multistep_deterministic _ _ _ _ _ Ha H2) as Hc1.
  subst c1.
  destruct c as [q' t'].
  change (E;; t) with (f A;; t) in Hb.
  destruct (perm_multistep' _ _ _ perm _ _ _ _ _ Hb) as [q [Hq Hfq]].
  exists q.
  cbn [snd].
  split.
  - replace (n + 6) with (15 + (n - 9)) by lia.
    eapply multistep_trans; eassumption.
  - apply (perm_halted' _ _ _ _ _ perm).
    rewrite Hfq. exact Hh.
Qed.

Import TM63_bound.

Theorem halting_time_gt n:
  halts_in tm c0 n ->
  3 * b3 + 6 < n /\
  tet10 (tet10 (tet10 8)) < n /\
  tet (tet (tet 10)) < n /\
  pent 5 < n.
Proof.
  intros Hn.
  destruct (halts_in_to_TM63 n Hn) as [Hle H].
  pose proof (TM63_bound.halting_time_gt _ H) as H1.
  assert (H2: 3 * b3 + 6 < n /\ b3 < n).
  { generalize dependent b3. intros. lia. }
  destruct H2 as [H2 Hb].
  destruct b3_towers as [T1 [T2 T3]].
  exact (conj H2
           (conj (Nat.lt_trans _ _ _ T1 Hb)
              (conj (Nat.lt_trans _ _ _ T2 Hb) (Nat.lt_trans _ _ _ T3 Hb)))).
Qed.

Theorem halts_with_bound:
  exists n,
  halts_in tm c0 n /\
  n > 3 * b3 + 6 /\
  n > tet10 (tet10 (tet10 8)) /\
  n > tet (tet (tet 10)) /\
  n > pent 5.
Proof.
  destruct TM63.halt as [m Hm].
  exists (m + 6).
  pose proof (halts_in_from_TM63 m Hm) as H.
  split.
  1: exact H.
  exact (halting_time_gt _ H).
Qed.

(** The champion halts after [n] steps in a configuration [c] with [s]
    non-blank cells, where [s <= n] and [s] satisfies the same bounds. *)
Theorem halting_config_score:
  exists n c s,
  c0 -[ tm ]->> n / c /\ halted tm c /\ sigma_score c s /\
  s <= n /\
  3 * b3 < s /\
  tet10 (tet10 (tet10 8)) < s /\
  tet (tet (tet 10)) < s /\
  pent 5 < s.
Proof.
  destruct TM63_bound.halting_config_score as [n [c [s [H1 [H2 [H3 [H4 H5]]]]]]].
  destruct (halting_config_from_TM63 n c H1 H2) as [q [Hq Hh]].
  destruct c as [q' t'].
  cbn [snd] in *.
  pose proof (sigma_score_state q' q t' s H3) as H3'.
  assert (Hle: s <= n + 6) by lia.
  assert (Hb: b3 < s).
  { generalize dependent b3. intros. lia. }
  destruct b3_towers as [T1 [T2 T3]].
  exists (n + 6), (q;; t'), s.
  exact (conj Hq (conj Hh (conj H3' (conj Hle (conj H5
           (conj (Nat.lt_trans _ _ _ T1 Hb)
              (conj (Nat.lt_trans _ _ _ T2 Hb) (Nat.lt_trans _ _ _ T3 Hb)))))))).
Qed.

End Champion.

(** ** The same bounds for [SOBCv5.TM62] *)

Module TM62_bound.
Import TM62.

(** ** [t2] and [st2] against power towers *)

Lemma t2_tet a b k:
  tet k + 1 <= b ->
  tet (a + k) + 1 <= t2 a b.
Proof.
  intros Hb.
  induction a.
  - exact Hb.
  - rewrite t2_S.
    change (S a + k) with (S (a + k)).
    assert (H: 2 * tet (S (a + k)) <= 2 ^ t2 a b).
    { rewrite tet_S, <- Nat.pow_succ_r'.
      apply Nat.pow_le_mono_r.
      - lia.
      - lia. }
    pose proof (Nat.pow_le_mono_r 2 1 (tet (a + k)) ltac:(lia) (tet_ge1 (a + k))) as H2.
    change (2 ^ 1)%nat with 2%nat in H2.
    rewrite <- tet_S in H2.
    generalize dependent (tet (S (a + k))).
    generalize (2 ^ t2 a b).
    intros. lia.
Qed.

Lemma st2_ge_t2 a b:
  t2 a b <= st2 a b.
Proof.
  destruct a.
  - rewrite st2_O, t2_O. apply Nat.le_refl.
  - rewrite st2_S. apply Nat.le_add_l.
Qed.

(** ** The parameters of the run *)

Definition a1 := st2 7 6 + 12.
Definition n1 := 31 * 2 ^ a1 - 1.
Definition b1 := t2 8 6.
Definition len1 := 5 + a1.
Definition a2 := st2 n1 b1 + (n1 / 3 * 5 + 2).
Definition b2 := t2 (n1 + 1) b1.
Definition len2 := len1 + 1 + 1 + a2.
Definition n2 := (((2 ^ len1 - 1) * 2 + 1) * 2 + 1) * 2 ^ a2 - 1.
Definition a3 := st2 n2 b2 + (n2 / 3 * 5 + 4).
Definition b3 := t2 (n2 + 1) b2.

(** The last configuration of the run before the final (halting) rule:
    the right part of the tape holds [1 + b3] blocks [1 1 1]. *)
Definition last_config := S1 len2 0 m0 a3 0 b3.

Lemma Rsts2_v2 n len0 b:
  n<2^len0 ->
  n mod 3 = 2 ->
  S1 len0 n m2 b 0 (2^b-1) -->*
  S1 len0 0 m0 (st2 n b + (n/3*5+4)) 0 (t2 (n+1) b).
Proof.
  intros.
  epose proof (div_mod' n 3 2 H0) as Hn.
  rewrite Hn.
  follow Rsts2.
  1: lia.
  finish.
Qed.

(** The same numbers in a shorter form. *)
Lemma n1_eq: n1 = (2 ^ 5 - 1) * 2 ^ a1 - 1.
Proof. reflexivity. Qed.

Lemma n2_eq: n2 = (2 ^ (a1 + 7) - 1) * 2 ^ a2 - 1.
Proof.
  unfold n2, len1.
  replace (a1 + 7) with (2 + (5 + a1)) by lia.
  rewrite (Nat.pow_add_r 2 2 (5 + a1)).
  change (2 ^ 2)%nat with 4%nat.
  pose proof (Nat.pow_nonzero 2 (5 + a1)) as H.
  generalize dependent (2 ^ (5 + a1)).
  intros x Hx.
  replace (((x - 1) * 2 + 1) * 2 + 1) with (4 * x - 1) by lia.
  reflexivity.
Qed.

Lemma n1_lt: n1 < 2 ^ len1.
Proof.
  exact (Rst1'_WF 3 a1).
Qed.

Lemma n2_lt: n2 < 2 ^ len2.
Proof.
  exact (Rst1'_WF len1 a2).
Qed.

Lemma n1_mod3: n1 mod 3 = 1%nat.
Proof.
  unfold n1, a1.
  rw_mod; reflexivity.
  Unshelve.
  all: solve_ge.
Qed.

Lemma n2_mod3: n2 mod 3 = 2%nat.
Proof.
  unfold n2, a2, len1, b1, n1, a1.
  rw_mod; reflexivity.
  Unshelve.
  all: solve_ge.
  all: repeat
       match goal with
       | |- t2 _ _ >= _ => apply t2_ge1; solve_ge
       end.
Qed.

Lemma reach_last_config: c0 -->* last_config.
Proof.
  follow init.
  mid (S1 3 0 m1 a1 0 b1).
  1: exact (Rsts1 2 3 6 ltac:(cbn; lia)).
  mid (S1 len1 n1 m2 b1 0 (2 ^ b1 - 1)).
  1: exact (Rst1' 3 a1 b1).
  mid (S1 len1 0 m1 a2 0 b2).
  1: exact (Rsts1_v2 n1 len1 b1 n1_lt n1_mod3).
  mid (S1 len2 n2 m2 b2 0 (2 ^ b2 - 1)).
  1: exact (Rst1' len1 a2 b2).
  exact (Rsts2_v2 n2 len2 b2 n2_lt n2_mod3).
Qed.

Lemma last_config_halts: halts tm last_config.
Proof.
  apply Rst0'.
Qed.

Lemma S1_m0_score len0 a b:
  exists s, sigma_score (S1 len0 0 m0 a 0 b) s /\ 3 * b < s.
Proof.
  assert (Hl: has_score (LC (LC lh len0 0 <* d0 <* m0) a 0)).
  { unfold LC.
    apply has_score_BinDec.
    do 2 apply has_score_app.
    apply has_score_BinDec.
    apply has_score_app.
    apply has_score_const0. }
  destruct Hl as [sl Hl].
  exists (sl + (0 + (3 + (3 * (1 + b) + 0)))).
  split.
  2: lia.
  unfold S1, S0, RC.
  apply sigma_score_headL.
  1: exact Hl.
  apply sigma_score_Str_app.
  1: reflexivity.
  apply sigma_score_Str_app.
  1: reflexivity.
  apply sigma_score_Str_app.
  2: constructor.
  apply sigma_score_lpow.
  reflexivity.
Qed.

(** The last rule, [Rst0'], as a run to an explicit halting configuration.
    The blocks [1 1 1] on the right are still there at the halt. *)
Lemma Rst0'_run a0 a b:
  exists c s,
  S1 a0 0 m0 a 0 b -->* c /\
  halted tm c /\
  sigma_score c s /\
  3 * b < s.
Proof.
  do 2 eexists.
  split.
  { unfold S1,S0,LC,RC.
    rw_Bin.
    all: try solve_pow2_lt.
    repeat (rewrite lpow_add || rewrite lpow_mul || simpl_tape || simpl_rotate).
    repeat (step1 || sr || simpl_rotate).
    finish. }
  split.
  { constructor. }
  split.
  { apply sigma_score_intro.
    - score_side.
    - reflexivity.
    - score_side. }
  cbn. lia.
Qed.

Lemma halting_config:
  exists c s,
  c0 -->* c /\ halted tm c /\ sigma_score c s /\ 3 * b3 < s.
Proof.
  destruct (Rst0'_run len2 a3 b3) as [c [s [H1 [H2 [H3 H4]]]]].
  exists c, s.
  refine (conj _ (conj H2 (conj H3 H4))).
  eapply evstep_trans.
  - exact reach_last_config.
  - exact H1.
Qed.

(** ** The bound *)

(** The machine halts after [n] steps in a configuration [c] with [s]
    non-blank cells, and [3 * b3 < s <= n]. *)
Theorem halting_config_score:
  exists n c s,
  c0 -[ tm ]->> n / c /\ halted tm c /\ sigma_score c s /\
  s <= n /\ 3 * b3 < s.
Proof.
  destruct halting_config as [c [s [H1 [H2 [H3 H4]]]]].
  destruct (evstep_multistep _ _ _ H1) as [n Hn].
  exists n, c, s.
  pose proof (sigma_score_bounded_fromc0 _ _ _ _ Hn H3) as H5.
  exact (conj Hn (conj H2 (conj H3 (conj H5 H4)))).
Qed.

Theorem halting_time_gt n:
  halts_in tm c0 n ->
  3 * b3 < n.
Proof.
  intros Hn.
  destruct (S1_m0_score len2 a3 b3) as [s [Hs Hlt]].
  pose proof (halting_time_ge_sigma_score _ _ _ _ reach_last_config Hs Hn).
  lia.
Qed.

Theorem halts_with_bound:
  exists n, halts_in tm c0 n /\ n > 3 * b3.
Proof.
  destruct halt as [n Hn].
  exists n. split.
  - exact Hn.
  - apply halting_time_gt, Hn.
Qed.

(** ** The bound as a power tower *)

Lemma b1_ge: tet (8 + 2) + 1 <= b1.
Proof.
  apply t2_tet. cbn. lia.
Qed.

Lemma a1_ge: tet (7 + 2) <= a1.
Proof.
  unfold a1.
  pose proof (t2_tet 7 6 2 ltac:(cbn; lia)) as H.
  pose proof (st2_ge_t2 7 6) as H1.
  generalize dependent (tet (7 + 2)).
  generalize dependent (t2 7 6).
  generalize (st2 7 6).
  intros. lia.
Qed.

Lemma n1_ge: tet 10 <= n1.
Proof.
  unfold n1.
  apply (mul_pow2_tet 31 a1 (7 + 2)).
  - lia.
  - exact a1_ge.
Qed.

Lemma b2_ge: tet (n1 + 1 + (8 + 2)) + 1 <= b2.
Proof.
  apply t2_tet, b1_ge.
Qed.

Lemma a2_ge: tet (n1 + (8 + 2)) <= a2.
Proof.
  unfold a2.
  pose proof (t2_tet n1 b1 (8 + 2) b1_ge) as H.
  pose proof (st2_ge_t2 n1 b1) as H1.
  generalize dependent (tet (n1 + (8 + 2))).
  generalize dependent (t2 n1 b1).
  generalize (st2 n1 b1) (n1 / 3 * 5 + 2).
  intros. lia.
Qed.

Lemma n2_ge: tet (S (n1 + (8 + 2))) <= n2.
Proof.
  unfold n2.
  apply mul_pow2_tet.
  - generalize (2 ^ len1). intros. lia.
  - exact a2_ge.
Qed.

Lemma b3_ge: tet (n2 + 1 + (n1 + 1 + (8 + 2))) + 1 <= b3.
Proof.
  apply t2_tet, b2_ge.
Qed.

Lemma b3_ge_tower: tet (tet (tet 10)) < b3.
Proof.
  pose proof b3_ge as H3.
  pose proof n2_ge as H2.
  pose proof n1_ge as H1.
  assert (Ha: tet (tet 10) <= n2).
  { eapply Nat.le_trans.
    2: exact H2.
    apply tet_mono.
    eapply Nat.le_trans.
    1: exact H1.
    apply Nat.le_trans with (m := n1 + (8 + 2)).
    - apply Nat.le_add_r.
    - apply Nat.le_succ_diag_r. }
  assert (Hb: tet (tet (tet 10)) <= tet (n2 + 1 + (n1 + 1 + (8 + 2)))).
  { apply tet_mono.
    eapply Nat.le_trans.
    1: exact Ha.
    rewrite <- Nat.add_assoc.
    apply Nat.le_add_r. }
  eapply Nat.le_lt_trans.
  1: exact Hb.
  unfold lt.
  rewrite <- Nat.add_1_r.
  exact H3.
Qed.

Lemma pent5_le: pent 5 <= tet (tet (tet 10)).
Proof.
  rewrite (pent_S 4), (pent_S 3), (pent_S 2).
  change (pent 2) with 4%nat.
  do 3 apply tet_mono.
  repeat constructor.
Qed.

(** The same in base 10. *)

Lemma t2_tet10 a b k:
  4 * tet10 k + 2 <= b ->
  4 * tet10 (a + k) + 2 <= t2 a b.
Proof.
  intros Hb.
  induction a.
  - exact Hb.
  - rewrite t2_S.
    change (S a + k) with (S (a + k)).
    rewrite tet10_S.
    apply pow2_step10.
    + apply tet10_ge1.
    + exact IHa.
Qed.

Lemma t2_6_tet10 a: 4 * tet10 a + 2 <= t2 a 6.
Proof.
  pose proof (t2_tet10 a 6 0 ltac:(cbn; lia)) as H.
  rewrite Nat.add_0_r in H.
  exact H.
Qed.

Lemma a1_ge10: 4 * tet10 7 <= a1.
Proof.
  unfold a1.
  pose proof (t2_6_tet10 7) as H.
  pose proof (st2_ge_t2 7 6) as H1.
  generalize dependent (tet10 7).
  generalize dependent (t2 7 6).
  generalize (st2 7 6).
  intros. lia.
Qed.

Lemma n1_ge10: tet10 8 <= n1.
Proof.
  unfold n1.
  apply (mul_pow2_tet10 31 a1 7).
  - lia.
  - exact a1_ge10.
Qed.

Lemma b1_ge10: 4 * tet10 8 + 2 <= b1.
Proof.
  exact (t2_6_tet10 8).
Qed.

Lemma b2_ge10: 4 * tet10 (n1 + 1 + 8) + 2 <= b2.
Proof.
  apply t2_tet10, b1_ge10.
Qed.

Lemma a2_ge10: 4 * tet10 (n1 + 8) <= a2.
Proof.
  unfold a2.
  pose proof (t2_tet10 n1 b1 8 b1_ge10) as H.
  pose proof (st2_ge_t2 n1 b1) as H1.
  generalize dependent (tet10 (n1 + 8)).
  generalize dependent (t2 n1 b1).
  generalize (st2 n1 b1) (n1 / 3 * 5 + 2).
  intros. lia.
Qed.

Lemma n2_ge10: tet10 (S (n1 + 8)) <= n2.
Proof.
  unfold n2.
  apply mul_pow2_tet10.
  - generalize (2 ^ len1). intros. lia.
  - exact a2_ge10.
Qed.

Lemma b3_ge10: 4 * tet10 (n2 + 1 + (n1 + 1 + 8)) + 2 <= b3.
Proof.
  apply t2_tet10, b2_ge10.
Qed.

Lemma b3_ge_tower10: tet10 (tet10 (tet10 8)) < b3.
Proof.
  pose proof b3_ge10 as H3.
  assert (Ha: tet10 (tet10 8) <= n2).
  { eapply Nat.le_trans.
    2: exact n2_ge10.
    apply tet10_mono.
    eapply Nat.le_trans.
    1: exact n1_ge10.
    apply Nat.le_trans with (m := n1 + 8).
    - apply Nat.le_add_r.
    - apply Nat.le_succ_diag_r. }
  assert (Hb: tet10 (tet10 (tet10 8)) <= tet10 (n2 + 1 + (n1 + 1 + 8))).
  { apply tet10_mono.
    eapply Nat.le_trans.
    1: exact Ha.
    rewrite <- Nat.add_assoc.
    apply Nat.le_add_r. }
  generalize dependent (tet10 (n2 + 1 + (n1 + 1 + 8))).
  generalize (tet10 (tet10 (tet10 8))).
  generalize b3.
  intros. lia.
Qed.

(** [b3] exceeds 10^^(10^^(10^^8)), 2^^(2^^(2^^10)) and 2^^^5. *)
Lemma b3_towers:
  tet10 (tet10 (tet10 8)) < b3 /\
  tet (tet (tet 10)) < b3 /\
  pent 5 < b3.
Proof.
  exact (conj b3_ge_tower10
           (conj b3_ge_tower (Nat.le_lt_trans _ _ _ pent5_le b3_ge_tower))).
Qed.

Theorem halting_time_gt_tower n:
  halts_in tm c0 n ->
  tet10 (tet10 (tet10 8)) < n /\
  tet (tet (tet 10)) < n /\
  pent 5 < n.
Proof.
  intros Hn.
  pose proof (halting_time_gt n Hn) as H.
  assert (Hb: b3 < n).
  { generalize dependent b3. intros. lia. }
  destruct b3_towers as [T1 [T2 T3]].
  exact (conj (Nat.lt_trans _ _ _ T1 Hb)
           (conj (Nat.lt_trans _ _ _ T2 Hb) (Nat.lt_trans _ _ _ T3 Hb))).
Qed.

Theorem halts_with_tower_bound:
  exists n,
  halts_in tm c0 n /\
  n > tet10 (tet10 (tet10 8)) /\
  n > tet (tet (tet 10)) /\
  n > pent 5.
Proof.
  destruct halt as [n Hn].
  exists n.
  split.
  1: exact Hn.
  exact (halting_time_gt_tower n Hn).
Qed.

(** The number of non-blank cells at the halt satisfies the same bounds. *)
Theorem halting_config_score_tower:
  exists n c s,
  c0 -[ tm ]->> n / c /\ halted tm c /\ sigma_score c s /\
  s <= n /\
  tet10 (tet10 (tet10 8)) < s /\
  tet (tet (tet 10)) < s /\
  pent 5 < s.
Proof.
  destruct halting_config_score as [n [c [s [H1 [H2 [H3 [H4 H5]]]]]]].
  exists n, c, s.
  assert (Hb: b3 < s).
  { generalize dependent b3. intros. lia. }
  destruct b3_towers as [T1 [T2 T3]].
  exact (conj H1 (conj H2 (conj H3 (conj H4
           (conj (Nat.lt_trans _ _ _ T1 Hb)
              (conj (Nat.lt_trans _ _ _ T2 Hb) (Nat.lt_trans _ _ _ T3 Hb))))))).
Qed.

End TM62_bound.

Print Assumptions TM63_bound.halts_with_bound.
Print Assumptions TM63_bound.halts_with_tower_bound.
Print Assumptions TM63_bound.halting_config_score.
Print Assumptions TM63_bound.halting_config_score_tower.
Print Assumptions Champion.halts_with_bound.
Print Assumptions Champion.halting_config_score.
Print Assumptions TM62_bound.halts_with_bound.
Print Assumptions TM62_bound.halts_with_tower_bound.
Print Assumptions TM62_bound.halting_config_score.
Print Assumptions TM62_bound.halting_config_score_tower.
