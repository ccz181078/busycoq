From BusyCoq Require Import Individual62.
From BusyCoq Require Import BinaryCounterFull.
From BusyCoq Require Import BinaryCounter.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.


Section SOCv1.

Hypothesis tm: TM.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Hypothesis QL QR:Q.
Hypothesis m0 m1:list Sym.
Hypothesis v0: nat.
Hypothesis ls0 ls1 ls2: list nat.
Hypothesis ls3 ls4 ls5: list nat.

Hypothesis k_init:positive.
Hypothesis n_init:N.

Notation "l <| r" :=
  (l <{{QL}} m0 *> r) (at level 30).

Notation "l |> r" :=
  (l <* m1 {{QR}}> r) (at level 30).

Definition d0 := [0;1].
Definition d1 := [1;1].
Definition d1' := [1;1].
Definition d1a := [1].

Hypothesis LInc:
  forall (l r:side) n,
    l <* d0 <* d1^^n <| r -->+
    l <* d1 <* d0^^n |> r.

Definition rd0 := [0;0;0;0].
Definition rd1 := [1;0;0;0].

Hypothesis RInc:
  forall (l r:side) n,
    l |> rd1^^n *> [0] *> r -->+
    l <| rd0^^n *> [1] *> r.

Definition r0 := [1].
Definition r1 := [1].

Lemma L_rotate:
  d1' = r0 ++ r1.
Proof.
  reflexivity.
Qed.

Lemma L_rotate':
  d1' = r1 ++ r0.
Proof.
  reflexivity.
Qed.

Definition to_Ldigit(n:nat):=
match n with
| O => d0
| _ => d1
end.

Hypothesis LOverflow_0:
  forall r n,
    const 0 <* d1a <* d1^^(n+1) <| rd0 *> r -->+
    const 0 <* d1a <* d0^^(n+1)|> rd1 *> [0] *> r.

Hypothesis LOverflow_1:
  forall r n,
    const 0 <* d1a <* d1^^(n+1) <| rd1 *> r -->+
    const 0 <* d1a <* d0^^(n+1) <* (to_Ldigit v0) |> [0;0;0] *> r.

Hypothesis Hls02:
  length ls0 + length ls2 = 2.
Hypothesis Hls1:
  length ls1 = 2.
Hypothesis Hls35:
  length ls3 + length ls5 = 1%nat.
Hypothesis Hls4:
  length ls4 = 2.

Hypothesis ROverflow_1001:
  forall l r n,
    l |> rd1^^n *> [1;0;0;1] *> r -->+
    l <* (flat_map to_Ldigit (ls0++ls1^^n++ls2)) |> r.

Hypothesis ROverflow_11:
  forall l r n,
    l |> rd1^^n *> [1;1] *> r -->+
    l <* (flat_map to_Ldigit (ls3++ls4^^n++ls5)) |> r.


Definition LC n :=
  BinaryCounter d0 d1 (d1a *> const 0) n.

Definition RC n :=
  BinaryCounter_0 rd0 rd1 (rd1 *> const 0) n.

Definition RC0 n m :=
  BinaryCounter rd0 rd1 ([0] *> rd1 *> RC m) n.

Definition RC1 n m :=
  BinaryCounter rd0 rd1 ([1] *> rd1 *> RC m) n.

Definition RC2 n m :=
  BinaryCounter rd0 rd1 ([0;0;0] *> rd1 *> RC m) n.

Definition RC3 n m :=
  BinaryCounter rd0 rd1 ([1;0;0] *> rd1 *> RC m) n.

Lemma rotate_000 n r:
  rd0^^n *> [0;0;0] *> r =
  [0;0;0] *> rd0^^n *> r.
Proof.
  induction n.
  - reflexivity.
  - cbn[lpow].
    repeat rewrite Str_app_assoc.
    rewrite IHn.
    reflexivity.
Qed.

Lemma rotate_0 n r:
  rd0^^n *> [0] *> r =
  [0] *> rd0^^n *> r.
Proof.
  induction n.
  - reflexivity.
  - cbn[lpow].
    repeat rewrite Str_app_assoc.
    rewrite IHn.
    reflexivity.
Qed.

Lemma LC_shl n ls:
  (exists n0,
  flat_map to_Ldigit ls *> LC n = LC n0 /\
  n*(pow2 (length ls)) <= n0 /\
  n0 < (n+1)*(pow2 (length ls)))%positive.
Proof.
  induction ls.
  - cbn. exists n. split; auto; lia.
  - cbn. repeat rewrite Str_app_assoc.
    destruct IHls as [n0 [H0 [H1 H2]]].
    rewrite H0.
    destruct a as [|a].
    + exists (xO n0).
      split; auto; lia.
    + exists (xI n0).
      split; auto; lia.
Qed.




Lemma LC_Inc n (Hnf:not_full n) r:
  LC n <| r -->+
  LC (Pos.succ n) |> r.
Proof.
  apply BinaryCounter.LInc; assumption.
Qed.

Lemma LC_Overflow_0' n:
  pow2' n <> xH ->
  LC (pow2' n) <| RC 0 -->+
  LC (pow2 n) |> RC 1.
Proof.
  intro H.
  destruct n as [|n].
  1: cbn in H; lia.
  replace (S n) with (n+1) by lia.
  unfold LC.
  rewrite Counter_pow2,Counter_pow2'.
  replace (RC 0) with (rd0 *> const 0). 2:{
    cbn.
    repeat rewrite <-const_unfold.
    reflexivity.
  }
  follow10 LOverflow_0.
  cbn.
  repeat rewrite <-const_unfold.
  finish.
Qed.

Lemma LC_Overflow_1' n:
  pow2' n <> xH ->
  (exists k0,
  LC (pow2' n) <| RC 1 -->+
  LC k0 |> RC 0 /\
  ((pow2 n)*2 <= k0 < ((pow2 n)+1)*2)%positive
  ).
Proof.
  intro H.
  destruct n as [|n].
  1: cbn in H; lia.
  replace (S n) with (n+1) by lia.
  destruct (LC_shl (pow2 (n+1)) [v0]) as [k0 [H0 H1]].
  cbn in H0,H1.
  rewrite app_nil_r in H0.
  exists k0.
  split.
  - rewrite <-H0.
    unfold LC.
    rewrite Counter_pow2,Counter_pow2'.
    replace (RC 1) with (rd1 *> const 0). 2:{
      cbn.
      repeat rewrite <-const_unfold.
      reflexivity.
    }
    follow10 LOverflow_1.
    replace (RC 0) with ([0;0;0]*>const 0). 2:{
      cbn.
      repeat rewrite <-const_unfold.
      reflexivity.
    }
    finish.
  - lia.
Qed.

Lemma LC_Overflow_0 n m:
  pow2' n <> xH ->
  LC (pow2' n) <| RC (Npos (m~0)) -->+
  LC (pow2 n) |> RC0 ((pow2 (ctz m))~1) (shr m (S (ctz m))).
Proof.
  intro H.
  destruct n as [|n].
  1: cbn in H; lia.
  replace (S n) with (n+1) by lia.
  unfold LC.
  rewrite Counter_pow2,Counter_pow2'.
  unfold RC.
  rewrite BinaryCounter_0_d0.
  follow10 LOverflow_0.
  unfold RC0,RC.
  cbn[BinaryCounter].
  rewrite Counter_pow2.
  rewrite rotate_0.
  rewrite <-Counter_shr_S_ctz; auto.
Qed.

Lemma LC_Overflow_1 n m:
  pow2' n <> xH ->
  (exists k0,
  LC (pow2' n) <| RC (Npos (m~1)) -->+
  LC k0 |> RC2 (pow2 (ctz m)) (shr m (S (ctz m))) /\
  (pow2 n)*2 <= k0 < ((pow2 n)+1)*2)%positive.
Proof.
  intro H.
  destruct n as [|n].
  1: cbn in H; lia.
  replace (S n) with (n+1) by lia.
  destruct (LC_shl (pow2 (n+1)) [v0]) as [k0 [H0 H1]].
  cbn in H0,H1.
  rewrite app_nil_r in H0.
  exists k0.
  split.
  - rewrite <-H0.
    unfold LC.
    rewrite Counter_pow2,Counter_pow2'.
    unfold RC.
    rewrite BinaryCounter_0_d1.
    follow10 LOverflow_1.
    unfold RC2,RC.
    cbn[BinaryCounter].
    rewrite Counter_pow2.
    rewrite rotate_000.
    rewrite <-Counter_shr_S_ctz; auto.
  - apply H1.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (N.succ n).
Proof.
  apply BinaryCounter.RInc_0; auto.
  - intros. apply RInc.
  - cbv; (repeat rewrite <-const_unfold); reflexivity.
Qed.

Lemma RC0_Inc n m (Hnf:not_full n) l:
  l |> RC0 n m -->+
  l <| RC0 (Pos.succ n) m.
Proof.
  apply BinaryCounter.RInc; auto.
  intros. apply RInc.
Qed.

Lemma RC0_Overflow n m l:
  l |> RC0 (pow2' n) m -->+
  l <| RC1 (pow2 n) m.
Proof.
  unfold RC0,RC1.
  rewrite Counter_pow2,Counter_pow2'.
  apply RInc.
Qed.

Lemma RC1_Inc n m (Hnf:not_full n) l:
  l |> RC1 n m -->+
  l <| RC1 (Pos.succ n) m.
Proof.
  apply BinaryCounter.RInc; auto.
  intros. apply RInc.
Qed.

Lemma RC1_Overflow_0 k n:
  (exists k0,
  LC k |> RC1 (pow2' n) N0 -->+
  LC k0 |> RC N0 /\
  k*(pow2 (n*2+1)) <= k0 < (k+1)*(pow2 (n*2+1)))%positive.
Proof.
  destruct (LC_shl k (ls3 ++ ls4 ^^ n ++ ls5)) as [k0 [H0 H1]].
  exists k0.
  split.
  - unfold RC1.
    rewrite Counter_pow2'.
    change ([1] *> rd1 *> RC N0) with ([1;1] *> [0;0;0] *> RC N0).
    follow10 ROverflow_11.
    rewrite H0.
    cbn.
    repeat rewrite <-const_unfold.
    finish.
  - replace (n * 2 + 1) with (length (ls3 ++ ls4 ^^ n ++ ls5)).
    + apply H1.
    + repeat rewrite app_length.
      rewrite lpow_length.
      lia.
Qed.

Lemma RC1_Overflow k n m:
  (exists k0,
  LC k |> RC1 (pow2' n) (Npos m) -->+
  LC k0 |> RC2 (pow2 (ctz m)) (shr m (S (ctz m))) /\
  k*(pow2 (n*2+1)) <= k0 < (k+1)*(pow2 (n*2+1)))%positive.
Proof.
  destruct (LC_shl k (ls3 ++ ls4 ^^ n ++ ls5)) as [k0 [H0 H1]].
  exists k0.
  split.
  - unfold RC1,RC2.
    rewrite Counter_pow2,Counter_pow2'.
    change ([1] *> rd1 *> RC (N.pos m)) with ([1;1] *> [0;0;0] *> RC (N.pos m)).
    follow10 ROverflow_11.
    rewrite rotate_000.
    unfold RC.
    rewrite <-Counter_shr_S_ctz; auto.
    rewrite H0.
    finish.
  - replace (n * 2 + 1) with (length (ls3 ++ ls4 ^^ n ++ ls5)).
    + apply H1.
    + repeat rewrite app_length.
      rewrite lpow_length.
      lia.
Qed.

Lemma RC2_Inc n m (Hnf:not_full n) l:
  l |> RC2 n m -->+
  l <| RC2 (Pos.succ n) m.
Proof.
  apply BinaryCounter.RInc; auto.
  intros. apply RInc.
Qed.

Lemma RC2_Overflow n m l:
  l |> RC2 (pow2' n) m -->+
  l <| RC3 (pow2 n) m.
Proof.
  unfold RC2,RC3.
  rewrite Counter_pow2,Counter_pow2'.
  apply RInc.
Qed.

Lemma RC3_Inc n m (Hnf:not_full n) l:
  l |> RC3 n m -->+
  l <| RC3 (Pos.succ n) m.
Proof.
  apply BinaryCounter.RInc; auto.
  intros. apply RInc.
Qed.

Lemma RC3_Overflow_0 k n:
  (exists k0,
  LC k |> RC3 (pow2' n) N0 -->+
  LC k0 |> RC N0 /\
  k*(pow2 (n*2+2)) <= k0 < (k+1)*(pow2 (n*2+2)))%positive.
Proof.
  destruct (LC_shl k (ls0 ++ ls1 ^^ n ++ ls2)) as [k0 [H0 H1]].
  exists k0.
  split.
  - unfold RC3.
    rewrite Counter_pow2'.
    change ([1;0;0] *> rd1 *> RC N0) with ([1;0;0;1] *> [0;0;0] *> RC N0).
    follow10 ROverflow_1001.
    rewrite H0.
    cbn.
    repeat rewrite <-const_unfold.
    finish.
  - replace (n * 2 + 2) with (length (ls0 ++ ls1 ^^ n ++ ls2)).
    + apply H1.
    + repeat rewrite app_length.
      rewrite lpow_length.
      lia.
Qed.

Lemma RC3_Overflow k n m:
  (exists k0,
  LC k |> RC3 (pow2' n) (Npos m) -->+
  LC k0 |> RC2 (pow2 (ctz m)) (shr m (S (ctz m))) /\
  k*(pow2 (n*2+2)) <= k0 < (k+1)*(pow2 (n*2+2)))%positive.
Proof.
  destruct (LC_shl k (ls0 ++ ls1 ^^ n ++ ls2)) as [k0 [H0 H1]].
  exists k0.
  split.
  - unfold RC3,RC2.
    rewrite Counter_pow2,Counter_pow2'.
    change ([1;0;0] *> rd1 *> RC (N.pos m)) with ([1;0;0;1] *> [0;0;0] *> RC (N.pos m)).
    follow10 ROverflow_1001.
    rewrite rotate_000.
    unfold RC.
    rewrite <-Counter_shr_S_ctz; auto.
    rewrite H0.
    finish.
  - replace (n * 2 + 2) with (length (ls0 ++ ls1 ^^ n ++ ls2)).
    + apply H1.
    + repeat rewrite app_length.
      rewrite lpow_length.
      lia.
Qed.




Inductive Config :=
| cfgL(k:positive)(n:N)
| cfgR(k:positive)(n:N)
| cfg0L(k n:positive)(m:N)
| cfg0R(k n:positive)(m:N)
| cfg1L(k n:positive)(m:N)
| cfg1R(k n:positive)(m:N)
| cfg2L(k n:positive)(m:N)
| cfg2R(k n:positive)(m:N)
| cfg3L(k n:positive)(m:N)
| cfg3R(k n:positive)(m:N)
.



Definition to_config(x:Config):=
match x with
| cfgL k n => LC k <| RC n
| cfgR k n => LC k |> RC n
| cfg0L k n m => LC k <| RC0 n m
| cfg0R k n m => LC k |> RC0 n m
| cfg1L k n m => LC k <| RC1 n m
| cfg1R k n m => LC k |> RC1 n m
| cfg2L k n m => LC k <| RC2 n m
| cfg2R k n m => LC k |> RC2 n m
| cfg3L k n m => LC k <| RC3 n m
| cfg3R k n m => LC k |> RC3 n m
end.

Definition P(x:Config):Prop :=
(match x with
| cfgL k n => k<>xH /\ rest (pow2 (log2 k)) >= n + rest k + 0 /\ n + rest k >= 2
| cfgR k n => k<>xH /\ rest (pow2 (log2 k)) >= n + rest k + 1 /\ n + rest k >= 1
| cfg0L k n m => rest n + m + rest (pow2 (log2 n)) + 3 <= rest k
| cfg0R k n m => rest n + m + rest (pow2 (log2 n)) + 2 <= rest k
| cfg1L k n m => rest n + m + 2 <= rest k
| cfg1R k n m => rest n + m + 1 <= rest k < rest (pow2 (log2 k))
| cfg2L k n m => rest n + m + rest (pow2 (log2 n)) + 3 <= rest k
| cfg2R k n m => rest n + m + rest (pow2 (log2 n)) + 2 <= rest k
| cfg3L k n m => rest n + m + 2 <= rest k
| cfg3R k n m => rest n + m + 1 <= rest k < rest (pow2 (log2 k))
end)%N.

Hypothesis init: c0 -->* to_config (cfgL k_init n_init).
Hypothesis P_init: P (cfgL k_init n_init).



Lemma nonhalt: ~halts tm c0.
Proof.
apply multistep_nonhalt with (c':=to_config (cfgL k_init n_init)).
1: apply init.
apply (progress_nonhalt_cond tm _ _ _ P).
2: apply P_init.
intros i H.
destruct i.
- cbn[to_config].
  destruct H as [H0 H1].
  destruct (full_cases k) as [E|E].
  + destruct n as [|[n|n|]].
    * rewrite full_iff_rest in E. lia.
    * epose proof (LC_Overflow_1 (log2 k) n _) as H2.
      destruct H2 as [k0 [H2 H3]].
      exists (cfg2R k0 (pow2 (ctz n)) (shr n (S (ctz n)))). split.
      -- rewrite full_iff_pow2' in E.
        rewrite E.
        apply H2.
      -- cbn[P].
        destruct (rest_pow2_add _ 1 _ H3) as [H3' H3''].
        pose proof (le_pow2a _ _ 0 0 H3').
        rewrite log2_pow2.
        pose proof (split_bound n). lia.
    * epose proof (LC_Overflow_0 (log2 k) n _) as H2.
      rewrite full_iff_pow2' in E.
      rewrite E.
      eexists (cfg0R _ _ _). split.
      -- apply H2.
      -- cbn[P].
        cbn[log2].
        rewrite log2_pow2.
        rewrite rest_mul2add1.
        pose proof (rest_pow2 (ctz n)) as E1.
        pose proof (rest_pow2 (S (ctz n))) as E2.
        cbn[pow2] in E2. cbn[pow2].
        pose proof (rest_pow2 (log2 k)) as E3.
        assert (2 <= n*2 < pow2 (log2 k))%positive as E4 by lia.
        pose proof (split_bound' _ _ E4).
        lia.
    * rewrite full_iff_rest in E. lia.
  + exists (cfgR (Pos.succ k) n). split.
    * cbn[to_config].
      apply LC_Inc,E.
    * cbn[P].
      rewrite not_full_log2_S; auto.
      rewrite not_full_iff_rest in E.
      rewrite <-(rest_S k) in H1; auto.
      lia.
- cbn[to_config].
  cbn[P] in H.
  exists (cfgL k (N.succ n)). split.
  + apply RC_Inc.
  + cbn[P].
    lia.
- cbn[to_config].
  cbn[P] in H.
  assert (rest k <> 0%N) as E by (lia).
  rewrite <-not_full_iff_rest in E.
  exists (cfg0R (Pos.succ k) n m). split.
  + apply (LC_Inc _ E).
  + cbn[P].
    rewrite not_full_iff_rest in E.
    rewrite <-(rest_S k) in H; auto. lia.
- cbn[to_config].
  cbn[P] in H.
  destruct (full_cases n) as [E0|E0].
  + eexists (cfg1L k (pow2 (log2 n)) m). split.
    * rewrite full_iff_pow2' in E0.
      rewrite E0.
      cbn[to_config].
      follow10 (RC0_Overflow).
      rewrite <-E0.
      finish.
    * cbn[P]. lia.
  + eexists (cfg0L k (Pos.succ n) m). split.
    * apply (RC0_Inc n m E0).
    * cbn[P].
      rewrite not_full_log2_S; auto.
      rewrite not_full_iff_rest in E0.
      rewrite <-(rest_S n) in H; auto. lia.
- cbn[to_config].
  cbn[P] in H.
  assert (rest k <> 0%N) as E by lia.
  rewrite <-not_full_iff_rest in E.
  exists (cfg1R (Pos.succ k) n m). split.
  + apply LC_Inc,E.
  + cbn[P].
    rewrite not_full_iff_rest in E.
    rewrite <-(rest_S k) in H; auto. split; try lia.
    apply rest_S_not_empty,E.
- cbn[to_config].
  cbn[P] in H.
  destruct (full_cases n) as [E0|E0].
  + rewrite full_iff_pow2' in E0.
    rewrite E0.
    destruct m as [|m].
    * destruct (RC1_Overflow_0 k (log2 n)) as [k0 [H2 H3]].
      eexists (cfgR k0 0). split.
      -- apply H2.
      -- cbn[P].
        pose proof (not_empty_rest_pow2_add _ _ _ H3).
        repeat split; try lia.
        destruct (rest_pow2_add _ _ _ H3) as [H1 _].
        epose proof (N.mul_le_mono_l 1 (N.pos (pow2 (log2 n * 2 + 1))) (rest k)).
        lia.
    * destruct (RC1_Overflow k (log2 n) m) as [k0 [H2 H3]].
      eexists (cfg2R k0 _ _). split.
      -- follow10 H2. finish.
      -- cbn[P].
        destruct (rest_pow2_add _ _ _ H3) as [H3' H3''].
        pose proof (le_pow2a _ _ _ _ H3').
        rewrite log2_pow2.
        pose proof (split_bound m). lia.
  + eexists (cfg1L _ _ _). split.
    * apply (RC1_Inc n m E0).
    * cbn[P].
      rewrite not_full_iff_rest in E0.
      rewrite <-(rest_S n) in H; auto. lia.
- cbn[to_config].
  cbn[P] in H.
  assert (rest k <> 0%N) as E by lia.
  rewrite <-not_full_iff_rest in E.
  eexists (cfg2R _ _ _). split.
  + apply LC_Inc,E.
  + cbn[P].
    rewrite not_full_iff_rest in E.
    rewrite <-(rest_S k) in H; auto. lia.
- cbn[to_config].
  cbn[P] in H.
  destruct (full_cases n) as [E0|E0].
  + rewrite full_iff_pow2' in E0.
    rewrite E0.
    eexists (cfg3L _ _ _). split.
    * apply RC2_Overflow.
    * cbn[P]. lia.
  + eexists (cfg2L _ _ _). split.
    * apply RC2_Inc,E0.
    * cbn[P].
      rewrite not_full_log2_S; auto.
      rewrite not_full_iff_rest in E0.
      rewrite <-(rest_S n) in H; auto. lia.
- cbn[to_config].
  cbn[P] in H.
  assert (rest k <> 0%N) as E by lia.
  rewrite <-not_full_iff_rest in E.
  eexists (cfg3R _ _ _). split.
  + apply LC_Inc,E.
  + cbn[P].
    rewrite not_full_iff_rest in E.
    rewrite <-(rest_S k) in H; auto.
    split. 1: lia.
    apply rest_S_not_empty,E.
- cbn[to_config].
  cbn[P] in H.
  destruct (full_cases n) as [E0|E0].
  + rewrite full_iff_pow2' in E0.
    rewrite E0.
    destruct m as [|m].
    * destruct (RC3_Overflow_0 k (log2 n)) as [k0 [H2 H3]].
      eexists (cfgR k0 0). split.
      -- apply H2.
      -- cbn[P].
        epose proof (not_empty_rest_pow2_add _ _ _ H3).
        destruct (rest_pow2_add _ _ _ H3) as [H1 _].
        epose proof (N.mul_le_mono_l 1 (N.pos (pow2 (log2 n * 2 + 1))) (rest k)).
        lia.
    * destruct (RC3_Overflow k (log2 n) m) as [k0 [H2 H3]].
      eexists (cfg2R k0 _ _). split.
      -- follow10 H2. finish.
      -- cbn[P].
        destruct (rest_pow2_add _ _ _ H3) as [H3' H3''].
        pose proof (le_pow2a _ _ _ _ H3').
        rewrite log2_pow2.
        pose proof (split_bound m). lia.
  + eexists (cfg3L _ _ _). split.
    * apply (RC3_Inc n m E0).
    * cbn[P].
      rewrite not_full_iff_rest in E0.
      rewrite <-(rest_S n) in H; auto. lia.
Unshelve.
all: destruct k; cbn in H0; cbn; lia.
Qed.

End SOCv1.





Inductive SOC_cert_v1 :=
| Build_SOC_cert_v1
  (QL QR : Q)
  (qL qR : list Sym)
  (v0 : nat)
  (ls0 ls1 ls2 ls3 ls4 ls5: list nat)
  (k_init: positive)
  (n_init : N).

Ltac solve_LOverflow :=
  intros;
  simpl_tape; cbn; step1s;
  use_shift_rule; cbn;
  step1s;
  use_shift_rule; cbn;
  simpl_rotate;
  step1s.

Ltac solve_SOCv1 tm cert :=
match cert with
  (Build_SOC_cert_v1
  ?QL ?QR
  ?qL ?qR
  ?v0
  ?ls0 ?ls1 ?ls2 ?ls3 ?ls4 ?ls5
  ?k_init
  ?n_init) =>
  eapply (nonhalt tm
    QL QR
    qL qR
    v0
    ls0 ls1 ls2 ls3 ls4 ls5
    k_init n_init);
  [ try (intros l r n; casen_execute_with_shift_rule n; fail)
  | try (intros l r n; casen_execute_with_shift_rule n; fail)
  | try (solve_LOverflow; fail)
  | try (solve_LOverflow; fail)
  | reflexivity
  | reflexivity
  | reflexivity
  | reflexivity
  | try (intros l r n;
    simpl_flat_map;
    casen_execute_with_shift_rule n;
    fail)
  | try (intros l r n;
    simpl_flat_map;
    casen_execute_with_shift_rule n;
    fail)
  | try (cbn; solve_init; fail)
  | try (cbn; lia; fail)
  ]
end.








