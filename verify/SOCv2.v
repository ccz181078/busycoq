From BusyCoq Require Import Individual62.
From BusyCoq Require Import BinaryCounterFull.
From BusyCoq Require Import BinaryCounter.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.


Section SOCv2.

Hypothesis tm: TM.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Hypothesis QL QR:Q.
Hypothesis m0 m1:list Sym.
Hypothesis v0: nat.
Hypothesis ls0 ls1 ls2: list nat.

Hypothesis k_init:positive.
Hypothesis n_init:N.

Notation "l <| r" :=
  (l <{{QL}} m0 *> r) (at level 30).

Notation "l |> r" :=
  (l <* m1 {{QR}}> r) (at level 30).

Definition d0 := [0;1].
Definition d1 := [1;1].
Definition d1a := [1].

Hypothesis LInc:
  forall (l r:side) n,
    l <* d0 <* d1^^n <| r -->+
    l <* d1 <* d0^^n |> r.

Definition rd0 := [0;0;0;0].
Definition rd1 := [0;0;0;1].

Hypothesis RInc:
  forall (l r:side) n,
    l |> rd1^^n *> rd0 *> r -->+
    l <| rd0^^n *> rd1 *> r.

Definition to_Ldigit(n:nat):=
match n with
| O => d0
| _ => d1
end.

Hypothesis LOverflow:
  forall r n,
    const 0 <* d1a <* d1^^(n+1) <| [0] *> r -->+
    const 0 <* d1a <* d0^^(n+1) <* (to_Ldigit v0) |> r.

Hypothesis Hls02:
  length ls0 + length ls2 = 2.
Hypothesis Hls1:
  length ls1 = 2.

Hypothesis ROverflow:
  forall l r n,
    l |> rd1^^n *> [0;0;1;0] *> r -->+
    l <* (flat_map to_Ldigit (ls0++ls1^^n++ls2)) <| r.


Definition LC n :=
  BinaryCounter d0 d1 (d1a *> const 0) n.

Definition RC n :=
  BinaryCounter_0 rd0 rd1 (rd1 *> const 0) n.

Definition RC0 n m :=
  BinaryCounter rd0 rd1 ([0;0;1] *> RC m) n.

Lemma rotate_0 n r:
  rd0^^n *> rd1 *> r =
  [0] *> rd0^^n *> [0;0;1] *> r.
Proof.
  unfold rd0,rd1; cbn.
  simpl_rotate.
  reflexivity.
Qed.

Lemma rotate_rd1 n r:
  [0;0;1] *> rd0^^n *> rd1 *> r =
  [0;0;1;0] *> rd0^^n *> [0;0;1] *> r.
Proof.
  unfold rd0,rd1; cbn.
  simpl_rotate.
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




Ltac solve_const0_eq:=
  cbv; (repeat rewrite <-const_unfold); reflexivity.


Lemma LC_Inc n (Hnf:not_full n) r:
  LC n <| r -->+
  LC (Pos.succ n) |> r.
Proof.
  apply BinaryCounter.LInc; assumption.
Qed.

Lemma LC_Overflow n m:
  pow2' n <> xH ->
  (exists k0,
  LC (pow2' n) <| RC (Npos m) -->+
  LC k0 |> RC0 (pow2 (ctz m)) (shr m (S (ctz m))) /\
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
    rewrite Counter_shr_S_ctz; auto.
    rewrite rotate_0.
    follow10 LOverflow.
    unfold RC0,RC.
    rewrite Counter_pow2.
    finish.
  - apply H1.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (N.succ n).
Proof.
  apply BinaryCounter.RInc_0; auto.
  solve_const0_eq.
Qed.

Lemma RC0_Inc n m (Hnf:not_full n) l:
  l |> RC0 n m -->+
  l <| RC0 (Pos.succ n) m.
Proof.
  apply BinaryCounter.RInc; auto.
Qed.

Lemma RC0_Overflow_0 k n:
  (exists k0,
  LC k |> RC0 (pow2' n) N0 -->+
  LC k0 <| RC N0 /\
  k*(pow2 (n*2+2)) <= k0 < (k+1)*(pow2 (n*2+2)))%positive.
Proof.
  destruct (LC_shl k (ls0 ++ ls1 ^^ n ++ ls2)) as [k0 [H0 H1]].
  exists k0.
  split.
  - unfold RC0.
    rewrite Counter_pow2'.
    replace ([0;0;1] *> RC N0) with ([0;0;1;0] *> RC N0) by solve_const0_eq.
    follow10 ROverflow.
    rewrite H0.
    finish.
  - replace (n * 2 + 2) with (length (ls0 ++ ls1 ^^ n ++ ls2)).
    + apply H1.
    + repeat rewrite app_length.
      rewrite lpow_length.
      lia.
Qed.

Lemma RC0_Overflow k n m:
  (exists k0,
  LC k |> RC0 (pow2' n) (Npos m) -->+
  LC k0 <| RC0 (pow2 (ctz m)) (shr m (S (ctz m))) /\
  k*(pow2 (n*2+2)) <= k0 < (k+1)*(pow2 (n*2+2)))%positive.
Proof.
  destruct (LC_shl k (ls0 ++ ls1 ^^ n ++ ls2)) as [k0 [H0 H1]].
  exists k0.
  split.
  - unfold RC0,RC.
    rewrite Counter_shr_S_ctz; auto.
    rewrite Counter_pow2,Counter_pow2'.
    rewrite rotate_rd1.
    follow10 ROverflow.
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
.



Definition to_config(x:Config):=
match x with
| cfgL k n => LC k <| RC n
| cfgR k n => LC k |> RC n
| cfg0L k n m => LC k <| RC0 n m
| cfg0R k n m => LC k |> RC0 n m
end.

Definition P(x:Config):Prop :=
(match x with
| cfgL k n => k<>xH /\ rest (pow2 (log2 k)) >= n + rest k + 0 /\ n + rest k >= 1
| cfgR k n => k<>xH /\ rest (pow2 (log2 k)) >= n + rest k + 1 /\ n + rest k >= 0
| cfg0L k n m => rest n + m + 2 <= rest k
| cfg0R k n m => rest n + m + 1 <= rest k
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
  + destruct n as [|n].
    * rewrite full_iff_rest in E. lia.
    * epose proof (LC_Overflow (log2 k) n _) as H2.
      destruct H2 as [k0 [H2 H3]].
      rewrite full_iff_pow2' in E.
      rewrite E.
      eexists (cfg0R _ _ _). split.
      -- apply H2.
      -- cbn[P].
        destruct (rest_pow2_add _ 1 _ H3) as [H3' H3''].
        pose proof (le_pow2a _ _ 0 0 H3').
        pose proof (split_bound n). lia.
  + eexists (cfgR _ _). split.
    * apply LC_Inc,E.
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
  + apply LC_Inc,E.
  + cbn[P].
    rewrite not_full_iff_rest in E.
    rewrite <-(rest_S k) in H; auto. lia.
- cbn[to_config].
  cbn[P] in H.
  destruct (full_cases n) as [E0|E0].
  + rewrite full_iff_pow2' in E0.
    rewrite E0.
    destruct m as [|m].
    * destruct (RC0_Overflow_0 k (log2 n)) as [k0 [H2 H3]].
      eexists (cfgL k0 0). split.
      -- apply H2.
      -- cbn[P].
        pose proof (rest_le k0).
        destruct (rest_pow2_add _ _ _ H3) as [H1 _].
        epose proof (N.mul_le_mono_l 1 (N.pos (pow2 (log2 n * 2 + 2))) (rest k)).
        lia.
    * destruct (RC0_Overflow k (log2 n) m) as [k0 [H2 H3]].
      eexists (cfg0L k0 _ _). split.
      -- apply H2.
      -- cbn[P].
        destruct (rest_pow2_add _ _ _ H3) as [H3' H3''].
        pose proof (le_pow2a _ _ _ _ H3').
        pose proof (split_bound m). lia.
  + eexists (cfg0L _ _ _). split.
    * apply RC0_Inc,E0.
    * cbn[P].
      rewrite not_full_iff_rest in E0.
      rewrite <-(rest_S n) in H; auto. lia.
Unshelve.
all: destruct k; cbn in H0; cbn; lia.
Qed.

End SOCv2.





Inductive SOC_cert_v2 :=
| Build_SOC_cert_v2
  (QL QR : Q)
  (qL qR : list Sym)
  (v0 : nat)
  (ls0 ls1 ls2: list nat)
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

Ltac solve_SOCv2 tm cert :=
match cert with
  (Build_SOC_cert_v2
  ?QL ?QR
  ?qL ?qR
  ?v0
  ?ls0 ?ls1 ?ls2
  ?k_init
  ?n_init) =>
  eapply (nonhalt tm
    QL QR
    qL qR
    v0
    ls0 ls1 ls2
    k_init n_init);
  [ try (intros l r n; casen_execute_with_shift_rule n; fail)
  | try (intros l r n; unfold rd0,rd1; casen_execute_with_shift_rule n; fail)
  | try (execute_with_shift_rule; fail)
  | reflexivity
  | reflexivity
  | try (intros l r n;
    simpl_flat_map;
    casen_execute_with_shift_rule n;
    fail)
  | try (cbn; solve_init; fail)
  | try (cbn; lia; fail)
  ]
end.

Definition tm0 := Eval compute in (TM_from_str "1RB1LA_1LC1RF_0RD0LD_1LE0LC_1RA---_1RE0RB").

Theorem nonhalt0: ~halts tm0 c0.
Proof.
  solve_SOCv2 tm0 (Build_SOC_cert_v2 A F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 127 23).
Qed.






