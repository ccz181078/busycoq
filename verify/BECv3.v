From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import BinaryCounter.
From BusyCoq Require Import BinaryCounterFull.

Open Scope list.

Module ShiftDigit.
Section ShiftDigit.
Hypothesis tm:TM.
Hypothesis QL QR:Q.
Hypothesis qL qR d1' w0 w1 w2:list Sym.
Hypothesis k_init n_init:N.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{QL}} qL *> r) (at level 30).

Notation "l |> r" :=
  (l <* qR {{QR}}> r) (at level 30).


Definition d1:=[0]++d1'.
Definition d0:=BinaryCounter.d0 d1.

Definition LC n := BinaryCounter_0 d1 n.
Definition LC0 n m := BinaryCounter d0 d1 (d1' *> BinaryCounter_0 d1 m) n.

Definition R n m := w0^^n *> w1 *> w2^^m *> const 0.

Hypothesis LInc:
  forall l r n,
    l <* d0 <* d1^^n <| r -->+
    l <* d1 <* d0^^n |> r.

Hypothesis LOv:
  forall l r n,
    l <* [0] <* d1' <* d1^^n <| r -->+
    l <* d0^^(1+n) |> r.

Hypothesis RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).

Hypothesis ROv:
  forall l n m,
    l <* d0 <* d1^^n |> R 0 m -->+
    l <* d1' <* d0^^n |> R (1+m) 0.

Lemma rotate_0 n r:
  d0^^n *> d1 *> r =
  [0] *> d0^^n *> d1' *> r.
Proof.
  unfold d0,d1.
  cbn.
  simpl_rotate.
  rewrite List.repeat_cons.
  reflexivity.
Qed.

Lemma LC_Inc:
  forall r n,
    LC n <| r -->+
    LC (N.succ n) |> r.
Proof.
  intros.
  apply LInc_0.
  apply LInc.
Qed.

Lemma LC0_Inc:
  forall r n m,
    not_full n ->
    LC0 n m <| r -->+
    LC0 (Pos.succ n) m |> r.
Proof.
  introv Hnf.
  apply BinaryCounter.LInc.
  2: apply Hnf.
  apply LInc.
Qed.

Lemma LC_Overflow_0 r n:
  LC0 (pow2' n) N0 <| r -->+
  LC N0 |> r.
Proof.
  intros.
  unfold LC0.
  rewrite Counter_pow2'.
  replace (BinaryCounter_0 d1 0) with ([0] *> const 0) by solve_const0_eq.
  follow10 LOv.
  finish.
  unfold d0.
  rewrite lpow_all0.
  - reflexivity.
  - apply BinaryCounter.d0_all0.
Qed.

Lemma LC_Overflow r n m:
  LC0 (pow2' n) (Npos m) <| r -->+
  LC0 (pow2 (1+n+(ctz m))) (shr m (S (ctz m))) |> r.
Proof.
  intros.
  unfold LC0.
  rewrite Counter_pow2',Counter_pow2.
  rewrite Counter_shr_S_ctz.
  change (BinaryCounter.d0 d1) with d0.
  rewrite rotate_0.
  follow10 LOv.
  simpl_tape.
  finish.
Qed.


Lemma R_Overflow k m:
  LC k |> R 0 m -->+
  LC0 (pow2 (ctz (N.succ_pos k)))(shr (N.succ_pos k) (S (ctz (N.succ_pos k)))) |> R (1+m) 0.
Proof.
  unfold LC,LC0.
  rewrite Counter_shr_S_ctzS.
  rewrite Counter_pow2.
  follow10 ROv.
  finish.
Qed.

Lemma Inc0 k j n m (Hnf:not_full k):
  LC0 k j |> R (1+n) m -->+
  LC0 (Pos.succ k) j |> R n (1+m).
Proof.
  follow11 RInc.
  apply LC0_Inc,Hnf.
Qed.

Lemma LC0_Incs k j n m:
  LC0 k j |> R ((N.to_nat (rest k))+n) m -->*
  LC0 (pow2' (log2 k)) j |> R n ((N.to_nat (rest k))+m).
Proof.
  remember (N.to_nat (rest k)) as r.
  gen k j n m.
  induction r; intros.
  - assert (rest k = 0)%N as E by lia.
    rewrite <-full_iff_rest in E.
    rewrite full_iff_pow2' in E.
    rewrite <-E.
    finish.
  - assert (rest k <> 0)%N as E by lia.
    rewrite <-not_full_iff_rest in E.
    follow100 (Inc0 k j (r+n) m E).
    epose proof (IHr (Pos.succ k) _ _ _ (1+m)).
    follow H.
    rewrite not_full_log2_S; auto.
    finish.
Unshelve.
  rewrite not_full_iff_rest in E.
  pose proof (rest_S _ E) as H.
  lia.
Qed.

Lemma rest_pow2_add1 k n:
  N.to_nat (rest (pow2 k)) + (1+n) =
  Pos.to_nat (pow2 k) + n.
Proof.
  pose proof (rest_pow2 k).
  lia.
Qed.

Lemma LC0_Incs' k j n m:
  LC0 (pow2 k) j |> R ((Pos.to_nat (pow2 k))+n) m -->*
  LC0 (pow2' k) j <| R n ((Pos.to_nat (pow2 k))+m).
Proof.
  pose proof (LC0_Incs (pow2 k) j (1+n) m) as H.
  rewrite rest_pow2_add1 in H.
  rewrite log2_pow2 in H.
  follow H.
  follow100 RInc.
  rewrite <-rest_pow2_add1.
  finish.
Qed.

Definition v j i :=
  ((N.succ_pos (j*2))*(pow2 i))%positive.

Lemma v_S j i:
  (v (Npos j) i =
  (pow2 i)+(v (shr j (S (ctz j))) (1 + i + ctz j)))%positive.
Proof.
  unfold v.
  replace (N.succ_pos (N.pos j*2)) with (Pos.succ (j*2))%positive by lia.
  rewrite Pos.mul_succ_l.
  f_equal.
  gen i.
  induction j; intros.
  - cbn[shr].
    cbn[ctz].
    cbn[shr].
    replace (1+i+0) with (S i) by lia.
    cbn[pow2].
    lia.
  - cbn[shr].
    cbn[ctz].
    specialize (IHj i).
    replace (1+i+S (ctz j)) with (S(1+i+ctz j)) by lia.
    cbn[pow2].
    lia.
  - cbn.
    do 2 f_equal.
    lia.
Qed.

Lemma v_shrSctz_ctz n:
  (v (shr n (S (ctz n))) (ctz n)) = n.
Proof.
  unfold v.
  induction n.
  - cbn. lia.
  - cbn[shr].
    cbn[ctz].
    cbn[pow2].
    lia.
  - cbn. lia.
Qed.

Lemma LC0_Incs'' i j n m:
  LC0 (pow2 i) j |> R ((Pos.to_nat (v j i))+n) m -->*
  LC 0 |> R n ((Pos.to_nat (v j i))+m).
Proof.
  gen i n m.
  induction j using N_strong_induction.
  intros.
  destruct j as [|j].
  - unfold v.
    cbn[N.mul].
    cbn[N.succ_pos].
    cbn[Pos.mul].
    follow LC0_Incs'.
    follow100 LC_Overflow_0.
    finish.
  - rewrite v_S.
    rewrite Pos2Nat.inj_add.
    repeat rewrite <-Nat.add_assoc.
    follow LC0_Incs'.
    follow100 LC_Overflow.
    epose proof (H (shr j (S (ctz j))) _ (1+i+ctz j)) as H0.
    follow H0.
    repeat rewrite Nat.add_assoc.
    finish.
Unshelve.
  apply shr_S_lt.
Qed.

Lemma Incs k n m:
  LC k |> R n m -->*
  LC (k+(N.of_nat n)) |> R 0 (n+m).
Proof.
  gen k m.
  induction n; intros.
  - finish.
  - follow100 RInc.
    follow100 LC_Inc.
    follow IHn.
    finish.
Qed.

Lemma BigStep k m:
  LC k |> R 0 ((N.to_nat k)+m) -->+ LC (N.of_nat m) |> R 0 ((N.to_nat k)+m+1).
Proof.
  follow10 R_Overflow.
  remember (N.succ_pos k) as k'.
  epose proof (LC0_Incs'' (ctz k') (shr k' (S (ctz k'))) m 0).
  rewrite v_shrSctz_ctz in H.
  replace (1+((N.to_nat k) + m)) with (Pos.to_nat k' + m) by lia.
  follow H.
  follow Incs.
  finish.
Qed.

Inductive Config:=
| cfg0 (k n:N)
| cfg1 (k n:N)
.

Definition to_config(x:Config):=
match x with
| cfg0 k n => LC k |> R 0 ((N.to_nat (k+n)))
| cfg1 k n => LC n |> R 0 ((N.to_nat (k+n+1)))
end.

Hypothesis init:
  c0 -->*
  to_config (cfg0 k_init n_init).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  apply progress_nonhalt_simple.
  intro i.
  destruct i as [k|k].
  - exists (cfg1 k n).
    cbn[to_config].
    replace (N.to_nat (k+n)) with (N.to_nat k + N.to_nat n) by lia.
    follow10 BigStep.
    finish.
  - exists (cfg0 (N.succ k) (N.succ n)).
    cbn[to_config].
    replace (N.to_nat (k+n+1)) with (N.to_nat n + (N.to_nat k + 1)) by lia.
    follow10 BigStep.
    finish.
Qed.

End ShiftDigit.

Inductive Cert :=
| cert1
  (QL QR : Q)
  (qL qR d1' w0 w1 w2 : list Sym)
  (k_init n_init : N).

Ltac solve_cert cert :=
match cert with
  (cert1
  ?QL ?QR
  ?qL ?qR ?d1' ?w0 ?w1 ?w2
  ?k_init ?n_init) =>
  eapply (nonhalt _
    QL QR
    qL qR d1' w0 w1 w2
    k_init n_init);
  [ unfold d0,d1;
    try (execute_with_shift_rule; fail)
  | unfold d0,d1;
    try (execute_with_shift_rule; fail)
  | unfold R;
    try (execute_with_shift_rule; fail)
  | unfold d0,d1,R;
    try (execute_with_shift_rule; fail)
  | cbn;
    try (solve_init; fail)
  ]
end.


Definition tm0 := Eval compute in (TM_from_str "1LB0RA_1RC1LE_1LD1RD_0LB1LA_0LB0LF_0LB---").
Lemma nonhalt0: ~halts tm0 c0.
Proof.
  solve_cert (cert1 E D [1;0] [1;1] [0;0;1] [1;0] [0] [1;0] 0 0).
Qed.

Definition tm1 := Eval compute in (TM_from_str "1LB0RA_1RC1LE_1LD1RD_0LE1LA_0LB0LF_---0RC").
Lemma nonhalt1: ~halts tm1 c0.
Proof.
  solve_cert (cert1 E D [1;0] [1;1] [0;0;1] [1;0] [0] [1;0] 0 0).
Qed.

Definition tm2 := Eval compute in (TM_from_str "1LB1RB_0LC1LD_1RA1LE_1LC0RD_0LC0LF_0LC---").
Lemma nonhalt2: ~halts tm2 c0.
Proof.
  solve_cert (cert1 E B [1;0] [1;1] [0;0;1] [1;0] [0] [1;0] 2 0).
Qed.

Definition tm3 := Eval compute in (TM_from_str "1LB1RB_0LC1LE_0LD1LF_1RA1LC_1LD0RE_---0LC").
Lemma nonhalt3: ~halts tm3 c0.
Proof.
  solve_cert (cert1 C B [1;0] [1;1] [0;0;1] [1;0] [0] [1;0] 1 1).
Qed.

Definition tm4 := Eval compute in (TM_from_str "1RB1LE_1LC1RC_0LA1LD_1LA0RD_0LA0LF_0LA---").
Lemma nonhalt4: ~halts tm4 c0.
Proof.
  solve_cert (cert1 E C [1;0] [1;1] [0;0;1] [1;0] [0] [1;0] 1 0).
Qed.

Definition tm5 := Eval compute in (TM_from_str "1RB1LE_1LC1RC_0LE1LD_1LA0RD_0LA0LF_---0RB").
Lemma nonhalt5: ~halts tm5 c0.
Proof.
  solve_cert (cert1 E C [1;0] [1;1] [0;0;1] [1;0] [0] [1;0] 1 0).
Qed.

Definition tm6 := Eval compute in (TM_from_str "1RB1LE_1LC1RC_0LE1LD_1LA0RD_0LA1LF_---0LE").
Lemma nonhalt6: ~halts tm6 c0.
Proof.
  solve_cert (cert1 E C [1;0] [1;1] [0;0;1] [1;0] [0] [1;0] 1 0).
Qed.

Definition tm7 := Eval compute in (TM_from_str "1LB0LC_1LC0RD_1RD1LA_0LE0RD_1RC1LF_---0LA").
Lemma nonhalt7: ~halts tm7 c0.
Proof.
  solve_cert (cert1 A D [1;0] [1;1] [0;1] [1;0] [0] [1;0] 1 0).
Qed.

Definition tm8 := Eval compute in (TM_from_str "1RB1LD_1RC1LE_0LA0RC_---0LE_1LF0LB_1LB0RC").
Lemma nonhalt8: ~halts tm8 c0.
Proof.
  solve_cert (cert1 E C [1;0] [1;1] [0;1] [1;0] [0] [1;0] 1 1).
Qed.




End ShiftDigit.
