From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import BinaryCounter_v2.
From BusyCoq Require Import Longitudinal.
From BusyCoq Require ES_v2.

Ltac es_v2 := ES_v2.es.


Module TM1.
Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC1LE_1RA0LD_1RC1LC_1LF0LE_---1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <1| r" := (l <{{C}} r) (at level 30).
Notation "l |1> r" := (l {{A}}> r) (at level 30).

Notation "l <| r" := (l <{{E}} 0>>r) (at level 30).
Notation "l |> r" := (l<<1 {{A}}> r) (at level 30).

Inductive LC: nat->side->Prop :=
| LC_0: LC 0 (0inf)
| LC_1 n l:
  LC n l ->
  LC (n*2+1) (l<*<[0;1])
| LC_2 n l:
  LC n l ->
  LC (n*2+2) (l<*<[1;1]).

Ltac eex := eexists; repeat split.

Lemma LInc n l:
  LC n l ->
  exists l',
  LC (S n) l' /\
  (forall r, l <1| r -->* l' |1> r).
Proof.
  intros HLC.
  induction HLC.
  - eex.
    + apply (LC_1 0),LC_0.
    + es.
  - eex.
    + apply LC_2 in HLC.
      applys_eq HLC; lia.
    + es.
  - destruct IHHLC as [l' [I1 I2]].
    apply (LC_1) in I1.
    eex.
    + applys_eq I1; lia.
    + es; er; follow I2; es.
Qed.

Notation w := [1;1;1;0].

Inductive RC: nat->side->Prop :=
| RC_0: RC 0 ([1;1;1;1;1]*>0inf)
| RC_1 n r:
  RC n r ->
  RC (n*2+1) ([0;0]*>w^^((n+1)/2)*>r)
| RC_2 n r:
  RC n r ->
  RC (n*2+2) ([1;1]*>w^^((n+1)/2+1)*>r).

Lemma RInc n r:
  RC n r ->
  exists r',
  RC (S n) r' /\
  (n mod 2 = 0 -> forall l, l |> r -->* l <| r')%nat /\
  (n mod 2 = 1 -> forall l, l |> w *> r -->* l <| r')%nat.
Proof.
  intros HRC.
  induction HRC.
  - eex.
    + apply (RC_1 0),RC_0.
    + es.
    + lia.
  - eex.
    + apply RC_2 in HRC.
      applys_eq HRC; lia.
    + lia.
    + es.
  - destruct IHHRC as [r' [I1 [I2 I3]]].
    assert (n mod 2 = 0 \/ n mod 2 = 1)%nat as [E|E] by lia.
    + eex.
      * apply RC_1 in I1.
        applys_eq I1; lia.
      * intros.
        replace ((S n+1)/2) with ((n+1)/2+1) by lia.
        es; er; follow I2; es.
      * lia.
    + eex.
      * apply RC_1 in I1.
        applys_eq I1; lia.
      * intros.
        rewrite lpow_add,Str_app_assoc.
        remember (w^^1*>r) as r0.
        replace ((S n+1)/2) with ((n+1)/2) by lia.
        es; er.
        subst.
        follow I3.
        es.
      * lia.
Qed.

Definition S0 l m r :=
  l <* <[0;1;0] |> w^^m *> r.

Lemma RR l n r:
  l |> w^^n *> r -->*
  l <* <[1;1;1;0]^^n |> r.
Proof.
  es.
Qed.

Lemma RR' l n r:
  l |> w^^(S n) *> r -->*
  l <* <[1;1;1;0]^^n |> w *> r.
Proof.
  intros.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  sr.
  finish.
Qed.

Lemma LL l n r:
  l <* <[1;1;1;0]^^n <| r -->*
  l <| w^^n *> r.
Proof.
  es.
Qed.

Lemma ML l r:
  l <* <[0;1;0] <| r -->*
  l <1| [1;0;1;0] *> r.
Proof. es. Qed.

Lemma MR l r:
  l |1> [1;0;1;0] *> r -->*
  l <* <[0;1;0] |> r.
Proof. es. Qed.

Ltac follow_LInc H :=
  follow ML;
  follow H;
  follow MR.

Lemma Incs0 l k m n r:
  LC k l ->
  RC n r ->
  n mod 2 = 1%nat ->
  exists l' r',
  LC (k+m*2) l' /\
  RC (n+m*2) r' /\
  S0 l m r -->* S0 l' 0 r'.
Proof.
  gen l k n r.
  induction m; intros.
  - eex; eex.
    + applys_eq H; lia.
    + applys_eq H0; lia.
    + es.
  - apply RInc in H0.
    destruct H0 as [r0 [I1 [_ I2]]].
    apply LInc in H.
    destruct H as [l0 [I3 I4]].
    apply RInc in I1.
    destruct I1 as [l1 [I5 [I6 _]]].
    apply LInc in I3.
    destruct I3 as [r1 [I7 I8]].
    unshelve epose proof (IHm _ _ _ _ I7 I5 _) as [l' [r' [I9 [I10 I11]]]].
    1: lia.
    eex; eex.
    + applys_eq I9; lia.
    + applys_eq I10; lia.
    + unfold S0 in *.
      follow RR'.
      follow I2.
      follow LL.
      follow_LInc I4.
      follow RR.
      follow I6.
      1: lia.
      follow LL.
      follow_LInc I8.
      apply I11.
Qed.

Lemma Incs1 l k m n r:
  LC k l ->
  RC n r ->
  n mod 2 = O ->
  exists l' r',
  LC (k+m*2+1) l' /\
  RC (n+m*2+1) r' /\
  S0 l m r -->* S0 l' 0 r'.
Proof.
  intros.
  apply RInc in H0.
  destruct H0 as [r0 [I1 [I2 _]]].
  apply LInc in H.
  destruct H as [l0 [I3 I4]].
  unshelve epose proof (Incs0 _ _ m _ _ I3 I1 _) as [l' [r' [I5 [I6 I7]]]].
  1: lia.
  eex; eex.
  - applys_eq I5; lia.
  - applys_eq I6; lia.
  - unfold S0 in *.
    follow RR.
    follow I2.
    follow LL.
    follow_LInc I4.
    apply I7.
Qed.

Lemma Ov l k n r:
  LC (k*2+2) l ->
  RC (n*2+1) r ->
  exists l' r',
  LC (k+1) l' /\
  RC n r' /\
  S0 l 0 r -->+
  S0 l' ((n+1)/2+1) r'.
Proof.
  intros.
  inverts H; try lia.
  replace n0 with k in * by lia.
  inverts H0; try lia.
  replace n1 with n in * by lia.
  apply LInc in H2.
  destruct H2 as [l' [I1 I2]].
  eex; eex.
  - applys_eq I1; lia.
  - apply H3.
  - unfold S0.
    es; er; follow I2; es.
Qed.

Definition S' '(l,r) := S0 l 0 r.

Lemma init:
  exists l r,
  LC 2 l /\
  RC 1 r /\
  c0 -->* S' (l,r).
Proof.
  eex; eex.
  - apply (LC_2 0),LC_0.
  - apply (RC_1 0),RC_0.
  - unfold S',S0; esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  destruct init as [l0 [r0 [I1 [I2 I3]]]].
  eapply multistep_nonhalt.
  1: apply I3.
  eapply progress_nonhalt_cond with (P:=fun '(l,r) => exists i, LC (i*2+2) l /\ RC (i*2+1) r).
  2: exists O; split; assumption.
  clear.
  intros [l r] [i [I1 I2]].
  unfold S'.
  epose proof (Ov _ _ _ _ I1 I2) as [l' [r' [I3 [I4 I5]]]].
  assert (i mod 2 = 0 \/ i mod 2 = 1)%nat as [E|E] by lia.
  - epose proof (Incs1 _ _ _ _ _ I3 I4 E) as [l'0 [r'0 [I6 [I7 I8]]]].
    eexists (_,_); split.
    + follow10 I5.
      apply I8.
    + exists (S i); split.
      * applys_eq I6; lia.
      * applys_eq I7; lia.
  - epose proof (Incs0 _ _ _ _ _ I3 I4 E) as [l'0 [r'0 [I6 [I7 I8]]]].
    eexists (_,_); split.
    + follow10 I5.
      apply I8.
    + exists (S i); split.
      * applys_eq I6; lia.
      * applys_eq I7; lia.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB0LF_0LC1LD_1RC1LD_0LA1RE_0RD0RE_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} r) (at level 30).
Notation "l |> r" := (l {{D}}> r) (at level 30).

Ltac eex := eexists; repeat split.

Notation ld0 := <[1;1;1;0;0].
Notation ld1 := <[1;1;0;0;0].
Notation ld2 := <[1;0;0;1;0].
Notation w' := <[1;0;0].

Inductive LC: nat->side->Prop :=
| LC_0: LC 0 (0inf<*ld0)
| LC_1: LC 1 (0inf<*ld1)
| LC_2: LC 2 (0inf<*ld2)
| LC_3: LC 3 (0inf<*<[1;1;0;0]<*ld0)
| LC_4: LC 4 (0inf<*<[1;1;0;0]<*ld1)
| LC_5: LC 5 (0inf<*<[1;1;0;0]<*ld2)
| LC_6: LC 6 (0inf<*<[1;0;0;0]<*ld0)
| LC_7: LC 7 (0inf<*<[1;0;0;0]<*ld1)
| LC_8: LC 8 (0inf<*<[1;0;0;0]<*ld2)
| LC_9: LC 9 (0inf<*<[1;1;0;0;1;0;1;0]<*ld0)
| LC_10: LC 10 (0inf<*<[1;1;0;0;1;0;1;0]<*ld1)
| LC_11: LC 11 (0inf<*<[1;1;0;0;1;0;1;0]<*ld2)
| LC_12 n l:
  LC n l ->
  LC (n*3+12) (l<*w'<*ld0)
| LC_13 n l:
  LC n l ->
  LC (n*3+13) (l<*w'<*ld1)
| LC_14 n l:
  LC n l ->
  LC (n*3+14) (l<*w'<*ld2)
.

Lemma LInc n l:
  LC n l ->
  exists l',
  LC (S n) l' /\
  (forall r, l <| r -->* l' |> r).
Proof.
  intros HLC.
  induction HLC.
  1-11: eex; [solve[econstructor]|]; es.
  - eex.
    + apply (LC_12 0),LC_0.
    + es.
  - eex.
    + apply LC_13 in HLC.
      applys_eq HLC; lia.
    + es.
  - eex.
    + apply LC_14 in HLC.
      applys_eq HLC; lia.
    + es.
  - destruct IHHLC as [l' [I1 I2]].
    apply (LC_12) in I1.
    eex.
    + applys_eq I1; lia.
    + es; er; follow I2; es.
Qed.

Notation w := [1;1;0].
Notation d0 := [1;1;1;0;1;0;0].
Notation d1 := [1;0;1;0].

Inductive RC: nat->side->Prop :=
| RC_0: RC 0 ([1;0;1;0;1;1]*>0inf)
| RC_1: RC 1 ([1;1;1;0;1;0;0;1;0;1]*>0inf)
| RC_2: RC 2 ([1;0;1;0;1;1;0;1;0;1]*>0inf)
| RC_3: RC 3 (d0*>[1;1;1;0;0;1;1]*>0inf)
| RC_4: RC 4 (d1*>w*>[1;1;1;0;0;1;1]*>0inf)
| RC_5 n r:
  RC n r ->
  RC (n*2+5) (d0*>w^^(n/2+2)*>r)
| RC_6 n r:
  RC n r ->
  RC (n*2+6) (d1*>w^^(n/2+3)*>r).

Lemma RInc n r:
  RC n r ->
  exists r',
  RC (S n) r' /\
  (n mod 2 = 1 -> forall l, l |> r -->* l <| r')%nat /\
  (n mod 2 = 0 -> forall l, l |> w *> r -->* l <| r')%nat.
Proof.
  intros HRC.
  induction HRC.
  - eex.
    + apply RC_1.
    + lia.
    + es.
  - eex.
    + apply RC_2.
    + es.
    + lia.
  - eex.
    + apply RC_3.
    + lia.
    + es.
  - eex.
    + apply RC_4.
    + es.
    + lia.
  - eex.
    + apply (RC_5 0),RC_0.
    + lia.
    + es.
  - eex.
    + apply RC_6 in HRC.
      applys_eq HRC; lia.
    + es.
    + lia.
  - destruct IHHRC as [r' [I1 [I2 I3]]].
    assert (n mod 2 = 1 \/ n mod 2 = 0)%nat as [E|E] by lia.
    + eex.
      * apply RC_5 in I1.
        applys_eq I1; lia.
      * lia.
      * intros.
        replace ((S n)/2) with (n/2+1) by lia.
        es; er; follow I2; es.
    + eex.
      * apply RC_5 in I1.
        applys_eq I1; lia.
      * lia.
      * intros.
        replace (n/2+3) with (n/2+2+1) by lia.
        rewrite lpow_add,Str_app_assoc.
        remember (w^^1*>r) as r0.
        replace ((S n)/2) with (n/2) by lia.
        es; er.
        subst.
        follow I3.
        es.
Qed.

Definition S0 (l:side) m r :=
  l |> w^^m *> r.

Lemma RR l n r:
  l |> w^^n *> r -->*
  l <* w'^^n |> r.
Proof.
  es.
Qed.

Lemma RR' l n r:
  l |> w^^(S n) *> r -->*
  l <* w'^^n |> w *> r.
Proof.
  intros.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  sr.
  finish.
Qed.

Lemma LL l n r:
  l <* w'^^n <| r -->*
  l <| w^^n *> r.
Proof.
  es.
Qed.

Lemma Incs0 l k m n r:
  LC k l ->
  RC n r ->
  n mod 2 = 0%nat ->
  exists l' r',
  LC (k+m*2) l' /\
  RC (n+m*2) r' /\
  S0 l m r -->* S0 l' 0 r'.
Proof.
  gen l k n r.
  induction m; intros.
  - eex; eex.
    + applys_eq H; lia.
    + applys_eq H0; lia.
    + es.
  - apply RInc in H0.
    destruct H0 as [r0 [I1 [_ I2]]].
    apply LInc in H.
    destruct H as [l0 [I3 I4]].
    apply RInc in I1.
    destruct I1 as [l1 [I5 [I6 _]]].
    apply LInc in I3.
    destruct I3 as [r1 [I7 I8]].
    unshelve epose proof (IHm _ _ _ _ I7 I5 _) as [l' [r' [I9 [I10 I11]]]].
    1: lia.
    eex; eex.
    + applys_eq I9; lia.
    + applys_eq I10; lia.
    + unfold S0 in *.
      follow RR'.
      follow I2.
      follow LL.
      follow I4.
      follow RR.
      follow I6.
      1: lia.
      follow LL.
      follow I8.
      apply I11.
Qed.

Lemma Ov l k n r:
  n mod 2 = 1%nat ->
  LC (k*3+13) l ->
  RC (n*2+6) r ->
  exists l' r',
  LC (k+1) l' /\
  RC (n+1) r' /\
  S0 l 0 r -->+
  S0 l' (n/2+7) r'.
Proof.
  intros I0 H H0.
  inverts H; try lia.
  replace n0 with k in * by lia.
  inverts H0; try lia.
  replace n1 with n in * by lia.
  apply RInc in H3.
  destruct H3 as [r' [I1 [I2 _]]].
  apply LInc in H2.
  destruct H2 as [l' [I3 I4]].
  eex; eex.
  - applys_eq I3; lia.
  - applys_eq I1; lia.
  - unfold S0.
    es; er.
    follow I2.
    es; er.
    follow I4.
    es.
Qed.

Definition S' '(l,r) := S0 l 0 r.

Lemma init:
  exists l r,
  LC 16 l /\
  RC 20 r /\
  c0 -->* S' (l,r).
Proof.
  eex; eex.
  - apply (LC_13 1),LC_1.
  - apply (RC_6 7),(RC_5 1),RC_1.
  - unfold S',S0; esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  destruct init as [l0 [r0 [I1 [I2 I3]]]].
  eapply multistep_nonhalt.
  1: apply I3.
  eapply progress_nonhalt_cond with (P:=fun '(l,r) => exists i, LC ((i*2+1)*3+13) l /\ RC ((i*4+7)*2+6) r).
  2: exists O; split; assumption.
  clear.
  intros [l r] [i [I1 I2]].
  unfold S'.
  epose proof (Ov _ _ _ _ _ I1 I2) as [l' [r' [I3 [I4 I5]]]].
  assert (i mod 2 = 1 \/ i mod 2 = 0)%nat as [E|E] by lia.
  - epose proof (Incs0 _ _ _ _ _ I3 I4 _) as [l'0 [r'0 [I6 [I7 I8]]]].
    eexists (_,_); split.
    + follow10 I5.
      apply I8.
    + exists (S i); split.
      * applys_eq I6; try lia.
      * applys_eq I7; lia.
  - epose proof (Incs0 _ _ _ _ _ I3 I4 _) as [l'0 [r'0 [I6 [I7 I8]]]].
    eexists (_,_); split.
    + follow10 I5.
      apply I8.
    + exists (S i); split.
      * applys_eq I6; lia.
      * applys_eq I7; lia.
  Unshelve.
  all: lia.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC1LB_1RD0RC_1LA0RB_1LA1LF_0LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} r) (at level 30).
Notation "l |> r" := (l {{D}}> r) (at level 30).

Definition LC n := BinInc [1] n.

Lemma LInc n r:
  LC n <{{B}} [] *> r -->*
  LC (S n) <* [] {{C}}> r.
Proof.
  apply progress_evstep.
  apply LBinInc_spec.
  es.
Qed.

Definition LC' n := LC n <* <[0;0;1].

Lemma LInc' n r:
  LC' n <| r -->*
  LC' (S n) |> r.
Proof.
  er; follow LInc; er.
Qed.

Notation d0 := [1;0;0].
Notation d1 := [0;1;0].
Notation d2 := [1;1;0].
Notation w := [1;0;1;0].

Inductive RC: nat->side->Prop :=
| RC_0: RC 0 ([1]*>0inf)
| RC_1 n r:
  RC (n*2) r ->
  RC (n*3+1) (d1*>w^^((n+2)/3)*>r)
| RC_2 n r:
  RC (n*2) r ->
  RC (n*3+2) (d2*>w^^((n+2)/3)*>r)
| RC_3 n r:
  RC (n*2+1) r ->
  RC (n*3+3) (d0*>w^^((n+1)/3+1)*>r)
.

Ltac eex := eexists; repeat split.

Lemma RInc n r:
  RC n r ->
  exists r',
  RC (S n) r' /\
  (n mod 3 <> 2 -> forall l, l |> r -->* l <| r')%nat /\
  (n mod 3 = 2 -> forall l, l |> w *> r -->* l <| r')%nat.
Proof.
  intros HRC.
  induction HRC.
  - eex.
    + apply (RC_1 0),RC_0.
    + es.
    + lia.
  - eex.
    + apply RC_2 in HRC.
      applys_eq HRC; lia.
    + es.
    + lia.
  - destruct IHHRC as [r' [I1 [I2 I3]]].
    destruct (Nat.eqb_spec ((n*2) mod 3) 2) as [E|E].
    + eex.
      * replace (S(n*2)) with (n*2+1) in I1 by lia.
        apply RC_3 in I1.
        applys_eq I1; lia.
      * lia.
      * intros.
        replace ((n+2)/3) with ((n+1)/3+1) by lia.
        rewrite lpow_add,Str_app_assoc.
        remember (w^^1*>r) as r0.
        es; er; subst; follow I3; es.
    + eex.
      * replace (S(n*2)) with (n*2+1) in I1 by lia.
        apply RC_3 in I1.
        applys_eq I1; lia.
      * lia.
      * intros.
        replace ((n+2)/3) with ((n+1)/3) by lia.
        es; er; follow I2; es.
  - destruct IHHRC as [r' [I1 [I2 I3]]].
    destruct (Nat.eqb_spec ((n*2+1) mod 3) 2) as [E|E].
    + eex.
      * replace (S(n*2+1)) with ((S n)*2) in I1 by lia.
        apply RC_1 in I1.
        applys_eq I1; lia.
      * intros.
        replace ((S n+2)/3) with ((n+1)/3) by lia.
        rewrite lpow_add,Str_app_assoc.
        remember (w^^1*>r) as r0.
        es; er; subst; follow I3; es.
      * lia.
    + eex.
      * replace (S(n*2+1)) with ((S n)*2) in I1 by lia.
        apply RC_1 in I1.
        applys_eq I1; lia.
      * intros.
        replace ((S n+2)/3) with ((n+1)/3+1) by lia.
        es; er; follow I2; es.
      * lia.
Qed.

Notation w' := <[0;1;0;1].

Lemma RR l n r:
  l |> w^^n *> r -->*
  l <* w'^^n |> r.
Proof.
  es.
Qed.

Lemma RR' l n r:
  l |> w^^(S n) *> r -->*
  l <* w'^^n |> w *> r.
Proof.
  intros.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  sr.
  finish.
Qed.

Lemma LL l n r:
  l <* w'^^n <| r -->*
  l <| w^^n *> r.
Proof.
  es.
Qed.

Definition S0 k m r := LC' k |> w^^m *> r.

Lemma Incs0 k m n r:
  RC n r ->
  n mod 3 = 2%nat ->
  exists r',
  RC (n+m*3) r' /\
  S0 k m r -->* S0 (k+m*3) 0 r'.
Proof.
  gen k n r.
  induction m; intros.
  - eex.
    + applys_eq H; lia.
    + finish.
  - apply RInc in H.
    destruct H as [r0 [I1 [_ I2]]].
    apply RInc in I1.
    destruct I1 as [r1 [I3 [I4 _]]].
    apply RInc in I3.
    destruct I3 as [r2 [I5 [I6 _]]].
    unshelve epose proof (IHm (3+k) _ _ I5 _) as [r' [I7 I8]].
    1: lia.
    eex.
    + applys_eq I7; lia.
    + unfold S0 in *.
      follow RR'.
      follow I2.
      follow LL.
      follow LInc'.
      follow RR.
      follow I4.
      1: lia.
      follow LL.
      follow LInc'.
      follow RR.
      follow I6.
      1: lia.
      follow LL.
      follow LInc'.
      follow I8.
      finish.
Qed.

Lemma Incs1 k m n r:
  RC n r ->
  n mod 3 = 1%nat ->
  exists r',
  RC (n+m*3+1) r' /\
  S0 k m r -->* S0 (k+m*3+1) 0 r'.
Proof.
  intros.
  apply RInc in H.
  destruct H as [r0 [I1 [I2 I3]]].
  unshelve epose proof (Incs0 (S k) m _ _ I1 _) as [r1 [I4 I5]].
  1: lia.
  eex.
  - applys_eq I4; lia.
  - unfold S0 in *.
    follow RR.
    follow I2.
    1: lia.
    follow LL.
    follow LInc'.
    follow I5.
    finish.
Qed.

Lemma Incs2 k m n r:
  RC n r ->
  n mod 3 = 0%nat ->
  exists r',
  RC (n+m*3+2) r' /\
  S0 k m r -->* S0 (k+m*3+2) 0 r'.
Proof.
  intros.
  apply RInc in H.
  destruct H as [r0 [I1 [I2 I3]]].
  unshelve epose proof (Incs1 (S k) m _ _ I1 _) as [r1 [I4 I5]].
  1: lia.
  eex.
  - applys_eq I4; lia.
  - unfold S0 in *.
    follow RR.
    follow I2.
    1: lia.
    follow LL.
    follow LInc'.
    follow I5.
    finish.
Qed.

Lemma Incs k m n r:
  RC n r ->
  exists r',
  RC (n+m*3+(2-n mod 3)) r' /\
  S0 k m r -->* S0 (k+m*3+(2-n mod 3)) 0 r'.
Proof.
  intros.
  destruct (n mod 3) as [|[|[|]]] eqn:E.
  4: lia.
  - apply Incs2; assumption.
  - apply Incs1; assumption.
  - do 2 rewrite Nat.add_0_r.
    apply Incs0; assumption.
Qed.

Lemma LC'_m2a1 n:
  LC' (n*2+1) =
  LC n <* <[1;0;0;1].
Proof.
  unfold LC',LC.
  rw_Bin.
  reflexivity.
Qed.

Lemma Ov k n r:
  RC (n*3+2) r ->
  exists r',
  RC (n*2+1) r' /\
  S0 (k*2+1) 0 r -->+
  S0 (k+1) ((n+1)/3+1) r'.
Proof.
  intros.
  inverts H; try lia.
  replace n0 with n in * by lia.
  apply RInc in H1.
  destruct H1 as [r' [I1 [I2 I3]]].
  eex.
  - applys_eq I1; lia.
  - unfold S0.
    rewrite LC'_m2a1.
    destruct (Nat.eqb_spec (n mod 3) 1) as [E|E].
    + replace ((n+2)/3) with ((n+1)/3+1) by lia.
      rewrite lpow_add,Str_app_assoc.
      remember (w^^1*>r0) as r1.
      es; er.
      subst.
      follow I3.
      1: lia.
      es; er.
      follow LInc.
      toX D.
      finish.
    + replace ((n+2)/3) with ((n+1)/3) by lia.
      es; er.
      follow I2.
      1: lia.
      es; er.
      follow LInc.
      toX D.
      finish.
Qed.


Definition S' '(k,r) := S0 ((k+2)*2+1) 0 r.

Lemma init:
  exists r,
  RC 5 r /\
  c0 -->* S' (1%nat,r).
Proof.
  eex.
  - apply (RC_2 1),(RC_2 0),RC_0.
  - unfold S',S0; esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  destruct init as [r0 [I1 I2]].
  eapply multistep_nonhalt.
  1: apply I2.
  eapply progress_nonhalt_cond with (P:=fun '(k,r) => RC (k*3+2) r).
  2: assumption.
  clear.
  intros [k r] HP.
  unfold S'.
  epose proof (Ov _ _ _ HP) as [r' [I3 I4]].
  eapply Incs in I3.
  destruct I3 as [r'0 [I5 I6]].
  eexists (S k,_); split.
  - follow10 I4.
    follow I6.
    finish.
  - applys_eq I5; lia.
Qed.

End TM3.


Module TM4.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1LC0LD_1LD---_1RE1LA_1RF0RE_1RA1RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} r) (at level 30).
Notation "l |> r" := (l {{E}}> r) (at level 30).

Inductive Tp := t0|t1|t2|t3|t4|t5|t6|t7.

Definition rh x :=
match x with
| t0 => 1>>0>>1>>0inf
| t1 => 0>>0>>0>>0>>1>>0inf
| t2 => 1>>0>>1>>0>>1>>0>>1>>0inf
| t3 => 1>>0>>1>>0>>0>>0>>1>>0>>1>>0inf
| t4 => 0>>0>>0>>0>>1>>1>>0>>1>>0inf
| t5 => 0>>0>>0>>0>>1>>0>>0>>1>>0>>1>>0inf
| t6 => 1>>0>>1>>0>>0>>0>>0>>0>>1>>0inf
| t7 => 0>>0>>0>>0>>1>>0>>0>>1>>0inf
end.

Definition nxt x :=
match x with
| t0 => t1
| t1 => t2
| t2 => t3
| t3 => t4
| t4 => t5
| t5 => t6
| t6 => t7
| t7 => t0
end.

Definition offset x: nat :=
match x with
| t0 => 0
| t1 => 1
| t2 => 0
| t3 => 0
| t4 => 1
| t5 => 1
| t6 => 0
| t7 => 1
end.

Notation d0 := [0;0;1;1;1;1].
Notation d1 := [0;0;0;1;1;1].
Notation d2 := [1;0;1;1;1;1].
Notation w := [0;1;1;1;1].
Notation w' := <[1;1;0;0;0].
Notation "l |2> r" := (l <* w' {{E}}> r) (at level 30).

Inductive RC: nat->Tp->side->Prop :=
| RC_0 t: RC 0 t (d0*>rh t)
| RC_1 t: RC 1 t (d1*>rh t)
| RC_2 t: RC 2 t (d2*>rh t)
| RC_3 n t r:
  RC (n*2+(1-offset t)) (nxt t) r ->
  RC (n*3+3) t (d0*>w^^((n+1+offset t)/3)*>r)
| RC_4 n t r:
  RC (n*2+(1-offset t)) (nxt t) r ->
  RC (n*3+4) t (d1*>w^^((n+1+offset t)/3)*>r)
| RC_5 n t r:
  RC (n*2+(1-offset t)) (nxt t) r ->
  RC (n*3+5) t (d2*>w^^((n+1+offset t)/3)*>r)
.

Ltac eex := eexists; repeat split.

Ltac follow_lia H :=
  es; er;
  (try eapply progress_evstep);
  eapply progress_evstep_trans;
  [ apply H; try lia | ].

Lemma RInc n t r:
  RC n t r ->
  exists r',
  RC (S n) t r' /\
  (n mod 3 <> 2 -> forall l, l |> r -->+ l <| r')%nat /\
  (n mod 3 = 2 -> forall l, l |2> r -->+ l <| r')%nat.
Proof.
  gen t r.
  induction n using lt_wf_ind.
  introv HRC.
  inverts HRC.
  - eex.
    + apply RC_1.
    + es.
    + lia.
  - eex.
    + apply RC_2.
    + es.
    + lia.
  - destruct t;
    (eex; [ apply (RC_3 0); (apply RC_0||apply RC_1) | lia | es ]).
  - eex.
    + apply RC_4 in H0.
      applys_eq H0; lia.
    + es.
    + lia.
  - eex.
    + apply RC_5 in H0.
      applys_eq H0; lia.
    + es.
    + lia.
  - unshelve epose proof (H _ _ _ _ H0) as [r1 [I1 [I2 I3]]].
    1: lia.
    unshelve epose proof (H _ _ _ _ I1) as [r2 [I4 [I5 I6]]].
    1: lia.
    replace (S(S(n0*2+(1-offset t)))) with ((S n0)*2+(1-offset t)) in I4 by lia.
    apply RC_3 in I4.
    eex.
    + applys_eq I4; lia.
    + lia.
    + intros.
      (destruct (offset t) as [|[|]] eqn:E0; [ | | destruct t; cbn in E0; congruence]);
      assert (n0 mod 3 = 0 \/ n0 mod 3 = 1 \/ n0 mod 3 = 2)%nat as [E|[E|E]] by lia;
      intros.
      * replace ((S n0+1+0)/3) with ((n0+1+0)/3) by lia.
        follow_lia I2.
        follow_lia I6.
        es.
      * replace ((S n0+1+0)/3) with ((n0+1+0)/3+1) by lia.
        follow_lia I2.
        follow_lia I5.
        es.
      * replace ((S n0+1+0)/3) with ((n0+1+0)/3) by lia.
        follow_lia I3.
        follow_lia I5.
        es.
      * replace ((S n0+1+1)/3) with ((n0+1+1)/3+1) by lia.
        follow_lia I2.
        follow_lia I5.
        es.
      * replace ((S n0+1+1)/3) with ((n0+1+1)/3) by lia.
        follow_lia I3.
        follow_lia I5.
        es.
      * replace ((S n0+1+1)/3) with ((n0+1+1)/3) by lia.
        follow_lia I2.
        follow_lia I6.
        es.
Qed.

Notation hR := (E,[]).
Notation hL := (A,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma RIncs2 m n t r:
  RC n t r ->
  n mod 3 = 2 ->
  exists r',
  RC (n+m*3) t r' /\
  sideRLs tm (hRL^^(m*3)) (w^^m*>r) r'.
Proof.
  gen n t r.
  induction m; intros.
  - eex.
    + applys_eq H; lia.
    + esx.
  - apply RInc in H.
    destruct H as [r0 [I1 [_ I2]]].
    apply RInc in I1.
    destruct I1 as [r1 [I3 [I4 _]]].
    apply RInc in I3.
    destruct I3 as [r2 [I5 [I6 _]]].
    apply IHm in I5.
    2: lia.
    destruct I5 as [r' [I7 I8]].
    eex.
    + applys_eq I7; lia.
    + replace (S m*3) with (3+m*3) by lia.
      rewrite lpow_add.
      eapply sideRLs_trans.
      2: apply I8.
      eapply sideRLseq_S with (r2:=w^^m*>r0).
      1: unfold sideRL.
      1: follow_lia I2; es.
      eapply sideRLseq_S with (r2:=w^^m*>r1).
      1: unfold sideRL.
      1: follow_lia I4; es.
      eapply sideRLseq_S with (r2:=w^^m*>r2).
      1: unfold sideRL.
      1: follow_lia I6; es.
      esx.
Qed.

Lemma RIncs1 m n t r:
  RC n t r ->
  n mod 3 = 1%nat ->
  exists r',
  RC (n+m*3+1) t r' /\
  sideRLs tm (hRL^^(m*3+1)) (w^^m*>r) r'.
Proof.
  intros.
  apply RInc in H.
  destruct H as [r0 [I1 [I2 _]]].
  apply (RIncs2 m) in I1.
  2: lia.
  destruct I1 as [r1 [I3 I4]].
  eex.
  - applys_eq I3; lia.
  - rewrite Nat.add_comm.
    eapply sideRLseq_S.
    2: apply I4.
    unfold sideRL.
    follow_lia I2; es.
Qed.

Lemma RIncs0 m n t r:
  RC n t r ->
  n mod 3 = 0%nat ->
  exists r',
  RC (n+m*3+2) t r' /\
  sideRLs tm (hRL^^(m*3+2)) (w^^m*>r) r'.
Proof.
  intros.
  apply RInc in H.
  destruct H as [r0 [I1 [I2 _]]].
  apply (RIncs1 m) in I1.
  2: lia.
  destruct I1 as [r1 [I3 I4]].
  eex.
  - applys_eq I3; lia.
  - replace (m*3+2) with (S(m*3+1)) by lia.
    eapply sideRLseq_S.
    2: apply I4.
    unfold sideRL.
    follow_lia I2; es.
Qed.

Lemma RIncs m n t r:
  RC n t r ->
  exists r',
  RC (n+m*3+(2-n mod 3)) t r' /\
  sideRLs tm (hRL^^(m*3+(2-n mod 3))) (w^^m*>r) r'.
Proof.
  intros.
  destruct (n mod 3) as [|[|[|]]] eqn:E.
  4: lia.
  - apply RIncs0; assumption.
  - apply RIncs1; assumption.
  - do 2 rewrite Nat.add_0_r.
    apply RIncs2; assumption.
Qed.

Notation ld0 := <[0;0;0;0].
Notation ld1 := <[1;0;0;0].

Inductive LC: nat->(list nat)->side->Prop :=
| LC_0: LC 0 [] 0inf
| LC_1 n l:
  LC n [] l ->
  LC (n*2+1) [] (l<*ld1)
| LC_2 n l:
  LC (S n) [] l ->
  LC (n*2+2) [] (l<*ld0)
| LC_1' n h t l:
  LC n (h::t) l ->
  LC (n*2+1) (S h::t) (l<*ld1)
| LC_0' n h t l:
  LC n (h::t) l ->
  LC (n*2) (S h::t) (l<*ld0)
| LC_w n ls l:
  LC n ls l ->
  LC n (O::ls) (l<*w')
.

Lemma LInc n ls l:
  LC n ls l ->
  exists l',
  LC (S n) ls l' /\
  (forall r, l <| r -->+ l' |> r).
Proof.
  intros HLC.
  induction HLC.
  - eex.
    + apply (LC_1 0),LC_0.
    + es.
  - destruct IHHLC as [l' [I1 I2]].
    apply LC_2 in I1.
    eex.
    + applys_eq I1; lia.
    + follow_lia I2; es.
  - apply LC_1 in HLC.
    eex.
    + applys_eq HLC; lia.
    + es.
  - destruct IHHLC as [l' [I1 I2]].
    apply LC_0' in I1.
    eex.
    + applys_eq I1; lia.
    + follow_lia I2; es.
  - apply LC_1' in HLC.
    eex.
    + applys_eq HLC; lia.
    + es.
  - destruct IHHLC as [l' [I1 I2]].
    apply LC_w in I1.
    eex.
    + applys_eq I1; lia.
    + follow_lia I2; es.
Qed.

Definition tm' := flip tm.

Lemma LIncs m n ls l:
  LC n ls l ->
  exists l',
  LC (n+m) ls l' /\
  sideRLs tm' (hLR^^m) l l'.
Proof.
  gen n ls l.
  induction m; intros.
  - eex.
    + applys_eq H; lia.
    + esx.
  - apply LInc in H.
    destruct H as [l' [I1 I2]].
    apply IHm in I1.
    destruct I1 as [l'0 [I3 I4]].
    eex.
    + applys_eq I3; lia.
    + eapply sideRLseq_S.
      2: apply I4.
      unfold sideRL.
      intros.
      specialize (I2 l0).
      apply flip_progress in I2.
      apply I2.
Qed.

Lemma LRst n i l:
  LC ((n*2+1)*2^i) [] l ->
  exists l',
  LC ((n)*2^i) [i] l' /\
  sideRLs tm' (hLR^^(2^i)) (l<<0) l'.
Proof.
  gen n l.
  induction i; intros.
  - inverts H; try lia.
    replace n0 with n in * by lia.
    apply LC_w in H1.
    eex.
    + applys_eq H1; lia.
    + esx.
  - cbn[Nat.pow] in *.
    inverts H; try lia.
    replace (S n0) with ((n*2+1)*2^i) in * by lia.
    apply IHi in H1.
    destruct H1 as [l' [I1 I2]].
    apply LC_0' in I1.
    eex.
    + applys_eq I1; lia.
    + change (0>>ld0*>l1) with (ld0*>0>>l1).
      replace (2*2^i) with (2^i*2+0) by lia.
      eapply segRLs_sideRLs_concat.
      2: apply I2.
      eapply segRLs_addmul''; esx.
Qed.

Lemma LRst' n i h t l:
  LC ((n*2+1)*2^i) (i+S h::t) l ->
  exists l',
  LC ((n)*2^i) (i::h::t) l' /\
  sideRLs tm' (hLR^^(2^i)) (l<<0) l'.
Proof.
  gen n l.
  induction i; intros.
  - inverts H; try lia.
    replace n0 with n in * by lia.
    apply LC_w in H4.
    eex.
    + applys_eq H4; lia.
    + esx.
  - cbn[Nat.pow] in *.
    inverts H; try lia.
    replace (n0) with ((n*2+1)*2^i) in * by lia.
    apply IHi in H4.
    destruct H4 as [l' [I1 I2]].
    apply LC_0' in I1.
    eex.
    + applys_eq I1; lia.
    + change (0>>ld0*>l1) with (ld0*>0>>l1).
      replace (2*2^i) with (2^i*2+0) by lia.
      eapply segRLs_sideRLs_concat.
      2: apply I2.
      eapply segRLs_addmul''; esx.
Qed.

Lemma ROv01 n t r:
  RC (n*3+5) t r ->
  (n*2+(1-offset t)) mod 3 <> 2 ->
  exists r',
  RC (S(n*2+(1-offset t))) (nxt t) r' /\
  (forall l, l |> r -->* l<<0 <| w^^((n+1+offset t)/3+1) *> r').
Proof.
  intros.
  inverts H; try lia.
  replace n0 with n in * by lia.
  apply RInc in H2.
  destruct H2 as [r' [I1 [I2 _]]].
  eex.
  - apply I1.
  - follow_lia I2.
    es_v2.
Qed.

Lemma ROv2 n t r:
  RC (n*3+5) t r ->
  (n*2+(1-offset t)) mod 3 = 2 ->
  exists r',
  RC (S(n*2+(1-offset t))) (nxt t) r' /\
  (forall l, l |> r -->* l<<0 <| w^^((n+1+offset t)/3) *> r').
Proof.
  intros.
  inverts H; try lia.
  replace n0 with n in * by lia.
  apply RInc in H2.
  destruct H2 as [r' [I1 [_ I2]]].
  eex.
  - apply I1.
  - follow_lia I2.
    es_v2.
Qed.

Lemma ROv n t r:
  RC (n*3+5) t r ->
  exists r',
  RC (S(n*2+(1-offset t))) (nxt t) r' /\
  (forall l, l |> r -->* l<<0 <| w^^((n+1+offset t)/3+(1-((n*2+(1-offset t)) mod 3)/2)) *> r').
Proof.
  intros H.
  destruct ((n*2+(1-offset t)) mod 3) as [|[|[|]]] eqn:E.
  4: lia.
  1,2: apply ROv01; [assumption|lia].
  rewrite Nat.add_0_r.
  apply ROv2; assumption.
Qed.

Definition S0 (l:side) m r := l |> w^^m *> r.

Definition S' '(l,r) := S0 l 0 r.

Lemma lrcons_hL_hRL_hR n:
  lrcons hL (hRL^^n) hR = (hLR^^(1+n)).
Proof.
  induction n; cbn in *; trivial.
  rewrite IHn; trivial.
Qed.

Lemma BigStep0 [k ls l n t r]:
  LC k (O::ls) l ->
  RC (n*3+5) t r ->
  exists l' r',
  LC (3+k) ls l' /\
  RC ((S n)*3+5) t r' /\
  S' (l,r) -->+
  S' (l',r').
Proof.
  intros HLC HRC.
  unfold S',S0.
  inverts HLC.
  rename H1 into HLC.
  apply RInc in HRC.
  destruct HRC as [r0 [HRC [_ I1]]].
  apply LInc in HLC.
  destruct HLC as [l0 [HLC I2]].
  apply RInc in HRC.
  destruct HRC as [r1 [HRC [I3 _]]].
  apply LInc in HLC.
  destruct HLC as [l1' [HLC I4]].
  apply RInc in HRC.
  destruct HRC as [r2 [HRC [I5 _]]].
  apply LInc in HLC.
  destruct HLC as [l2 [HLC I6]].
  eex; eex.
  - apply HLC.
  - apply HRC.
  - follow_lia I1.
    follow_lia I2.
    follow_lia I3.
    follow_lia I4.
    follow_lia I5.
    follow_lia I6.
    finish.
Qed.

Lemma BigStep [k i l n t r]:
  LC ((k*2+1)*2^i) [] l ->
  RC (n*3+5) t r ->
  2^i-1 <= n ->
  exists l' r',
  let v1:=((n+1+offset t)/3+(1-((n*2+(1-offset t)) mod 3)/2)) in
  let v3:=(2-((S(n*2+(1-offset t))) mod 3)) in
  let v2:=(v1*3+v3) in
  LC (k*2^i+(v2-(2^i-1))) [i] l' /\
  RC ((n*2+1+(1-offset t))+v2) (nxt t) r' /\
  S' (l,r) -->+
  S' (l',r').
Proof.
  intros HLC HRC Hv1.
  unfold S',S0.
  apply ROv in HRC.
  destruct HRC as [r0 [HRC I1]].
  remember ((n+1+offset t)/3+(1-((n*2+(1-offset t)) mod 3)/2)) as v1.
  apply (RIncs v1) in HRC.
  destruct HRC as [r' [HRC I2]].
  rewrite <-Nat.add_assoc in HRC.
  apply LRst in HLC.
  destruct HLC as [l' [HLC I3]].
  remember (v1*3+(2-((S(n*2+(1-offset t))) mod 3))) as v2.
  eapply (LIncs (v2-(2^i-1))) in HLC.
  destruct HLC as [l'0 [HLC I4]].
  eassert _ as I5. {
    eapply sideRLs_trans.
    - apply I3.
    - apply I4.
  }
  rewrite <-lpow_add in I5.
  replace (2^i+(v2-(2^i-1))) with (1+v2) in I5 by lia.
  rewrite <-lrcons_hL_hRL_hR in I5.
  epose proof (sideRLs_concat_L I5 I2) as I.
  eex; eex.
  - apply HLC.
  - applys_eq HRC; lia.
  - follow I1.
    follow10 I.
    finish.
Qed.

Lemma BigStep' [k i h ls l n t r]:
  LC ((k*2+1)*2^i) (i+S h::ls) l ->
  RC (n*3+5) t r ->
  2^i-1 <= n ->
  exists l' r',
  let v1:=((n+1+offset t)/3+(1-((n*2+(1-offset t)) mod 3)/2)) in
  let v3:=(2-((S(n*2+(1-offset t))) mod 3)) in
  let v2:=(v1*3+v3) in
  LC (k*2^i+(v2-(2^i-1))) (i::h::ls) l' /\
  RC ((n*2+1+(1-offset t))+v2) (nxt t) r' /\
  S' (l,r) -->+
  S' (l',r').
Proof.
  intros HLC HRC Hv1.
  unfold S',S0.
  apply ROv in HRC.
  destruct HRC as [r0 [HRC I1]].
  remember ((n+1+offset t)/3+(1-((n*2+(1-offset t)) mod 3)/2)) as v1.
  apply (RIncs v1) in HRC.
  destruct HRC as [r' [HRC I2]].
  rewrite <-Nat.add_assoc in HRC.
  apply LRst' in HLC.
  destruct HLC as [l' [HLC I3]].
  remember (v1*3+(2-((S(n*2+(1-offset t))) mod 3))) as v2.
  eapply (LIncs (v2-(2^i-1))) in HLC.
  destruct HLC as [l'0 [HLC I4]].
  eassert _ as I5. {
    eapply sideRLs_trans.
    - apply I3.
    - apply I4.
  }
  rewrite <-lpow_add in I5.
  replace (2^i+(v2-(2^i-1))) with (1+v2) in I5 by lia.
  rewrite <-lrcons_hL_hRL_hR in I5.
  epose proof (sideRLs_concat_L I5 I2) as I.
  eex; eex.
  - apply HLC.
  - applys_eq HRC; lia.
  - follow I1.
    follow10 I.
    finish.
Qed.

Lemma init:
  exists l r,
  LC 18 [] l /\
  RC 20 t0 r /\
  c0 -->*
  S' (l,r).
Proof.
  eex; eex.
  - apply (LC_2 8),(LC_1 4),(LC_2 1),(LC_2 0),(LC_1 0),LC_0.
  - apply (RC_5 5),(RC_5 2),(RC_4 0),RC_1.
  - unfold S',S0; esx.
Qed.

Ltac rp1 x i :=
  match goal with
  | [ H: LC ?a _ _ |- _] =>
    replace a with x in H by 
    (destruct (i mod 3) as [|[|[|]]] eqn:E; lia)
  end.

Ltac rp2 x i :=
  match goal with
  | [ H: RC ?a _ _ |- _] =>
    replace a with (x*3+5) in H by 
    (destruct (i mod 3) as [|[|[|]]] eqn:E; lia)
  end.

Ltac BS :=
  match goal with
  | [ I1: LC _ ?ls _ ,
      I2: RC _ _ _
    |- _ ] =>
    let l0:=fresh "l" in
    let r0:=fresh "r" in
    let I1a:=fresh "I" in
    let I2a:=fresh "I" in
    let I3a:=fresh "I" in
    match ls with
    | [] =>
      unshelve epose proof (BigStep I1 I2 _) as [l0 [r0 [I1a [I2a I3a]]]]; [lia|]
    | O::_ =>
      epose proof (BigStep0 I1 I2) as [l0 [r0 [I1a [I2a I3a]]]]
    | _ =>
      unshelve epose proof (BigStep' I1 I2 _) as [l0 [r0 [I1a [I2a I3a]]]]; [lia|]
    end;
    clear I1 I2;
    unfold nxt,offset in *
  end.
Lemma nonhalt: ~halts tm c0.
Proof.
  destruct init as [l0 [r0 [I1 [I2 I3]]]].
  eapply multistep_nonhalt.
  1: apply I3.
  eapply progress_nonhalt_cond with (P:=fun '(l,r) => exists i, LC (i*16+18) [] l /\ RC (i*24+20) t0 r).
  2: exists O; split; assumption.
  clear.
  intros [l r] [i [I1 I2]].
  rp1 (((i*4+4)*2+1)*2^1) i.
  rp2 (i*8+5) i.
  BS.
  rp1 (((i*8+7)*2+1)*2^0) i.
  rp2 (i*8+5) i.
  BS.
  rp2 (i*8+5) i.
  BS.
  BS.
  rp1 (((i*4+5)*2+1)*2^1) i.
  rp2 (i*8+7) i.
  BS.
  rp1 (((i*8+9)*2+1)*2^0) i.
  rp2 (i*8+7) i.
  BS.
  rp2 (i*8+7) i.
  BS.
  BS.
  rp1 (((i*8+12)*2+1)*2^0) i.
  rp2 (i*8+9) i.
  BS.
  rp2 (i*8+9) i.
  BS.
  rp1 (((i*2+3)*2+1)*2^2) i.
  rp2 (i*8+10) i.
  BS.
  rp1 (((i*8+11)*2+1)*2^0) i.
  rp2 (i*8+10) i.
  BS.
  rp2 (i*8+10) i.
  BS.
  rp1 (((i*8+13)*2+1)*2^0) i.
  rp2 (i*8+11) i.
  BS.
  rp2 (i*8+11) i.
  BS.
  BS.
  rp1 ((S i)*16+18) i.
  rp2 ((S i)*8+5) i.
  eexists; split.
  - follow10 I3.
    repeat
    match goal with
    | [H: _ |- _] =>
      follow100 H
    end.
    finish.
  - exists (S i); split.
    + applys_eq I1; lia.
    + applys_eq I2; lia.
Qed.

End TM4.


Module TM5.
Definition tm := Eval compute in (TM_from_str "1RB1LD_1RC0RB_1RD1RB_1LE0LD_1LF0LA_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} r) (at level 30).
Notation "l |> r" := (l {{B}}> r) (at level 30).

Inductive Tp := t0|t1|t2|t3|t4|t5|t6|t7.

Definition rh x :=
match x with
| t0 => 1>>0>>1>>0inf
| t1 => 0>>0>>0>>0>>1>>0inf
| t2 => 1>>0>>1>>0>>1>>0>>1>>0inf
| t3 => 1>>0>>1>>0>>0>>0>>1>>0>>1>>0inf
| t4 => 0>>0>>0>>0>>1>>1>>0>>1>>0inf
| t5 => 0>>0>>0>>0>>1>>0>>0>>1>>0>>1>>0inf
| t6 => 1>>0>>1>>0>>0>>0>>0>>0>>1>>0inf
| t7 => 0>>0>>0>>0>>1>>0>>0>>1>>0inf
end.

Definition nxt x :=
match x with
| t0 => t1
| t1 => t2
| t2 => t3
| t3 => t4
| t4 => t5
| t5 => t6
| t6 => t7
| t7 => t0
end.

Definition offset x: nat :=
match x with
| t0 => 0
| t1 => 1
| t2 => 0
| t3 => 0
| t4 => 1
| t5 => 1
| t6 => 0
| t7 => 1
end.

Notation d0 := [0;0;1;1;1;1].
Notation d1 := [0;0;0;1;1;1].
Notation d2 := [1;0;1;1;1;1].
Notation w := [0;1;1;1;1].
Notation w' := <[1;1;0;0;0].
Notation "l |2> r" := (l <* w' |> r) (at level 30).

Inductive RC: nat->Tp->side->Prop :=
| RC_0 t: RC 0 t (d0*>rh t)
| RC_1 t: RC 1 t (d1*>rh t)
| RC_2 t: RC 2 t (d2*>rh t)
| RC_3 n t r:
  RC (n*2+(1-offset t)) (nxt t) r ->
  RC (n*3+3) t (d0*>w^^((n+1+offset t)/3)*>r)
| RC_4 n t r:
  RC (n*2+(1-offset t)) (nxt t) r ->
  RC (n*3+4) t (d1*>w^^((n+1+offset t)/3)*>r)
| RC_5 n t r:
  RC (n*2+(1-offset t)) (nxt t) r ->
  RC (n*3+5) t (d2*>w^^((n+1+offset t)/3)*>r)
.

Ltac eex := eexists; repeat split.

Ltac follow_lia H :=
  es; er;
  (try eapply progress_evstep);
  eapply progress_evstep_trans;
  [ apply H; try lia | ].

Lemma RInc n t r:
  RC n t r ->
  exists r',
  RC (S n) t r' /\
  (n mod 3 <> 2 -> forall l, l |> r -->+ l <| r')%nat /\
  (n mod 3 = 2 -> forall l, l |2> r -->+ l <| r')%nat.
Proof.
  gen t r.
  induction n using lt_wf_ind.
  introv HRC.
  inverts HRC.
  - eex.
    + apply RC_1.
    + es.
    + lia.
  - eex.
    + apply RC_2.
    + es.
    + lia.
  - destruct t;
    (eex; [ apply (RC_3 0); (apply RC_0||apply RC_1) | lia | es ]).
  - eex.
    + apply RC_4 in H0.
      applys_eq H0; lia.
    + es.
    + lia.
  - eex.
    + apply RC_5 in H0.
      applys_eq H0; lia.
    + es.
    + lia.
  - unshelve epose proof (H _ _ _ _ H0) as [r1 [I1 [I2 I3]]].
    1: lia.
    unshelve epose proof (H _ _ _ _ I1) as [r2 [I4 [I5 I6]]].
    1: lia.
    replace (S(S(n0*2+(1-offset t)))) with ((S n0)*2+(1-offset t)) in I4 by lia.
    apply RC_3 in I4.
    eex.
    + applys_eq I4; lia.
    + lia.
    + intros.
      (destruct (offset t) as [|[|]] eqn:E0; [ | | destruct t; cbn in E0; congruence]);
      assert (n0 mod 3 = 0 \/ n0 mod 3 = 1 \/ n0 mod 3 = 2)%nat as [E|[E|E]] by lia;
      intros.
      * replace ((S n0+1+0)/3) with ((n0+1+0)/3) by lia.
        follow_lia I2.
        follow_lia I6.
        es.
      * replace ((S n0+1+0)/3) with ((n0+1+0)/3+1) by lia.
        follow_lia I2.
        follow_lia I5.
        es.
      * replace ((S n0+1+0)/3) with ((n0+1+0)/3) by lia.
        follow_lia I3.
        follow_lia I5.
        es.
      * replace ((S n0+1+1)/3) with ((n0+1+1)/3+1) by lia.
        follow_lia I2.
        follow_lia I5.
        es.
      * replace ((S n0+1+1)/3) with ((n0+1+1)/3) by lia.
        follow_lia I3.
        follow_lia I5.
        es.
      * replace ((S n0+1+1)/3) with ((n0+1+1)/3) by lia.
        follow_lia I2.
        follow_lia I6.
        es.
Qed.

Notation hR := (B,[]).
Notation hL := (D,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma RIncs2 m n t r:
  RC n t r ->
  n mod 3 = 2 ->
  exists r',
  RC (n+m*3) t r' /\
  sideRLs tm (hRL^^(m*3)) (w^^m*>r) r'.
Proof.
  gen n t r.
  induction m; intros.
  - eex.
    + applys_eq H; lia.
    + esx.
  - apply RInc in H.
    destruct H as [r0 [I1 [_ I2]]].
    apply RInc in I1.
    destruct I1 as [r1 [I3 [I4 _]]].
    apply RInc in I3.
    destruct I3 as [r2 [I5 [I6 _]]].
    apply IHm in I5.
    2: lia.
    destruct I5 as [r' [I7 I8]].
    eex.
    + applys_eq I7; lia.
    + replace (S m*3) with (3+m*3) by lia.
      rewrite lpow_add.
      eapply sideRLs_trans.
      2: apply I8.
      eapply sideRLseq_S with (r2:=w^^m*>r0).
      1: unfold sideRL.
      1: follow_lia I2; es.
      eapply sideRLseq_S with (r2:=w^^m*>r1).
      1: unfold sideRL.
      1: follow_lia I4; es.
      eapply sideRLseq_S with (r2:=w^^m*>r2).
      1: unfold sideRL.
      1: follow_lia I6; es.
      esx.
Qed.

Lemma RIncs1 m n t r:
  RC n t r ->
  n mod 3 = 1%nat ->
  exists r',
  RC (n+m*3+1) t r' /\
  sideRLs tm (hRL^^(m*3+1)) (w^^m*>r) r'.
Proof.
  intros.
  apply RInc in H.
  destruct H as [r0 [I1 [I2 _]]].
  apply (RIncs2 m) in I1.
  2: lia.
  destruct I1 as [r1 [I3 I4]].
  eex.
  - applys_eq I3; lia.
  - rewrite Nat.add_comm.
    eapply sideRLseq_S.
    2: apply I4.
    unfold sideRL.
    follow_lia I2; es.
Qed.

Lemma RIncs0 m n t r:
  RC n t r ->
  n mod 3 = 0%nat ->
  exists r',
  RC (n+m*3+2) t r' /\
  sideRLs tm (hRL^^(m*3+2)) (w^^m*>r) r'.
Proof.
  intros.
  apply RInc in H.
  destruct H as [r0 [I1 [I2 _]]].
  apply (RIncs1 m) in I1.
  2: lia.
  destruct I1 as [r1 [I3 I4]].
  eex.
  - applys_eq I3; lia.
  - replace (m*3+2) with (S(m*3+1)) by lia.
    eapply sideRLseq_S.
    2: apply I4.
    unfold sideRL.
    follow_lia I2; es.
Qed.

Lemma RIncs m n t r:
  RC n t r ->
  exists r',
  RC (n+m*3+(2-n mod 3)) t r' /\
  sideRLs tm (hRL^^(m*3+(2-n mod 3))) (w^^m*>r) r'.
Proof.
  intros.
  destruct (n mod 3) as [|[|[|]]] eqn:E.
  4: lia.
  - apply RIncs0; assumption.
  - apply RIncs1; assumption.
  - do 2 rewrite Nat.add_0_r.
    apply RIncs2; assumption.
Qed.

Notation ld0 := <[0;0;0;0].
Notation ld1 := <[1;0;0;0].

Inductive LC: nat->(list nat)->side->Prop :=
| LC_0: LC 0 [] 0inf
| LC_1 n l:
  LC n [] l ->
  LC (n*2+1) [] (l<*ld1)
| LC_2 n l:
  LC (S n) [] l ->
  LC (n*2+2) [] (l<*ld0)
| LC_1' n h t l:
  LC n (h::t) l ->
  LC (n*2+1) (S h::t) (l<*ld1)
| LC_0' n h t l:
  LC n (h::t) l ->
  LC (n*2) (S h::t) (l<*ld0)
| LC_w n ls l:
  LC n ls l ->
  LC n (O::ls) (l<*w')
.

Lemma LInc n ls l:
  LC n ls l ->
  exists l',
  LC (S n) ls l' /\
  (forall r, l <| r -->+ l' |> r).
Proof.
  intros HLC.
  induction HLC.
  - eex.
    + apply (LC_1 0),LC_0.
    + es.
  - destruct IHHLC as [l' [I1 I2]].
    apply LC_2 in I1.
    eex.
    + applys_eq I1; lia.
    + follow_lia I2; es.
  - apply LC_1 in HLC.
    eex.
    + applys_eq HLC; lia.
    + es.
  - destruct IHHLC as [l' [I1 I2]].
    apply LC_0' in I1.
    eex.
    + applys_eq I1; lia.
    + follow_lia I2; es.
  - apply LC_1' in HLC.
    eex.
    + applys_eq HLC; lia.
    + es.
  - destruct IHHLC as [l' [I1 I2]].
    apply LC_w in I1.
    eex.
    + applys_eq I1; lia.
    + follow_lia I2; es.
Qed.

Definition tm' := flip tm.

Lemma LIncs m n ls l:
  LC n ls l ->
  exists l',
  LC (n+m) ls l' /\
  sideRLs tm' (hLR^^m) l l'.
Proof.
  gen n ls l.
  induction m; intros.
  - eex.
    + applys_eq H; lia.
    + esx.
  - apply LInc in H.
    destruct H as [l' [I1 I2]].
    apply IHm in I1.
    destruct I1 as [l'0 [I3 I4]].
    eex.
    + applys_eq I3; lia.
    + eapply sideRLseq_S.
      2: apply I4.
      unfold sideRL.
      intros.
      specialize (I2 l0).
      apply flip_progress in I2.
      apply I2.
Qed.

Lemma LRst n i l:
  LC ((n*2+1)*2^i) [] l ->
  exists l',
  LC ((n)*2^i) [i] l' /\
  sideRLs tm' (hLR^^(2^i)) (l<<0) l'.
Proof.
  gen n l.
  induction i; intros.
  - inverts H; try lia.
    replace n0 with n in * by lia.
    apply LC_w in H1.
    eex.
    + applys_eq H1; lia.
    + esx.
  - cbn[Nat.pow] in *.
    inverts H; try lia.
    replace (S n0) with ((n*2+1)*2^i) in * by lia.
    apply IHi in H1.
    destruct H1 as [l' [I1 I2]].
    apply LC_0' in I1.
    eex.
    + applys_eq I1; lia.
    + change (0>>ld0*>l1) with (ld0*>0>>l1).
      replace (2*2^i) with (2^i*2+0) by lia.
      eapply segRLs_sideRLs_concat.
      2: apply I2.
      eapply segRLs_addmul''; esx.
Qed.

Lemma LRst' n i h t l:
  LC ((n*2+1)*2^i) (i+S h::t) l ->
  exists l',
  LC ((n)*2^i) (i::h::t) l' /\
  sideRLs tm' (hLR^^(2^i)) (l<<0) l'.
Proof.
  gen n l.
  induction i; intros.
  - inverts H; try lia.
    replace n0 with n in * by lia.
    apply LC_w in H4.
    eex.
    + applys_eq H4; lia.
    + esx.
  - cbn[Nat.pow] in *.
    inverts H; try lia.
    replace (n0) with ((n*2+1)*2^i) in * by lia.
    apply IHi in H4.
    destruct H4 as [l' [I1 I2]].
    apply LC_0' in I1.
    eex.
    + applys_eq I1; lia.
    + change (0>>ld0*>l1) with (ld0*>0>>l1).
      replace (2*2^i) with (2^i*2+0) by lia.
      eapply segRLs_sideRLs_concat.
      2: apply I2.
      eapply segRLs_addmul''; esx.
Qed.

Ltac LC_inv :=
match goal with
| [H:LC _ _ _ |- _] =>
  inverts H; try lia
end.

Lemma ROv01 n t r:
  RC (n*3+5) t r ->
  (n*2+(1-offset t)) mod 3 <> 2 ->
  exists r',
  RC (S(n*2+(1-offset t))) (nxt t) r' /\
  (forall l, l |> r -->* l<<0 <| w^^((n+1+offset t)/3+1) *> r').
Proof.
  intros.
  inverts H; try lia.
  replace n0 with n in * by lia.
  apply RInc in H2.
  destruct H2 as [r' [I1 [I2 _]]].
  eex.
  - apply I1.
  - follow_lia I2.
    es_v2.
Qed.

Lemma ROv2 n t r:
  RC (n*3+5) t r ->
  (n*2+(1-offset t)) mod 3 = 2 ->
  exists r',
  RC (S(n*2+(1-offset t))) (nxt t) r' /\
  (forall l, l |> r -->* l<<0 <| w^^((n+1+offset t)/3) *> r').
Proof.
  intros.
  inverts H; try lia.
  replace n0 with n in * by lia.
  apply RInc in H2.
  destruct H2 as [r' [I1 [_ I2]]].
  eex.
  - apply I1.
  - follow_lia I2.
    es_v2.
Qed.

Lemma ROv n t r:
  RC (n*3+5) t r ->
  exists r',
  RC (S(n*2+(1-offset t))) (nxt t) r' /\
  (forall l, l |> r -->* l<<0 <| w^^((n+1+offset t)/3+(1-((n*2+(1-offset t)) mod 3)/2)) *> r').
Proof.
  intros H.
  destruct ((n*2+(1-offset t)) mod 3) as [|[|[|]]] eqn:E.
  4: lia.
  1,2: apply ROv01; [assumption|lia].
  rewrite Nat.add_0_r.
  apply ROv2; assumption.
Qed.

Definition S0 (l:side) m r := l |> w^^m *> r.

Definition S' '(l,r) := S0 l 0 r.

Lemma lrcons_hL_hRL_hR n:
  lrcons hL (hRL^^n) hR = (hLR^^(1+n)).
Proof.
  induction n; cbn in *; trivial.
  rewrite IHn; trivial.
Qed.

Lemma BigStep0 [k ls l n t r]:
  LC k (O::ls) l ->
  RC (n*3+5) t r ->
  exists l' r',
  LC (3+k) ls l' /\
  RC ((S n)*3+5) t r' /\
  S' (l,r) -->+
  S' (l',r').
Proof.
  intros HLC HRC.
  unfold S',S0.
  inverts HLC.
  rename H1 into HLC.
  apply RInc in HRC.
  destruct HRC as [r0 [HRC [_ I1]]].
  apply LInc in HLC.
  destruct HLC as [l0 [HLC I2]].
  apply RInc in HRC.
  destruct HRC as [r1 [HRC [I3 _]]].
  apply LInc in HLC.
  destruct HLC as [l1' [HLC I4]].
  apply RInc in HRC.
  destruct HRC as [r2 [HRC [I5 _]]].
  apply LInc in HLC.
  destruct HLC as [l2 [HLC I6]].
  eex; eex.
  - apply HLC.
  - apply HRC.
  - follow_lia I1.
    follow_lia I2.
    follow_lia I3.
    follow_lia I4.
    follow_lia I5.
    follow_lia I6.
    finish.
Qed.

Lemma BigStep [k i l n t r]:
  LC ((k*2+1)*2^i) [] l ->
  RC (n*3+5) t r ->
  2^i-1 <= n ->
  exists l' r',
  let v1:=((n+1+offset t)/3+(1-((n*2+(1-offset t)) mod 3)/2)) in
  let v3:=(2-((S(n*2+(1-offset t))) mod 3)) in
  let v2:=(v1*3+v3) in
  LC (k*2^i+(v2-(2^i-1))) [i] l' /\
  RC ((n*2+1+(1-offset t))+v2) (nxt t) r' /\
  S' (l,r) -->+
  S' (l',r').
Proof.
  intros HLC HRC Hv1.
  unfold S',S0.
  apply ROv in HRC.
  destruct HRC as [r0 [HRC I1]].
  remember ((n+1+offset t)/3+(1-((n*2+(1-offset t)) mod 3)/2)) as v1.
  apply (RIncs v1) in HRC.
  destruct HRC as [r' [HRC I2]].
  rewrite <-Nat.add_assoc in HRC.
  apply LRst in HLC.
  destruct HLC as [l' [HLC I3]].
  remember (v1*3+(2-((S(n*2+(1-offset t))) mod 3))) as v2.
  eapply (LIncs (v2-(2^i-1))) in HLC.
  destruct HLC as [l'0 [HLC I4]].
  eassert _ as I5. {
    eapply sideRLs_trans.
    - apply I3.
    - apply I4.
  }
  rewrite <-lpow_add in I5.
  replace (2^i+(v2-(2^i-1))) with (1+v2) in I5 by lia.
  rewrite <-lrcons_hL_hRL_hR in I5.
  epose proof (sideRLs_concat_L I5 I2) as I.
  eex; eex.
  - apply HLC.
  - applys_eq HRC; lia.
  - follow I1.
    follow10 I.
    finish.
Qed.

Lemma BigStep' [k i h ls l n t r]:
  LC ((k*2+1)*2^i) (i+S h::ls) l ->
  RC (n*3+5) t r ->
  2^i-1 <= n ->
  exists l' r',
  let v1:=((n+1+offset t)/3+(1-((n*2+(1-offset t)) mod 3)/2)) in
  let v3:=(2-((S(n*2+(1-offset t))) mod 3)) in
  let v2:=(v1*3+v3) in
  LC (k*2^i+(v2-(2^i-1))) (i::h::ls) l' /\
  RC ((n*2+1+(1-offset t))+v2) (nxt t) r' /\
  S' (l,r) -->+
  S' (l',r').
Proof.
  intros HLC HRC Hv1.
  unfold S',S0.
  apply ROv in HRC.
  destruct HRC as [r0 [HRC I1]].
  remember ((n+1+offset t)/3+(1-((n*2+(1-offset t)) mod 3)/2)) as v1.
  apply (RIncs v1) in HRC.
  destruct HRC as [r' [HRC I2]].
  rewrite <-Nat.add_assoc in HRC.
  apply LRst' in HLC.
  destruct HLC as [l' [HLC I3]].
  remember (v1*3+(2-((S(n*2+(1-offset t))) mod 3))) as v2.
  eapply (LIncs (v2-(2^i-1))) in HLC.
  destruct HLC as [l'0 [HLC I4]].
  eassert _ as I5. {
    eapply sideRLs_trans.
    - apply I3.
    - apply I4.
  }
  rewrite <-lpow_add in I5.
  replace (2^i+(v2-(2^i-1))) with (1+v2) in I5 by lia.
  rewrite <-lrcons_hL_hRL_hR in I5.
  epose proof (sideRLs_concat_L I5 I2) as I.
  eex; eex.
  - apply HLC.
  - applys_eq HRC; lia.
  - follow I1.
    follow10 I.
    finish.
Qed.

Lemma BigStep'' [k k' k'' ls ls' l n t r]:
  LC k ls l ->
  RC (n*3+5) t r ->
  (LC k ls l ->
  exists l',
  LC k' ls' l' /\
  sideRLs tm' (hLR^^k'') (l<<0) l') ->
  1 <= k'' <= n ->
  exists l' r',
  let v1:=((n+1+offset t)/3+(1-((n*2+(1-offset t)) mod 3)/2)) in
  let v3:=(2-((S(n*2+(1-offset t))) mod 3)) in
  let v2:=(v1*3+v3) in
  LC (k'+(v2-(k''-1))) ls' l' /\
  RC ((n*2+1+(1-offset t))+v2) (nxt t) r' /\
  S' (l,r) -->+
  S' (l',r').
Proof.
  intros HLC HRC HLRst Hv1.
  unfold S',S0.
  apply ROv in HRC.
  destruct HRC as [r0 [HRC I1]].
  remember ((n+1+offset t)/3+(1-((n*2+(1-offset t)) mod 3)/2)) as v1.
  apply (RIncs v1) in HRC.
  destruct HRC as [r' [HRC I2]].
  rewrite <-Nat.add_assoc in HRC.
  apply HLRst in HLC.
  destruct HLC as [l' [HLC I3]].
  remember (v1*3+(2-((S(n*2+(1-offset t))) mod 3))) as v2.
  eapply (LIncs (v2-(k''-1))) in HLC.
  destruct HLC as [l'0 [HLC I4]].
  eassert _ as I5. {
    eapply sideRLs_trans.
    - apply I3.
    - apply I4.
  }
  rewrite <-lpow_add in I5.
  replace (k''+(v2-(k''-1))) with (1+v2) in I5 by lia.
  rewrite <-lrcons_hL_hRL_hR in I5.
  epose proof (sideRLs_concat_L I5 I2) as I.
  eex; eex.
  - apply HLC.
  - applys_eq HRC; lia.
  - follow I1.
    follow10 I.
    finish.
Qed.

Lemma init:
  exists l r,
  LC 25 [1;0;2]%nat l /\
  RC 56 t1 r /\
  c0 -->*
  S' (l,r).
Proof.
  eex; eex.
  - apply (LC_1' 12),LC_w,LC_w,(LC_0' 6),(LC_0' 3),LC_w,(LC_1 1),(LC_1 0),LC_0.
  - apply (RC_5 17),(RC_4 10),(RC_3 6),(RC_4 3),(RC_3 1),RC_2.
  - unfold S',S0; esx.
Qed.

Ltac rp1 x i :=
  match goal with
  | [ H: LC ?a _ _ |- _] =>
    replace a with x in H by 
    (destruct (i mod 3) as [|[|[|]]] eqn:E; lia)
  end.

Ltac rp2 x i :=
  match goal with
  | [ H: RC ?a _ _ |- _] =>
    replace a with (x*3+5) in H by 
    (destruct (i mod 3) as [|[|[|]]] eqn:E; lia)
  end.

Ltac BS :=
  match goal with
  | [ I1: LC _ ?ls _ ,
      I2: RC _ _ _
    |- _ ] =>
    let l0:=fresh "l" in
    let r0:=fresh "r" in
    let I1a:=fresh "I" in
    let I2a:=fresh "I" in
    let I3a:=fresh "I" in
    match ls with
    | [] =>
      unshelve epose proof (BigStep I1 I2 _) as [l0 [r0 [I1a [I2a I3a]]]]; [lia|]
    | O::_ =>
      epose proof (BigStep0 I1 I2) as [l0 [r0 [I1a [I2a I3a]]]]
    | _ =>
      unshelve epose proof (BigStep' I1 I2 _) as [l0 [r0 [I1a [I2a I3a]]]]; [lia|]
    end;
    clear I1 I2;
    unfold nxt,offset in *
  end.

Ltac BS' H' :=
  match goal with
  | [ I1: LC _ ?ls _ ,
      I2: RC _ _ _
    |- _ ] =>
    let l0:=fresh "l" in
    let r0:=fresh "r" in
    let I1a:=fresh "I" in
    let I2a:=fresh "I" in
    let I3a:=fresh "I" in
    unshelve epose proof (BigStep'' I1 I2 H' _) as [l0 [r0 [I1a [I2a I3a]]]]; [lia|];
    clear I1 I2;
    unfold nxt,offset in *
  end.

Lemma LRst_a n l:
  LC ((n+1)*32+10) [1;0]%nat l ->
  exists l',
  LC ((n+1)*16+10) [1;0;0]%nat l' /\
  sideRLs tm' (hLR^^(10)) (l<<0) l'.
Proof.
  intros.
  do 7 LC_inv.
  replace n2 with n in * by lia.
  apply LC_1 in H1.
  apply LC_2 in H1.
  fold Nat.add Nat.mul in H1.
  apply LC_1 in H1.
  do 3 apply LC_w in H1.
  apply LC_0' in H1.
  eex.
  - applys_eq H1; lia.
  - esx.
Qed.

Lemma LRst_b n l:
  LC ((n+1)*32+8) [1;0;0]%nat l ->
  exists l',
  LC ((n+1)*16+12) [1;0;0;0]%nat l' /\
  sideRLs tm' (hLR^^(14)) (l<<0) l'.
Proof.
  intros.
  do 8 LC_inv.
  replace n3 with n in * by lia.
  apply LC_1 in H2.
  apply LC_1 in H2.
  apply LC_2 in H2.
  fold Nat.add Nat.mul in H2.
  do 4 apply LC_w in H2.
  apply LC_0' in H2.
  eex.
  - applys_eq H2; lia.
  - esx.
Qed.

Lemma LRst_c n l:
  LC ((n+1)*32+4) [2]%nat l ->
  exists l',
  LC ((n+1)*16+0) [2;2]%nat l' /\
  sideRLs tm' (hLR^^(24)) (l<<0) l'.
Proof.
  intros.
  do 6 LC_inv.
  replace n0 with n in * by lia.
  apply LC_w in H2.
  apply LC_0' in H2.
  apply LC_0' in H2.
  apply LC_w in H2.
  apply LC_0' in H2.
  apply LC_0' in H2.
  eex.
  - applys_eq H2; lia.
  - esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  destruct init as [l0 [r0 [I1 [I2 I3]]]].
  eapply multistep_nonhalt.
  1: apply I3.
  eapply progress_nonhalt_cond with (P:=fun '(l,r) => exists i, LC (i*32+25) [1;0;2]%nat l /\ RC (i*48+56) t1 r).
  2: exists O; split; assumption.
  clear.
  intros [l r] [i [I1 I2]].
  rp1 (((i*16+12)*2+1)*2^0) i.
  rp2 (i*16+17) i.
  BS.
  rp2 (i*16+17) i.
  do 3 BS.
  rp1 (((i*8+10)*2+1)*2^1) i.
  rp2 (i*16+20) i.
  BS.
  rp1 ((i+1)*32+10) i.
  rp2 (i*16+20) i.
  BS' (LRst_a i l4).
  rp1 ((i+1)*32+8) i.
  rp2 (i*16+20) i.
  BS' (LRst_b i l5).
  rp1 (((i*16+19)*2+1)*2^0) i.
  rp2 (i*16+20) i.
  BS.
  rp2 (i*16+20) i.
  do 5 BS.
  rp1 (((i*8+14)*2+1)*2^1) i.
  rp2 (i*16+25) i.
  BS.
  rp1 (((i*16+27)*2+1)*2^0) i.
  rp2 (i*16+25) i.
  BS.
  rp2 (i*16+25) i.
  do 2 BS.
  rp1 (((i*8+15)*2+1)*2^1) i.
  rp2 (i*16+27) i.
  BS.
  rp1 (((i*16+29)*2+1)*2^0) i.
  rp2 (i*16+27) i.
  BS.
  rp2 (i*16+27) i.
  do 2 BS.
  rp1 (((i*8+16)*2+1)*2^1) i.
  rp2 (i*16+29) i.
  BS.
  rp1 (((i*16+31)*2+1)*2^0) i.
  rp2 (i*16+29) i.
  BS.
  rp2 (i*16+29) i.
  do 2 BS.
  rp1 (((i*16+34)*2+1)*2^0) i.
  rp2 (i*16+31) i.
  BS.
  rp2 (i*16+31) i.
  BS.
  rp1 (((i*2+4)*2+1)*2^3) i.
  rp2 (i*16+32) i.
  BS.
  rp1 (((i*16+30)*2+1)*2^0) i.
  rp2 (i*16+32) i.
  BS.
  rp2 (i*16+32) i.
  BS.
  rp1 ((i+1+1)*32+4) i.
  rp2 (i*16+33) i.
  BS' (LRst_c (i+1) l29).
  rp1 (((i*8+11)*2+1)*2^1) i.
  rp2 (i*16+33) i.
  BS.
  rp1 ((S i)*32+25) i.
  rp2 ((S i)*16+17) i.
  eexists; split.
  - follow10 I3.
    repeat
    match goal with
    | [H: _ |- _] =>
      follow100 H
    end.
    finish.
  - exists (S i); split.
    + applys_eq I1; lia.
    + applys_eq I2; lia.
Qed.

End TM5.


