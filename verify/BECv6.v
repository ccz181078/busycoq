From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1LB0LF_1RC0RD_1LF1RA_---1RE_1RB0RE_1RB1LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := [1;1;0;0].
Notation d1 := [0;0;0;0].
Notation d2 := [1;0;0;0].

Inductive RC: nat->side->Prop :=
| RC_0: RC 0 (d2*>0inf)
| RC_1 n r: RC n r -> RC (1+n*3) (d0*>r)
| RC_2 n r: RC n r -> RC (2+n*3) (d1*>r)
| RC_3 n r: RC n r -> RC (3+n*3) (d2*>r)
.

Notation "l |> r" := (l <* <[1] {{C}}> r) (at level 30).
Notation "l <| r" := (l <{{C}} [1] *> r) (at level 30).

Lemma RInc n r:
  RC n r ->
  exists r', RC (S n) r' /\
  forall l, l |> r -->* l <| r'.
Proof.
  gen r.
  induction n using Wf_nat.lt_wf_ind; intros.
  inverts H0.
  - eexists; split.
    1: eapply (RC_1 0),RC_0.
    es.
  - eexists; split.
    1: apply RC_2,H1.
    es.
  - eexists; split.
    1: apply RC_3,H1.
    es.
  - eapply H in H1.
    2: lia.
    destruct H1 as [r' [I1 I2]].
    eexists; split.
    1: apply (RC_1 (S n0)),I1.
    es; er; follow I2; es.
Qed.

Definition LC a b := 0inf <* <[1;0;1]^^a <* <[0;0] <* <[1;0;1]^^b <* <[1].

Lemma LInc a b r:
  LC a (1+b) <| r -->*
  LC (1+a) b |> r.
Proof.
  unfold LC.
  es.
Qed.

Lemma LOv a r:
  LC a 0 <| d0 *> r -->+
  LC 0 (2+a) |> r.
Proof.
  unfold LC.
  es.
Qed.

Lemma Incs a b n r:
  RC n r ->
  exists r',
  RC (b+n) r' /\
  LC a b <| r -->*
  LC (b+a) 0 <| r'.
Proof.
  gen a n r.
  induction b; intros.
  - eexists; split.
    1: apply H.
    finish.
  - apply RInc in H.
    destruct H as [r0 [I1 I2]].
    eapply IHb in I1.
    destruct I1 as [r1 [I3 I4]].
    eexists; split.
    1: applys_eq I3; lia.
    follow LInc.
    follow I2.
    follow I4.
    finish.
Qed.

Definition S' '(a,r) := LC a 0 <| r.

Lemma init:
  exists r,
  RC 1 r /\
  c0 -->* S' (1%nat,r).
Proof.
  eexists; split.
  1: apply (RC_1 0),RC_0.
  es.
Qed.

Lemma BigStep a n r:
  RC (1+n*3) r ->
  exists r',
  RC (3+a+n) r' /\
  S' (a,r) -->+
  S' (2+a,r').
Proof.
  intros.
  unfold S'.
  inverts H; try lia.
  replace n0 with n in * by lia.
  apply RInc in H1.
  destruct H1 as [r [I1 I2]].
  eapply Incs in I1.
  destruct I1 as [r' [I3 I4]].
  eexists r'; split.
  2:{
    follow10 LOv.
    follow I2.
    follow I4.
    finish.
  }
  applys_eq I3; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  pose proof init as [r0 [I1 I2]].
  eapply multistep_nonhalt.
  1: apply I2.
  eapply progress_nonhalt_cond with (P:=fun '(a,r) => exists n, RC (1+n*3) r /\ a=n*2+1).
  2: exists O; split; trivial.
  intros [a r] [n [I3 I4]].
  subst.
  eapply BigStep in I3.
  destruct I3 as [r' [I4 I5]].
  eexists; split.
  1: apply I5.
  exists (S n); split.
  1: applys_eq I4; lia.
  lia.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB1RF_0LC1RC_0RA1LD_1LB1RE_1RC0LE_0RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := [0;0;1;0].
Notation d1 := [1;0;1;0].

Inductive RC: nat->side->Prop :=
| RC_0: RC 0 0inf
| RC_1: RC 1 ([1]*>0inf)
| RC_2: RC 2 ([1;0;1;1]*>0inf)
| RC_3 n r: RC n r -> RC (3+n*2) (d0*>r)
| RC_4 n r: RC n r -> RC (4+n*2) (d1*>r)
.

Notation "l |> r" := (l <* <[1;0] {{A}}> r) (at level 30).
Notation "l <| r" := (l <{{E}} [0;0] *> r) (at level 30).

Lemma RInc n r:
  RC n r ->
  exists r', RC (S n) r' /\
  forall l, l |> r -->* l <| r'.
Proof.
  gen r.
  induction n using Wf_nat.lt_wf_ind; intros.
  inverts H0.
  - eexists; split.
    1: eapply RC_1.
    es.
  - eexists; split.
    1: eapply RC_2.
    es.
  - eexists; split.
    1: eapply (RC_3 0),RC_0.
    es.
  - eexists; split.
    1: apply RC_4,H1.
    es.
  - eapply H in H1.
    2: lia.
    destruct H1 as [r' [I1 I2]].
    eexists; split.
    1: apply (RC_3 (S n0)),I1.
    es; er; follow I2; es.
Qed.

Definition LC a b := 0inf <* <[1;0;1]^^2 <* <[0;0;1]^^b <* <[1;0;1]^^a.

Lemma LInc a b r:
  LC a (1+b) <| r -->*
  LC (1+a) b |> r.
Proof.
  unfold LC.
  es.
Qed.

Lemma LOv a r:
  LC a 0 <| d0 *> r -->+
  LC 0 (2+a) |> r.
Proof.
  unfold LC.
  es.
Qed.

Lemma Incs a b n r:
  RC n r ->
  exists r',
  RC (b+n) r' /\
  LC a b <| r -->*
  LC (b+a) 0 <| r'.
Proof.
  gen a n r.
  induction b; intros.
  - eexists; split.
    1: apply H.
    finish.
  - apply RInc in H.
    destruct H as [r0 [I1 I2]].
    eapply IHb in I1.
    destruct I1 as [r1 [I3 I4]].
    eexists; split.
    1: applys_eq I3; lia.
    follow LInc.
    follow I2.
    follow I4.
    finish.
Qed.

Definition S' '(a,r) := LC a 0 <| r.

Lemma init:
  exists r,
  RC 17 r /\
  c0 -->* S' (11,r).
Proof.
  eexists; split.
  1: apply (RC_3 7),(RC_3 2),RC_2.
  esx.
Qed.

Lemma BigStep a n r:
  RC (3+n*2) r ->
  exists r',
  RC (3+a+n) r' /\
  S' (a,r) -->+
  S' (2+a,r').
Proof.
  intros.
  unfold S'.
  inverts H; try lia.
  replace n0 with n in * by lia.
  apply RInc in H1.
  destruct H1 as [r [I1 I2]].
  eapply Incs in I1.
  destruct I1 as [r' [I3 I4]].
  eexists r'; split.
  2:{
    follow10 LOv.
    follow I2.
    follow I4.
    finish.
  }
  applys_eq I3; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  pose proof init as [r0 [I1 I2]].
  eapply multistep_nonhalt.
  1: apply I2.
  eapply progress_nonhalt_cond with (P:=fun '(a,r) => exists n, RC (3+(1+n*2)*2) r /\ a=n*2+5).
  2: exists 3; split; trivial.
  intros [a r] [n [I3 I4]].
  subst.
  eapply BigStep in I3.
  destruct I3 as [r' [I4 I5]].
  eexists; split.
  1: apply I5.
  exists (S n); split.
  1: applys_eq I4; lia.
  lia.
Qed.

End TM2.

