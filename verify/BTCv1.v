From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Open Scope list.

Module V1.

Section V1.
Hypothesis tm:TM.
Hypothesis QR QL:Q.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Hypothesis d3 d2 d0 qL qR Lh Rh: list Sym.

Notation "l |> r" := (l <* qR {{QR}}> r) (at level 30).
Notation "l <3| r" := (l <{{QL}} qL *> d3 *> r) (at level 30).

Inductive RD :=
| D0(n:nat)(r:RD)
| D3(n:nat)(r:RD)
| D2(n:nat).

Fixpoint RC(x:RD):side :=
match x with
| D2 n => d2^^n *> Rh *> 0inf
| D0 n r => d2^^n *> d0 *> RC r
| D3 n r => d2^^n *> d3 *> RC r
end.

Fixpoint D30 n x :=
match n with
| O => x
| S n0 => D3 0 (D30 n0 x)
end.

Fixpoint p0 x :=
match x with
| D2 n => true
| D0 n r => negb (p0 r)
| D3 n r => p0 r
end.

Inductive RInc: RD->RD->Prop :=
| RInc_S0 n r1 r2:
    RInc r1 r2 ->
    RInc (D0 n r1) (D0 n r2)
| RInc_S3 n r1 r2:
    RInc r1 r2 ->
    RInc (D3 n r1) (D3 n r2)
| RInc0 n:
    RInc (D3 n (D2 0)) (D2 (1+n))
| RInc1 n:
    RInc (D2 (1+n)) (D0 n (D0 0 (D2 0)))
| RInc2 n:
    RInc (D0 (1+n) (D2 0)) (D3 n (D0 0 (D2 0)))
| RInc3 n m:
    RInc (D3 (1+n) (D30 m (D0 0 (D2 0)))) (D3 n (D0 0 (D30 (1+m) (D2 0))))
| RInc4 n m:
    RInc (D0 (1+n) (D30 m (D0 0 (D2 0)))) (D0 n (D0 0 (D30 (1+m) (D2 0))))
| RInc5 n m:
    RInc (D3 n (D0 0 (D30 m (D0 0 (D2 0))))) (D3 (1+n) (D30 m (D2 0)))
| RInc6 n m:
    RInc (D0 n (D0 0 (D30 m (D0 0 (D2 0))))) (D0 (1+n) (D30 m (D2 0)))
.


Lemma D30_spec n x:
  RC (D30 n x) = d3^^n *> RC x.
Proof.
  induction n; cbn; try rewrite Str_app_assoc; try congruence.
Qed.

Hypothesis RInc_spec:
  forall r1 r2,
  RInc r1 r2 ->
  forall l, l |> RC r1 -->* l <3| RC r2.

Lemma D30_p0 n x:
  p0 (D30 n x) = p0 x.
Proof.
  induction n; cbn; congruence.
Qed.

Lemma RInc_p0 r1 r2:
  RInc r1 r2 ->
  p0 r1 = p0 r2.
Proof.
  intros H.
  induction H; cbn; repeat rewrite D30_p0; cbn; try congruence.
Qed.

Inductive Rbad: RD->Prop :=
| Rbad030 n: Rbad (D0 0 (D30 n (D0 0 (D2 0))))
| Rbad30 n: Rbad (D30 (1+n) (D0 0 (D2 0)))
.

Lemma RInc_S30 n x x':
  RInc (D3 0 x) x' ->
  RInc (D30 (1+n) x) (D30 n x').
Proof.
  gen x x'.
  induction n; intros.
  - eapply H.
  - cbn; eapply RInc_S3,IHn,H.
Qed.

Ltac solve_Rbad :=
  (right; constructor) ||
  (left; eexists;
  repeat (
  eapply RInc0 ||
  eapply RInc1 ||
  eapply RInc2 ||
  eapply RInc3 ||
  eapply RInc4 ||
  eapply RInc5 ||
  eapply RInc6 ||
  eapply RInc_S30 ||
  eapply RInc_S3 ||
  eapply RInc_S0)).

Lemma Rbad_spec r1 r2:
  RInc r1 r2 ->
  ((exists r3, RInc r2 r3) \/ Rbad r2).
Proof.
  intros H.
  induction H.
  - destruct IHRInc as [[r3 HI]|HB].
    + left. eexists.
      eapply RInc_S0,HI.
    + inverts HB.
      * solve_Rbad.
      * destruct n; solve_Rbad.
  - destruct IHRInc as [[r3 HI]|HB].
    + left. eexists.
      eapply RInc_S3,HI.
    + inverts HB.
      * solve_Rbad.
      * destruct n; solve_Rbad.
  - solve_Rbad.
  - destruct n.
    + right; eapply (Rbad030 0).
    + left; eexists; eapply (RInc4 _ 0).
  - destruct n.
    + right; eapply (Rbad30 0).
    + left; eexists; eapply (RInc3 _ 0).
  - solve_Rbad.
  - solve_Rbad.
  - destruct m; solve_Rbad.
  - destruct m; solve_Rbad.
Qed.

Lemma BigStep r1 r2:
  p0 r1 = true ->
  RInc r1 r2 ->
  exists r3, RInc (D3 0 r2) r3.
Proof.
  intros I1 I2.
  epose proof (Rbad_spec _ _ I2) as [[r3 HI]|HB].
  - eexists.
    eapply RInc_S3,HI.
  - inverts HB.
    + eexists.
      eapply RInc5.
    + rewrite (RInc_p0 _ _ I2) in I1.
      cbn in I1.
      rewrite D30_p0 in I1.
      cbn in I1.
      congruence.
Qed.

Definition S0 x :=
  0inf <* Lh |> RC x.

Hypothesis x0: RD.
Hypothesis init: c0 -->* S0 x0.
Hypothesis p0x0: p0 x0 = true.
Hypothesis RIncx0: exists x', RInc x0 x'.
Hypothesis LR:
  forall x',
  0inf <* Lh <3| RC x' -->+
  0inf <* Lh |> RC (D3 0 x').

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun x => p0 x = true /\ exists x', RInc x x').
  2: {
    split; assumption.
  }
  intros x [Hp0 [x' HI]].
  epose proof (BigStep _ _ Hp0 HI) as HI'.
  exists (D3 0 x').
  split.
  - unfold S0.
    follow RInc_spec.
    apply LR.
  - split.
    + rewrite (RInc_p0 _ _ HI) in Hp0.
      eapply Hp0.
    + eapply HI'.
Qed.

End V1.
End V1.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1LB---_1RC1LE_1LD0RB_1RF0LB_0LF---_1LD0RC").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=C) (QL:=E)
  (d3:=[1;0;1;1;1;0]) (d2:=[1;0;1;1;0]) (qR:=<[1;0;1]) (Rh:=[]) (Lh:=<[1;1;0;0; 1;0;0;1;0;0])
  (qL:=[]) (d0:=[1;0])
  (x0:=(D3 0 (D0 0 (D0 0 (D2 0))))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc5 0 0).
  - es.
Qed.

End TM1.

Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB0LC_0RC0RD_1RD1LE_1LA0RC_0LF---_1LA0RD").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=D) (QL:=E)
  (d3:=[1;0;1;1;1;0]) (d2:=[1;0;1;1;0]) (qR:=<[1;0;1]) (Rh:=[]) (Lh:=<[1;1;0;0; 1;0;0;1;0;0])
  (qL:=[]) (d0:=[1;0])
  (x0:=(D3 0 (D0 0 (D0 0 (D2 0))))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc5 0 0).
  - es.
Qed.

End TM2.

Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB0LC_0RC0RD_1RD1LE_1LA0RC_0LF---_1LA0RF").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=D) (QL:=E)
  (d3:=[1;0;1;1;1;0]) (d2:=[1;0;1;1;0]) (qR:=<[1;0;1]) (Rh:=[]) (Lh:=<[1;1;0;0; 1;0;0;1;0;0])
  (qL:=[]) (d0:=[1;0])
  (x0:=(D3 0 (D0 0 (D0 0 (D2 0))))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc5 0 0).
  - es.
Qed.

End TM3.

Module TM4.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC1LE_1LD0RB_1RA0LB_0LF---_1LD0RC").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=C) (QL:=E)
  (d3:=[1;0;1;1;1;0]) (d2:=[1;0;1;1;0]) (qR:=<[1;0;1]) (Rh:=[]) (Lh:=<[1;1;0;0; 1;0;0;1;0;0])
  (qL:=[]) (d0:=[1;0])
  (x0:=(D3 0 (D0 0 (D0 0 (D2 0))))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc5 0 0).
  - es.
Qed.

End TM4.

Module TM5.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC1LE_1LD0RB_1RA0LB_0LF---_1LD0RF").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=C) (QL:=E)
  (d3:=[1;0;1;1;1;0]) (d2:=[1;0;1;1;0]) (qR:=<[1;0;1]) (Rh:=[]) (Lh:=<[1;1;0;0; 1;0;0;1;0;0])
  (qL:=[]) (d0:=[1;0])
  (x0:=(D3 0 (D0 0 (D0 0 (D2 0))))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc5 0 0).
  - es.
Qed.

End TM5.

Module TM6.

Definition tm := Eval compute in (TM_from_str "1LB1RC_1RA0LE_0RD1LB_1LA0RE_1RD1LF_0LA---").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=D) (QL:=F)
  (d3:=[1;0;1;1;1;0]) (d2:=[1;0;1;1;0]) (qR:=<[1;0;1]) (Rh:=[]) (Lh:=<[1;1;0;0; 1;0;0;1;0;0])
  (qL:=[]) (d0:=[1;0])
  (x0:=(D3 0 (D0 0 (D0 0 (D2 0))))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc5 0 0).
  - es.
Qed.

End TM6.

Module TM7.

Definition tm := Eval compute in (TM_from_str "1RB---_1RC0LD_1LB0RF_1RF1LE_0LC---_1LB0RD").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=F) (QL:=E)
  (d3:=[1;0;1;1;1;0]) (d2:=[1;0;1;1;0]) (qR:=<[1;0;1]) (Rh:=[]) (Lh:=<[1;1;0;0; 1;0;0;1;0;0])
  (qL:=[]) (d0:=[1;0])
  (x0:=(D3 1 (D2 0))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc0).
  - es.
Qed.

End TM7.

Module TM8.

Definition tm := Eval compute in (TM_from_str "1RB1LD_1LC0RA_1RE1LD_0LE---_1LF0RB_1RE0LC").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=B) (QL:=D)
  (d3:=[1;0;1;1;1;0]) (d2:=[1;0;1;1;0]) (qR:=<[1;0;1]) (Rh:=[1]) (Lh:=<[1;1;0;0; 1;0;0;1;0;0])
  (qL:=[]) (d0:=[1;0])
  (x0:=(D3 1 (D2 0))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: execute_with_shift_rule'.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc0).
  - es.
Qed.

End TM8.

Module TM9.

Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LE_1LD0RB_1RF0LB_0LF---_1LD0RC").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=C) (QL:=E)
  (d3:=[1;0;1;1;1;0]) (d2:=[1;0;1;1;0]) (qR:=<[1;0;1]) (Rh:=[]) (Lh:=<[1;1;0;0; 1;0;0;1;0;0])
  (qL:=[]) (d0:=[1;0])
  (x0:=(D3 1 (D2 0))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc0).
  - es.
Qed.

End TM9.

Module TM10.

Definition tm := Eval compute in (TM_from_str "1RB0RC_1RC1LE_1LD0RB_1RA0LB_0LF---_1LD0RC").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=C) (QL:=E)
  (d3:=[1;0;1;1;1;0]) (d2:=[1;0;1;1;0]) (qR:=<[1;0;1]) (Rh:=[]) (Lh:=<[1;1;0;0; 1;0;0;1;0;0])
  (qL:=[]) (d0:=[1;0])
  (x0:=(D3 1 (D2 0))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc0).
  - es.
Qed.

End TM10.

Module TM11.

Definition tm := Eval compute in (TM_from_str "1RB0RC_1RC1LE_1LD0RB_1RA0LB_0LF---_1LD0RF").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=C) (QL:=E)
  (d3:=[1;0;1;1;1;0]) (d2:=[1;0;1;1;0]) (qR:=<[1;0;1]) (Rh:=[]) (Lh:=<[1;1;0;0; 1;0;0;1;0;0])
  (qL:=[]) (d0:=[1;0])
  (x0:=(D3 1 (D2 0))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc0).
  - es.
Qed.

End TM11.

Module TM12.

Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC0RC_1LA0RD_1RC1LE_0LF---_1LA0RC").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=C) (QL:=E)
  (d3:=[1;0;1;1;1;0]) (d2:=[1;0;1;1;0]) (qR:=<[1;0;1]) (Rh:=[]) (Lh:=<[1;1;0;0; 1;0;0;1;0;0])
  (qL:=[]) (d0:=[1;0])
  (x0:=(D3 1 (D2 0))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc0).
  - es.
Qed.

End TM12.

Module TM13.

Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC0RC_1LA0RD_1RC1LE_0LF---_1LA0RF").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=C) (QL:=E)
  (d3:=[1;0;1;1;1;0]) (d2:=[1;0;1;1;0]) (qR:=<[1;0;1]) (Rh:=[]) (Lh:=<[1;1;0;0; 1;0;0;1;0;0])
  (qL:=[]) (d0:=[1;0])
  (x0:=(D3 1 (D2 0))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc0).
  - es.
Qed.

End TM13.

Module TM14.

Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC0RF_1LA0RC_1RF1LE_0LC---_1LA0RD").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=F) (QL:=E)
  (d3:=[1;0;1;1;1;0]) (d2:=[1;0;1;1;0]) (qR:=<[1;0;1]) (Rh:=[]) (Lh:=<[1;1;0;0; 1;0;0;1;0;0])
  (qL:=[]) (d0:=[1;0])
  (x0:=(D3 1 (D2 0))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc0).
  - es.
Qed.

End TM14.

Module TM15.

Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC0RF_1LA0RF_1RF1LE_0LC---_1LA0RD").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=F) (QL:=E)
  (d3:=[1;0;1;1;1;0]) (d2:=[1;0;1;1;0]) (qR:=<[1;0;1]) (Rh:=[]) (Lh:=<[1;1;0;0; 1;0;0;1;0;0])
  (qL:=[]) (d0:=[1;0])
  (x0:=(D3 1 (D2 0))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc0).
  - es.
Qed.

End TM15.

Module TM16.

Definition tm := Eval compute in (TM_from_str "1LB1RA_1RC0LE_0RD1RC_0LA0RE_1RD1LF_0LC---").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=D) (QL:=F)
  (d3:=[1;0;1;1;1;0]) (d2:=[1;0;1;1;0]) (qR:=<[1;0;1]) (Rh:=[]) (Lh:=<[1;1;0;0; 1;0;0;1;0;0])
  (qL:=[]) (d0:=[1;0])
  (x0:=(D3 1 (D2 0))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc0).
  - es.
Qed.

End TM16.

Module TM17.

Definition tm := Eval compute in (TM_from_str "1LB0RE_1LC1RD_1RB0LE_0RA1LC_1RA1LF_0LB---").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=A) (QL:=F)
  (d3:=[1;0;1;1;1;0]) (d2:=[1;0;1;1;0]) (qR:=<[1;0;1]) (Rh:=[]) (Lh:=<[1;1;0;0; 1;0;0;1;0;0])
  (qL:=[]) (d0:=[1;0])
  (x0:=(D3 1 (D2 0))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc0).
  - es.
Qed.

End TM17.

Module TM18.

Definition tm := Eval compute in (TM_from_str "1LB0RE_1RC0LE_0RD1RC_0LA0RE_1RA1LF_0LC---").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=A) (QL:=F)
  (d3:=[1;0;1;1;1;0]) (d2:=[1;0;1;1;0]) (qR:=<[1;0;1]) (Rh:=[]) (Lh:=<[1;1;0;0; 1;0;0;1;0;0])
  (qL:=[]) (d0:=[1;0])
  (x0:=(D3 1 (D2 0))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc0).
  - es.
Qed.

End TM18.

Module TM19.

Definition tm := Eval compute in (TM_from_str "1LB1RC_1RA0RC_0RD1LE_0LA0RF_0LE1LD_1RD---").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=D) (QL:=D)
  (d3:=[1;0;0;0;1;0]) (d2:=[1;0;0;1;0]) (qR:=<[1;0;1]) (Rh:=[]) (Lh:=<[1;1;0;0; 1;0;0;1;0;0])
  (qL:=[]) (d0:=[1;0])
  (x0:=(D3 1 (D2 0))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc0).
  - es.
Qed.

End TM19.

Module TM20.

Definition tm := Eval compute in (TM_from_str "1LB1RC_1RC0LE_0RD1RD_0LA0RF_0LE1LD_1RD---").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=D) (QL:=D)
  (d3:=[1;0;0;0;1;0]) (d2:=[1;0;0;1;0]) (qR:=<[1;0;1]) (Rh:=[]) (Lh:=<[1;1;0;0; 1;0;0;1;0;0])
  (qL:=[]) (d0:=[1;0])
  (x0:=(D3 1 (D2 0))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc0).
  - es.
Qed.

End TM20.

Module TM21.

Definition tm := Eval compute in (TM_from_str "1LB1RC_1RA0LE_0RD---_0LA0RF_0LE1LD_1RD---").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=D) (QL:=D)
  (d3:=[1;0;0;0;1;0]) (d2:=[1;0;0;1;0]) (qR:=<[1;0;1]) (Rh:=[]) (Lh:=<[1;1;0;0; 1;0;0;1;0;0])
  (qL:=[]) (d0:=[1;0])
  (x0:=(D3 1 (D2 0))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc0).
  - es.
Qed.

End TM21.

Module TM22.

Definition tm := Eval compute in (TM_from_str "1LB1RC_1RC0LE_0RD1RC_0LA0RF_0LE1LD_1RD---").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=D) (QL:=D)
  (d3:=[1;0;0;0;1;0]) (d2:=[1;0;0;1;0]) (qR:=<[1;0;1]) (Rh:=[]) (Lh:=<[1;1;0;0; 1;0;0;1;0;0])
  (qL:=[]) (d0:=[1;0])
  (x0:=(D3 1 (D2 0))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc0).
  - es.
Qed.

End TM22.

Module TM23.

Definition tm := Eval compute in (TM_from_str "1LB1RC_1RA0LE_0RD0RF_0LA0RF_0LE1LD_1RC---").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=C) (QL:=D)
  (d3:=[1;0;0;0;1;0]) (d2:=[1;0;0;1;0]) (qR:=<[1;0;1]) (Rh:=[]) (Lh:=<[1;1;0;0; 1;0;0;1;0;0])
  (qL:=[]) (d0:=[1;0])
  (x0:=(D3 1 (D2 0))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc0).
  - es.
Qed.

End TM23.

Module TM24.

Definition tm := Eval compute in (TM_from_str "1RB1LD_1RC1RF_0LA0RF_0LD0LE_1LC---_0RB1LB").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=B) (QL:=C)
  (d3:=[1;0;0;0;1;0]) (d2:=[1;0;0;1;0]) (qR:=<[0;1;0]) (Rh:=[]) (Lh:=<[1;1;0;0; 1;0;0;1;0])
  (qL:=[]) (d0:=[1;0])
  (x0:=(D3 1 (D2 0))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc0).
  - es.
Qed.

End TM24.

Module TM25.

Definition tm := Eval compute in (TM_from_str "1RB0LE_1LC0RA_---1LD_1RD0RA_1LA0LF_0RD1LB").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=B) (QL:=E)
  (d3:=[1;0;0;0;1;0]) (d2:=[1;0;0;1;0]) (qR:=<[0;1;0;1;0;1]) (Rh:=[]) (Lh:=<[1;1;0;1;1])
  (qL:=[0;1;0]) (d0:=[1;0])
  (x0:=(D3 1 (D2 0))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc0).
  - es.
Qed.

End TM25.

Module TM26.

Definition tm := Eval compute in (TM_from_str "1RB0LF_0RC---_1RD1LF_0LE1RC_0LA1LD_0LB0RF").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=D) (QL:=E)
  (d3:=[1;0;0;0;1;0]) (d2:=[1;0;0;1;0]) (qR:=<[1;1;1;1]) (Rh:=[]) (Lh:=<[1;0;1;0;0;1;0;0;1])
  (qL:=[0]) (d0:=[1;0])
  (x0:=(D3 1 (D2 0))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc0).
  - es.
Qed.

End TM26.

Module TM27.

Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LD_0LB0RE_0LA1RE_0RD0LF_1LC1LE").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=C) (QL:=B)
  (d3:=[1;0;0;0;0;1;0;0]) (d2:=[1;0;0;0;1;0;0]) (qR:=<[0;1;1;0;1;1]) (Rh:=[]) (Lh:=<[1;1;0;0;1; 0;1;1;1; 0;1;1;1; 0;1;1;1])
  (qL:=[0]) (d0:=[1;0;0])
  (x0:=(D3 1 (D2 0))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc0).
  - es.
Qed.

End TM27.

Module TM28.

Definition tm := Eval compute in (TM_from_str "1LB---_1RC1LD_1RD0RC_0LE1RC_0LA0LF_1RA0LB").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=D) (QL:=F)
  (d3:=[1;1;0;0;0;1;1;0]) (d2:=[1;1;0;0;1;1;0]) (qR:=<[1;1;0;1;1;0;1]) (Rh:=[]) (Lh:=<[1;0;0; 1;1;0;0; 1;1;0;0])
  (qL:=[0;0]) (d0:=[1;1;0])
  (x0:=(D3 1 (D2 0))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc0).
  - es.
Qed.

End TM28.

Module TM29.

Definition tm := Eval compute in (TM_from_str "1LB---_1RC1LD_1RD0RC_0LE1RC_1LA0LF_1RA0LB").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=D) (QL:=F)
  (d3:=[1;1;0;0;0;1;1;0]) (d2:=[1;1;0;0;1;1;0]) (qR:=<[1;1;0;1;1;0;1]) (Rh:=[]) (Lh:=<[1;0;0; 1;1;0;0; 1;1;0;0])
  (qL:=[0;0]) (d0:=[1;1;0])
  (x0:=(D3 1 (D2 0))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc0).
  - es.
Qed.

End TM29.

Module TM30.

Definition tm := Eval compute in (TM_from_str "1RB0LF_1LC0LA_1LE1LD_0LB1RE_1RD0RE_0LC---").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=D) (QL:=A)
  (d3:=[1;1;0;0;0;1;1;0]) (d2:=[1;1;0;0;1;1;0]) (qR:=<[1;1;0;1;1;0;1]) (Rh:=[]) (Lh:=<[1;1;0;0; 1;1;0;0])
  (qL:=[0;0]) (d0:=[1;1;0])
  (x0:=(D3 1 (D2 0))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc0).
  - es.
Qed.

End TM30.

Module TM31.

Definition tm := Eval compute in (TM_from_str "1LB1LF_0LC0RF_1RB1LD_0LE1RF_1RC---_0RD0LA").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=B) (QL:=C)
  (d3:=[1;0;0;0;0;1;0;0]) (d2:=[1;0;0;0;1;0;0]) (qR:=<[0;1;1;0;1;1]) (Rh:=[1;0;1]) (Lh:=<[1;1;0;0;1; 0;1;1;1; 0;1;1;1; 0;1;1;1])
  (qL:=[0]) (d0:=[1;0;0])
  (x0:=(D3 1 (D2 0))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: execute_with_shift_rule'.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc0).
  - es.
Qed.

End TM31.

Module TM32.

Definition tm := Eval compute in (TM_from_str "1LB1LD_1RC0RE_0LA1RB_1RF0LE_0LD1LC_0RC---").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=C) (QL:=E)
  (d3:=[1;0;0;0;1;0]) (d2:=[1;0;0;1;0]) (qR:=<[1;1;1;1;1;1]) (Rh:=[]) (Lh:=<[1;1;1;0; 1;1;0])
  (qL:=[0;1;0]) (d0:=[1;0])
  (x0:=(D3 1 (D2 0))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc0).
  - es.
Qed.

End TM32.

Module TM33.

Definition tm := Eval compute in (TM_from_str "1LB0RD_1LC1RA_1RB0LE_0LB0RF_0LE1LD_1RD---").

Lemma nonhalt: ~halts tm c0.
Proof.
  Import V1.
  eapply nonhalt with (QR:=D) (QL:=D)
  (d3:=[1;0;0;0;1;0]) (d2:=[1;0;0;1;0]) (qR:=<[1;0;1]) (Rh:=[]) (Lh:=<[1;1;0;0; 1;0;0;1;0;0])
  (qL:=[]) (d0:=[1;0])
  (x0:=(D3 1 (D2 0))).
  - intros r1 r2 H.
    induction H; intros; cbn[RC]; repeat rewrite D30_spec; cbn[RC].
    1,2: es; er; follow IHRInc; es.
    all: es.
  - unfold S0; cbn; solve_init.
  - reflexivity.
  - eexists.
    eapply (RInc0).
  - es.
Qed.

End TM33.

