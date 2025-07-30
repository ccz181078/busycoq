From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.

Open Scope list.

Module V1.
Section V1.
Hypothesis tm:TM.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Hypothesis QL QR:Q.
Hypothesis rh0:list Sym.

Notation "l <| r" :=
  (l <{{QL}} [1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [1;1] {{QR}}> r) (at level 30).

Notation lh := (0inf <* [1]).
Notation rh := (rh0 *> 0inf).

Hypothesis RL0:
  forall l r n,
  l |> [1]^^(n*3) *> [0;1] *> r -->*
  l <| [1]^^(n*3) *> [0;1] *> [1] *> r.

Hypothesis R1:
  forall l r n,
  l |> [1]^^(n*3+1) *> [0;1] *> r -->*
  l <* [1]^^(n*3+2) <* [0] |> r.

Hypothesis R2:
  forall l r n,
  l |> [1]^^(n*3+2) *> [0;1] *> r -->*
  l <* [1]^^(n*3+3) <* [0] |> r.

Hypothesis L1:
  forall l r n,
  l <* [1]^^(n*3+2) <* [0] <| r -->*
  l <| [1]^^(n*3+1) *> [0;1] *> r.

Hypothesis L2:
  forall l r n,
  l <* [1]^^(n*3+3) <* [0] <| r -->*
  l <| [1]^^(n*3+2) *> [0;1] *> r.

Hypothesis LR:
  forall r,
  lh <| r -->+
  lh |> [1] *> r.

Hypothesis RL:
  forall l,
  l |> rh -->*
  l <| [1]^^1 *> [0;1] *> rh.

Hypothesis init:
  c0 -->*
  lh |> rh.

Inductive RD := D0|D1|D2.

Inductive RC: (list RD) -> side -> Prop :=
| RC_rh: RC [] rh
| RC_0 n x x':
  RC x x' ->
  RC (D0::x) ([1]^^(n*3) *> [0;1] *> x')
| RC_1 n x x':
  RC x x' ->
  RC (D1::x) ([1]^^(n*3+1) *> [0;1] *> x')
| RC_2 n x x':
  RC x x' ->
  RC (D2::x) ([1]^^(n*3+2) *> [0;1] *> x')
.

Inductive RPush1: (list RD) -> (list RD) -> Prop :=
| RPush1_0 x: RPush1 (D0::x) (D1::x) 
| RPush1_1 x: RPush1 (D1::x) (D2::x) 
| RPush1_2 x: RPush1 (D2::x) (D0::x) 
.

Inductive RInc: (list RD) -> (list RD) -> Prop :=
| RInc_0 x x':
  RPush1 x x' ->
  RInc (D0::x) (D0::x')
| RInc_1 x x':
  RInc x x' ->
  RInc (D1::x) (D1::x')
| RInc_2 x x':
  RInc x x' ->
  RInc (D2::x) (D2::x')
| RInc_rh:
  RInc [] [D1]
.


Lemma RPush1_spec [x y x']:
  RPush1 x y ->
  RC x x' ->
  RC y ([1] *> x').
Proof.
  intros.
  inverts H; inverts H0.
  - applys_eq (RC_1 n).
    2: eauto.
    st; simpl_rotate.
    reflexivity.
  - applys_eq (RC_2 n).
    2: eauto.
    st; simpl_rotate.
    reflexivity.
  - applys_eq (RC_0 (S n)).
    2: eauto.
    st; simpl_rotate.
    reflexivity.
Qed.

Lemma RInc_spec [x y x']:
  RInc x y ->
  RC x x' ->
  exists y',
  RC y y' /\
  forall l, l |> x' -->* l <| y'.
Proof.
  intro H.
  gen x'.
  induction H; intros.
  - inverts H0.
    epose proof (RPush1_spec H H2).
    eexists; split.
    + eapply (RC_0 n); eauto.
    + intros.
      apply RL0.
  - inverts H0.
    epose proof (IHRInc _ H2) as [y' [I1 I2]].
    eexists; split.
    + eapply (RC_1 n); eauto.
    + intros.
      follow R1.
      follow I2.
      follow L1.
      finish.
  - inverts H0.
    epose proof (IHRInc _ H2) as [y' [I1 I2]].
    eexists; split.
    + eapply (RC_2 n); eauto.
    + intros.
      follow R2.
      follow I2.
      follow L2.
      finish.
  - inverts H.
    eexists; split.
    + eapply (RC_1 0),RC_rh.
    + apply RL.
Qed.

Inductive ROpSeq :=
| I0_P1I2
| I1_P1I2
| I2_P1I2
| P0_I2P1
| P1_I2P1
| P2_I2P1
| I0_P2I1
| I1_P2I1
| I2_P2I1
| P0_I1P2
| P1_I1P2
| P2_I1P2
| IP
| PI
.

Inductive RWF: ROpSeq -> (list RD) -> Prop :=
| RWF0:
  RWF I1_P1I2 []
| RWF1 x:
  RWF I2_P2I1 x ->
  RWF I0_P1I2 (D1::x)
| RWF2 x:
  RWF I1_P2I1 x ->
  RWF I2_P1I2 (D1::x)
| RWF3 x:
  RWF I0_P2I1 x ->
  RWF I1_P1I2 (D1::x)
| RWF4 x:
  RWF I2_P2I1 x ->
  RWF P0_I2P1 (D2::x)
| RWF5 x:
  RWF I2_P2I1 x ->
  RWF P2_I2P1 (D0::x)
| RWF6 x:
  RWF I2_P2I1 x ->
  RWF P1_I2P1 (D1::x)
| RWF7 x:
  RWF I1_P2I1 x ->
  RWF I1_P1I2 (D2::x)
| RWF8 x:
  RWF I0_P2I1 x ->
  RWF I0_P1I2 (D2::x)
| RWF9 x:
  RWF I2_P2I1 x ->
  RWF I2_P1I2 (D2::x)
| RWF10 x:
  RWF I0_P2I1 x ->
  RWF P0_I2P1 (D0::x)
| RWF11 x:
  RWF I0_P2I1 x ->
  RWF P2_I2P1 (D1::x)
| RWF12 x:
  RWF I0_P2I1 x ->
  RWF P1_I2P1 (D2::x)
| RWF13 x:
  RWF P1_I1P2 x ->
  RWF I1_P1I2 (D0::x)
| RWF14 x:
  RWF P0_I1P2 x ->
  RWF I0_P1I2 (D0::x)
| RWF15 x:
  RWF P2_I1P2 x ->
  RWF I2_P1I2 (D0::x)
| RWF16 x:
  RWF P0_I1P2 x ->
  RWF P0_I2P1 (D1::x)
| RWF17 x:
  RWF P0_I1P2 x ->
  RWF P2_I2P1 (D2::x)
| RWF18 x:
  RWF P0_I1P2 x ->
  RWF P1_I2P1 (D0::x)
| RWF19:
  RWF I2_P2I1 []
| RWF20 x:
  RWF I1_P1I2 x ->
  RWF I1_P2I1 (D1::x)
| RWF21 x:
  RWF I0_P1I2 x ->
  RWF I0_P2I1 (D1::x)
| RWF22 x:
  RWF I2_P1I2 x ->
  RWF I2_P2I1 (D1::x)
| RWF23 x:
  RWF I0_P1I2 x ->
  RWF P1_I1P2 (D2::x)
| RWF24 x:
  RWF I0_P1I2 x ->
  RWF P0_I1P2 (D0::x)
| RWF25 x:
  RWF I0_P1I2 x ->
  RWF P2_I1P2 (D1::x)
| RWF26 x:
  RWF P0_I2P1 x ->
  RWF I0_P2I1 (D0::x)
| RWF27 x:
  RWF P2_I2P1 x ->
  RWF I2_P2I1 (D0::x)
| RWF28 x:
  RWF P1_I2P1 x ->
  RWF I1_P2I1 (D0::x)
| RWF29 x:
  RWF P0_I2P1 x ->
  RWF P1_I1P2 (D1::x)
| RWF30 x:
  RWF P0_I2P1 x ->
  RWF P0_I1P2 (D2::x)
| RWF31 x:
  RWF P0_I2P1 x ->
  RWF P2_I1P2 (D0::x)
| RWF32 x:
  RWF I1_P1I2 x ->
  RWF I0_P2I1 (D2::x)
| RWF33 x:
  RWF I0_P1I2 x ->
  RWF I2_P2I1 (D2::x)
| RWF34 x:
  RWF I2_P1I2 x ->
  RWF I1_P2I1 (D2::x)
| RWF35 x:
  RWF I1_P1I2 x ->
  RWF P1_I1P2 (D0::x)
| RWF36 x:
  RWF I1_P1I2 x ->
  RWF P0_I1P2 (D1::x)
| RWF37 x:
  RWF I1_P1I2 x ->
  RWF P2_I1P2 (D2::x)
| RWF38:
  RWF IP []
| RWF39 x:
  RWF I1_P1I2 x ->
  RWF PI (D1::x)
| RWF40 x:
  RWF I1_P1I2 x ->
  RWF IP (D2::x)
| RWF41 x:
  RWF I0_P1I2 x ->
  RWF PI (D2::x)
| RWF42 x:
  RWF I0_P1I2 x ->
  RWF IP (D0::x)
| RWF43 x:
  RWF P0_I2P1 x ->
  RWF PI (D0::x)
| RWF44 x:
  RWF P0_I2P1 x ->
  RWF IP (D1::x)
.

Inductive ROp := RI | RP.

Inductive ROp1: ROp -> (list RD) -> (list RD) -> Prop :=
| ROp1_Inc x y:
  RInc x y ->
  ROp1 RI x y
| ROp1_Push1 x y:
  RPush1 x y ->
  ROp1 RP x y
.

Inductive ROpSeq_nxt: ROpSeq -> ROp -> ROpSeq -> Prop :=
| ROpSeq_0: ROpSeq_nxt I0_P1I2 RI I2_P1I2
| ROpSeq_1: ROpSeq_nxt I0_P1I2 RP P0_I2P1
| ROpSeq_2: ROpSeq_nxt I1_P1I2 RI I0_P1I2
| ROpSeq_3: ROpSeq_nxt I2_P1I2 RI I1_P1I2
| ROpSeq_4: ROpSeq_nxt P0_I2P1 RP P2_I2P1
| ROpSeq_5: ROpSeq_nxt P0_I2P1 RI I1_P1I2
| ROpSeq_6: ROpSeq_nxt P1_I2P1 RP P0_I2P1
| ROpSeq_7: ROpSeq_nxt P2_I2P1 RP P1_I2P1
| ROpSeq_8: ROpSeq_nxt I0_P2I1 RI I2_P2I1
| ROpSeq_9: ROpSeq_nxt I0_P2I1 RP P1_I1P2
| ROpSeq_10: ROpSeq_nxt I1_P2I1 RI I0_P2I1
| ROpSeq_11: ROpSeq_nxt I2_P2I1 RI I1_P2I1
| ROpSeq_12: ROpSeq_nxt P0_I1P2 RP P2_I1P2
| ROpSeq_13: ROpSeq_nxt P0_I1P2 RI I0_P2I1
| ROpSeq_14: ROpSeq_nxt P1_I1P2 RP P0_I1P2
| ROpSeq_15: ROpSeq_nxt P2_I1P2 RP P1_I1P2
| ROpSeq_16: ROpSeq_nxt IP RI PI
| ROpSeq_17: ROpSeq_nxt PI RP IP
.

Hint Constructors RC RWF RInc RPush1 ROp ROp1 ROpSeq_nxt : core.

Lemma RWF_spec [s x o s']:
  RWF s x ->
  ROpSeq_nxt s o s' ->
  exists y,
  ROp1 o x y /\
  RWF s' y.
Proof.
  intros H.
  gen o s'.
  induction H; intros.
  all: 
  match goal with
  | [ H: ROpSeq_nxt _ _ _ |- _ ] => inverts H
  end.
  all: eauto.
  all: 
  try
  solve[
  match goal with
  | [ H: forall (o:ROp), _ |- _ ] =>
    eassert _ as E by (eapply (H RI); eauto);
    destruct E as [y [I1 I2]];
    inverts I1;
    eauto 10
  end].
  all: 
  try
  solve[
  match goal with
  | [ H: forall (o:ROp), _ |- _ ] =>
    eassert _ as E by (eapply (H RP); eauto);
    destruct E as [y [I1 I2]];
    inverts I1;
    eauto 10
  end].
Qed.

Definition S r:Q*tape := lh |> r.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S rh).
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun r => exists x, RC x r /\ RWF IP x).
  2: eauto.
  unfold S.
  intros r [x [I1 I2]].
  epose proof (RWF_spec I2 ROpSeq_16) as [x0 [I3 I4]].
  epose proof (RWF_spec I4 ROpSeq_17) as [x1 [I5 I6]].
  inverts I3.
  inverts I5.
  epose proof (RInc_spec H I1) as [r0 [I7 I8]].
  epose proof (RPush1_spec H0 I7) as I9.
  eexists ([1] *> r0); split.
  - follow I8.
    apply LR.
  - eauto.
Qed.

End V1.
End V1.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LC_1LC1RE_1RD1LC_0RD1LA_1RF0RA_---1LD").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ C E [1]).
  all: es.
Qed.
End TM1.

Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB1LF_1RC0LE_---1RD_1RA0RB_1RF1LE_0RF1LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ E D [1;0;1]).
  all: es.
Qed.
End TM2.

Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB0RC_1LC1LE_1RF0LD_1RE1LD_0RE1LC_---1RA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ D A []).
  all: es.
Qed.
End TM3.


Module V2.
Section V2.
Hypothesis tm:TM.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{D}} [] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [1] {{E}}> r) (at level 30).

Notation lh := (0inf <* [1]).
Notation rh := ([0;1] *> 0inf).

Hypothesis RL0:
  forall l r n,
  l |> [1]^^(n*3+2) *> [0;1;1] *> r -->*
  l <| [1]^^(n*3+2) *> [0;1;1] *> [1] *> r.

Hypothesis R1:
  forall l r n,
  l |> [1]^^(n*3+0) *> [0;1;1] *> r -->*
  l <* [1]^^(n*3+1) <* [0;0] |> r.

Hypothesis R2:
  forall l r n,
  l |> [1]^^(n*3+1) *> [0;1;1] *> r -->*
  l <* [1]^^(n*3+2) <* [0;0] |> r.

Hypothesis L1:
  forall l r n,
  l <* [1]^^(n*3+1) <* [0;0] <| r -->*
  l <| [1]^^(n*3+0) *> [0;1;1] *> r.

Hypothesis L2:
  forall l r n,
  l <* [1]^^(n*3+2) <* [0;0] <| r -->*
  l <| [1]^^(n*3+1) *> [0;1;1] *> r.

Hypothesis LR:
  forall r,
  lh <| r -->+
  lh |> [1] *> r.

Hypothesis RL:
  forall l,
  l |> rh -->*
  l <| [1]^^0 *> [0;1;1] *> rh.

Hypothesis init:
  c0 -->*
  lh |> rh.

Inductive RD := D0|D1|D2.

Inductive RC: (list RD) -> side -> Prop :=
| RC_rh: RC [] rh
| RC_0 n x x':
  RC x x' ->
  RC (D0::x) ([1]^^(n*3+2) *> [0;1;1] *> x')
| RC_1 n x x':
  RC x x' ->
  RC (D1::x) ([1]^^(n*3+0) *> [0;1;1] *> x')
| RC_2 n x x':
  RC x x' ->
  RC (D2::x) ([1]^^(n*3+1) *> [0;1;1] *> x')
.

Inductive RPush1: (list RD) -> (list RD) -> Prop :=
| RPush1_0 x: RPush1 (D0::x) (D1::x) 
| RPush1_1 x: RPush1 (D1::x) (D2::x) 
| RPush1_2 x: RPush1 (D2::x) (D0::x) 
.

Inductive RInc: (list RD) -> (list RD) -> Prop :=
| RInc_0 x x':
  RPush1 x x' ->
  RInc (D0::x) (D0::x')
| RInc_1 x x':
  RInc x x' ->
  RInc (D1::x) (D1::x')
| RInc_2 x x':
  RInc x x' ->
  RInc (D2::x) (D2::x')
| RInc_rh:
  RInc [] [D1]
.


Lemma RPush1_spec [x y x']:
  RPush1 x y ->
  RC x x' ->
  RC y ([1] *> x').
Proof.
  intros.
  inverts H; inverts H0.
  - applys_eq (RC_1 (S n)).
    2: eauto.
    st; simpl_rotate.
    reflexivity.
  - applys_eq (RC_2 n).
    2: eauto.
    st; simpl_rotate.
    reflexivity.
  - applys_eq (RC_0 n).
    2: eauto.
    st; simpl_rotate.
    reflexivity.
Qed.

Lemma RInc_spec [x y x']:
  RInc x y ->
  RC x x' ->
  exists y',
  RC y y' /\
  forall l, l |> x' -->* l <| y'.
Proof.
  intro H.
  gen x'.
  induction H; intros.
  - inverts H0.
    epose proof (RPush1_spec H H2).
    eexists; split.
    + eapply (RC_0 n); eauto.
    + intros.
      apply RL0.
  - inverts H0.
    epose proof (IHRInc _ H2) as [y' [I1 I2]].
    eexists; split.
    + eapply (RC_1 n); eauto.
    + intros.
      follow R1.
      follow I2.
      follow L1.
      finish.
  - inverts H0.
    epose proof (IHRInc _ H2) as [y' [I1 I2]].
    eexists; split.
    + eapply (RC_2 n); eauto.
    + intros.
      follow R2.
      follow I2.
      follow L2.
      finish.
  - inverts H.
    eexists; split.
    + eapply (RC_1 0),RC_rh.
    + apply RL.
Qed.

Inductive ROpSeq :=
| I0_P1I2
| I1_P1I2
| I2_P1I2
| P0_I2P1
| P1_I2P1
| P2_I2P1
| I0_P2I1
| I1_P2I1
| I2_P2I1
| P0_I1P2
| P1_I1P2
| P2_I1P2
| IP
| PI
.

Inductive RWF: ROpSeq -> (list RD) -> Prop :=
| RWF0:
  RWF I1_P1I2 []
| RWF1 x:
  RWF I2_P2I1 x ->
  RWF I0_P1I2 (D1::x)
| RWF2 x:
  RWF I1_P2I1 x ->
  RWF I2_P1I2 (D1::x)
| RWF3 x:
  RWF I0_P2I1 x ->
  RWF I1_P1I2 (D1::x)
| RWF4 x:
  RWF I2_P2I1 x ->
  RWF P0_I2P1 (D2::x)
| RWF5 x:
  RWF I2_P2I1 x ->
  RWF P2_I2P1 (D0::x)
| RWF6 x:
  RWF I2_P2I1 x ->
  RWF P1_I2P1 (D1::x)
| RWF7 x:
  RWF I1_P2I1 x ->
  RWF I1_P1I2 (D2::x)
| RWF8 x:
  RWF I0_P2I1 x ->
  RWF I0_P1I2 (D2::x)
| RWF9 x:
  RWF I2_P2I1 x ->
  RWF I2_P1I2 (D2::x)
| RWF10 x:
  RWF I0_P2I1 x ->
  RWF P0_I2P1 (D0::x)
| RWF11 x:
  RWF I0_P2I1 x ->
  RWF P2_I2P1 (D1::x)
| RWF12 x:
  RWF I0_P2I1 x ->
  RWF P1_I2P1 (D2::x)
| RWF13 x:
  RWF P1_I1P2 x ->
  RWF I1_P1I2 (D0::x)
| RWF14 x:
  RWF P0_I1P2 x ->
  RWF I0_P1I2 (D0::x)
| RWF15 x:
  RWF P2_I1P2 x ->
  RWF I2_P1I2 (D0::x)
| RWF16 x:
  RWF P0_I1P2 x ->
  RWF P0_I2P1 (D1::x)
| RWF17 x:
  RWF P0_I1P2 x ->
  RWF P2_I2P1 (D2::x)
| RWF18 x:
  RWF P0_I1P2 x ->
  RWF P1_I2P1 (D0::x)
| RWF19:
  RWF I2_P2I1 []
| RWF20 x:
  RWF I1_P1I2 x ->
  RWF I1_P2I1 (D1::x)
| RWF21 x:
  RWF I0_P1I2 x ->
  RWF I0_P2I1 (D1::x)
| RWF22 x:
  RWF I2_P1I2 x ->
  RWF I2_P2I1 (D1::x)
| RWF23 x:
  RWF I0_P1I2 x ->
  RWF P1_I1P2 (D2::x)
| RWF24 x:
  RWF I0_P1I2 x ->
  RWF P0_I1P2 (D0::x)
| RWF25 x:
  RWF I0_P1I2 x ->
  RWF P2_I1P2 (D1::x)
| RWF26 x:
  RWF P0_I2P1 x ->
  RWF I0_P2I1 (D0::x)
| RWF27 x:
  RWF P2_I2P1 x ->
  RWF I2_P2I1 (D0::x)
| RWF28 x:
  RWF P1_I2P1 x ->
  RWF I1_P2I1 (D0::x)
| RWF29 x:
  RWF P0_I2P1 x ->
  RWF P1_I1P2 (D1::x)
| RWF30 x:
  RWF P0_I2P1 x ->
  RWF P0_I1P2 (D2::x)
| RWF31 x:
  RWF P0_I2P1 x ->
  RWF P2_I1P2 (D0::x)
| RWF32 x:
  RWF I1_P1I2 x ->
  RWF I0_P2I1 (D2::x)
| RWF33 x:
  RWF I0_P1I2 x ->
  RWF I2_P2I1 (D2::x)
| RWF34 x:
  RWF I2_P1I2 x ->
  RWF I1_P2I1 (D2::x)
| RWF35 x:
  RWF I1_P1I2 x ->
  RWF P1_I1P2 (D0::x)
| RWF36 x:
  RWF I1_P1I2 x ->
  RWF P0_I1P2 (D1::x)
| RWF37 x:
  RWF I1_P1I2 x ->
  RWF P2_I1P2 (D2::x)
| RWF38:
  RWF IP []
| RWF39 x:
  RWF I1_P1I2 x ->
  RWF PI (D1::x)
| RWF40 x:
  RWF I1_P1I2 x ->
  RWF IP (D2::x)
| RWF41 x:
  RWF I0_P1I2 x ->
  RWF PI (D2::x)
| RWF42 x:
  RWF I0_P1I2 x ->
  RWF IP (D0::x)
| RWF43 x:
  RWF P0_I2P1 x ->
  RWF PI (D0::x)
| RWF44 x:
  RWF P0_I2P1 x ->
  RWF IP (D1::x)
.

Inductive ROp := RI | RP.

Inductive ROp1: ROp -> (list RD) -> (list RD) -> Prop :=
| ROp1_Inc x y:
  RInc x y ->
  ROp1 RI x y
| ROp1_Push1 x y:
  RPush1 x y ->
  ROp1 RP x y
.

Inductive ROpSeq_nxt: ROpSeq -> ROp -> ROpSeq -> Prop :=
| ROpSeq_0: ROpSeq_nxt I0_P1I2 RI I2_P1I2
| ROpSeq_1: ROpSeq_nxt I0_P1I2 RP P0_I2P1
| ROpSeq_2: ROpSeq_nxt I1_P1I2 RI I0_P1I2
| ROpSeq_3: ROpSeq_nxt I2_P1I2 RI I1_P1I2
| ROpSeq_4: ROpSeq_nxt P0_I2P1 RP P2_I2P1
| ROpSeq_5: ROpSeq_nxt P0_I2P1 RI I1_P1I2
| ROpSeq_6: ROpSeq_nxt P1_I2P1 RP P0_I2P1
| ROpSeq_7: ROpSeq_nxt P2_I2P1 RP P1_I2P1
| ROpSeq_8: ROpSeq_nxt I0_P2I1 RI I2_P2I1
| ROpSeq_9: ROpSeq_nxt I0_P2I1 RP P1_I1P2
| ROpSeq_10: ROpSeq_nxt I1_P2I1 RI I0_P2I1
| ROpSeq_11: ROpSeq_nxt I2_P2I1 RI I1_P2I1
| ROpSeq_12: ROpSeq_nxt P0_I1P2 RP P2_I1P2
| ROpSeq_13: ROpSeq_nxt P0_I1P2 RI I0_P2I1
| ROpSeq_14: ROpSeq_nxt P1_I1P2 RP P0_I1P2
| ROpSeq_15: ROpSeq_nxt P2_I1P2 RP P1_I1P2
| ROpSeq_16: ROpSeq_nxt IP RI PI
| ROpSeq_17: ROpSeq_nxt PI RP IP
.

Hint Constructors RC RWF RInc RPush1 ROp ROp1 ROpSeq_nxt : core.

Lemma RWF_spec [s x o s']:
  RWF s x ->
  ROpSeq_nxt s o s' ->
  exists y,
  ROp1 o x y /\
  RWF s' y.
Proof.
  intros H.
  gen o s'.
  induction H; intros.
  all: 
  match goal with
  | [ H: ROpSeq_nxt _ _ _ |- _ ] => inverts H
  end.
  all: eauto.
  all: 
  try
  solve[
  match goal with
  | [ H: forall (o:ROp), _ |- _ ] =>
    eassert _ as E by (eapply (H RI); eauto);
    destruct E as [y [I1 I2]];
    inverts I1;
    eauto 10
  end].
  all: 
  try
  solve[
  match goal with
  | [ H: forall (o:ROp), _ |- _ ] =>
    eassert _ as E by (eapply (H RP); eauto);
    destruct E as [y [I1 I2]];
    inverts I1;
    eauto 10
  end].
Qed.

Definition S r:Q*tape := lh |> r.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S rh).
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun r => exists x, RC x r /\ RWF IP x).
  2: eauto.
  unfold S.
  intros r [x [I1 I2]].
  epose proof (RWF_spec I2 ROpSeq_16) as [x0 [I3 I4]].
  epose proof (RWF_spec I4 ROpSeq_17) as [x1 [I5 I6]].
  inverts I3.
  inverts I5.
  epose proof (RInc_spec H I1) as [r0 [I7 I8]].
  epose proof (RPush1_spec H0 I7) as I9.
  eexists ([1] *> r0); split.
  - follow I8.
    apply LR.
  - eauto.
Qed.

End V2.
End V2.


Module TM4.
Definition tm := Eval compute in (TM_from_str "1LB1RE_0RC0LD_0LA1RA_1LA1LD_0RF1RC_---0RA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply V2.nonhalt.
  all: es.
Qed.
End TM4.

Module TM5.
Definition tm := Eval compute in (TM_from_str "1LB1RE_0RC0LD_0RF1RA_1LA1LD_0LE1RC_---0RA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply V2.nonhalt.
  all: es.
Qed.
End TM5.

Module TM6.
Definition tm := Eval compute in (TM_from_str "1LB1RE_0RC0LD_0RF1RA_1LA1LD_0RF1RC_---0RA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply V2.nonhalt.
  all: es.
Qed.
End TM6.


