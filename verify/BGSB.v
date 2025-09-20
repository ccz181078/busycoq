From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Inductive RH := R0|R1|R2|R3|R4|R5.

Fixpoint RC x n :=
match x with
| [] =>
  match n with
  | R0 => ([1;0;1;0;1]*>0inf)
  | R1 => ([1;0;1;1;0;1;1]*>0inf)
  | R2 => ([1;0;0;1;0;1]*>0inf)
  | R3 => ([1;0;1;1;0;1]*>0inf)
  | R4 => ([1;0;1;0;1;0;1]*>0inf)
  | R5 => ([1]*>0inf)
  end
| a::x0 => [1;0;1;0] *> [0;1;0]^^a *> RC x0 n
end.

Inductive RInc: (list nat)->RH->(list nat)->RH->nat->Prop :=
| RInc_0:
  RInc [] R0 [] R1 1
| RInc_1:
  RInc [] R1 [] R2 0
| RInc_2:
  RInc [] R2 [] R3 1
| RInc_3:
  RInc [] R3 [] R4 0
| RInc_4:
  RInc [] R4 [2] R5 1
| RInc_5:
  RInc [] R5 [] R0 1
| RInc_S a x n x0 n0 k:
  k<=a*2 ->
  RInc x n x0 n0 k ->
  RInc (a::x) n (a*2-k::x0) n0 a
.

Inductive F: nat->nat->Prop :=
| F_0: F 0 2
| F_1: F 1 3
| F_2: F 2 5
| F_3: F 3 10
| F_4: F 4 19
| F_5: F 5 38
| F_6: F 6 75
| F_S n y0 y1:
    F n y0 ->
    F (6+n) y1 ->
    F (7+n) (y1*2-y0)
.

Lemma F_unique {n y0 y1}:
  F n y0 ->
  F n y1 ->
  y0 = y1.
Proof.
  gen y0 y1.
  induction n using Wf_nat.lt_wf_ind; intros.
  do 7 (
  destruct n; [ inverts H0; inverts H1; lia | ]).
  inverts H0; inverts H1.
  epose proof (H _ _ _ _ H2 H3).
  epose proof (H _ _ _ _ H4 H5).
  lia.
  Unshelve. all: lia.
Qed.

Ltac F_uni :=
  repeat
  match goal with
  | [ H1: F _ _, H2: F _ _ |- _ ] => epose proof (F_unique H1 H2); subst; clear H2
  end.

Lemma F_ex n:
  exists y, F n y.
Proof.
  induction n using Wf_nat.lt_wf_ind; intros.
  do 7 (
  destruct n; [ eexists; constructor | ]).
  epose proof (H n _) as [y0 Hy0].
  epose proof (H (6+n) _) as [y1 Hy1].
  eexists; eapply F_S; eassumption.
  Unshelve. all: lia.
Qed.


Lemma F_mono n y0 y1:
  F n y0 ->
  F (S n) y1 ->
  y0<y1.
Proof.
  gen y0 y1.
  induction n using Wf_nat.lt_wf_ind; intros.
  do 6 (
  destruct n; [ inverts H0; inverts H1; lia | ]).
  inverts H1.
  epose proof (F_ex (1+n)) as [y1 Hy1].
  epose proof (F_ex (2+n)) as [y2' Hy2].
  epose proof (F_ex (3+n)) as [y3' Hy3].
  epose proof (F_ex (4+n)) as [y4 Hy4].
  epose proof (F_ex (5+n)) as [y5 Hy5].
  epose proof (H _ _ _ _ H3 Hy1).
  epose proof (H _ _ _ _ Hy1 Hy2).
  epose proof (H _ _ _ _ Hy2 Hy3).
  epose proof (H _ _ _ _ Hy3 Hy4).
  epose proof (H _ _ _ _ Hy4 Hy5).
  epose proof (H _ _ _ _ Hy5 H4).
  F_uni.
  lia.
  Unshelve. all: lia.
Qed.

Lemma F_mono' n0 n1 y0 y1:
  n0<n1 ->
  F n0 y0 ->
  F n1 y1 ->
  y0<y1.
Proof.
  gen n0 y0 y1.
  induction n1 using Wf_nat.lt_wf_ind; intros.
  destruct n1.
  1: lia.
  epose proof (F_ex n1) as [y2 Hy2].
  epose proof (F_mono _ _ _ Hy2 H2).
  assert (n0<n1\/n0=n1) as [E|E] by lia.
  - epose proof (H n1 _ _ _ _ _ H1 Hy2).
    lia.
  - subst.
    F_uni.
    lia.
  Unshelve. all: lia.
Qed.


Inductive Rn: nat->(list nat)->RH->Prop :=
| Rn_0: Rn 0 [2] R5
| Rn_1: Rn 1 [3] R0
| Rn_2: Rn 2 [5] R1
| Rn_3: Rn 3 [10] R2
| Rn_4: Rn 4 [19] R3
| Rn_5: Rn 5 [38] R4
| Rn_S i x n y:
    F (6+i) y ->
    Rn i x n ->
    Rn (6+i) (y::x) n.

Lemma RInc_Rn i x n x0 n0 y:
  Rn i x n ->
  Rn (1+i) x0 n0 ->
  F i y ->
  RInc x n x0 n0 y.
Proof.
  gen x n x0 n0 y.
  induction i using Wf_nat.lt_wf_ind; intros.
  destruct i as [|[|[|[|[|[|]]]]]].
  1-6: inverts H0; inverts H1; inverts H2.
  1: eapply RInc_S with (k:=1%nat); [lia|constructor].
  1: eapply RInc_S with (k:=1%nat); [lia|constructor].
  1: eapply RInc_S with (k:=0%nat); [lia|constructor].
  1: eapply RInc_S with (k:=1%nat); [lia|constructor].
  1: eapply RInc_S with (k:=0%nat); [lia|constructor].
  1: inverts H3; inverts H4;
     eapply RInc_S with (k:=1%nat); [lia|constructor].
  inverts H0; inverts H1.
  inverts H3.
  F_uni.
  econstructor.
  2: eapply (H n1); try eassumption.
  2: lia.
  epose proof (F_mono' _ _ _ _ _ H1 H2).
  lia.
  Unshelve. all: lia.
Qed.

Lemma Rn_ex i:
  exists x n, Rn i x n.
Proof.
  induction i using Wf_nat.lt_wf_ind; intros.
  do 6 (
  destruct i; [ eexists; repeat econstructor | ]).
  epose proof (H (i) _) as [x0 [n0 I0]].
  epose proof (F_ex (6+i)) as [y Hy].
  eexists _,_.
  econstructor; eassumption.
  Unshelve. all: lia.
Qed.

Ltac solve_RInc :=
  solve
  [ eapply RInc_S; [ | solve_RInc ]; lia
  | constructor ].


Module TM1.
Definition tm := Eval compute in (TM_from_str "1LB0LA_0RC1RB_1RD1RB_0LE1LD_---1LF_0LA0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l {{C}}> r) (at level 30).
Notation "l <| r" := (l <{{A}} [0;0;0] *> r) (at level 30).


Definition S1 a b r :=
  0inf <* <[1;0;1;0] <* <[1;1;0]^^a |> [0;1;0]^^b *> r.

Lemma Inc1 a b r:
  S1 a (1+b) r -->*
  S1 (2+a) b r.
Proof.
  es.
Qed.

Lemma Incs1 a b r:
  S1 a b r -->*
  S1 (b*2+a) 0 r.
Proof.
  gen a r.
  ind b Inc1.
Qed.

Definition S2 l a b c r :=
  l <* <[1;1;0]^^a <* <[1;0;1;0] <* <[1;1;0]^^b |> [0;1;0]^^c *> r.

Lemma Inc2 l a b c r:
  S2 l (1+a) b (1+c) r -->*
  S2 l a (2+b) c r.
Proof.
  es.
Qed.

Lemma Incs2 l a b c r:
  S2 l (c+a) b c r -->*
  S2 l a (c*2+b) 0 r.
Proof.
  gen a b.
  ind c Inc2.
Qed.


Lemma RInc_spec x n x0 n0 k:
  RInc x n x0 n0 k ->
  forall l,
  l <* <[1;1;0]^^k |> RC x n -->+
  l <| RC x0 n0.
Proof.
  intros I.
  induction I; cbn[RC].
  1-6: es.
  intros.
  mid01 (S2 l (a+0) 0 a (RC x n)).
  1: es.
  follow Incs2.
  replace (a*2+0) with (k+(a*2-k)) by lia.
  unfold S2.
  rewrite lpow_add,Str_app_assoc.
  follow10 IHI.
  es.
Qed.

Definition S0 '(a,x,n) := S1 5 a (RC x n).

Lemma BigStep a x n x0 n0 k:
  k<=a*2+3 ->
  RInc x n x0 n0 k ->
  S0 (a,x,n) -->+
  S0 (a*2+3-k,x0,n0).
Proof.
  intros Hk I.
  eapply RInc_spec in I.
  unfold S0.
  follow Incs1.
  unfold S1.
  replace (a*2+5) with (k+(2+(a*2+3-k))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow10 I.
  es.
Qed.

Lemma init:
  c0 -->*
  S0 (4,[],R0).
Proof.
  unfold S0,S1.
  esx.
Qed.

Opaque S0.
Ltac mstep :=
eapply progress_evstep;
eapply progress_evstep_trans; [
apply BigStep; [ | solve_RInc ]; lia | ];
cbn.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: follow init; do 5 mstep; finish.
  eapply progress_nonhalt_cond with (P:=fun '(a,x,n) => exists i y, Rn i x n /\ F (6+i) y /\ y<=a).
  2: eexists O,_; repeat split.
  2: econstructor.
  2: econstructor.
  2: lia.
  intros [[a x] n] [i [y [I1 [I2 I3]]]].
  epose proof (Rn_ex (S i)) as [x0 [n0 I4]].
  epose proof (F_ex i) as [y0 Hy0].
  epose proof (F_mono' _ _ _ _ _ Hy0 I2) as I5.
  eexists (_,_,_); split.
  1: eapply BigStep.
  2: eapply (RInc_Rn i); eassumption.
  1: lia.
  eexists _,_; repeat split.
  - apply I4.
  - econstructor; eassumption.
  - lia.
  Unshelve. all: lia.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB0LA_0RC0RF_1RD1RB_0LE1LD_---1LF_0LA0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l {{C}}> r) (at level 30).
Notation "l <| r" := (l <{{A}} [0;0;0] *> r) (at level 30).


Definition S1 a b r :=
  0inf <* <[1;0;1;0] <* <[1;1;0]^^a |> [0;1;0]^^b *> r.

Lemma Inc1 a b r:
  S1 a (1+b) r -->*
  S1 (2+a) b r.
Proof.
  es.
Qed.

Lemma Incs1 a b r:
  S1 a b r -->*
  S1 (b*2+a) 0 r.
Proof.
  gen a r.
  ind b Inc1.
Qed.

Definition S2 l a b c r :=
  l <* <[1;1;0]^^a <* <[1;0;1;0] <* <[1;1;0]^^b |> [0;1;0]^^c *> r.

Lemma Inc2 l a b c r:
  S2 l (1+a) b (1+c) r -->*
  S2 l a (2+b) c r.
Proof.
  es.
Qed.

Lemma Incs2 l a b c r:
  S2 l (c+a) b c r -->*
  S2 l a (c*2+b) 0 r.
Proof.
  gen a b.
  ind c Inc2.
Qed.


Lemma RInc_spec x n x0 n0 k:
  RInc x n x0 n0 k ->
  forall l,
  l <* <[1;1;0]^^k |> RC x n -->+
  l <| RC x0 n0.
Proof.
  intros I.
  induction I; cbn[RC].
  1-6: es.
  intros.
  mid01 (S2 l (a+0) 0 a (RC x n)).
  1: es.
  follow Incs2.
  replace (a*2+0) with (k+(a*2-k)) by lia.
  unfold S2.
  rewrite lpow_add,Str_app_assoc.
  follow10 IHI.
  es.
Qed.

Definition S0 '(a,x,n) := S1 5 a (RC x n).

Lemma BigStep a x n x0 n0 k:
  k<=a*2+3 ->
  RInc x n x0 n0 k ->
  S0 (a,x,n) -->+
  S0 (a*2+3-k,x0,n0).
Proof.
  intros Hk I.
  eapply RInc_spec in I.
  unfold S0.
  follow Incs1.
  unfold S1.
  replace (a*2+5) with (k+(2+(a*2+3-k))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow10 I.
  es.
Qed.

Lemma init:
  c0 -->*
  S0 (4,[],R0).
Proof.
  unfold S0,S1.
  esx.
Qed.

Opaque S0.
Ltac mstep :=
eapply progress_evstep;
eapply progress_evstep_trans; [
apply BigStep; [ | solve_RInc ]; lia | ];
cbn.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: follow init; do 5 mstep; finish.
  eapply progress_nonhalt_cond with (P:=fun '(a,x,n) => exists i y, Rn i x n /\ F (6+i) y /\ y<=a).
  2: eexists O,_; repeat split.
  2: econstructor.
  2: econstructor.
  2: lia.
  intros [[a x] n] [i [y [I1 [I2 I3]]]].
  epose proof (Rn_ex (S i)) as [x0 [n0 I4]].
  epose proof (F_ex i) as [y0 Hy0].
  epose proof (F_mono' _ _ _ _ _ Hy0 I2) as I5.
  eexists (_,_,_); split.
  1: eapply BigStep.
  2: eapply (RInc_Rn i); eassumption.
  1: lia.
  eexists _,_; repeat split.
  - apply I4.
  - econstructor; eassumption.
  - lia.
  Unshelve. all: lia.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB0LA_0RC1RB_1RD1RB_0LE1LD_---1LF_0LA0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l {{C}}> r) (at level 30).
Notation "l <| r" := (l <{{A}} [0;0;0] *> r) (at level 30).


Definition S1 a b r :=
  0inf <* <[1;0;1;0] <* <[1;1;0]^^a |> [0;1;0]^^b *> r.

Lemma Inc1 a b r:
  S1 a (1+b) r -->*
  S1 (2+a) b r.
Proof.
  es.
Qed.

Lemma Incs1 a b r:
  S1 a b r -->*
  S1 (b*2+a) 0 r.
Proof.
  gen a r.
  ind b Inc1.
Qed.

Definition S2 l a b c r :=
  l <* <[1;1;0]^^a <* <[1;0;1;0] <* <[1;1;0]^^b |> [0;1;0]^^c *> r.

Lemma Inc2 l a b c r:
  S2 l (1+a) b (1+c) r -->*
  S2 l a (2+b) c r.
Proof.
  es.
Qed.

Lemma Incs2 l a b c r:
  S2 l (c+a) b c r -->*
  S2 l a (c*2+b) 0 r.
Proof.
  gen a b.
  ind c Inc2.
Qed.


Lemma RInc_spec x n x0 n0 k:
  RInc x n x0 n0 k ->
  forall l,
  l <* <[1;1;0]^^k |> RC x n -->+
  l <| RC x0 n0.
Proof.
  intros I.
  induction I; cbn[RC].
  1-6: es.
  intros.
  mid01 (S2 l (a+0) 0 a (RC x n)).
  1: es.
  follow Incs2.
  replace (a*2+0) with (k+(a*2-k)) by lia.
  unfold S2.
  rewrite lpow_add,Str_app_assoc.
  follow10 IHI.
  es.
Qed.

Definition S0 '(a,x,n) := S1 5 a (RC x n).

Lemma BigStep a x n x0 n0 k:
  k<=a*2+3 ->
  RInc x n x0 n0 k ->
  S0 (a,x,n) -->+
  S0 (a*2+3-k,x0,n0).
Proof.
  intros Hk I.
  eapply RInc_spec in I.
  unfold S0.
  follow Incs1.
  unfold S1.
  replace (a*2+5) with (k+(2+(a*2+3-k))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow10 I.
  es.
Qed.

Lemma init:
  c0 -->*
  S0 (4,[],R0).
Proof.
  unfold S0,S1.
  esx.
Qed.

Opaque S0.
Ltac mstep :=
eapply progress_evstep;
eapply progress_evstep_trans; [
apply BigStep; [ | solve_RInc ]; lia | ];
cbn.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: follow init; do 5 mstep; finish.
  eapply progress_nonhalt_cond with (P:=fun '(a,x,n) => exists i y, Rn i x n /\ F (6+i) y /\ y<=a).
  2: eexists O,_; repeat split.
  2: econstructor.
  2: econstructor.
  2: lia.
  intros [[a x] n] [i [y [I1 [I2 I3]]]].
  epose proof (Rn_ex (S i)) as [x0 [n0 I4]].
  epose proof (F_ex i) as [y0 Hy0].
  epose proof (F_mono' _ _ _ _ _ Hy0 I2) as I5.
  eexists (_,_,_); split.
  1: eapply BigStep.
  2: eapply (RInc_Rn i); eassumption.
  1: lia.
  eexists _,_; repeat split.
  - apply I4.
  - econstructor; eassumption.
  - lia.
  Unshelve. all: lia.
Qed.

End TM3.


