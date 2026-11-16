From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import DivModCases.

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


Module TM4.
Definition tm := Eval compute in (TM_from_str "1RB0LC_0LC0LD_1LF1LD_1RE1RB_0RB0RD_---1LA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 l a b c r :=
  l <* <[1;0;1]^^a <* <[1] <* <[1;0;1]^^b {{E}}> [0;1;0]^^c *> r.

Lemma Inc1 l a b c r:
  S1 l (1+a) b (1+c) r -->*
  S1 l a (2+b) c r.
Proof.
  es.
Qed.

Lemma Incs1 n l a b c r:
  S1 l (n+a) b (n+c) r -->*
  S1 l a (n*2+b) c r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition S2 b c r :=
  0inf <* <[1;0] <* <[1;0;1]^^b {{E}}> [0;1;0]^^c *> r.

Lemma Inc2 b c r:
  S2 b (1+c) r -->*
  S2 (2+b) c r.
Proof.
  es.
Qed.

Lemma Incs2 b c r:
  S2 b c r -->*
  S2 (c*2+b) 0 r.
Proof.
  gen b.
  ind c Inc2.
Qed.

Fixpoint RC(ls:list (nat*bool)) :=
match ls with
| [] => [1] *> 0inf
| (n,b)::t => (if b then [1] else [0]) *> [0;1;0]^^(2+n) *> RC t
end.

Lemma Ov_1 l a b r:
  b<=a ->
  l <* <[1;0;1]^^(2+a) {{E}}> [1] *> [0;1;0]^^(2+b) *> r -->*
  S1 l (a-b) (b*2+4) 0 r.
Proof.
  intros.
  mid (S1 l a 4 b r).
  1: es.
  follow (Incs1 b l (a-b) 4 0 r).
  finish.
Qed.

Definition P r1 r2 c1 :=
  forall l a,
  l <* <[1;0;1]^^(c1+a) {{E}}> RC r1 -->*
  l <{{D}} [1;0;0] *> [0;1;0]^^(2+a) *> RC r2.

Lemma P_O:
  P [] [(O,false)] 4.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S0 n t:
  P ((n,false)::t) ((n,true)::t) 3.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S1 n t t' c1:
  P t t' c1 ->
  c1<=n*2+4 ->
  P ((n,true)::t) ((n*2+4-c1,false)::t') (4+n).
Proof.
  unfold P.
  intros.
  cbn[RC].
  replace (4+n+a) with (2+(2+n+a)) by lia.
  follow Ov_1.
  1: lia.
  unfold S1.
  replace (n*2+4) with (c1+(n*2+4-c1)) by lia.
  replace (2+n+a-n) with (2+a) by lia.
  follow H.
  er; sr.
  finish.
Qed.

Definition S' '(a,ls) := S2 a 0 (RC ls).

Lemma BigStep a r1 r2 c1:
  P r1 r2 c1 ->
  c1+1<=a ->
  S' (a,r1) -->+
  S' ((a-c1)*2+4,r2).
Proof.
  unfold P,S',S2.
  intros.
  follow (H ([0;1]*>0inf) (1+(a-c1-1))).
  mid10 (S2 6 (a-c1-1) (RC r2)).
  1: es.
  follow Incs2.
  unfold S2.
  finish.
Qed.

Inductive F: nat->nat->Prop :=
| F_0: F 0 0
| F_1: F 1 0
| F_2 x y: F (x*2+1) y -> F (x*2+2) (y*2+1)
| F_3 x y y0: F (x*2+2) y -> F x y0 -> y0<=y*2 -> F (x*2+3) (y*2-y0)
.

Inductive Rn: nat->(list (nat*bool))->nat->Prop :=
| Rn_0: Rn 0 [] 4
| Rn_1 n r c1 y:
  Rn n r c1 ->
  F n y ->
  Rn (n*2+1) ((y,false)::r) 3
| Rn_2 n r c1 y:
  Rn n r c1 ->
  F n y ->
  Rn (n*2+2) ((y,true)::r) (4+y).

Ltac inv H := inverts H; try lia.
Ltac rlia a b := replace a with b in * by lia.

Lemma F_unique [n y1 y2]:
  F n y1 ->
  F n y2 ->
  y1 = y2.
Proof.
  intro F1.
  gen y2.
  induction F1; intros.
  - inv H.
  - inv H.
  - inv H.
    rlia x0 x.
    apply IHF1 in H1.
    congruence.
  - inv H0.
    rlia x0 x.
    apply IHF1_1 in H2.
    apply IHF1_2 in H3.
    congruence.
Qed.

Ltac F_unique :=
repeat
match goal with
| [H1: F ?x _, H2: F ?x _ |- _] => epose proof (F_unique H1 H2); clear H2
end.

Lemma Rn_unique [n r1 r2 c1 c2]:
  Rn n r1 c1 ->
  Rn n r2 c2 ->
  (r1=r2/\c1=c2).
Proof.
  intro R1.
  gen r2 c2.
  induction R1; intros.
  - inv H; tauto.
  - inv H0.
    rlia n0 n.
    apply IHR1 in H2.
    destruct H2.
    epose proof (F_unique H H3).
    split; congruence.
  - inv H0.
    rlia n0 n.
    apply IHR1 in H2.
    destruct H2.
    F_unique.
    split; congruence.
Qed.

Lemma F_mono [n1 n2 y1 y2]:
  F n1 y1 ->
  F n2 y2 ->
  n1<=n2 ->
  y1<=y2.
Proof.
  gen n1 y1 y2.
  induction n2 using lt_wf_ind; intros.
  inv H1.
  - inv H0.
  - inv H0.
  - assert (n1<=x*2+1\/n1=x*2+2) as [E|E] by lia.
    + unshelve epose proof (H _ _ _ _ _ H0 H3 _).
      all: try lia.
    + subst n1.
      inv H0.
      rlia x0 x.
      F_unique; lia.
  - assert (n1<=x*2+2\/n1=x*2+3) as [E|E] by lia.
    + unshelve epose proof (H _ _ _ _ _ H0 H3 _).
      all: try lia.
      unshelve epose proof (H _ _ _ _ _ H4 H3 _).
      all: lia.
    + subst n1.
      inv H0.
      rlia x0 x.
      F_unique; lia.
Qed.

Lemma F_ex n:
  exists y, F n y.
Proof.
  induction n using lt_wf_ind.
  destruct n as [|[|n]].
  1,2: eexists; econstructor.
  destruct (mod2 n); subst n.
  - unshelve epose proof (H (a*2+1) _) as [y I1].
    1: lia.
    eapply F_2 in I1.
    eexists.
    applys_eq I1; flia.
  - unshelve epose proof (H (a*2+2) _) as [y I1].
    1: lia.
    unshelve epose proof (H (a) _) as [y0 I2].
    1: lia.
    eapply F_3 in I2.
    2: apply I1.
    2: epose proof (F_mono I2 I1); lia.
    eexists.
    applys_eq I2; flia.
Qed.

Lemma Rn_ex n:
  exists r1 c1, Rn n r1 c1.
Proof.
  induction n using lt_wf_ind.
  destruct n.
  - eexists _,_.
    econstructor.
  - destruct (mod2 n); subst n.
    + unshelve epose proof (H a _) as [r1 [c1 I1]].
      1: lia.
      epose proof (F_ex a) as [y1 I2].
      eexists _,_.
      applys_eq (Rn_1 a).
      1: lia.
      all: eauto 1.
    + unshelve epose proof (H a _) as [r1 [c1 I1]].
      1: lia.
      epose proof (F_ex a) as [y1 I2].
      eexists _,_.
      applys_eq (Rn_2 a).
      1: lia.
      all: eauto 1.
Qed.

Lemma Rn_spec [n r1 r2 c1 c2]:
  Rn n r1 c1 ->
  Rn (1+n) r2 c2 ->
  P r1 r2 c1.
Proof.
  gen r1 r2 c1 c2.
  induction n using lt_wf_ind; introv R1 R2.
  inv R1.
  - inv R2.
    rlia n O.
    inv H1.
    inv H2.
    apply P_O.
  - inv R2.
    rlia n0 n.
    epose proof (Rn_unique H0 H3) as [I1 I2]; subst.
    F_unique; subst.
    apply P_S0.
  - inv R2.
    rlia n (1+n0).
    unshelve epose proof (H _ _ _ _ _ _ H0 H3) as H.
    1: lia.
    assert (y0+c3=y*2+4). {
      clear H2 H.
      inv H0.
      - inv H1; inv H4.
      - clear c1 c2 y1 n r0 r1 H H2 H3.
        inv H4.
        inv H1.
        + rlia n1 O.
          inv H0.
        + rlia n1 (1+x0).
          rlia x (1+x0).
          inv H0.
          rlia x1 x0.
          F_unique; lia.
      - clear c1 c2 n r0 r1 H H3.
        inv H4.
        rlia x n1.
        F_unique; lia.
    }
    eapply (P_S1 y) in H.
    2: lia.
    applys_eq H; flia.
Qed.

Lemma F_S n y1 y2:
  F n y1 ->
  F (1+n) y2 ->
  y2<=y1*2+1.
Proof.
  intros.
  inv H0.
  - rlia n (x*2+1).
    F_unique; lia.
  - rlia n (x*2+2).
    F_unique; lia.
Qed.

Lemma init:
  c0 -->* S' (22,[(O,true)]).
Proof.
  unfold S',S2.
  esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(a,ls) => exists n c1, Rn (n*2+2) ls c1 /\ c1*2+1<=a).
  2: {
    eexists O,_; split.
    eapply Rn_2.
    1: apply Rn_0.
    1: apply F_0.
    lia.
  }
  intros [a r1] [n [c1 [I1 I4]]].
  epose proof (Rn_ex (1+(n*2+2))) as [r2 [c2 I2]].
  epose proof (Rn_ex (2+(n*2+2))) as [r3 [c3 I3]].
  epose proof (Rn_spec I1 I2) as HP1.
  epose proof (Rn_spec I2 I3) as HP2.
  assert (c3+3<=c1*2/\c2=3). {
    inv I1.
    rlia n0 n.
    inv I2.
    rlia n1 (1+n).
    inv I3.
    rlia n2 (1+n).
    epose proof (F_S _ _ _ H1 H4).
    F_unique; lia.
  }
  eapply BigStep in HP1,HP2.
  2,3: shelve.
  eexists (_,_); split.
  - follow11 HP1.
    apply HP2.
  - eexists (1+n),_; split.
    1: apply I3.
    shelve.
  Unshelve.
  all: lia.
Qed.

End TM4.

