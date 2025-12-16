From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import ES_v3.
From BusyCoq Require Import DivModCases.


Tactic Notation "efollow" uconstr(H) :=
  (let I1:=fresh "I" in
  epose proof H as I1;
  try (follow I1; clear I1)).

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LC_1LA1RF_1LD1RE_1RC0LA_0RA0RF_0RC---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation w := [0;0;1;0;1;1;0;1;1].
Notation d0 := [0;0;1;0;1;1;0;1].
Notation d1 := [0;0;1;0;1;0;1;1].

Inductive RC:nat->side->Prop :=
| RC_0: RC 0 ([0;1]*>0inf)
| RC_1: RC 1 (d0*>0inf)
| RC_2: RC 2 (w*>[0;0;1;0;1]*>0inf)
| RC_3: RC 3 (w*>w*>0inf)
| RC_4 n r:
  RC (n) r ->
  RC (4+n*2) (w^^(2+n)*>d0*>r)
| RC_5 n r:
  RC (n) r ->
  RC (5+n*2) (w^^(3+n)*>d1*>r).

Lemma RC_ex n:
  exists r, RC n r.
Proof.
  induction n using lt_wf_ind.
  destruct n as [|[|[|[|]]]].
  1-4: eexists; econstructor.
  destruct (mod2 n); subst n.
  1-2: epose proof (H a _) as [r I1]; eexists; econstructor; apply I1.
  Unshelve.
  all: lia.
Qed.

Lemma RC_unique [n r r']:
  RC n r ->
  RC n r' ->
  r=r'.
Proof.
  intros H.
  gen r'.
  induction H; intros.
  1-4: inverts H; trivial.
  - inverts H0; try lia.
    replace n0 with n in * by lia.
    apply IHRC in H2; subst.
    trivial.
  - inverts H0; try lia.
    replace n0 with n in * by lia.
    apply IHRC in H2; subst.
    trivial.
Qed.

Notation "l |> r" := (l {{E}}> r) (at level 30).
Notation "l <| r" := (l <{{D}} [1] *> d1 *> r) (at level 30).

Lemma RInc [n l r r']:
  RC (1+n) r ->
  RC n r' ->
  l |> r -->*
  l <| r'.
Proof.
  gen l r r'.
  induction n using lt_wf_ind; introv R1 R0.
  inverts R0; inverts R1; try lia.
  1-3: es' & l.
  - replace n with O in * by lia.
    inverts H1.
    es.
  - replace n0 with n in * by lia.
    epose proof (RC_unique H0 H2); subst.
    es.
  - replace n with (1+n0) in * by lia.
    epose proof (H _ _ _ _ _ H2 H0) as I1.
    es; er; follow I1; es.
  Unshelve.
  lia.
Qed.

Definition S1 a b c r := 0inf <* <[0;1;1]^^(1+a) <{{C}} [0;0;1]^^b *> [0;1;1] *> w^^c *> d1 *> r.

Lemma Inc1 a b c n r r':
  RC (1+n) r ->
  RC n r' ->
  S1 (a) (2+b) c r -->*
  S1 (2+a) b (1+c) r'.
Proof.
  introv R1 R0.
  epose proof (RInc R1 R0) as I1.
  es; er; follow I1; es.
Qed.

Lemma Incs1 a b c n n0 r r':
  RC (n+n0) r ->
  RC n0 r' ->
  S1 a (n*2+b) c r -->*
  S1 (n*2+a) b (n+c) r'.
Proof.
  gen a b c r r'.
  induction n; intros.
  - epose proof (RC_unique H H0); subst.
    finish.
  - epose proof (RC_ex (n+n0)) as [r0 I1].
    cbn[Nat.mul]; cbn[Nat.add].
    efollow (Inc1 _ _ _ _ _ _ H I1).
    efollow (IHn _ _ _ _ _ I1 H0).
    finish.
Qed.

Definition S2 '(a,r) := 0inf <{{D}} [1] *> [0;0;1]^^(3+a) *> [0;1] *> r.

Ltac es_v3_pre ::= unfold_config; st.

Lemma BigStep n r r':
  RC n r ->
  RC (1+n) r' ->
  S2 (n,r) -->+
  S2 (1+n,r').
Proof.
  introv R0 R1.
  unfold S2.
  destruct n.
  1: inverts R0; inverts R1; es'.
  es; er.
  epose proof (RC_ex n) as [r0 I1].
  efollow (RInc R0 I1).
  mid (S1 1 (3+n) 0 r0).
  1: es.
  destruct (mod2 n); subst n.
  - destruct a.
    1: inverts I1; inverts R1; es'.
    epose proof (RC_ex a) as [r1 I2].
    efollow (Incs1 1 1 0 (2+a) (a) _ _).
    1: applys_eq I1; flia.
    inverts R1; try lia.
    replace a with n in * by lia.
    epose proof (RC_unique I2 H0); subst.
    es' n & r2.
  - destruct a.
    1: inverts I1; inverts R1; es.
    epose proof (RC_ex a) as [r1 I2].
    efollow (Incs1 1 0 0 (3+a) (a) _ _).
    1: applys_eq I1; flia.
    inverts R1; try lia.
    replace a with n in * by lia.
    epose proof (RC_unique I2 H0); subst.
    es' n & r2.
Qed.

Lemma init:
  exists r,
  c0 -->*
  S2 (O,r) /\
  RC O r.
Proof.
  eexists; split.
  2: econstructor.
  esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  epose proof init as [r0 [I1 I2]].
  eapply multistep_nonhalt.
  1: apply I1.
  eapply progress_nonhalt_cond with (P:=fun '(n,r) => RC n r).
  2: auto 1.
  intros [n r] HP.
  epose proof (RC_ex (1+n)) as [r' I3].
  eexists (_,_); split.
  2: apply I3.
  apply BigStep; auto 1.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB1RC_1RA0LD_0RD---_1LE1RF_1RD0LB_0RB0RC").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation w := [0;0;1;0;1;1;0;1;1].
Notation d0 := [0;0;1;0;1;1;0;1].
Notation d1 := [0;0;1;0;1;0;1;1].

Inductive RC:nat->side->Prop :=
| RC_0: RC 0 ([0;1]*>0inf)
| RC_1: RC 1 (d0*>0inf)
| RC_2: RC 2 (w*>[0;0;1;0;1]*>0inf)
| RC_3: RC 3 (w*>w*>0inf)
| RC_4 n r:
  RC (n) r ->
  RC (4+n*2) (w^^(2+n)*>d0*>r)
| RC_5 n r:
  RC (n) r ->
  RC (5+n*2) (w^^(3+n)*>d1*>r).

Lemma RC_ex n:
  exists r, RC n r.
Proof.
  induction n using lt_wf_ind.
  destruct n as [|[|[|[|]]]].
  1-4: eexists; econstructor.
  destruct (mod2 n); subst n.
  1-2: epose proof (H a _) as [r I1]; eexists; econstructor; apply I1.
  Unshelve.
  all: lia.
Qed.

Lemma RC_unique [n r r']:
  RC n r ->
  RC n r' ->
  r=r'.
Proof.
  intros H.
  gen r'.
  induction H; intros.
  1-4: inverts H; trivial.
  - inverts H0; try lia.
    replace n0 with n in * by lia.
    apply IHRC in H2; subst.
    trivial.
  - inverts H0; try lia.
    replace n0 with n in * by lia.
    apply IHRC in H2; subst.
    trivial.
Qed.

Notation "l |> r" := (l {{F}}> r) (at level 30).
Notation "l <| r" := (l <{{E}} [1] *> d1 *> r) (at level 30).

Lemma RInc [n l r r']:
  RC (1+n) r ->
  RC n r' ->
  l |> r -->*
  l <| r'.
Proof.
  gen l r r'.
  induction n using lt_wf_ind; introv R1 R0.
  inverts R0; inverts R1; try lia.
  1-3: es' & l.
  - replace n with O in * by lia.
    inverts H1.
    es.
  - replace n0 with n in * by lia.
    epose proof (RC_unique H0 H2); subst.
    es.
  - replace n with (1+n0) in * by lia.
    epose proof (H _ _ _ _ _ H2 H0) as I1.
    es; er; follow I1; es.
  Unshelve.
  lia.
Qed.

Definition S1 a b c r := 0inf <* <[0;1;1]^^(1+a) <{{D}} [0;0;1]^^b *> [0;1;1;0;0;1;0;1;1] *> w^^c *> d0 *> r.

Lemma Inc1 a b c n r r':
  RC (1+n) r ->
  RC n r' ->
  S1 (a) (2+b) c r -->*
  S1 (2+a) b (1+c) r'.
Proof.
  introv R1 R0.
  epose proof (RInc R1 R0) as I1.
  es; er; follow I1; es.
Qed.

Lemma Incs1 a b c n n0 r r':
  RC (n+n0) r ->
  RC n0 r' ->
  S1 a (n*2+b) c r -->*
  S1 (n*2+a) b (n+c) r'.
Proof.
  gen a b c r r'.
  induction n; intros.
  - epose proof (RC_unique H H0); subst.
    finish.
  - epose proof (RC_ex (n+n0)) as [r0 I1].
    cbn[Nat.mul]; cbn[Nat.add].
    efollow (Inc1 _ _ _ _ _ _ H I1).
    efollow (IHn _ _ _ _ _ I1 H0).
    finish.
Qed.

Definition S2 '(a,r) := 0inf <{{E}} [1] *> [0;0;1]^^(2+a) *> [0;1;0;0;1;0;1;1] *> r.

Ltac es_v3_pre ::= unfold_config; st.

Lemma BigStep n r r':
  6<=n ->
  RC n (w*>r) ->
  RC (1+n) (w*>r') ->
  S2 (n,r) -->+
  S2 (1+n,r').
Proof.
  introv Hn R0 R1.
  unfold S2.
  inverts R0; try lia.
  - destruct n0.
    1: lia.
    es; er.
    epose proof (RC_ex n0) as [r1 I1].
    efollow (RInc H1 I1).
    mid (S1 3 (5+n0*2) 0 (w^^(2+n0)*>d0*>r1)).
    1: es' n0 & r1.
    epose proof (RC_ex (2+n0)) as [r2 I2].
    efollow (Incs1 3 1 0 (2+n0) (2+n0) _ _).
    1: applys_eq (RC_4 _ _ I1); flia.
    es; er.
    efollow (RInc I2 H1).
    inverts R1; try lia.
    replace n with (S n0) in * by lia.
    epose proof (RC_unique H1 H2); subst.
    es' n0 & r.
  - destruct n0.
    1: lia.
    es; er.
    epose proof (RC_ex n0) as [r1 I1].
    efollow (RInc H1 I1).
    mid (S1 3 (6+n0*2) 0 (w^^(3+n0)*>d1*>r1)).
    1: es' n0 & r1.
    epose proof (RC_ex (2+n0)) as [r2 I2].
    efollow (Incs1 3 0 0 (3+n0) (2+n0) _ _).
    1: applys_eq (RC_5 _ _ I1); flia.
    inverts R1; try lia.
    replace n with (2+n0) in * by lia.
    epose proof (RC_unique I2 H2); subst.
    es' n0 & r.
Qed.

Lemma init:
  exists r,
  c0 -->*
  S2 (6,r) /\
  RC 6 (w*>r).
Proof.
  eexists; split.
  2: eapply (RC_4 1),RC_1.
  esx.
Qed.

Lemma RC_S n r:
  6<=n ->
  RC n (w*>r) ->
  exists r',
  RC (1+n) (w*>r').
Proof.
  intros Hn R0.
  inverts R0; try lia.
  - eexists.
    apply RC_5,H1.
  - epose proof (RC_ex (1+n0)) as [r1 I1].
    eexists.
    apply (RC_4 (1+n0)),I1.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  epose proof init as [r0 [I1 I2]].
  eapply multistep_nonhalt.
  1: apply I1.
  eapply progress_nonhalt_cond with (P:=fun '(n,r) => 6<=n /\ RC n (w*>r)).
  2: split; auto 1.
  intros [n r] [HP1 HP2].
  epose proof (RC_S _ _ HP1 HP2) as [r1 I3].
  eexists (_,_); split.
  - apply BigStep; eauto 1.
  - split; auto 1; lia.
Qed.

End TM2.


