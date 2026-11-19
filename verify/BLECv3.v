From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import ES_v3.
From BusyCoq Require Import DivModCases.
From BusyCoq Require Import Longitudinal.

Open Scope list.

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


Module TM3.

Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC1RF_1RD0LE_0RA0RE_0RA0RB_0LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation hR := (C,<[1;0;1]).
Notation hR' := (B,<[0]).
Notation hL := (E,[0;0;1]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL)].
Notation hLR := [(hL,hR)].
Notation hLR' := [(hL,hR')].

Notation dw := [0;1;1;1; 0;1;1;0;1; 0;1;1;0;1; 0;1;1;0;1].
Notation d0 := [0;1; 0;1;1;0;1; 0;1;1;0;1; 0;1;1;0;1].
Notation d1 := [0;1;1;1; 0;1;1;0;1; 0;1;1; 0;1;1;0;1].
Notation d2 := [0;1;1;1; 0;1;1;0;1; 0;1;1;0;1; 0;1;1].

Definition LC '(a,b) :=
  0inf <* <[1;0;1;1]^^a <* <[0;0] <* <[1;0;1;1]^^(1+b) <* <[0].

Close Scope sym.

Inductive RC: side->(nat*nat)->Prop :=
| RC_dw r a b:
  RC r (a,1+b) ->
  RC (dw*>r) (3+a,b)
| RC_d0 r a:
  RC r (a,0) ->
  RC (d0*>r) (0,3+a)
| RC_d1 r a:
  RC r (a,0) ->
  RC (d1*>r) (1,2+a)
| RC_d2 r a:
  RC r (a,0) ->
  RC (d2*>r) (2,1+a)
| RC_0:
  RC (0inf)%sym (1,1)
| RC_1:
  RC ([0;1;1]*>0inf)%sym (2,0)
| RC_2:
  RC ([0;1]*>0inf)%sym (0,3)
| RC_3:
  RC ([0;1;1;1; 0;1;1]*>0inf)%sym (1,2)
| RC_4:
  RC ([0;1;1;1; 0;1;1;0;1]*>0inf)%sym (2,1)
| RC_5:
  RC ([0;1;1;1; 0;1;1;0;1; 0;1;1]*>0inf)%sym (3,0)
| RC_6:
  RC ([0;1; 0;1;1;0;1; 0;1;1;0;1]*>0inf)%sym (0,4)
| RC_7:
  RC ([0;1;1;1; 0;1;1;0;1; 0;1;1]*>0inf)%sym (1,3)
| RC_8:
  RC ([0;1;1;1; 0;1;1;0;1; 0;1;1;0;1]*>0inf)%sym (2,2)
| RC_9:
  RC (d2*>0inf)%sym (3,1)
.

Definition nxt '(a,b) :=
  match b with
  | O => (0,1+a)
  | S b => (1+a,b)
  end.

Lemma LInc (a b:nat):
  sideRLs tm' (if b then hLR' else hLR) (LC (a,b)) (LC (nxt (a,b))).
Proof.
  destruct b; cbn; esx.
Qed.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Ltac ssc H := eapply segRLs_sideRLs_concat; [|apply H]; esc.

Ltac ec := econstructor.

Lemma RInc r a b:
  RC r (a,b) ->
  exists r',
  sideRLs tm (if b then hRL' else hRL) r r' /\
  RC r' (nxt (a,b)).
Proof.
  intro HRC.
  remember (a,b) as x.
  gen a b.
  induction HRC; intros; inverts Heqx.
  1-4: destruct (IHHRC _ _ eq_refl) as [r' [I1 I2]]; clear IHHRC.
  - destruct b0.
    + eexists (d0*>r'); split.
      * ssc I1.
      * apply RC_d0,I2.
    + eexists (dw*>r'); split.
      * ssc I1.
      * apply RC_dw,I2.
  - eexists (d1*>r); split.
    + esc.
    + apply RC_d1,HRC.
  - eexists (d2*>r); split.
    + esc.
    + apply RC_d2,HRC.
  - eexists (dw*>r'); split.
    + ssc I1.
    + apply RC_dw,I2.
  - eexists; split; [|solve[ec]]; esc.
  - eexists; split; [|solve[ec]]; esc.
  - eexists; split; [|solve[ec]]; esc.
  - eexists; split; [|solve[ec]]; esc.
  - eexists; split; [|solve[ec]]; esc.
  - eexists; split; [|solve[ec]]; esc.
  - eexists; split; [|solve[ec]]; esc.
  - eexists; split; [|solve[ec]]; esc.
  - eexists; split; [|solve[ec]]; esc.
  - eexists (dw*>0inf)%sym; split.
    + esc.
    + apply RC_dw; ec.
Qed.

Definition S' '(x,r) := LC x {{{ (hL,L) }}} r.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' ((3,1),(d2*>0inf)%sym)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(x,r) => RC r x).
  2: ec.
  intros [[a b] r] HP.
  apply RInc in HP.
  destruct HP as [r' [I1 I2]].
  pose proof (LInc a b) as I3.
  destruct b.
  - eapply sideRLs_1 in I1,I3.
    apply unflip_progress in I3.
    exists (nxt (a,0),r'); split; [|apply I2].
    unfold S'.
    eapply progress_trans.
    1: apply I3.
    apply I1.
  - eapply sideRLs_1 in I1,I3.
    apply unflip_progress in I3.
    exists (nxt (a,S b),r'); split; [|apply I2].
    unfold S'.
    eapply progress_trans.
    1: apply I3.
    apply I1.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC1RF_1RD0LE_0RA0RE_0RA0RB_0RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation hR := (C,<[1;0;1]).
Notation hR' := (B,<[0]).
Notation hL := (E,[0;0;1]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL)].
Notation hLR := [(hL,hR)].
Notation hLR' := [(hL,hR')].

Notation dw := [0;1;1;1; 0;1;1;0;1; 0;1;1;0;1; 0;1;1;0;1].
Notation d0 := [0;1; 0;1;1;0;1; 0;1;1;0;1; 0;1;1;0;1].
Notation d1 := [0;1;1;1; 0;1;1;0;1; 0;1;1; 0;1;1;0;1].
Notation d2 := [0;1;1;1; 0;1;1;0;1; 0;1;1;0;1; 0;1;1].

Definition LC '(a,b) :=
  0inf <* <[1;0;1;1]^^a <* <[0;0] <* <[1;0;1;1]^^(1+b) <* <[0].

Close Scope sym.

Inductive RC: side->(nat*nat)->Prop :=
| RC_dw r a b:
  RC r (a,1+b) ->
  RC (dw*>r) (3+a,b)
| RC_d0 r a:
  RC r (a,0) ->
  RC (d0*>r) (0,3+a)
| RC_d1 r a:
  RC r (a,0) ->
  RC (d1*>r) (1,2+a)
| RC_d2 r a:
  RC r (a,0) ->
  RC (d2*>r) (2,1+a)
| RC_0:
  RC (0inf)%sym (1,1)
| RC_1:
  RC ([0;1;1]*>0inf)%sym (2,0)
| RC_2:
  RC ([0;1]*>0inf)%sym (0,3)
| RC_3:
  RC ([0;1;1;1; 0;1;1]*>0inf)%sym (1,2)
| RC_4:
  RC ([0;1;1;1; 0;1;1;0;1]*>0inf)%sym (2,1)
| RC_5:
  RC ([0;1;1;1; 0;1;1;0;1; 0;1;1]*>0inf)%sym (3,0)
| RC_6:
  RC ([0;1; 0;1;1;0;1; 0;1;1;0;1]*>0inf)%sym (0,4)
| RC_7:
  RC ([0;1;1;1; 0;1;1;0;1; 0;1;1]*>0inf)%sym (1,3)
| RC_8:
  RC ([0;1;1;1; 0;1;1;0;1; 0;1;1;0;1]*>0inf)%sym (2,2)
| RC_9:
  RC (d2*>0inf)%sym (3,1)
.

Definition nxt '(a,b) :=
  match b with
  | O => (0,1+a)
  | S b => (1+a,b)
  end.

Lemma LInc (a b:nat):
  sideRLs tm' (if b then hLR' else hLR) (LC (a,b)) (LC (nxt (a,b))).
Proof.
  destruct b; cbn; esx.
Qed.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Ltac ssc H := eapply segRLs_sideRLs_concat; [|apply H]; esc.

Ltac ec := econstructor.

Lemma RInc r a b:
  RC r (a,b) ->
  exists r',
  sideRLs tm (if b then hRL' else hRL) r r' /\
  RC r' (nxt (a,b)).
Proof.
  intro HRC.
  remember (a,b) as x.
  gen a b.
  induction HRC; intros; inverts Heqx.
  1-4: destruct (IHHRC _ _ eq_refl) as [r' [I1 I2]]; clear IHHRC.
  - destruct b0.
    + eexists (d0*>r'); split.
      * ssc I1.
      * apply RC_d0,I2.
    + eexists (dw*>r'); split.
      * ssc I1.
      * apply RC_dw,I2.
  - eexists (d1*>r); split.
    + esc.
    + apply RC_d1,HRC.
  - eexists (d2*>r); split.
    + esc.
    + apply RC_d2,HRC.
  - eexists (dw*>r'); split.
    + ssc I1.
    + apply RC_dw,I2.
  - eexists; split; [|solve[ec]]; esc.
  - eexists; split; [|solve[ec]]; esc.
  - eexists; split; [|solve[ec]]; esc.
  - eexists; split; [|solve[ec]]; esc.
  - eexists; split; [|solve[ec]]; esc.
  - eexists; split; [|solve[ec]]; esc.
  - eexists; split; [|solve[ec]]; esc.
  - eexists; split; [|solve[ec]]; esc.
  - eexists; split; [|solve[ec]]; esc.
  - eexists (dw*>0inf)%sym; split.
    + esc.
    + apply RC_dw; ec.
Qed.

Definition S' '(x,r) := LC x {{{ (hL,L) }}} r.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' ((3,1),(d2*>0inf)%sym)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(x,r) => RC r x).
  2: ec.
  intros [[a b] r] HP.
  apply RInc in HP.
  destruct HP as [r' [I1 I2]].
  pose proof (LInc a b) as I3.
  destruct b.
  - eapply sideRLs_1 in I1,I3.
    apply unflip_progress in I3.
    exists (nxt (a,0),r'); split; [|apply I2].
    unfold S'.
    eapply progress_trans.
    1: apply I3.
    apply I1.
  - eapply sideRLs_1 in I1,I3.
    apply unflip_progress in I3.
    exists (nxt (a,S b),r'); split; [|apply I2].
    unfold S'.
    eapply progress_trans.
    1: apply I3.
    apply I1.
Qed.

End TM4.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1RB1RA_0RC0RA_1LD0RF_0LE---_0RA0LF_1LE0LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation hR := (C,@nil Sym).
Notation hR' := (F,<[0]).
Notation hR'' := (B,<[0;1;1]).
Notation hL := (D,@nil Sym).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL)].
Notation hRL'' := [(hR'',hL)].
Notation hLR := [(hL,hR)].
Notation hLR' := [(hL,hR')].
Notation hLR'' := [(hL,hR'')].

Notation dw := [1;0;0;0].
Notation d0 := [1;0;0;0;0].
Notation dw' := [1;0;0;1;0;1;0;0].
Notation d0' := [1;0;0;0;1;0;1;0;0].
Notation d1' := [1;0;0;1;0;1;0;0;1].
Notation dW := (dw^^4++dw'^^2).
Notation rh0 := (dw^^2*>0inf).
Notation rh1 := (dW*>rh0).
Notation dA := (d0++dw^^3++dw'^^2).

Close Scope sym.

Inductive RC: side->(nat*nat)->Prop :=
| RC_dW r a b:
  RC r (a,4+b) ->
  RC (dW*>r) (12+a,b)
| RC_dW'_0 r a:
  RC r (4+a,0) ->
  RC ((dw^^4++dw'++d1')*>r) (11,3+a)
| RC_dW'_1 r a:
  RC r (2+a,2) ->
  RC ((dw^^4++dw'++d0')*>r) (10,4+a)
| RC_dW'_2 r a:
  RC r (2+a,2) ->
  RC ((dw^^4++d1'++dw')*>r) (9,5+a)
| RC_dW'_3 r a:
  RC r (a,4) ->
  RC ((dw^^4++d0'++dw')*>r) (8,6+a)
| RC_dW'_4 r a:
  RC r (a,4) ->
  RC (dA*>r) (0,14+a)
| RC_dW' w r a a0 a1:
  RC r (a,4) ->
  segRLs tm (hRL^^(1+a0)) [] w (dw^^4++d0'++dw') ->
  a0+a1=6 ->
  RC (w*>r) (1+a1,7+a0+a)
| RC_0 r a0 a1:
  sideRLs tm (hRL^^a0++hRL'++hRL^^8++hRL'++hRL^^10++hRL'++hRL^^12++hRL'++hRL^^14) r rh1 ->
  a0+a1=4 ->
  RC r (2+a1,a0)
| RC_1 r a0 a1:
  sideRLs tm (hRL^^a0++hRL'++hRL^^10++hRL'++hRL^^12++hRL'++hRL^^14) r rh1 ->
  a0+a1=8 ->
  RC r (a1,a0)
| RC_2 r a0 a1:
  sideRLs tm (hRL^^a0++hRL'++hRL^^12++hRL'++hRL^^14) r rh1 ->
  a0+a1=10 ->
  RC r (a1,a0)
| RC_3 r a0 a1:
  sideRLs tm (hRL^^a0++hRL'++hRL^^14) r rh1 ->
  a0+a1=12 ->
  RC r (a1,a0)
| RC_4 r a0 a1:
  sideRLs tm (hRL^^(1+a0)) r rh1 ->
  a0+a1=13 ->
  RC r (a1,1+a0)
.

Definition nxt '(a,b) :=
  match b with
  | O => (0,2+a)
  | S b => (1+a,b)
  end.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Ltac ssc H := eapply segRLs_sideRLs_concat; [|apply H]; esc.

Ltac ec := econstructor.

Ltac des_v1 H H3 r' I1 I2 :=
  pose proof H3 as HRC;
  eapply H in HRC; [| | trivial]; [|lia];
  destruct HRC as [r' [I1 I2]].

Lemma RInc r a b:
  RC r (a,b) ->
  exists r',
  sideRLs tm (if b then hRL' else hRL) r r' /\
  RC r' (nxt (a,b)).
Proof.
  remember (a+b) as c.
  gen r a b.
  induction c using lt_wf_ind; intros.
  subst c.
  inverts H0.
  - des_v1 H H3 r' I1 I2.
    destruct b.
    + eexists ((d0++dw^^3++dw'^^2)*>r0); split.
      * esc.
      * eapply RC_dW'_4; trivial.
    + eexists (dW*>r'); split.
      * ssc I1.
      * ec; eauto 1.
  - des_v1 H H3 r' I1 I2.
    eexists; split.
    2: ec; eauto 1.
    ssc I1.
  - des_v1 H H3 r' I1 I2.
    des_v1 H I2 r'0 I3 I4.
    eexists; split.
    2: ec; eauto 1.
    eassert (I5:_) by (eapply sideRLs_trans; [apply I1|apply I3]).
    ssc I5.
  - eexists; split.
    2: ec; eauto 1.
    esc.
  - des_v1 H H3 r' I1 I2.
    des_v1 H I2 r'0 I3 I4.
    eexists; split.
    2: ec; eauto 1.
    eassert (I5:_) by (eapply sideRLs_trans; [apply I1|apply I3]).
    ssc I5.
  - eexists ((dw++[1]%sym++dw^^3++dw'^^2)*>r0); split.
    1: esc.
    eapply RC_dW' with (a0:=6); eauto 1.
    esc.
  - destruct a1.
    + cbn in H6; subst.
      eexists; split.
      2: ec; eauto 1.
      eapply segRLs_sideRLs_concat; eauto 1.
      ec.
    + inverts H5.
      2: destruct ls2 as [|[]]; inverts H4.
      eexists; split.
      2: ec; eauto 1; lia.
      eapply @segRLs_sideRLs_concat with (ls2:=[]).
      2: ec.
      ec; eauto 1.
      ec.
  - destruct b.
    + cbn in H5; subst.
      inverts H4.
      eexists; split.
      2: apply RC_1; [eauto 1|lia].
      ec; [eauto 1|ec].
    + inverts H4.
      eexists; split.
      2: apply RC_0; [eauto 1|lia].
      ec; [eauto 1|ec].
  - destruct b.
    + cbn in H5; subst.
      inverts H4.
      eexists; split.
      2: apply RC_2; [eauto 1|lia].
      ec; [eauto 1|ec].
    + inverts H4.
      eexists; split.
      2: apply RC_1; [eauto 1|lia].
      ec; [eauto 1|ec].
  - destruct b.
    + cbn in H5; subst.
      inverts H4.
      eexists; split.
      2: apply RC_3; [eauto 1|lia].
      ec; [eauto 1|ec].
    + inverts H4.
      eexists; split.
      2: apply RC_2; [eauto 1|lia].
      ec; [eauto 1|ec].
  - destruct b.
    + cbn in H5; subst.
      inverts H4.
      eexists; split.
      2: apply RC_4; [eauto 1|lia].
      ec; [eauto 1|ec].
    + inverts H4.
      eexists; split.
      2: apply RC_3; [eauto 1|lia].
      ec; [eauto 1|ec].
  - destruct a0.
    + cbn in H5; subst.
      eexists; split.
      1: apply H4.
      apply RC_dW.
      apply RC_0 with (a1:=0); [esc|trivial].
    + inverts H4.
      eexists; split.
      2: apply RC_4; [eauto 1|lia].
      ec; [eauto 1|ec].
Qed.

Open Scope sym.

Notation du := [1;0;0;1;0;0].
Notation du' := [1;0;0;1;0;1;0;1;0;0].
Notation dU := (du^^4++du'^^2).

Lemma dU_Incs n:
  segRLs tm (hRL''++hRL) (hRL^^((1+n)*4)++hRL''++hRL) (du'^^2++dU^^n) (du'^^2++dU^^n).
Proof.
  induction n.
  1: esc.
  replace (S n) with (n+1) by lia.
  repeat rewrite lpow_add.
  rewrite (app_assoc (du'^^2)).
  eapply segRLs_concat.
  1: apply IHn.
  replace ((1+(n+1))*4) with (((1+n)*4)+4) by lia.
  rewrite lpow_add.
  rewrite <-app_assoc.
  eapply segRLs_trans.
  1: apply segRLs_wall''; esc.
  esc.
Qed.

Lemma lpow_add'_list {A} (a:list A) n1 n2 r:
  a^^n1 ++ a^^n2 ++ r = a^^(n1+n2) ++ r.
Proof.
  rewrite lpow_add,app_assoc; trivial.
Qed.

Lemma lpow_S'_list {A} (a:list A) n r:
  a ++ a^^n ++ r = a^^(S n) ++ r.
Proof.
  rewrite app_assoc; trivial.
Qed.

Ltac rw_list :=
  repeat rewrite <-app_assoc;
  repeat rewrite app_nil_l;
  repeat rewrite app_nil_r;
  repeat rewrite lpow_add'_list;
  repeat rewrite lpow_S'_list.

Lemma LIncs n:
  segRLs tm ((hRL''++hRL)^^6)
  (
  (hRL^^4++hRL')++
  (hRL^^(4+n*4)++hRL')++
  (hRL^^(6+n*4)++hRL')++
  (hRL^^(8+n*4)++hRL')++
  (hRL^^(10+n*4)++hRL')++
  (hRL^^(12+n*4)++hRL')++
  (hRL^^(14+n*4)++hRL')
  )
  (du'^^2++dU^^(2+n)++dA) (du'^^2++dU^^(2+n+1)).
Proof.
  rewrite (lpow_add _ (2+n) 1).
  do 2 rewrite (app_assoc (du'^^2)).
  eapply segRLs_concat.
  1: eapply segRLs_wall''.
  1: apply dU_Incs.
  match goal with
  | |- segRLs _ ?a ?b _ _ =>
  replace a with
    (hRL^^12++hRL^^(n*4)++(hRL''++hRL)++
     hRL^^10++hRL^^(2+n*4)++(hRL''++hRL)++
     hRL^^8++hRL^^(4+n*4)++(hRL''++hRL)++
     hRL^^6++hRL^^(6+n*4)++(hRL''++hRL)++
     hRL^^4++hRL^^(8+n*4)++(hRL''++hRL)++
     hRL^^2++hRL^^(10+n*4)++(hRL''++hRL))
  end.
  2:{
    repeat rewrite (lpow_S _ (hRL^^((3+n)*4)++hRL''++hRL)).
    rw_list.
    flia.
  }
  match goal with
  | |- segRLs _ ?a ?b _ _ =>
  replace b with
  (
  (hRL^^4++hRL')++hRL^^(n*4)++[]++
  (hRL^^4++hRL')++hRL^^(2+n*4)++[]++
  (hRL^^4++hRL')++hRL^^(4+n*4)++[]++
  (hRL^^4++hRL')++hRL^^(6+n*4)++[]++
  (hRL^^4++hRL')++hRL^^(8+n*4)++(hRL^^2)++
  (hRL^^2++hRL')++hRL^^(10+n*4)++(hRL^^4++hRL')
  )
  end.
  2:{
    rw_list.
    flia.
  }

  eapply @segRLs_trans with (w2:=dW); [esc|].
  eapply segRLs_trans; [apply segRLs_wall''; esc|].
  eapply @segRLs_trans with (w2:=(du++d0++dw^^2++dw'^^2)); [esc|].

  eapply @segRLs_trans with (w2:=(du++dw^^3++dw'^^2)); [esc|].
  eapply segRLs_trans; [apply segRLs_wall''; esc|].
  eapply @segRLs_trans with (w2:=(du^^2++d0++dw++dw'^^2)); [esc|].

  eapply @segRLs_trans with (w2:=(du^^2++dw^^2++dw'^^2)); [esc|].
  eapply segRLs_trans; [apply segRLs_wall''; esc|].
  eapply @segRLs_trans with (w2:=(du^^3++d0++dw'^^2)); [esc|].

  eapply @segRLs_trans with (w2:=(du^^3++dw++dw'^^2)); [esc|].
  eapply segRLs_trans; [apply segRLs_wall''; esc|].
  eapply @segRLs_trans with (w2:=(du^^4++d0'++dw')); [esc|].

  eapply @segRLs_trans with (w2:=(du^^4++dw'^^2)); [esc|].
  eapply segRLs_trans; [apply segRLs_wall''; esc|].
  eapply @segRLs_trans with (w2:=(du^^4++du'++d0')); [esc|].

  eapply @segRLs_trans with (w2:=(du^^4++du'++dw')); [esc|].
  eapply segRLs_trans; [apply segRLs_wall''; esc|].
  esc.
Qed.

Close Scope sym.

Lemma RIncs r a b:
  RC r (a,b) ->
  exists r',
  sideRLs tm (hRL^^b++hRL') r r' /\
  RC r' (0,2+b+a).
Proof.
  gen r a.
  induction b; intros.
  - eapply RInc in H.
    destruct H as [r' [I1 I2]].
    eexists; split; eauto 1.
  - eapply RInc in H.
    destruct H as [r' [I1 I2]].
    apply IHb in I2.
    destruct I2 as [r'0 [I3 I4]].
    eexists; split.
    2: applys_eq I4; flia.
    cbn[lpow]; rewrite <-app_assoc.
    eapply sideRLs_trans; eauto 1.
Qed.

Ltac des_v2 H :=
  apply RIncs in H;
  let r':=fresh "r'" in
  let I1:=fresh "Ia" in
  let I2:=fresh "Ib" in
  destruct H as [r' [I1 I2]].

Definition RC' n r := 
  ((du'^^2++dU^^(3+n))++dA) *> r.

Lemma RIncs' r n:
  RC r (n*4+2,4) ->
  exists r',
  sideRLs tm ((hRL''++hRL)^^6) (RC' n r) (RC' (1+n) r') /\
  RC r' ((1+n)*4+2,4).
Proof.
  intros H.
  des_v2 H.
  des_v2 Ib.
  des_v2 Ib0.
  des_v2 Ib.
  des_v2 Ib0.
  des_v2 Ib.
  des_v2 Ib0.
  assert (I:RC r'5 (0,n*4+20)) by (applys_eq Ib; flia).
  inverts I; try lia.
  exists r0; split.
  2: applys_eq H1; flia.
  unfold RC'.
  replace (((du' ^^ 2 ++ dU ^^ (3 + (1 + n))) ++ dA) *> r0)
  with (((du' ^^ 2 ++ dU ^^ (3 + n)) ++ dU^^1) *> dA *> r0).
  2: st; simpl_rotate; trivial.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (LIncs (1+n)).
  1: rw_list.
  1: rewrite <-lpow_add; flia.
  eapply sideRLs_trans; [apply Ia|].
  eapply sideRLs_trans; [applys_eq Ia0; flia|].
  eapply sideRLs_trans; [applys_eq Ia1; flia|].
  eapply sideRLs_trans; [applys_eq Ia2; flia|].
  eapply sideRLs_trans; [applys_eq Ia3; flia|].
  eapply sideRLs_trans; [applys_eq Ia4; flia|].
  applys_eq Ia5; flia.
Qed.

Open Scope sym.

Definition S' '(n,r) := 0inf <* <[1;0;1;0] {{{ (hR'',R) }}} RC' n r.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (O,rh0)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(n,r)=>RC r (n*4+2,4)).
  2:{
    ec; trivial.
    esc.
  }
  intros [n r] HP.
  apply RIncs' in HP.
  destruct HP as [r' [I1 I2]].
  exists (1+n,r'); split; [|apply I2].
  unfold S'.
  eapply @sideRLs_concat_v2 with (ls:=(hLR++hLR'')^^6).
  1: reflexivity.
  1: cbn; congruence.
  1: esc.
  apply I1.
Qed.

End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1RB1RA_0RC0RD_1LD0RF_0LE---_0RA0LF_1LE0LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation hR := (C,@nil Sym).
Notation hR' := (F,<[0]).
Notation hR'' := (B,<[0;1;1]).
Notation hL := (D,@nil Sym).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL)].
Notation hRL'' := [(hR'',hL)].
Notation hLR := [(hL,hR)].
Notation hLR' := [(hL,hR')].
Notation hLR'' := [(hL,hR'')].

Notation dw := [1;0;0;0].
Notation d0 := [1;0;0;0;0].
Notation dw' := [1;0;0;1;0;1;0;0].
Notation d0' := [1;0;0;0;1;0;1;0;0].
Notation d1' := [1;0;0;1;0;1;0;0;1].
Notation dW := (dw^^4++dw'^^2).
Notation rh0 := (dw^^2*>0inf).
Notation rh1 := (dW*>rh0).
Notation dA := (d0++dw^^3++dw'^^2).

Close Scope sym.

Inductive RC: side->(nat*nat)->Prop :=
| RC_dW r a b:
  RC r (a,4+b) ->
  RC (dW*>r) (12+a,b)
| RC_dW'_0 r a:
  RC r (4+a,0) ->
  RC ((dw^^4++dw'++d1')*>r) (11,3+a)
| RC_dW'_1 r a:
  RC r (2+a,2) ->
  RC ((dw^^4++dw'++d0')*>r) (10,4+a)
| RC_dW'_2 r a:
  RC r (2+a,2) ->
  RC ((dw^^4++d1'++dw')*>r) (9,5+a)
| RC_dW'_3 r a:
  RC r (a,4) ->
  RC ((dw^^4++d0'++dw')*>r) (8,6+a)
| RC_dW'_4 r a:
  RC r (a,4) ->
  RC (dA*>r) (0,14+a)
| RC_dW' w r a a0 a1:
  RC r (a,4) ->
  segRLs tm (hRL^^(1+a0)) [] w (dw^^4++d0'++dw') ->
  a0+a1=6 ->
  RC (w*>r) (1+a1,7+a0+a)
| RC_0 r a0 a1:
  sideRLs tm (hRL^^a0++hRL'++hRL^^8++hRL'++hRL^^10++hRL'++hRL^^12++hRL'++hRL^^14) r rh1 ->
  a0+a1=4 ->
  RC r (2+a1,a0)
| RC_1 r a0 a1:
  sideRLs tm (hRL^^a0++hRL'++hRL^^10++hRL'++hRL^^12++hRL'++hRL^^14) r rh1 ->
  a0+a1=8 ->
  RC r (a1,a0)
| RC_2 r a0 a1:
  sideRLs tm (hRL^^a0++hRL'++hRL^^12++hRL'++hRL^^14) r rh1 ->
  a0+a1=10 ->
  RC r (a1,a0)
| RC_3 r a0 a1:
  sideRLs tm (hRL^^a0++hRL'++hRL^^14) r rh1 ->
  a0+a1=12 ->
  RC r (a1,a0)
| RC_4 r a0 a1:
  sideRLs tm (hRL^^(1+a0)) r rh1 ->
  a0+a1=13 ->
  RC r (a1,1+a0)
.

Definition nxt '(a,b) :=
  match b with
  | O => (0,2+a)
  | S b => (1+a,b)
  end.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Ltac ssc H := eapply segRLs_sideRLs_concat; [|apply H]; esc.

Ltac ec := econstructor.

Ltac des_v1 H H3 r' I1 I2 :=
  pose proof H3 as HRC;
  eapply H in HRC; [| | trivial]; [|lia];
  destruct HRC as [r' [I1 I2]].

Lemma RInc r a b:
  RC r (a,b) ->
  exists r',
  sideRLs tm (if b then hRL' else hRL) r r' /\
  RC r' (nxt (a,b)).
Proof.
  remember (a+b) as c.
  gen r a b.
  induction c using lt_wf_ind; intros.
  subst c.
  inverts H0.
  - des_v1 H H3 r' I1 I2.
    destruct b.
    + eexists ((d0++dw^^3++dw'^^2)*>r0); split.
      * esc.
      * eapply RC_dW'_4; trivial.
    + eexists (dW*>r'); split.
      * ssc I1.
      * ec; eauto 1.
  - des_v1 H H3 r' I1 I2.
    eexists; split.
    2: ec; eauto 1.
    ssc I1.
  - des_v1 H H3 r' I1 I2.
    des_v1 H I2 r'0 I3 I4.
    eexists; split.
    2: ec; eauto 1.
    eassert (I5:_) by (eapply sideRLs_trans; [apply I1|apply I3]).
    ssc I5.
  - eexists; split.
    2: ec; eauto 1.
    esc.
  - des_v1 H H3 r' I1 I2.
    des_v1 H I2 r'0 I3 I4.
    eexists; split.
    2: ec; eauto 1.
    eassert (I5:_) by (eapply sideRLs_trans; [apply I1|apply I3]).
    ssc I5.
  - eexists ((dw++[1]%sym++dw^^3++dw'^^2)*>r0); split.
    1: esc.
    eapply RC_dW' with (a0:=6); eauto 1.
    esc.
  - destruct a1.
    + cbn in H6; subst.
      eexists; split.
      2: ec; eauto 1.
      eapply segRLs_sideRLs_concat; eauto 1.
      ec.
    + inverts H5.
      2: destruct ls2 as [|[]]; inverts H4.
      eexists; split.
      2: ec; eauto 1; lia.
      eapply @segRLs_sideRLs_concat with (ls2:=[]).
      2: ec.
      ec; eauto 1.
      ec.
  - destruct b.
    + cbn in H5; subst.
      inverts H4.
      eexists; split.
      2: apply RC_1; [eauto 1|lia].
      ec; [eauto 1|ec].
    + inverts H4.
      eexists; split.
      2: apply RC_0; [eauto 1|lia].
      ec; [eauto 1|ec].
  - destruct b.
    + cbn in H5; subst.
      inverts H4.
      eexists; split.
      2: apply RC_2; [eauto 1|lia].
      ec; [eauto 1|ec].
    + inverts H4.
      eexists; split.
      2: apply RC_1; [eauto 1|lia].
      ec; [eauto 1|ec].
  - destruct b.
    + cbn in H5; subst.
      inverts H4.
      eexists; split.
      2: apply RC_3; [eauto 1|lia].
      ec; [eauto 1|ec].
    + inverts H4.
      eexists; split.
      2: apply RC_2; [eauto 1|lia].
      ec; [eauto 1|ec].
  - destruct b.
    + cbn in H5; subst.
      inverts H4.
      eexists; split.
      2: apply RC_4; [eauto 1|lia].
      ec; [eauto 1|ec].
    + inverts H4.
      eexists; split.
      2: apply RC_3; [eauto 1|lia].
      ec; [eauto 1|ec].
  - destruct a0.
    + cbn in H5; subst.
      eexists; split.
      1: apply H4.
      apply RC_dW.
      apply RC_0 with (a1:=0); [esc|trivial].
    + inverts H4.
      eexists; split.
      2: apply RC_4; [eauto 1|lia].
      ec; [eauto 1|ec].
Qed.

Open Scope sym.

Notation du := [1;0;0;1;0;0].
Notation du' := [1;0;0;1;0;1;0;1;0;0].
Notation dU := (du^^4++du'^^2).

Lemma dU_Incs n:
  segRLs tm (hRL''++hRL) (hRL^^((1+n)*4)++hRL''++hRL) (du'^^2++dU^^n) (du'^^2++dU^^n).
Proof.
  induction n.
  1: esc.
  replace (S n) with (n+1) by lia.
  repeat rewrite lpow_add.
  rewrite (app_assoc (du'^^2)).
  eapply segRLs_concat.
  1: apply IHn.
  replace ((1+(n+1))*4) with (((1+n)*4)+4) by lia.
  rewrite lpow_add.
  rewrite <-app_assoc.
  eapply segRLs_trans.
  1: apply segRLs_wall''; esc.
  esc.
Qed.

Lemma lpow_add'_list {A} (a:list A) n1 n2 r:
  a^^n1 ++ a^^n2 ++ r = a^^(n1+n2) ++ r.
Proof.
  rewrite lpow_add,app_assoc; trivial.
Qed.

Lemma lpow_S'_list {A} (a:list A) n r:
  a ++ a^^n ++ r = a^^(S n) ++ r.
Proof.
  rewrite app_assoc; trivial.
Qed.

Ltac rw_list :=
  repeat rewrite <-app_assoc;
  repeat rewrite app_nil_l;
  repeat rewrite app_nil_r;
  repeat rewrite lpow_add'_list;
  repeat rewrite lpow_S'_list.

Lemma LIncs n:
  segRLs tm ((hRL''++hRL)^^6)
  (
  (hRL^^4++hRL')++
  (hRL^^(4+n*4)++hRL')++
  (hRL^^(6+n*4)++hRL')++
  (hRL^^(8+n*4)++hRL')++
  (hRL^^(10+n*4)++hRL')++
  (hRL^^(12+n*4)++hRL')++
  (hRL^^(14+n*4)++hRL')
  )
  (du'^^2++dU^^(2+n)++dA) (du'^^2++dU^^(2+n+1)).
Proof.
  rewrite (lpow_add _ (2+n) 1).
  do 2 rewrite (app_assoc (du'^^2)).
  eapply segRLs_concat.
  1: eapply segRLs_wall''.
  1: apply dU_Incs.
  match goal with
  | |- segRLs _ ?a ?b _ _ =>
  replace a with
    (hRL^^12++hRL^^(n*4)++(hRL''++hRL)++
     hRL^^10++hRL^^(2+n*4)++(hRL''++hRL)++
     hRL^^8++hRL^^(4+n*4)++(hRL''++hRL)++
     hRL^^6++hRL^^(6+n*4)++(hRL''++hRL)++
     hRL^^4++hRL^^(8+n*4)++(hRL''++hRL)++
     hRL^^2++hRL^^(10+n*4)++(hRL''++hRL))
  end.
  2:{
    repeat rewrite (lpow_S _ (hRL^^((3+n)*4)++hRL''++hRL)).
    rw_list.
    flia.
  }
  match goal with
  | |- segRLs _ ?a ?b _ _ =>
  replace b with
  (
  (hRL^^4++hRL')++hRL^^(n*4)++[]++
  (hRL^^4++hRL')++hRL^^(2+n*4)++[]++
  (hRL^^4++hRL')++hRL^^(4+n*4)++[]++
  (hRL^^4++hRL')++hRL^^(6+n*4)++[]++
  (hRL^^4++hRL')++hRL^^(8+n*4)++(hRL^^2)++
  (hRL^^2++hRL')++hRL^^(10+n*4)++(hRL^^4++hRL')
  )
  end.
  2:{
    rw_list.
    flia.
  }

  eapply @segRLs_trans with (w2:=dW); [esc|].
  eapply segRLs_trans; [apply segRLs_wall''; esc|].
  eapply @segRLs_trans with (w2:=(du++d0++dw^^2++dw'^^2)); [esc|].

  eapply @segRLs_trans with (w2:=(du++dw^^3++dw'^^2)); [esc|].
  eapply segRLs_trans; [apply segRLs_wall''; esc|].
  eapply @segRLs_trans with (w2:=(du^^2++d0++dw++dw'^^2)); [esc|].

  eapply @segRLs_trans with (w2:=(du^^2++dw^^2++dw'^^2)); [esc|].
  eapply segRLs_trans; [apply segRLs_wall''; esc|].
  eapply @segRLs_trans with (w2:=(du^^3++d0++dw'^^2)); [esc|].

  eapply @segRLs_trans with (w2:=(du^^3++dw++dw'^^2)); [esc|].
  eapply segRLs_trans; [apply segRLs_wall''; esc|].
  eapply @segRLs_trans with (w2:=(du^^4++d0'++dw')); [esc|].

  eapply @segRLs_trans with (w2:=(du^^4++dw'^^2)); [esc|].
  eapply segRLs_trans; [apply segRLs_wall''; esc|].
  eapply @segRLs_trans with (w2:=(du^^4++du'++d0')); [esc|].

  eapply @segRLs_trans with (w2:=(du^^4++du'++dw')); [esc|].
  eapply segRLs_trans; [apply segRLs_wall''; esc|].
  esc.
Qed.

Close Scope sym.

Lemma RIncs r a b:
  RC r (a,b) ->
  exists r',
  sideRLs tm (hRL^^b++hRL') r r' /\
  RC r' (0,2+b+a).
Proof.
  gen r a.
  induction b; intros.
  - eapply RInc in H.
    destruct H as [r' [I1 I2]].
    eexists; split; eauto 1.
  - eapply RInc in H.
    destruct H as [r' [I1 I2]].
    apply IHb in I2.
    destruct I2 as [r'0 [I3 I4]].
    eexists; split.
    2: applys_eq I4; flia.
    cbn[lpow]; rewrite <-app_assoc.
    eapply sideRLs_trans; eauto 1.
Qed.

Ltac des_v2 H :=
  apply RIncs in H;
  let r':=fresh "r'" in
  let I1:=fresh "Ia" in
  let I2:=fresh "Ib" in
  destruct H as [r' [I1 I2]].

Definition RC' n r := 
  ((du'^^2++dU^^(3+n))++dA) *> r.

Lemma RIncs' r n:
  RC r (n*4+2,4) ->
  exists r',
  sideRLs tm ((hRL''++hRL)^^6) (RC' n r) (RC' (1+n) r') /\
  RC r' ((1+n)*4+2,4).
Proof.
  intros H.
  des_v2 H.
  des_v2 Ib.
  des_v2 Ib0.
  des_v2 Ib.
  des_v2 Ib0.
  des_v2 Ib.
  des_v2 Ib0.
  assert (I:RC r'5 (0,n*4+20)) by (applys_eq Ib; flia).
  inverts I; try lia.
  exists r0; split.
  2: applys_eq H1; flia.
  unfold RC'.
  replace (((du' ^^ 2 ++ dU ^^ (3 + (1 + n))) ++ dA) *> r0)
  with (((du' ^^ 2 ++ dU ^^ (3 + n)) ++ dU^^1) *> dA *> r0).
  2: st; simpl_rotate; trivial.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (LIncs (1+n)).
  1: rw_list.
  1: rewrite <-lpow_add; flia.
  eapply sideRLs_trans; [apply Ia|].
  eapply sideRLs_trans; [applys_eq Ia0; flia|].
  eapply sideRLs_trans; [applys_eq Ia1; flia|].
  eapply sideRLs_trans; [applys_eq Ia2; flia|].
  eapply sideRLs_trans; [applys_eq Ia3; flia|].
  eapply sideRLs_trans; [applys_eq Ia4; flia|].
  applys_eq Ia5; flia.
Qed.

Open Scope sym.

Definition S' '(n,r) := 0inf <* <[1;0;1;0] {{{ (hR'',R) }}} RC' n r.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (O,rh0)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(n,r)=>RC r (n*4+2,4)).
  2:{
    ec; trivial.
    esc.
  }
  intros [n r] HP.
  apply RIncs' in HP.
  destruct HP as [r' [I1 I2]].
  exists (1+n,r'); split; [|apply I2].
  unfold S'.
  eapply @sideRLs_concat_v2 with (ls:=(hLR++hLR'')^^6).
  1: reflexivity.
  1: cbn; congruence.
  1: esc.
  apply I1.
Qed.

End TM6.


