From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import BinaryCounter_v2.


Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB1LE_0RC0LF_0RD1RB_1LD1LE_0LA0LB_---0LA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation w1 := [0;1;1;1;1;1].
Notation w0 := [0;0;0;1].
Notation w := [0;1].

Inductive RC: nat->nat->side->Prop :=
| RC_O:
  RC 0 0 ([0]*>[1]^^8*>0inf)
| RC_S0 n m k r:
  RC n m r ->
  m+k=n*2 ->
  RC (1+n) (m*2) (w^^k *> w1 *> r)
| RC_S1 n m k r:
  RC n m r ->
  m+k=n*2 ->
  RC (1+n) (m*2+1) (w^^k *> w0 *> r)
.

Notation "l |> r" := (l <* <[0;1] {{B}}> r) (at level 30).
Notation "l <| r" := (l <{{A}} r) (at level 30).
Notation "l <2| r" := (l <{{B}} [0;1] *> r) (at level 30).

Lemma RInc n m r:
  RC n (1+m) r ->
  exists r',
  RC n m r' /\
  (forall l, l |> r -->* l <| r').
Proof.
  gen m r.
  induction n; intros; inverts H.
  - replace m0 with (S(m0-1)) in * by lia.
    epose proof H2 as I0.
    eapply IHn in I0.
    destruct I0 as [r' [I1 I2]].
    apply RC_S1 with (k:=1+k) in I1.
    2: lia.
    eexists; split.
    + applys_eq I1; lia.
    + es; er; follow I2; es.
  - epose proof H2 as I0.
    apply RC_S0 with (k:=k) in I0.
    2: lia.
    eexists; split.
    + applys_eq I0; lia.
    + es.
Qed.

Lemma RIncs n m k r:
  RC n (k+m) r ->
  exists r',
  RC n m r' /\
  (forall l, l <* <[1;0]^^(k*2) <* <[1;0;1;1;1;1] <2| r -->* l <2| w^^k *> w1 *> r').
Proof.
  gen m.
  induction k; intros.
  - eexists; split.
    + apply H.
    + es.
  - rewrite Nat.add_succ_comm in H.
    apply IHk in H.
    destruct H as [r' [I1 I2]].
    apply RInc in I1.
    destruct I1 as [r'0 [I3 I4]].
    eexists; split.
    + apply I3.
    + intro l.
      specialize (I2 (w^^2*>l)).
      replace (S k*2) with (k*2+2) by lia.
      gen I2; st; intro I2.
      follow I2.
      es; er; follow I4; es.
Qed.

Ltac solve_RC :=
match goal with
| |- RC _ ?n _ =>
  ((apply RC_S0 with (m:=n/2); [|reflexivity]) ||
    (apply RC_S1 with (m:=n/2); [|reflexivity]) ||
    apply RC_O); solve_RC
end.

Lemma ROv_0 r:
  RC 2 0 r ->
  exists r',
  RC 3 6 r' /\
  forall l, l <* [1] |> r -->* l <2| r'.
Proof.
  intros.
  inverts H; try lia.
  replace m with O in * by lia.
  cbn in *; subst.
  inverts H2; try lia.
  replace m0 with O in * by lia.
  cbn in *; subst.
  inverts H3.
  eexists; split.
  - solve_RC.
  - es.
Qed.

Lemma ROv n r:
  RC (n+2) 0 r ->
  exists r',
  RC (n+3) (n*2+6) r' /\
  forall l, l <* [1] |> r -->* l <2| r'.
Proof.
  gen r.
  induction n; intros.
  - apply ROv_0,H.
  - inverts H; try lia.
    replace m with O in * by lia.
    change (0*2) with O in *.
    cbn in H3; subst.
    apply IHn in H2.
    destruct H2 as [r' [I1 I2]].
    replace (n*2+6) with ((n+2)+(n+4)) in I1 by lia.
    apply RIncs in I1.
    destruct I1 as [r'0 [I3 I4]].
    eexists; split.
    + apply RC_S0 with (k:=n+2) in I3.
      2: lia.
      applys_eq I3; lia.
    + es; er.
      follow I2.
      specialize (I4 l).
      gen I4; st; simpl_rotate; intro I4.
      follow I4.
      finish.
Qed.

Lemma RIncs' n m r:
  RC n m r ->
  exists r',
  RC n 0 r' /\
  0inf <* [1] |> r -->* 0inf <* [1] |> r'. 
Proof.
  gen r.
  induction m; intros.
  - eexists; split.
    + apply H.
    + finish.
  - apply RInc in H.
    destruct H as [r' [I1 I2]].
    apply IHm in I1.
    destruct I1 as [r'0 [I3 I4]].
    eexists; split.
    + apply I3.
    + follow I2.
      eapply evstep_trans.
      2: apply I4.
      es.
Qed.

Definition S' (r:side) := 0inf <* [1] |> r.

Lemma BigStep n r:
  RC (n+2) 0 r ->
  exists r',
  RC (n+3) 0 r' /\
  S' r -->+ S' r'.
Proof.
  intros H.
  apply ROv in H.
  destruct H as [r' [I1 I2]].
  apply RIncs' in I1.
  destruct I1 as [r'0 [I3 I4]].
  eexists; split.
  - apply I3.
  - unfold S'.
    follow I2.
    eapply progress_evstep_trans.
    2: apply I4.
    es.
Qed.

Lemma init:
  exists r,
  RC 2 0 r /\
  c0 -->* S' r.
Proof.
  eexists; split.
  - solve_RC.
  - unfold S'.
    esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  destruct init as [r' [I1 I2]].
  eapply multistep_nonhalt.
  1: apply I2.
  eapply progress_nonhalt_cond with (P:=fun r=> exists n, RC (n+2) 0 r).
  2: exists O; apply I1.
  intros r [n I3].
  apply BigStep in I3.
  destruct I3 as [r'0 [I4 I5]].
  eexists; split.
  - apply I5.
  - exists (n+1).
    applys_eq I4; lia.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB1LC_0RC1LE_0RD0LF_1LD1LA_---0LA_0RA0LE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation w1 := [0;1;1;1;1;1].
Notation w0 := [0;0;0;1].
Notation w := [0;1].

Inductive RC: nat->nat->side->Prop :=
| RC_O:
  RC 0 0 ([1]^^5*>[0]*>[1]^^4*>0inf)
| RC_S0 n m k r:
  RC n m r ->
  m+k=n ->
  RC (1+n) (m*2) (w^^k *> w1 *> r)
| RC_S1 n m k r:
  RC n m r ->
  m+k=n ->
  RC (1+n) (m*2+1) (w^^k *> w0 *> r)
.

Notation "l |> r" := (l <* <[0;1] {{B}}> r) (at level 30).
Notation "l <| r" := (l <{{A}} r) (at level 30).
Notation "l <2| r" := (l <{{F}} [0;1] *> r) (at level 30).

Lemma RInc n m r:
  RC n (1+m) r ->
  exists r',
  RC n m r' /\
  (forall l, l |> r -->* l <| r').
Proof.
  gen m r.
  induction n; intros; inverts H.
  - replace m0 with (S(m0-1)) in * by lia.
    epose proof H2 as I0.
    eapply IHn in I0.
    destruct I0 as [r' [I1 I2]].
    apply RC_S1 with (k:=1+k) in I1.
    2: lia.
    eexists; split.
    + applys_eq I1; lia.
    + es; er; follow I2; es.
  - epose proof H2 as I0.
    apply RC_S0 with (k:=k) in I0.
    2: lia.
    eexists; split.
    + applys_eq I0; lia.
    + es.
Qed.

Lemma RIncs n m k r:
  RC n (k+m) r ->
  exists r',
  RC n m r' /\
  (forall l, l <* <[1;0]^^(k*2) <* <[1;0;1;1;1;1] <2| r -->* l <2| w^^k *> w1 *> r').
Proof.
  gen m.
  induction k; intros.
  - eexists; split.
    + apply H.
    + es.
  - rewrite Nat.add_succ_comm in H.
    apply IHk in H.
    destruct H as [r' [I1 I2]].
    apply RInc in I1.
    destruct I1 as [r'0 [I3 I4]].
    eexists; split.
    + apply I3.
    + intro l.
      specialize (I2 (w^^2*>l)).
      replace (S k*2) with (k*2+2) by lia.
      gen I2; st; intro I2.
      follow I2.
      es; er; follow I4; es.
Qed.

Ltac solve_RC :=
match goal with
| |- RC _ ?n _ =>
  ((apply RC_S0 with (m:=n/2); [|reflexivity]) ||
    (apply RC_S1 with (m:=n/2); [|reflexivity]) ||
    apply RC_O); solve_RC
end.

Lemma ROv_0 r:
  RC 0 0 r ->
  exists r',
  RC 1 1 r' /\
  forall l, l <* [1] |> r -->* l <2| r'.
Proof.
  intros.
  inverts H; try lia.
  eexists; split.
  - solve_RC.
  - es.
Qed.

Lemma ROv n r:
  RC n 0 r ->
  exists r',
  RC (1+n) (1+n) r' /\
  forall l, l <* [1] |> r -->* l <2| r'.
Proof.
  gen r.
  induction n; intros.
  - apply ROv_0,H.
  - inverts H; try lia.
    replace m with O in * by lia.
    change (0*2) with O in *.
    rewrite Nat.add_0_l in *.
    apply IHn in H2.
    destruct H2 as [r' [I1 I2]].
    divmod2_cases k.
    + replace (1+n'*2) with (n'+(n'+1)) in I1 by lia.
      apply RIncs in I1.
      destruct I1 as [r'0 [I3 I4]].
      eexists; split.
      * apply RC_S0 with (k:=n') in I3.
        2: lia.
        applys_eq I3; lia.
      * es; er.
        follow I2.
        specialize (I4 l).
        gen I4; st; simpl_rotate; intro I4.
        follow I4.
        finish.
    + replace (1+(n'*2+1)) with (n'+(1+(n'+1))) in I1 by lia.
      apply RIncs in I1.
      destruct I1 as [r'0 [I3 I4]].
      apply RInc in I3.
      destruct I3 as [r'1 [I5 I6]].
      eexists; split.
      * apply RC_S1 with (k:=n'+1) in I5.
        2: lia.
        applys_eq I5; lia.
      * es; er.
        follow I2.
        specialize (I4 (w*>l)).
        gen I4; st; simpl_rotate; intro I4.
        follow I4.
        es; er.
        follow I6.
        es.
Qed.

Lemma RIncs' n m r:
  RC n m r ->
  exists r',
  RC n 0 r' /\
  0inf <* [1] |> r -->* 0inf <* [1] |> r'. 
Proof.
  gen r.
  induction m; intros.
  - eexists; split.
    + apply H.
    + finish.
  - apply RInc in H.
    destruct H as [r' [I1 I2]].
    apply IHm in I1.
    destruct I1 as [r'0 [I3 I4]].
    eexists; split.
    + apply I3.
    + follow I2.
      eapply evstep_trans.
      2: apply I4.
      es.
Qed.

Definition S' (r:side) := 0inf <* [1] |> r.

Lemma BigStep n r:
  RC n 0 r ->
  exists r',
  RC (1+n) 0 r' /\
  S' r -->+ S' r'.
Proof.
  intros H.
  apply ROv in H.
  destruct H as [r' [I1 I2]].
  apply RIncs' in I1.
  destruct I1 as [r'0 [I3 I4]].
  eexists; split.
  - apply I3.
  - unfold S'.
    follow I2.
    eapply progress_evstep_trans.
    2: apply I4.
    es.
Qed.

Lemma init:
  exists r,
  RC 1 0 r /\
  c0 -->* S' r.
Proof.
  eexists; split.
  - solve_RC.
  - unfold S'.
    esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  destruct init as [r' [I1 I2]].
  eapply multistep_nonhalt.
  1: apply I2.
  eapply progress_nonhalt_cond with (P:=fun r=> exists n, RC (n) 0 r).
  2: eexists; apply I1.
  intros r [n I3].
  apply BigStep in I3.
  destruct I3 as [r'0 [I4 I5]].
  eexists; split.
  - apply I5.
  - exists (n+1).
    applys_eq I4; lia.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1LB0LB_1RC0RF_0RB0RD_0RE---_1LE0RF_0LA1LF").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation w1 := [1;1;1;1;0].
Notation w0 := [0;1;0].
Notation w := [1;0].

Inductive RC: nat->nat->side->Prop :=
| RC_O:
  RC 0 0 ([1]^^7*>[0]*>[1]^^3*>0inf)
| RC_S0 n m k r:
  RC n m r ->
  m+k=1+n ->
  RC (1+n) (m*2) (w^^k *> w1 *> r)
| RC_S1 n m k r:
  RC n m r ->
  m+k=1+n ->
  RC (1+n) (m*2+1) (w^^k *> w0 *> r)
.

Notation "l |> r" := (l <* <[0;1;0;0] {{E}}> r) (at level 30).
Notation "l <| r" := (l <{{B}} [1;0] *> r) (at level 30).
Notation "l <2| r" := (l <{{B}} [0;0;1;0] *> r) (at level 30).

Lemma RInc n m r:
  RC n (1+m) r ->
  exists r',
  RC n m r' /\
  (forall l, l |> r -->* l <| r').
Proof.
  gen m r.
  induction n; intros; inverts H.
  - replace m0 with (S(m0-1)) in * by lia.
    epose proof H2 as I0.
    eapply IHn in I0.
    destruct I0 as [r' [I1 I2]].
    apply RC_S1 with (k:=1+k) in I1.
    2: lia.
    eexists; split.
    + applys_eq I1; lia.
    + es; er; follow I2; es.
  - epose proof H2 as I0.
    apply RC_S0 with (k:=k) in I0.
    2: lia.
    eexists; split.
    + applys_eq I0; lia.
    + es.
Qed.

Lemma RIncs n m k r:
  RC n (k+m) r ->
  exists r',
  RC n m r' /\
  (forall l, l <* <[1;0]^^(k*2) <* <[1;0;1;1;1] <2| r -->* l <2| w^^k *> w1 *> r').
Proof.
  gen m.
  induction k; intros.
  - eexists; split.
    + apply H.
    + es.
  - rewrite Nat.add_succ_comm in H.
    apply IHk in H.
    destruct H as [r' [I1 I2]].
    apply RInc in I1.
    destruct I1 as [r'0 [I3 I4]].
    eexists; split.
    + apply I3.
    + intro l.
      specialize (I2 ([0;1]^^2*>l)).
      replace (S k*2) with (k*2+2) by lia.
      gen I2; st; intro I2.
      follow I2.
      es; er; follow I4; es.
Qed.

Ltac solve_RC :=
match goal with
| |- RC _ ?n _ =>
  ((apply RC_S0 with (m:=n/2); [|reflexivity]) ||
    (apply RC_S1 with (m:=n/2); [|reflexivity]) ||
    apply RC_O); solve_RC
end.

Lemma ROv_0 r:
  RC 1 0 r ->
  exists r',
  RC 2 3 r' /\
  forall l, l <* [1] |> r -->* l <2| r'.
Proof.
  intros.
  inverts H; try lia.
  replace m with O in * by lia.
  cbn in *; subst.
  inverts H2.
  eexists; split.
  - solve_RC.
  - es.
Qed.

Lemma ROv n r:
  RC (1+n) 0 r ->
  exists r',
  RC (2+n) (3+n) r' /\
  forall l, l <* [1] |> r -->* l <2| r'.
Proof.
  gen r.
  induction n; intros.
  - apply ROv_0,H.
  - inverts H; try lia.
    replace m with O in * by lia.
    cbn in H3; subst.
    change (0*2) with O in *.
    apply IHn in H2.
    destruct H2 as [r' [I1 I2]].
    divmod2_cases n.
    + replace (3+n'*2) with ((1+n')+(n'+2)) in I1 by lia.
      apply RIncs in I1.
      destruct I1 as [r'0 [I3 I4]].
      eexists; split.
      * apply RC_S0 with (k:=1+n') in I3.
        2: lia.
        applys_eq I3; lia.
      * es; er.
        follow I2.
        specialize (I4 l).
        gen I4; st; simpl_rotate; intro I4.
        follow I4.
        finish.
    + replace (3+(n'*2+1)) with ((1+n')+(1+(n'+2))) in I1 by lia.
      apply RIncs in I1.
      destruct I1 as [r'0 [I3 I4]].
      apply RInc in I3.
      destruct I3 as [r'1 [I5 I6]].
      eexists; split.
      * apply RC_S1 with (k:=1+(n'+1)) in I5.
        2: lia.
        applys_eq I5; lia.
      * es; er.
        follow I2.
        specialize (I4 ([0;1]*>l)).
        gen I4; st; simpl_rotate; intro I4.
        follow I4.
        es; er.
        follow I6.
        es.
Qed.

Lemma RIncs' n m r:
  RC n m r ->
  exists r',
  RC n 0 r' /\
  0inf <* [1] |> r -->* 0inf <* [1] |> r'. 
Proof.
  gen r.
  induction m; intros.
  - eexists; split.
    + apply H.
    + finish.
  - apply RInc in H.
    destruct H as [r' [I1 I2]].
    apply IHm in I1.
    destruct I1 as [r'0 [I3 I4]].
    eexists; split.
    + apply I3.
    + follow I2.
      eapply evstep_trans.
      2: apply I4.
      es.
Qed.

Definition S' (r:side) := 0inf <* [1] |> r.

Lemma BigStep n r:
  RC (1+n) 0 r ->
  exists r',
  RC (2+n) 0 r' /\
  S' r -->+ S' r'.
Proof.
  intros H.
  apply ROv in H.
  destruct H as [r' [I1 I2]].
  apply RIncs' in I1.
  destruct I1 as [r'0 [I3 I4]].
  eexists; split.
  - apply I3.
  - unfold S'.
    follow I2.
    eapply progress_evstep_trans.
    2: apply I4.
    es.
Qed.

Lemma init:
  exists r,
  RC 1 0 r /\
  c0 -->* S' r.
Proof.
  eexists; split.
  - solve_RC.
  - unfold S'.
    esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  destruct init as [r' [I1 I2]].
  eapply multistep_nonhalt.
  1: apply I2.
  eapply progress_nonhalt_cond with (P:=fun r=> exists n, RC (1+n) 0 r).
  2: eexists; apply I1.
  intros r [n I3].
  apply BigStep in I3.
  destruct I3 as [r'0 [I4 I5]].
  eexists; split.
  - apply I5.
  - exists (n+1).
    applys_eq I4; lia.
Qed.

End TM3.



