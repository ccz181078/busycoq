From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1LB1LC_1LC0RA_1RD0LA_---1RE_1RB0RF_1RB1RC").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r := 0inf <{{A}} [0] *> [1;0;1;0]^^a *> [1;1;1;0]^^b *> [1;1;0] *> [1;0]^^c *> r.

Definition Inc1 a b c r:
  S1 a b (3+c) r -->*
  S1 (2+a) (1+b) c r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a b (n*3+c) r -->*
  S1 (n*2+a) (n+b) c r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Notation w1 := [1;1;1;0].
Notation w0 := [1;0;1;0].

Inductive RC: side->bool->Prop :=
| RC_0: RC 0inf false
| RC_1: RC ([1;1]*>0inf) true
| RC_w1 r t: RC r t -> RC (w1*>r) t
| RC_w0 r t: RC r t -> RC (w0*>r) t
.

Notation "l |> r" := (l <* <[1;0;1] {{B}}> r) (at level 30).
Notation "l <0| r" := (l <{{A}} [0;1;0] *> r) (at level 30).
Notation "l <1| r" := (l <{{C}} [1;0;1;0] *> r) (at level 30).

Ltac eex := repeat eexists.

Ltac esf := repeat ((es; er)||follow).

Lemma RC_spec r t:
  RC r t ->
  exists r', RC r' (negb t) /\
  forall l, l |> r -->*
  match t with
  | false => l <0| r'
  | true => l <1| r'
  end.
Proof.
  intros H.
  induction H.
  - eex.
    + apply RC_1.
    + es.
  - eex.
    + apply RC_w1,RC_0.
    + es.
  - destruct IHRC as [r' [I1 I2]].
    eex.
    + apply RC_w1,I1.
    + destruct t; esf.
  - destruct IHRC as [r' [I1 I2]].
    eex.
    + apply RC_w0,I1.
    + destruct t; esf.
Qed.

Lemma RC_w1s n r t:
  RC r t ->
  RC (w1^^n*>r) t.
Proof.
  intros.
  induction n.
  - apply H.
  - apply RC_w1,IHn.
Qed.

Lemma RC_w0s n r t:
  RC r t ->
  RC (w0^^n*>r) t.
Proof.
  intros.
  induction n.
  - apply H.
  - apply RC_w0,IHn.
Qed.

Definition S2 n k m k0 m0 k1 r := S1 2 0 n (w1^^k*>w0^^m*>w1^^k0*>w0^^m0*>w1^^k1*>r).

Lemma BigStep001 n k k0 m0 k1 r:
  RC r false ->
  exists r',
  S2 (n*3+0) (2+k) 1 (2+k0) m0 k1 r -->+
  S2 (10+n*4) (1+n) 1 (1+k) 2 k0 r' /\
  RC r' true.
Proof.
  unfold S2.
  intros H.
  apply RC_spec in H.
  destruct H as [r' [H I1]].
  apply RC_spec in H.
  destruct H as [r'0 [H I2]].
  apply RC_spec in H.
  destruct H as [r'1 [H I3]].
  cbn[negb] in I1,I2,I3.
  exists (w0^^m0*>w1^^k1*>r'1); split.
  2: apply RC_w0s,RC_w1s,H.
  follow Incs1.
  esf.
Qed.

Lemma BigStep002 n k k0 m0 k1 r:
  RC r false ->
  exists r',
  S2 (n*3+0) (2+k) 2 (1+k0) m0 k1 r -->+
  S2 (10+n*4) (1+n) 1 (2+k) 1 k0 r' /\
  RC r' false.
Proof.
  unfold S2.
  intros H.
  apply RC_spec in H.
  destruct H as [r' [H I1]].
  apply RC_spec in H.
  destruct H as [r'0 [H I2]].
  cbn[negb] in I1,I2.
  exists (w0^^m0*>w1^^k1*>r'0); split.
  2: apply RC_w0s,RC_w1s,H.
  follow Incs1.
  esf.
Qed.

Lemma BigStep01 n k m k0 m0 k1 r:
  RC r true ->
  exists r',
  S2 (n*3+0) (1+k) m k0 m0 k1 r -->+
  S2 (2+n*4) (1+n) 1 k m k0 r' /\
  RC r' false.
Proof.
  unfold S2.
  intros H.
  apply RC_spec in H.
  destruct H as [r' [H I1]].
  cbn[negb] in I1.
  exists (w0^^m0*>w1^^k1*>r'); split.
  2: apply RC_w0s,RC_w1s,H.
  follow Incs1.
  esf.
Qed.

Lemma BigStep10 n k m k0 m0 k1 r:
  RC r false ->
  exists r',
  S2 (n*3+1) (2+k) m k0 m0 k1 r -->+
  S2 (4+n*4) (1+n) 2 k m k0 r' /\
  RC r' true.
Proof.
  unfold S2.
  intros H.
  apply RC_spec in H.
  destruct H as [r' [H I1]].
  cbn[negb] in I1.
  exists (w0^^m0*>w1^^k1*>r'); split.
  2: apply RC_w0s,RC_w1s,H.
  follow Incs1.
  esf.
Qed.

Lemma BigStep11 n k m k0 m0 k1 r:
  RC r true ->
  exists r',
  S2 (n*3+1) (2+k) m k0 m0 k1 r -->+
  S2 (6+n*4) (1+n) 2 k m k0 r' /\
  RC r' true.
Proof.
  unfold S2.
  intros H.
  apply RC_spec in H.
  destruct H as [r' [H I1]].
  apply RC_spec in H.
  destruct H as [r'0 [H I2]].
  cbn[negb] in I1,I2.
  exists (w0^^m0*>w1^^k1*>r'0); split.
  2: apply RC_w0s,RC_w1s,H.
  follow Incs1.
  esf.
Qed.

Lemma BigStep201 n k k0 m0 k1 r:
  RC r false ->
  exists r',
  S2 (n*3+2) k 1 (2+k0) m0 k1 r -->+
  S2 (8+n*4) (2+n+k) 2 k0 m0 k1 r' /\
  RC r' true.
Proof.
  unfold S2.
  intros H.
  apply RC_spec in H.
  destruct H as [r' [H I1]].
  cbn[negb] in I1.
  exists r'; split.
  2: apply H.
  follow Incs1.
  esf.
Qed.

Lemma BigStep2021 n k k0 k1 r:
  RC r false ->
  exists r',
  S2 (n*3+2) k 2 (2+k0) 1 (2+k1) r -->+
  S2 (18+n*4) (3+n+k) 1 (1+k0) 2 k1 r' /\
  RC r' true.
Proof.
  unfold S2.
  intros H.
  apply RC_spec in H.
  destruct H as [r' [H I1]].
  apply RC_spec in H.
  destruct H as [r'0 [H I2]].
  apply RC_spec in H.
  destruct H as [r'1 [H I3]].
  cbn[negb] in I1,I2,I3.
  exists r'1; split.
  2: apply H.
  follow Incs1.
  esf.
Qed.

Lemma BigStep2022 n k k0 k1 r:
  RC r false ->
  exists r',
  S2 (n*3+2) k 2 (2+k0) 2 (1+k1) r -->+
  S2 (18+n*4) (3+n+k) 1 (2+k0) 1 k1 r' /\
  RC r' false.
Proof.
  unfold S2.
  intros H.
  apply RC_spec in H.
  destruct H as [r' [H I1]].
  apply RC_spec in H.
  destruct H as [r'0 [H I2]].
  cbn[negb] in I1,I2.
  exists r'0; split.
  2: apply H.
  follow Incs1.
  esf.
Qed.

Lemma BigStep211 n k k0 m0 k1 r:
  RC r true ->
  exists r',
  S2 (n*3+2) (1+k) 1 (2+k0) m0 k1 r -->+
  S2 (10+n*4) (3+n+k) 2 k0 m0 k1 r' /\
  RC r' true.
Proof.
  unfold S2.
  intros H.
  apply RC_spec in H.
  destruct H as [r' [H I1]].
  apply RC_spec in H.
  destruct H as [r'0 [H I2]].
  cbn[negb] in I1,I2.
  exists r'0; split.
  2: apply H.
  follow Incs1.
  esf.
Qed.

Lemma BigStep212 n k k0 m0 k1 r:
  RC r true ->
  exists r',
  S2 (n*3+2) (1+k) 2 (1+k0) m0 k1 r -->+
  S2 (10+n*4) (4+n+k) 1 k0 m0 k1 r' /\
  RC r' false.
Proof.
  unfold S2.
  intros H.
  apply RC_spec in H.
  destruct H as [r' [H I1]].
  cbn[negb] in I1.
  exists r'; split.
  2: apply H.
  follow Incs1.
  esf.
Qed.

Lemma init:
  exists r,
  c0 -->*
  S2 82 20 2 12 2 15 r /\
  RC r true.
Proof.
  exists (w0^^2*>w1*>w0^^4*>w1^^4*>[1;1]*>0inf); split.
  2: apply RC_w0s,RC_w1,RC_w0s,RC_w1s,RC_1.
  unfold S2,S1.
  esx.
Qed.

Lemma BigStep2 n k k0 m0 k1 r:
  RC r false ->
  exists r',
  S2 (n*9+2) k 1 (2+(1+k0)) m0 k1 r -->+
  S2 (n*16+18) (7+n*7+k) 1 k0 m0 k1 r' /\
  RC r' false.
Proof.
  intro H.
  eapply (BigStep201 (n*3)) in H.
  destruct H as [r' [I1 H]].
  eapply (BigStep212 (n*4+2) (1+n*3+k)) in H.
  destruct H as [r'0 [I2 H]].
  eexists r'0; split.
  2: auto 1.
  eapply progress_trans.
  - applys_eq I1; flia.
  - applys_eq I2; flia.
Qed.

Close Scope sym.

Inductive Tp := t0|t1|t2|t3|t4|t5.
Definition nxt t :=
match t with
| t0 => t1
| t1 => t2
| t2 => t3
| t3 => t4
| t4 => t5
| t5 => t3
end.

Definition f t :=
match t with
| t0 => 2
| t1 => 8
| t2 => 4
| t3 => 2
| t4 => 1
| t5 => 5
end.

Definition g t :=
match t with
| t0 => 18
| t1 => 16
| t2 => 8
| t3 => 4
| t4 => 2
| t5 => 9
end.

Inductive v9:nat->nat->Tp->Prop :=
| v9_S n i t: v9 n i (nxt t) -> v9 (n*9+f t) (S i) t
| v9_O n t: n mod 9 <> f t -> v9 n 0 t
.

Ltac solve_v9 t :=
    destruct t; unfold nxt,f,g in *; lia.

Lemma v9_spec n i t:
  v9 n (S i) t ->
  v9 (n/9*16+g t) i t.
Proof.
  gen n t.
  induction i; introv Hv9; inverts Hv9.
  - inverts H1.
    apply v9_O.
    solve_v9 t.
  - epose proof H1 as H1'.
    inverts H1'.
    apply IHi in H1.
    apply v9_S in H1.
    applys_eq H1;
    solve_v9 t.
Qed.

Lemma v9_ex n t:
  exists i, v9 n i t.
Proof.
  gen t.
  induction n using lt_wf_ind; intros.
  destruct (Nat.eqb_spec (n mod 9) (f t)).
  - unshelve epose proof (H (n/9) _ (nxt t)) as [i I1].
    1: solve_v9 t.
    apply v9_S in I1.
    eexists.
    applys_eq I1; solve_v9 t.
  - eexists.
    apply v9_O; auto 1.
Qed.

Lemma v9_le n i t:
  v9 n i t ->
  9^i<=n*8+1.
Proof.
  intro H.
  induction H.
  2: lia.
  cbn[Nat.pow].
  solve_v9 t.
Qed.


Definition S' '(n,m,m0,k,k0,k1,r) := S2 n k m k0 m0 k1 r.

Notation n_0 := 200.
Notation k_0 := 1.
Notation k0_0 := 0.
Notation k1_0 := 2.

Inductive P: nat*nat*nat*nat*nat*nat*side->Prop :=
| P_201 n m0 k k0 k1 r i:
  RC r false ->
  (m0=1\/m0=2) ->
  v9 n i t0 ->
  n mod 3 = 2 ->
  k0>=i*3+4+k1_0 ->
  k+k_0>=n/4 ->
  n>=n_0 ->
  P (n,1,m0,k,k0,k1,r)
| P_0 n m' m m0 k k0 k1 r:
  RC r m' ->
  (m=1\/m=2) ->
  (m0=1\/m0=2) ->
  n mod 3 <> 2 ->
  k0>=2+k1_0 ->
  k+k_0>=n/4 ->
  n>=n_0 ->
  P (n,m,m0,k,k0,k1,r)
| P_212 n m0 k k0 k1 r i:
  RC r true ->
  (m0=1\/m0=2) ->
  n mod 3 = 2 ->
  v9 (10+n/3*4) i t0 ->
  k0>=i*3+5+k1_0 ->
  k+k_0>=n/4 ->
  n>=n_0 ->
  P (n,2,m0,k,k0,k1,r)
| P_211 n m0 k k0 k1 r i:
  RC r true ->
  (m0=1\/m0=2) ->
  n mod 3 = 2 ->
  v9 (10+(10+n/3*4)/3*4) i t0 ->
  k0>=i*3+7+k1_0 ->
  k+k_0>=n/4 ->
  n>=n_0 ->
  P (n,1,m0,k,k0,k1,r)
| P_2021 n k k0 k1 r i:
  RC r false ->
  n mod 3 = 2 ->
  v9 (10+(10+(18+n/3*4)/3*4)/3*4) i t0 ->
  k0>=i*3+8+k1_0 ->
  k+k_0>=n/4 ->
  n>=n_0 ->
  k1>=k1_0 ->
  P (n,2,1,k,k0,k1,r)
| P_2022 n k k0 k1 r i:
  RC r false ->
  n mod 3 = 2 ->
  v9 (18+n/3*4) i t0 ->
  k0>=i*3+4+k1_0 ->
  k+k_0>=n/4 ->
  n>=n_0 ->
  k1>=k1_0 ->
  P (n,2,2,k,k0,k1,r)
.

Lemma pow9_ge i:
  9^i>=i*8+1.
Proof.
  induction i; cbn[Nat.pow]; lia.
Qed.

Lemma P_spec n m' m m0 k k0 k1 r:
  RC r m' ->
  (m=1\/m=2) ->
  (m0=1\/m0=2) ->
  k0+k0_0>=n/6 ->
  k+k_0>=n/4 ->
  n>=n_0 ->
  k1>=k1_0 ->
  P (n,m,m0,k,k0,k1,r).
Proof with (eauto 1; try lia).
  intros.
  destruct (Nat.eqb_spec (n mod 3) 2).
  - destruct m'.
    + destruct H0; subst m.
      * epose proof (v9_ex (10+(10+n/3*4)/3*4) t0) as [i I1].
        eapply P_211...
        eapply v9_le in I1.
        destruct i as [|[|[|i]]].
        1-3: lia.
        epose proof (pow9_ge i).
        cbn[Nat.pow] in *.
        lia.
      * epose proof (v9_ex (10+n/3*4) t0) as [i I1].
        eapply P_212...
        eapply v9_le in I1.
        destruct i as [|[|[|i]]].
        1-3: lia.
        epose proof (pow9_ge i).
        cbn[Nat.pow] in *.
        lia.
    + destruct H0; subst m.
      * epose proof (v9_ex n t0) as [i I1].
        eapply P_201...
        eapply v9_le in I1.
        destruct i as [|[|[|i]]].
        1-3: lia.
        epose proof (pow9_ge i).
        cbn[Nat.pow] in *.
        lia.
      * destruct H1; subst m0.
        { epose proof (v9_ex (10+(10+(18+n/3*4)/3*4)/3*4) t0) as [i I1].
          eapply P_2021...
          eapply v9_le in I1.
          destruct i as [|[|[|i]]].
          1-3: lia.
          epose proof (pow9_ge i).
          cbn[Nat.pow] in *.
          lia. }
        { epose proof (v9_ex (18+n/3*4) t0) as [i I1].
          eapply P_2022...
          eapply v9_le in I1.
          destruct i as [|[|[|i]]].
          1-3: lia.
          epose proof (pow9_ge i).
          cbn[Nat.pow] in *.
          lia. }
  - eapply P_0...
Qed.


Ltac rw_sub n c :=
  replace n with (c+(n-c)) in * by lia.

Ltac eex ::=
  eexists (_,_,_,_,_,_,_); split.

Lemma closed x:
  P x ->
  exists x',
  S' x -->+ S' x' /\ P x'.
Proof with (eauto 1; try lia).
  intros HP.
  unfold S'.
  inverts HP.
  - destruct i.
    + inverts H1.
      unfold nxt,f,g in *.
      rw_sub k0 2.
      eapply (BigStep201 (n/3)) in H.
      destruct H as [r' [I1 I2]].
      eex.
      1: applys_eq I1; flia.
      eapply P_0...
    + epose proof H1 as H1'.
      inverts H1'.
      apply v9_spec in H1.
      unfold nxt,f,g in *.
      rw_sub k0 3.
      eapply BigStep2 in H.
      destruct H as [r' [I1 I2]].
      eex.
      1: apply I1.
      destruct (Nat.eqb_spec ((n0*16+18) mod 3) 2) as [E|E].
      * eapply P_201.
        3: applys_eq H1; flia.
        all: idtac...
      * eapply P_0...
  - destruct (n mod 3) as [|[|]] eqn:E.
    3: lia.
    + destruct m'.
      * rw_sub k 1.
        eapply (BigStep01 (n/3)) in H.
        destruct H as [r' [I1 I2]].
        eex.
        1: applys_eq I1; flia.
        eapply P_spec...
      * destruct H0; subst m.
        {
          rw_sub k 2.
          rw_sub k0 2.
          eapply (BigStep001 (n/3)) in H.
          destruct H as [r' [I1 I2]].
          eex.
          1: applys_eq I1; flia.
          eapply P_spec...
        }
        {
          rw_sub k 2.
          rw_sub k0 1.
          eapply (BigStep002 (n/3)) in H.
          destruct H as [r' [I1 I2]].
          eex.
          1: applys_eq I1; flia.
          eapply P_spec...
        }
    + destruct m'.
      * rw_sub k 2.
        eapply (BigStep11 (n/3)) in H.
        destruct H as [r' [I1 I2]].
        eex.
        1: applys_eq I1; flia.
        eapply P_spec...
      * rw_sub k 2.
        eapply (BigStep10 (n/3)) in H.
        destruct H as [r' [I1 I2]].
        eex.
        1: applys_eq I1; flia.
        eapply P_spec...
  - rw_sub k 1.
    rw_sub k0 1.
    eapply (BigStep212 (n/3)) in H.
    destruct H as [r' [I1 I2]].
    eex.
    1: applys_eq I1; flia.
    destruct (Nat.eqb_spec ((10+n/3*4) mod 3) 2) as [E|E].
    + eapply P_201...
    + eapply P_0...
  - rw_sub k 1.
    rw_sub k0 2.
    eapply (BigStep211 (n/3)) in H.
    destruct H as [r' [I1 I2]].
    eex.
    1: applys_eq I1; flia.
    destruct (Nat.eqb_spec ((10+n/3*4) mod 3) 2) as [E|E].
    + eapply P_212...
    + eapply P_0...
  - rw_sub k1 2.
    rw_sub k0 2.
    eapply (BigStep2021 (n/3)) in H.
    destruct H as [r' [I1 I2]].
    eex.
    1: applys_eq I1; flia.
    destruct (Nat.eqb_spec ((18+n/3*4) mod 3) 2) as [E|E].
    + eapply P_211...
    + eapply P_0...
  - rw_sub k1 1.
    rw_sub k0 2.
    eapply (BigStep2022 (n/3)) in H.
    destruct H as [r' [I1 I2]].
    eex.
    1: applys_eq I1; flia.
    destruct (Nat.eqb_spec ((18+n/3*4) mod 3) 2) as [E|E].
    + eapply P_201...
    + eapply P_0...
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  epose proof init as [r0 [I1 I2]].
  eapply (BigStep11 27) in I2.
  destruct I2 as [r1 [I3 I4]].
  eapply (BigStep01 38) in I4.
  destruct I4 as [r2 [I5 I6]].
  eapply (BigStep10 51) in I6.
  destruct I6 as [r3 [I7 I8]].
  eapply multistep_nonhalt with (c':=S' (_,_,_,_,_,_,_)).
  1:{
    follow I1.
    follow100 I3.
    follow100 I5.
    follow100 I7.
    unfold S'.
    finish.
  }
  eapply progress_nonhalt_cond with (P:=P).
  - apply closed.
  - eapply P_spec; eauto 1; try lia.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB1RC_1LC0RD_1RE0LD_1LB1LC_---1RF_1RB0RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r := 0inf <{{D}} [0] *> [1;0;1;0]^^a *> [1;1;1;0]^^b *> [1;1;0] *> [1;0]^^c *> r.

Definition Inc1 a b c r:
  S1 a b (3+c) r -->*
  S1 (2+a) (1+b) c r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a b (n*3+c) r -->*
  S1 (n*2+a) (n+b) c r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Notation w1 := [1;1;1;0].
Notation w0 := [1;0;1;0].

Inductive RC: side->bool->Prop :=
| RC_0: RC 0inf false
| RC_1: RC ([1;1]*>0inf) true
| RC_w1 r t: RC r t -> RC (w1*>r) t
| RC_w0 r t: RC r t -> RC (w0*>r) t
.

Notation "l |> r" := (l <* <[1;0;1] {{B}}> r) (at level 30).
Notation "l <0| r" := (l <{{D}} [0;1;0] *> r) (at level 30).
Notation "l <1| r" := (l <{{C}} [1;0;1;0] *> r) (at level 30).

Ltac eex := repeat eexists.

Ltac esf := repeat ((es; er)||follow).

Lemma RC_spec r t:
  RC r t ->
  exists r', RC r' (negb t) /\
  forall l, l |> r -->*
  match t with
  | false => l <0| r'
  | true => l <1| r'
  end.
Proof.
  intros H.
  induction H.
  - eex.
    + apply RC_1.
    + es.
  - eex.
    + apply RC_w1,RC_0.
    + es.
  - destruct IHRC as [r' [I1 I2]].
    eex.
    + apply RC_w1,I1.
    + destruct t; esf.
  - destruct IHRC as [r' [I1 I2]].
    eex.
    + apply RC_w0,I1.
    + destruct t; esf.
Qed.

Lemma RC_w1s n r t:
  RC r t ->
  RC (w1^^n*>r) t.
Proof.
  intros.
  induction n.
  - apply H.
  - apply RC_w1,IHn.
Qed.

Lemma RC_w0s n r t:
  RC r t ->
  RC (w0^^n*>r) t.
Proof.
  intros.
  induction n.
  - apply H.
  - apply RC_w0,IHn.
Qed.

Definition S2 n k m k0 m0 k1 r := S1 2 0 n (w1^^k*>w0^^m*>w1^^k0*>w0^^m0*>w1^^k1*>r).

Lemma BigStep001 n k k0 m0 k1 r:
  RC r false ->
  exists r',
  S2 (n*3+0) (2+k) 1 (2+k0) m0 k1 r -->+
  S2 (10+n*4) (1+n) 1 (1+k) 2 k0 r' /\
  RC r' true.
Proof.
  unfold S2.
  intros H.
  apply RC_spec in H.
  destruct H as [r' [H I1]].
  apply RC_spec in H.
  destruct H as [r'0 [H I2]].
  apply RC_spec in H.
  destruct H as [r'1 [H I3]].
  cbn[negb] in I1,I2,I3.
  exists (w0^^m0*>w1^^k1*>r'1); split.
  2: apply RC_w0s,RC_w1s,H.
  follow Incs1.
  esf.
Qed.

Lemma BigStep002 n k k0 m0 k1 r:
  RC r false ->
  exists r',
  S2 (n*3+0) (2+k) 2 (1+k0) m0 k1 r -->+
  S2 (10+n*4) (1+n) 1 (2+k) 1 k0 r' /\
  RC r' false.
Proof.
  unfold S2.
  intros H.
  apply RC_spec in H.
  destruct H as [r' [H I1]].
  apply RC_spec in H.
  destruct H as [r'0 [H I2]].
  cbn[negb] in I1,I2.
  exists (w0^^m0*>w1^^k1*>r'0); split.
  2: apply RC_w0s,RC_w1s,H.
  follow Incs1.
  esf.
Qed.

Lemma BigStep01 n k m k0 m0 k1 r:
  RC r true ->
  exists r',
  S2 (n*3+0) (1+k) m k0 m0 k1 r -->+
  S2 (2+n*4) (1+n) 1 k m k0 r' /\
  RC r' false.
Proof.
  unfold S2.
  intros H.
  apply RC_spec in H.
  destruct H as [r' [H I1]].
  cbn[negb] in I1.
  exists (w0^^m0*>w1^^k1*>r'); split.
  2: apply RC_w0s,RC_w1s,H.
  follow Incs1.
  esf.
Qed.

Lemma BigStep10 n k m k0 m0 k1 r:
  RC r false ->
  exists r',
  S2 (n*3+1) (2+k) m k0 m0 k1 r -->+
  S2 (4+n*4) (1+n) 2 k m k0 r' /\
  RC r' true.
Proof.
  unfold S2.
  intros H.
  apply RC_spec in H.
  destruct H as [r' [H I1]].
  cbn[negb] in I1.
  exists (w0^^m0*>w1^^k1*>r'); split.
  2: apply RC_w0s,RC_w1s,H.
  follow Incs1.
  esf.
Qed.

Lemma BigStep11 n k m k0 m0 k1 r:
  RC r true ->
  exists r',
  S2 (n*3+1) (2+k) m k0 m0 k1 r -->+
  S2 (6+n*4) (1+n) 2 k m k0 r' /\
  RC r' true.
Proof.
  unfold S2.
  intros H.
  apply RC_spec in H.
  destruct H as [r' [H I1]].
  apply RC_spec in H.
  destruct H as [r'0 [H I2]].
  cbn[negb] in I1,I2.
  exists (w0^^m0*>w1^^k1*>r'0); split.
  2: apply RC_w0s,RC_w1s,H.
  follow Incs1.
  esf.
Qed.

Lemma BigStep201 n k k0 m0 k1 r:
  RC r false ->
  exists r',
  S2 (n*3+2) k 1 (2+k0) m0 k1 r -->+
  S2 (8+n*4) (2+n+k) 2 k0 m0 k1 r' /\
  RC r' true.
Proof.
  unfold S2.
  intros H.
  apply RC_spec in H.
  destruct H as [r' [H I1]].
  cbn[negb] in I1.
  exists r'; split.
  2: apply H.
  follow Incs1.
  esf.
Qed.

Lemma BigStep2021 n k k0 k1 r:
  RC r false ->
  exists r',
  S2 (n*3+2) k 2 (2+k0) 1 (2+k1) r -->+
  S2 (18+n*4) (3+n+k) 1 (1+k0) 2 k1 r' /\
  RC r' true.
Proof.
  unfold S2.
  intros H.
  apply RC_spec in H.
  destruct H as [r' [H I1]].
  apply RC_spec in H.
  destruct H as [r'0 [H I2]].
  apply RC_spec in H.
  destruct H as [r'1 [H I3]].
  cbn[negb] in I1,I2,I3.
  exists r'1; split.
  2: apply H.
  follow Incs1.
  esf.
Qed.

Lemma BigStep2022 n k k0 k1 r:
  RC r false ->
  exists r',
  S2 (n*3+2) k 2 (2+k0) 2 (1+k1) r -->+
  S2 (18+n*4) (3+n+k) 1 (2+k0) 1 k1 r' /\
  RC r' false.
Proof.
  unfold S2.
  intros H.
  apply RC_spec in H.
  destruct H as [r' [H I1]].
  apply RC_spec in H.
  destruct H as [r'0 [H I2]].
  cbn[negb] in I1,I2.
  exists r'0; split.
  2: apply H.
  follow Incs1.
  esf.
Qed.

Lemma BigStep211 n k k0 m0 k1 r:
  RC r true ->
  exists r',
  S2 (n*3+2) (1+k) 1 (2+k0) m0 k1 r -->+
  S2 (10+n*4) (3+n+k) 2 k0 m0 k1 r' /\
  RC r' true.
Proof.
  unfold S2.
  intros H.
  apply RC_spec in H.
  destruct H as [r' [H I1]].
  apply RC_spec in H.
  destruct H as [r'0 [H I2]].
  cbn[negb] in I1,I2.
  exists r'0; split.
  2: apply H.
  follow Incs1.
  esf.
Qed.

Lemma BigStep212 n k k0 m0 k1 r:
  RC r true ->
  exists r',
  S2 (n*3+2) (1+k) 2 (1+k0) m0 k1 r -->+
  S2 (10+n*4) (4+n+k) 1 k0 m0 k1 r' /\
  RC r' false.
Proof.
  unfold S2.
  intros H.
  apply RC_spec in H.
  destruct H as [r' [H I1]].
  cbn[negb] in I1.
  exists r'; split.
  2: apply H.
  follow Incs1.
  esf.
Qed.

Lemma init:
  exists r,
  c0 -->*
  S2 90 22 2 13 1 16 r /\
  RC r true.
Proof.
  exists (w0*>w1*>w0*>w1*>w0*>w1^^5*>[1;1]*>0inf); split.
  2: apply RC_w0,RC_w1,RC_w0,RC_w1,RC_w0,RC_w1s,RC_1.
  unfold S2,S1.
  esx.
Qed.

Lemma BigStep2 n k k0 m0 k1 r:
  RC r false ->
  exists r',
  S2 (n*9+2) k 1 (2+(1+k0)) m0 k1 r -->+
  S2 (n*16+18) (7+n*7+k) 1 k0 m0 k1 r' /\
  RC r' false.
Proof.
  intro H.
  eapply (BigStep201 (n*3)) in H.
  destruct H as [r' [I1 H]].
  eapply (BigStep212 (n*4+2) (1+n*3+k)) in H.
  destruct H as [r'0 [I2 H]].
  eexists r'0; split.
  2: auto 1.
  eapply progress_trans.
  - applys_eq I1; flia.
  - applys_eq I2; flia.
Qed.

Close Scope sym.

Inductive Tp := t0|t1|t2|t3|t4|t5.
Definition nxt t :=
match t with
| t0 => t1
| t1 => t2
| t2 => t3
| t3 => t4
| t4 => t5
| t5 => t3
end.

Definition f t :=
match t with
| t0 => 2
| t1 => 8
| t2 => 4
| t3 => 2
| t4 => 1
| t5 => 5
end.

Definition g t :=
match t with
| t0 => 18
| t1 => 16
| t2 => 8
| t3 => 4
| t4 => 2
| t5 => 9
end.

Inductive v9:nat->nat->Tp->Prop :=
| v9_S n i t: v9 n i (nxt t) -> v9 (n*9+f t) (S i) t
| v9_O n t: n mod 9 <> f t -> v9 n 0 t
.

Ltac solve_v9 t :=
    destruct t; unfold nxt,f,g in *; lia.

Lemma v9_spec n i t:
  v9 n (S i) t ->
  v9 (n/9*16+g t) i t.
Proof.
  gen n t.
  induction i; introv Hv9; inverts Hv9.
  - inverts H1.
    apply v9_O.
    solve_v9 t.
  - epose proof H1 as H1'.
    inverts H1'.
    apply IHi in H1.
    apply v9_S in H1.
    applys_eq H1;
    solve_v9 t.
Qed.

Lemma v9_ex n t:
  exists i, v9 n i t.
Proof.
  gen t.
  induction n using lt_wf_ind; intros.
  destruct (Nat.eqb_spec (n mod 9) (f t)).
  - unshelve epose proof (H (n/9) _ (nxt t)) as [i I1].
    1: solve_v9 t.
    apply v9_S in I1.
    eexists.
    applys_eq I1; solve_v9 t.
  - eexists.
    apply v9_O; auto 1.
Qed.

Lemma v9_le n i t:
  v9 n i t ->
  9^i<=n*8+1.
Proof.
  intro H.
  induction H.
  2: lia.
  cbn[Nat.pow].
  solve_v9 t.
Qed.


Definition S' '(n,m,m0,k,k0,k1,r) := S2 n k m k0 m0 k1 r.

Notation n_0 := 200.
Notation k_0 := 1.
Notation k0_0 := 0.
Notation k1_0 := 2.

Inductive P: nat*nat*nat*nat*nat*nat*side->Prop :=
| P_201 n m0 k k0 k1 r i:
  RC r false ->
  (m0=1\/m0=2) ->
  v9 n i t0 ->
  n mod 3 = 2 ->
  k0>=i*3+4+k1_0 ->
  k+k_0>=n/4 ->
  n>=n_0 ->
  P (n,1,m0,k,k0,k1,r)
| P_0 n m' m m0 k k0 k1 r:
  RC r m' ->
  (m=1\/m=2) ->
  (m0=1\/m0=2) ->
  n mod 3 <> 2 ->
  k0>=2+k1_0 ->
  k+k_0>=n/4 ->
  n>=n_0 ->
  P (n,m,m0,k,k0,k1,r)
| P_212 n m0 k k0 k1 r i:
  RC r true ->
  (m0=1\/m0=2) ->
  n mod 3 = 2 ->
  v9 (10+n/3*4) i t0 ->
  k0>=i*3+5+k1_0 ->
  k+k_0>=n/4 ->
  n>=n_0 ->
  P (n,2,m0,k,k0,k1,r)
| P_211 n m0 k k0 k1 r i:
  RC r true ->
  (m0=1\/m0=2) ->
  n mod 3 = 2 ->
  v9 (10+(10+n/3*4)/3*4) i t0 ->
  k0>=i*3+7+k1_0 ->
  k+k_0>=n/4 ->
  n>=n_0 ->
  P (n,1,m0,k,k0,k1,r)
| P_2021 n k k0 k1 r i:
  RC r false ->
  n mod 3 = 2 ->
  v9 (10+(10+(18+n/3*4)/3*4)/3*4) i t0 ->
  k0>=i*3+8+k1_0 ->
  k+k_0>=n/4 ->
  n>=n_0 ->
  k1>=k1_0 ->
  P (n,2,1,k,k0,k1,r)
| P_2022 n k k0 k1 r i:
  RC r false ->
  n mod 3 = 2 ->
  v9 (18+n/3*4) i t0 ->
  k0>=i*3+4+k1_0 ->
  k+k_0>=n/4 ->
  n>=n_0 ->
  k1>=k1_0 ->
  P (n,2,2,k,k0,k1,r)
.

Lemma pow9_ge i:
  9^i>=i*8+1.
Proof.
  induction i; cbn[Nat.pow]; lia.
Qed.

Lemma P_spec n m' m m0 k k0 k1 r:
  RC r m' ->
  (m=1\/m=2) ->
  (m0=1\/m0=2) ->
  k0+k0_0>=n/6 ->
  k+k_0>=n/4 ->
  n>=n_0 ->
  k1>=k1_0 ->
  P (n,m,m0,k,k0,k1,r).
Proof with (eauto 1; try lia).
  intros.
  destruct (Nat.eqb_spec (n mod 3) 2).
  - destruct m'.
    + destruct H0; subst m.
      * epose proof (v9_ex (10+(10+n/3*4)/3*4) t0) as [i I1].
        eapply P_211...
        eapply v9_le in I1.
        destruct i as [|[|[|i]]].
        1-3: lia.
        epose proof (pow9_ge i).
        cbn[Nat.pow] in *.
        lia.
      * epose proof (v9_ex (10+n/3*4) t0) as [i I1].
        eapply P_212...
        eapply v9_le in I1.
        destruct i as [|[|[|i]]].
        1-3: lia.
        epose proof (pow9_ge i).
        cbn[Nat.pow] in *.
        lia.
    + destruct H0; subst m.
      * epose proof (v9_ex n t0) as [i I1].
        eapply P_201...
        eapply v9_le in I1.
        destruct i as [|[|[|i]]].
        1-3: lia.
        epose proof (pow9_ge i).
        cbn[Nat.pow] in *.
        lia.
      * destruct H1; subst m0.
        { epose proof (v9_ex (10+(10+(18+n/3*4)/3*4)/3*4) t0) as [i I1].
          eapply P_2021...
          eapply v9_le in I1.
          destruct i as [|[|[|i]]].
          1-3: lia.
          epose proof (pow9_ge i).
          cbn[Nat.pow] in *.
          lia. }
        { epose proof (v9_ex (18+n/3*4) t0) as [i I1].
          eapply P_2022...
          eapply v9_le in I1.
          destruct i as [|[|[|i]]].
          1-3: lia.
          epose proof (pow9_ge i).
          cbn[Nat.pow] in *.
          lia. }
  - eapply P_0...
Qed.


Ltac rw_sub n c :=
  replace n with (c+(n-c)) in * by lia.

Ltac eex ::=
  eexists (_,_,_,_,_,_,_); split.

Lemma closed x:
  P x ->
  exists x',
  S' x -->+ S' x' /\ P x'.
Proof with (eauto 1; try lia).
  intros HP.
  unfold S'.
  inverts HP.
  - destruct i.
    + inverts H1.
      unfold nxt,f,g in *.
      rw_sub k0 2.
      eapply (BigStep201 (n/3)) in H.
      destruct H as [r' [I1 I2]].
      eex.
      1: applys_eq I1; flia.
      eapply P_0...
    + epose proof H1 as H1'.
      inverts H1'.
      apply v9_spec in H1.
      unfold nxt,f,g in *.
      rw_sub k0 3.
      eapply BigStep2 in H.
      destruct H as [r' [I1 I2]].
      eex.
      1: apply I1.
      destruct (Nat.eqb_spec ((n0*16+18) mod 3) 2) as [E|E].
      * eapply P_201.
        3: applys_eq H1; flia.
        all: idtac...
      * eapply P_0...
  - destruct (n mod 3) as [|[|]] eqn:E.
    3: lia.
    + destruct m'.
      * rw_sub k 1.
        eapply (BigStep01 (n/3)) in H.
        destruct H as [r' [I1 I2]].
        eex.
        1: applys_eq I1; flia.
        eapply P_spec...
      * destruct H0; subst m.
        {
          rw_sub k 2.
          rw_sub k0 2.
          eapply (BigStep001 (n/3)) in H.
          destruct H as [r' [I1 I2]].
          eex.
          1: applys_eq I1; flia.
          eapply P_spec...
        }
        {
          rw_sub k 2.
          rw_sub k0 1.
          eapply (BigStep002 (n/3)) in H.
          destruct H as [r' [I1 I2]].
          eex.
          1: applys_eq I1; flia.
          eapply P_spec...
        }
    + destruct m'.
      * rw_sub k 2.
        eapply (BigStep11 (n/3)) in H.
        destruct H as [r' [I1 I2]].
        eex.
        1: applys_eq I1; flia.
        eapply P_spec...
      * rw_sub k 2.
        eapply (BigStep10 (n/3)) in H.
        destruct H as [r' [I1 I2]].
        eex.
        1: applys_eq I1; flia.
        eapply P_spec...
  - rw_sub k 1.
    rw_sub k0 1.
    eapply (BigStep212 (n/3)) in H.
    destruct H as [r' [I1 I2]].
    eex.
    1: applys_eq I1; flia.
    destruct (Nat.eqb_spec ((10+n/3*4) mod 3) 2) as [E|E].
    + eapply P_201...
    + eapply P_0...
  - rw_sub k 1.
    rw_sub k0 2.
    eapply (BigStep211 (n/3)) in H.
    destruct H as [r' [I1 I2]].
    eex.
    1: applys_eq I1; flia.
    destruct (Nat.eqb_spec ((10+n/3*4) mod 3) 2) as [E|E].
    + eapply P_212...
    + eapply P_0...
  - rw_sub k1 2.
    rw_sub k0 2.
    eapply (BigStep2021 (n/3)) in H.
    destruct H as [r' [I1 I2]].
    eex.
    1: applys_eq I1; flia.
    destruct (Nat.eqb_spec ((18+n/3*4) mod 3) 2) as [E|E].
    + eapply P_211...
    + eapply P_0...
  - rw_sub k1 1.
    rw_sub k0 2.
    eapply (BigStep2022 (n/3)) in H.
    destruct H as [r' [I1 I2]].
    eex.
    1: applys_eq I1; flia.
    destruct (Nat.eqb_spec ((18+n/3*4) mod 3) 2) as [E|E].
    + eapply P_201...
    + eapply P_0...
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  epose proof init as [r0 [I1 I2]].
  eapply (BigStep01 30) in I2.
  destruct I2 as [r1 [I3 I4]].
  eapply (BigStep201 40) in I4.
  destruct I4 as [r2 [I5 I6]].
  eapply (BigStep01 56) in I6.
  destruct I6 as [r3 [I7 I8]].
  eapply multistep_nonhalt with (c':=S' (_,_,_,_,_,_,_)).
  1:{
    follow I1.
    follow100 I3.
    follow100 I5.
    follow100 I7.
    unfold S'.
    finish.
  }
  eapply progress_nonhalt_cond with (P:=P).
  - apply closed.
  - eapply P_spec; eauto 1; try lia.
Qed.

End TM2.


