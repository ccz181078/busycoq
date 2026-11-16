From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import BinaryCounter_v2 DivModCases Longitudinal.

Definition tm := Eval compute in (TM_from_str "1RB1RF_1RC0RA_1LD1RC_1LE0LE_0RA0LD_0RB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (C,<[0;1;1]).
Notation hL := (E,[1;0;0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation "l |> r" := (l {{{ (hR,R) }}} r) (at level 30).
Notation "l <| r" := (l {{{ (hL,L) }}} r) (at level 30).

Notation d0 := [0].
Notation d1 := [1].

Definition RC n := BinInc d1 n.

Definition LC a b := 0inf <* <[0;1]^^a <* <[0] <* <[0;1]^^b.

Inductive v2: nat->nat->Prop :=
| v2_O x: v2 (x*2) 0
| v2_S x i: v2 x i -> v2 (x*2+1) (S i).

Lemma v2_spec n i:
  v2 n i ->
  exists x, n = (x*2+1)*2^i-1.
Proof.
  intros H.
  induction H.
  - exists x; lia.
  - destruct IHv2 as [x0 I1].
    exists x0; cbn[Nat.pow]; lia.
Qed.

Lemma RInc n i:
  v2 n i ->
  sideRLs tm hRL (RC n) (RC (n+1+(i mod 2))).
Proof.
  unfold RC.
  intros Hv2.
  econstructor.
  2: constructor.
  intro l.
  apply v2_spec in Hv2.
  destruct Hv2 as [x I].
  subst.
  rewrite Nat.sub_add by lia.
  destruct (mod2 i); subst i.
  - replace ((a*2) mod 2) with O by lia.
    rewrite Nat.add_0_r.
    rw_Bin.
    es.
  - replace ((1+a*2) mod 2) with 1%nat by lia.
    rewrite (Nat.add_comm 1 (a*2)).
    rw_Bin.
    rewrite Nat.pow_add_r,Nat.mul_assoc.
    rw_Bin.
    es.
Qed.

Inductive step1: nat->nat->Prop :=
| step1_intro n i:
  v2 n i ->
  step1 n (n+1+(i mod 2)).

Inductive nstep: nat->nat->nat->Prop :=
| nstep_O x: nstep 0 x x
| nstep_S n x x0 x1:
  step1 x x0 ->
  nstep n x0 x1 ->
  nstep (S n) x x1.

Lemma nstep_spec n x x':
  nstep n x x' ->
  sideRLs tm (hRL^^n) (RC x) (RC x').
Proof.
  intros H.
  induction H.
  - esx.
  - cbn[lpow].
    eapply sideRLs_trans.
    2: apply IHnstep.
    inverts H.
    apply RInc; auto 1.
Qed.

Local Hint Constructors nstep : core.

Lemma nstep_step1 n x x0 x1:
  nstep n x x0 ->
  step1 x0 x1 ->
  nstep (S n) x x1.
Proof.
  intro H.
  induction H; eauto.
Qed.

Definition tm' := flip tm.

Lemma LIncs n a:
  sideRLs tm' (hLR^^n) (LC 0 (n+a)) (LC n a).
Proof.
  gen a.
  induction n; intros.
  - esx.
  - eapply sideRLs_trans_S.
    1: applys_eq (IHn (S a)); flia.
    esx.
Qed.

Definition S1 '(a,c) := LC 0 a |> RC c.

Lemma BigStep a c c':
  nstep (1+a) c (c'*2+1) ->
  S1 (a,c) -->+
  S1 (1+a,c').
Proof.
  replace (nstep (1+a)) with (nstep (a+1)) by flia.
  unfold S1.
  intros I1.
  apply nstep_spec in I1.
  epose proof (sideRLs_concat) as I.
  erewrite (lrcons_lpow1 _ _ (a+1)) in I by lia.
  rewrite Nat.add_sub in I.
  epose proof (I (LIncs _ 0) I1) as I.
  eapply progress_trans.
  1: applys_eq I; flia.
  unfold RC.
  rw_Bin.
  es.
Qed.

Lemma init:
  c0 -->*
  S1 (6,7)%nat.
Proof.
  esx.
Qed.

Inductive WF: nat*nat->Prop :=
| WF_000 a n i:
  v2 n (3+i*2) ->
  nstep (1+a) (n+1) ((n+2)*2+1) ->
  WF (a,n+1)
| WF_001 a n i:
  v2 n (3+i*2) ->
  nstep (1+a) (n+2) ((n+3)*2+1) ->
  WF (a,n+2)
| WF_010 a n i:
  v2 n (3+i*2) ->
  nstep (1+a) (n+3) ((n+4)*2+1) ->
  WF (a,n+3)
| WF_011 a n:
  nstep (1+a) (n*8+3) ((n*8+5)*2+1) ->
  WF (a,n*8+3)
| WF_101 a n:
  nstep (1+a) (n*8+5) ((n*8+7)*2+1) ->
  WF (a,n*8+5)
| WF_111 a n i:
  v2 n (3+i*2) ->
  nstep (1+a) n ((n+1)*2+1) ->
  WF (a,n)
| WF_111' a n i:
  v2 n (4+i*2) ->
  nstep (1+a) n ((n+2)*2+1) ->
  WF (a,n)
| WF_001' a n i:
  v2 n (4+i*2) ->
  nstep (1+a) (n+2) ((n+4)*2+1) ->
  WF (a,n+2)
.

Ltac solve_v2 :=
match goal with
| |- v2 ?n (S ?i) => applys_eq (v2_S (n/2) i); solve_v2
| |- v2 ?n O => applys_eq (v2_O (n/2)); solve_v2
| _ => try lia
end.

Ltac ec := econstructor.

Ltac rlia a b := replace a with b in * by lia.

Lemma v2_unique [n i i']:
  v2 n i ->
  v2 n i' ->
  i=i'.
Proof.
  intro H.
  gen i'.
  induction H; intros.
  - inverts H; lia.
  - inverts H0; try lia.
    rlia x0 x.
    apply IHv2 in H2.
    lia.
Qed.

Ltac v2_unique :=
match goal with
| [H: v2 ?x ?i, H0: v2 ?x ?i0 |- _] => pose proof (v2_unique H H0) as X; clear H0; subst
end.

Lemma v2_ex n:
  exists i, v2 n i.
Proof.
  induction n using lt_wf_ind.
  destruct (mod2 n); subst n.
  - exists O.
    solve_v2.
  - unshelve epose proof (H a _) as [i I].
    1: lia.
    apply v2_S in I.
    exists (S i).
    applys_eq I; flia.
Qed.

Lemma nstep_inv0 i a c c':
  nstep (1+a) c c' ->
  v2 c (i*2) ->
  nstep a (c+1) c'.
Proof.
  intros.
  inverts H.
  inverts H2.
  v2_unique.
  applys_eq H3; flia.
Qed.

Lemma nstep_inv1 i a c c':
  nstep (1+a) c c' ->
  v2 c (1+i*2) ->
  nstep a (c+2) c'.
Proof.
  intros.
  inverts H.
  inverts H2.
  v2_unique.
  applys_eq H3; flia.
Qed.

Lemma nstep_r0 i a c c':
  nstep a c c' ->
  v2 c' (i*2) ->
  nstep (1+a) c (c'+1).
Proof.
  intros.
  eapply nstep_step1.
  1: apply H.
  eapply step1_intro in H0.
  applys_eq H0; flia.
Qed.

Lemma nstep_r1 i a c c':
  nstep a c c' ->
  v2 c' (1+i*2) ->
  nstep (1+a) c (c'+2).
Proof.
  intros.
  eapply nstep_step1.
  1: apply H.
  eapply step1_intro in H0.
  applys_eq H0; flia.
Qed.

Lemma nstep_l0 i a c c':
  nstep a c c' ->
  v2 (c-1) (i*2) ->
  c>=1 ->
  nstep (1+a) (c-1) c'.
Proof.
  intros.
  eapply nstep_S.
  2: apply H.
  eapply step1_intro in H0.
  applys_eq H0; flia.
Qed.

Lemma nstep_l1 i a c c':
  nstep a c c' ->
  v2 (c-2) (1+i*2) ->
  c>=2 ->
  nstep (1+a) (c-2) c'.
Proof.
  intros.
  eapply nstep_S.
  2: apply H.
  eapply step1_intro in H0.
  applys_eq H0; flia.
Qed.

Ltac solve_v2' :=
match goal with
| |- v2 _ _ => cbn; solve_v2
| _ => idtac
end.

Lemma nonhalt: ~halts tm c0.
Proof with solve_v2'.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=WF).
  2:{
    eapply WF_111 with (i:=O)...
    cbn; ec.
    1: apply (step1_intro 7 3)...
    cbn; ec.
    1: apply (step1_intro 9 1)...
    cbn; ec.
    1: apply (step1_intro 11 2)...
    cbn; ec.
    1: apply (step1_intro 12 0)...
    cbn; ec.
    1: apply (step1_intro 13 1)...
    cbn; ec.
    1: apply (step1_intro 15 4)...
    cbn; ec.
    1: apply (step1_intro 16 0)...
    ec.
  }
  intros [a n] HWF.
  inverts HWF.
  - exists (1+a,n0+2); split.
    1: apply BigStep,H2.
    eapply WF_001.
    1: apply H1.
    inverts H1.
    inverts H3.
    inverts H1.
    apply (nstep_inv0 0) in H2...
    apply (nstep_r0 1) in H2...
    apply (nstep_r0 0) in H2...
    applys_eq H2; flia.
  - exists (1+a,n0+3); split.
    1: apply BigStep,H2.
    eapply WF_010.
    1: apply H1.
    inverts H1.
    inverts H3.
    inverts H1.
    apply (nstep_inv1 0) in H2...
    apply (nstep_r1 0) in H2...
    apply (nstep_l0 0) in H2...
    2: lia.
    applys_eq H2; flia.
  - exists (1+a,n0+4); split.
    1: apply BigStep,H2.
    inverts H1.
    inverts H3.
    inverts H1.
    applys_eq (WF_011 (1+a) (x+1)).
    1: flia.
    apply (nstep_inv0 0) in H2...
    apply (nstep_r1 1) in H2...
    apply (nstep_r1 0) in H2...
    applys_eq H2; flia.
  - exists (1+a,n0*8+5); split.
    1: apply BigStep,H0.
    apply WF_101.
    apply (nstep_inv0 1) in H0...
    apply (nstep_r0 1) in H0...
    apply (nstep_inv0 0) in H0...
    apply (nstep_r0 0) in H0...
    apply (nstep_r1 0) in H0...
    applys_eq H0; flia.
  - epose proof (v2_ex (n0*8+7)) as [i I1].
    exists (1+a,n0*8+7); split.
    1: apply BigStep,H0.
    inverts I1.
    1: lia.
    inverts H1.
    1: lia.
    inverts H2.
    1: lia.
    rlia x n0.
    clear H.
    destruct (mod2 i0); subst i0.
    + apply WF_111 with (i:=a0)...
      1: applys_eq H1; flia.
      apply (nstep_inv1 0) in H0...
      apply (nstep_r0 (2+a0)) in H0...
      2: applys_eq H1; flia.
      apply (nstep_r0 0) in H0...
      applys_eq H0; flia.
    + inverts H1.
      apply WF_111' with (i:=a0)...
      1: applys_eq H3; flia.
      apply (nstep_inv1 0) in H0...
      apply (nstep_r1 (2+a0)) in H0...
      2: applys_eq H3; flia.
      apply (nstep_r1 0) in H0...
      applys_eq H0; flia.
  - exists (1+a,n+1); split.
    1: apply BigStep,H2.
    eapply WF_000.
    1: apply H1.
    inverts H1.
    inverts H3.
    inverts H1.
    apply (nstep_inv1 (1+i)) in H2...
    2: applys_eq H3; flia.
    apply (nstep_r1 0) in H2...
    apply (nstep_l0 0) in H2...
    2: lia.
    applys_eq H2; flia.
  - exists (1+a,n+2); split.
    1: apply BigStep,H2.
    eapply WF_001'.
    1: apply H1.
    inverts H1.
    inverts H3.
    inverts H1.
    inverts H3.
    apply (nstep_inv0 (2+i)) in H2...
    2: applys_eq H1; flia.
    apply (nstep_r0 1) in H2...
    apply (nstep_inv0 0) in H2...
    apply (nstep_r0 0) in H2...
    apply (nstep_r1 0) in H2...
    applys_eq H2; flia.
  - exists (1+a,n0+4); split.
    1: apply BigStep,H2.
    inverts H1.
    inverts H3.
    inverts H1.
    inverts H3.
    applys_eq (WF_011 (1+a) (x0*2+2)).
    1: flia.
    apply (nstep_inv1 0) in H2...
    apply (nstep_r1 1) in H2...
    apply (nstep_r1 0) in H2...
    applys_eq H2; flia.
Qed.

