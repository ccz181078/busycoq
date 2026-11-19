From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import Longitudinal.


Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LF_1RC0RE_0LD1RB_0LA1LD_1LB0RD_---1LB").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hL := (D,[1]).
Notation hR := (B,[]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Definition tm' := flip tm.

Definition P1 n :=
  segRLs tm' (hLR^^n) (hLR^^n) (<[0;1;1;1;1;1]^^(1+n)) (<[0;1;1;1;1;1] <+ <[1;1;1;1;1;1]^^n).

Lemma P1_S n:
  P1 n ->
  P1 (n+(1+n)).
Proof.
  unfold P1.
  intros HP1.
  rewrite lpow_add.
  eapply segRLs_trans.
  1: {
    replace (1+(n+(1+n))) with ((1+n)+(1+n)) by lia.
    rewrite lpow_add.
    eapply segRLs_concat; apply HP1.
  }
  rewrite lpow_add.
  eapply segRLs_trans.
  2: {
    replace ((n+(1+n))) with ((1+n)+(n)) by lia.
    rewrite lpow_add,<-app_assoc.
    eapply segRLs_concat.
    2: apply HP1.
    eapply segRLs_wall''; esx.
  }
  esx.
Qed.

Lemma LIncs n:
  sideRLs tm' (hLR^^n) (0inf) (0inf <* [1;1;1]^^n).
Proof.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Lemma RIncs n:
  sideRLs tm (hRL^^n) 0inf 0inf.
Proof.
  apply sideRLs_wall; esx.
Qed.

Definition P2 a b c :=
  sideRLs tm' (hLR^^a) (0inf <* <[0;1;1;1;1;1]^^b) (0inf <* <[1]^^c).

Lemma P2_S a c n:
  P1 (n*2+1) ->
  P2 a (1+n) c ->
  P2 ((n*2+1)+(1+a)) (1+(n*2+1)) (n*12+12+c).
Proof.
  unfold P1,P2.
  intros HP1 HP2.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: {
    eapply segRLs_sideRLs_concat.
    1: apply HP1.
    apply LIncs.
  }
  rewrite lpow_add.
  eapply @sideRLs_trans with (r2:=[1]^^(n*12+12)*>[1;1;1;1;1;0]^^(1+n)*>0inf).
  1: esx.
  rewrite (lpow_add _ _ c),Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall'' with (h2:=hLR); esx.
  apply HP2.
Qed.

Lemma P1_n n: P1 (2^n-1).
Proof.
  induction n.
  1: unfold P1; esx.
  cbn[Nat.pow]. 
  apply P1_S in IHn.
  applys_eq IHn; lia.
Qed.

Lemma P2_n n: P2 (2^n*4-2) (1+(2^n*2-1)) (2^n*24-7).
Proof.
  induction n.
  1: unfold P2; esx.
  cbn[Nat.pow].
  apply P2_S in IHn.
  2: applys_eq (P1_n (2+n)); cbn; lia.
  applys_eq IHn; lia.
Qed.

Definition S1 n :=
  0inf <* <[0;1;1;1;1;1]^^(1+(2^n*2-1)) {{{ (hL,L) }}} 0inf.

Lemma BigStep n:
  S1 n -->+ S1 (S n).
Proof.
  unfold S1,P2.
  follow (sideRLs_concat_1L (RIncs _) (P2_n n)).
  cbn[Nat.pow].
  remember ((2^n-1)*4) as v1.
  replace (2^n*24-7) with (17+v1*6) by lia.
  replace (1+(2*2^n*2-1)) with (4+v1) by lia.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1 0).
  1: esx.
  eapply progress_nonhalt_simple.
  intros n; eexists; apply BigStep.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB0RB_1LC0LC_1LD1LB_0RE0LF_0RA1RE_0LE---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hL := (B,[]).
Notation hR := (A,<[1;0]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Definition tm' := flip tm.

Definition P1 n :=
  segRLs tm' (hLR^^n) (hLR^^n) (<[1;1]^^(1+n)) (<[1;0]^^n <+ <[1;1]).

Lemma P1_S n:
  P1 n ->
  P1 (n+(1+n)).
Proof.
  unfold P1.
  intros HP1.
  rewrite lpow_add.
  eapply segRLs_trans.
  1: {
    replace (1+(n+(1+n))) with ((1+n)+(1+n)) by lia.
    rewrite lpow_add.
    eapply segRLs_concat; apply HP1.
  }
  rewrite lpow_add.
  eapply segRLs_trans.
  2: {
    rewrite lpow_add,app_assoc.
    eapply segRLs_concat.
    1: apply HP1.
    eapply segRLs_wall''; esx.
  }
  esx.
Qed.

Lemma RIncs k n:
  sideRLs tm (hRL^^n) ([1;1]^^k*>0inf) ([1;1]^^(n*2+k)*>0inf).
Proof.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Definition S1 '(l,n) :=
  l <* <[1;1]^^(1+n) {{{ (hL,L) }}} [1;1]^^2 *> 0inf.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1 (0inf<*<[1;1;1;0;1;0;1;0;1],7)).
  1: esx.
  eapply progress_nonhalt_cond with (P:= fun '(l,n) => P1 n /\ sideRLs tm' hLR l l /\ n>=1).
  2: {
    repeat split.
    - apply (P1_S 3),(P1_S 1); unfold P1; esx.
    - esx.
    - lia.
  }
  intros [l n] [HP1 [Hl Hn]].
  eexists ([1;0;1]*>[0;1]^^n*>l,1+n*2); split.
  - unfold S1,P1 in *.
    epose proof (sideRLs_concat_1L (RIncs _ _)) as I1.
    follow I1. clear I1.
    1: eapply segRLs_sideRLs_concat.
    1: apply HP1.
    1: apply sideRLs_wall,Hl.
    eapply sideRLs_1L in Hl.
    es; er.
    follow100 Hl. clear Hl.
    es.
  - repeat split.
    + apply P1_S in HP1.
      applys_eq HP1; lia.
    + rewrite <-Str_app_assoc.
      eapply segRLs_sideRLs_concat.
      2: apply Hl.
      replace n with (1+(n-1)) by lia.
      esx.
    + lia.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB1RA_0LC0RC_1RE1LD_1RA0LD_1LF0RA_---0LE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (B,[1;0;1]).
Notation hL := (D,[0;0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Definition tm' := flip tm.

Definition P1 n := sideRLs tm (hRL^^(3+n)) ([0;1]*>0inf) ([0;1]^^(1+n)*>[0;0;1]^^2*>[0;1]^^(1+n)*>[0;0;1]*>0inf).

Ltac flia := repeat (lia||f_equal).

Lemma Incs1 n m:
  segRLs tm (hRL^^(2+n)) (hRL^^(1+n)) ([0;1]^^(2+(n+m)*2)++[0]) ([0;1]^^(1+n*2)++[0]++[0;1]^^(1+m*2)++[0]).
Proof.
  gen m.
  induction n; intros.
  - esx.
  - replace (2+S n) with (2+n+1) by lia.
    replace (1+S n) with (1+n+1) by lia.
    do 2 rewrite (lpow_add _ _ 1).
    eapply segRLs_trans.
    1: applys_eq (IHn (S m)); flia.
    esx.
Qed.

Lemma P1_S n:
  P1 (n*2) ->
  P1 (n*4+6).
Proof.
  unfold P1.
  intros HP1.
  replace (3+(n*4+6)) with ((3+n*2)+(1+(2+(3+n*2)))) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply HP1.
  rewrite lpow_add.
  eapply @sideRLs_trans with (r2:=([0;1]^^(8+n*2+n*2)++[0])*>[0;1]*>0inf).
  1: esx.
  change ([0;0;1]^^2) with ([0;0;1;0]++[0;1]).
  rewrite (Str_app_assoc [0;0;1;0]).
  rewrite <-(Str_app_assoc _ [0;0;1;0]).
  eapply segRLs_sideRLs_concat.
  applys_eq (Incs1 (3+n*2) 0); flia.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  1: apply HP1.
  replace (n*4) with (n*2+n*2) by lia.
  esx.
Qed.

Definition LC a b :=
  0inf <* <[0;1]^^(1+a*2) <* <[1;0]^^(1+b*2).

Lemma LIncs a b:
  sideRLs tm' (hLR^^b) (LC a b) (LC (b+a) 0).
Proof.
  unfold LC.
  gen a.
  induction b; intros.
  1: esx.
  replace (S b) with (1+b) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (IHb (1+a)); flia.
  esx.
Qed.

Definition S' n := LC 0 (3+n*2) {{{ (hR,R) }}} [0;1] *> 0inf.

Lemma BigStep n:
  P1 (n*2) ->
  S' (n) -->+
  S' (n*2+3).
Proof.
  unfold P1,S'.
  intros HP1.
  epose proof (sideRLs_concat_1 HP1 (LIncs _ _)) as I1.
  follow I1. clear I1.
  cbn.
  replace ((n*2+3)*2*2) with (12+n*2+n*2+n*2+n*2) by lia.
  replace ((n*2+0)*2) with (n*2+n*2) by lia.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' 0).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun n => P1 (n*2)).
  2: unfold P1; esx.
  intros n HP1.
  eexists; split.
  - apply BigStep,HP1.
  - apply P1_S in HP1.
    applys_eq HP1; flia.
Qed.

End TM3.


