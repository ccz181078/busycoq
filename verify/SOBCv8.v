From BusyCoq Require Import Individual62.

Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import BinaryCounter_v2 NatMod Longitudinal NatMod_v2.


Lemma segRLs_addmul_v2 a a' x b b' tm h w1 w2:
  segRLs tm (h^^b) (h^^b') w1 w2 ->
  segRLs tm (h^^a) (h^^a') w2 w2 ->
  segRLs tm (h^^(x*a+b)) (h^^(x*a'+b')) w1 w2.
Proof.
  intros.
  rewrite (Nat.add_comm _ b).
  rewrite (Nat.add_comm _ b').
  do 2 rewrite lpow_add.
  eapply segRLs_trans.
  1: apply H.
  induction x; cbn[Nat.mul].
  - cbn.
    constructor.
  - cbn[lpow].
    do 2 rewrite lpow_add.
    eapply segRLs_trans.
    2: apply IHx.
    apply H0.
Qed.

Ltac flia := repeat (lia||f_equal).

Lemma lpow_add'_x1{T} (a:list T) n r:
  a^^n *> a *> r = a^^(n+1) *> r.
Proof.
  rewrite lpow_add.
  cbn.
  repeat rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma lpow_add'_1x{T} (a:list T) n r:
  a *> a^^n *> r = a^^(n+1) *> r.
Proof.
  rewrite Nat.add_comm.
  cbn.
  rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma lpow_1{T} (a:list T):
  a^^1 = a.
Proof.
  cbn.
  apply app_nil_r.
Qed.

Ltac rw_lpow_add :=
  repeat (
  match goal with
  | |- context[?a^^1 *> _] =>
    rewrite (lpow_1 a)
  | |- context[?a *> ?a^^?y *> ?r] =>
    rewrite (lpow_add'_1x a y r)
  | |- context[?a^^?x *> ?a *> ?r] =>
    rewrite (lpow_add'_x1 a x r)
  end ||
  rewrite lpow_add').

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0RB_1LC0LE_0LD0LB_1RD0RE_0LA1RF_0RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (A,[0]).
Notation hL := (B,[0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d0 := [1;1;0;0].
Notation d1 := [1;0;0;0].
Notation d2 := [1;0;1;0].

Lemma RIncs0 n:
  sideRLs tm (hRL^^(3^n*4-1)) (d0^^(n*2+0)*>d2*>d1*>0inf) (d2^^(n*2+3)*>0inf).
Proof.
  induction n.
  - esx.
  - cbn[Nat.mul].
    do 2 rewrite <-Nat.add_assoc.
    do 2 rewrite <-(lpow_add' _ 2).
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    cbn[Nat.pow].
    replace (3*3^n*4-1) with ((3^n*2-1)*6+5) by lia.
    replace (3^n*4-1) with ((3^n*2-1)*2+1) by lia.
    apply segRLs_addmul_v2; esx.
Qed.

Lemma RIncs1 n:
  sideRLs tm (hRL^^(3^n*8-1)) (d0^^(n*2+3)*>d2*>d1*>0inf) (d2^^(n*2)*>d1*>d0*>d2^^3*>0inf).
Proof.
  induction n.
  - esx.
  - cbn[Nat.mul].
    rewrite <-Nat.add_assoc.
    do 2 rewrite <-(lpow_add' _ 2).
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    cbn[Nat.pow].
    replace (3*3^n*8-1) with ((3^n*4-4)*6+23) by lia.
    replace (3^n*8-1) with ((3^n*4-4)*2+7) by lia.
    apply segRLs_addmul_v2; esx.
Qed.

Definition LC a :=
  0inf <* <[1;0;1;0;1;1;0;1;1;0] <* <[1;0]^^a <* <[1;1;0;1].

Definition tm' := flip tm.

Lemma LIncs n a:
  sideRLs tm' (hLR^^n) (LC a) (LC (n*2+a)).
Proof.
  unfold LC.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Definition S1 n :=
  LC 5 {{{ (hR,R) }}} d0^^n *> d2 *> d1 *> 0inf.

Notation "l |> r" := (l {{B}}> r) (at level 30).

Definition S2 a b c :=
  LC a <* <[1;1;0;1]^^b <* <[0;1]^^c |> 0inf.

Lemma Inc2 a b c:
  S2 a (1+b) c -->*
  S2 a b (3+c).
Proof.
  es.
Qed.

Lemma Incs2 a b c:
  S2 a b c -->*
  S2 a 0 (b*3+c).
Proof.
  gen c.
  ind b Inc2.
Qed.

Definition S3 a b :=
  0inf <* <[1;0;1;0;1;1;0;1;1;0] <* <[1;0]^^a <* <[1;1] <* <[0;1]^^b |> 0inf.

Lemma Inc3 a b:
  S3 (2+a) b -->*
  S3 a (3+b).
Proof.
  es.
Qed.

Lemma Incs3 n a b:
  S3 (n*2+a) b -->*
  S3 a (n*3+b).
Proof.
  gen a b.
  ind n Inc3.
Qed.

Lemma Ov2 a c:
  S2 a 0 c -->*
  S3 a (1+c).
Proof.
  es.
Qed.

Definition S4 a b :=
  0inf <* <[1;0] <* <[1;1;0;1]^^(1+a) <* <[0;1]^^b |> 0inf.

Lemma Inc4 a b:
  S4 (1+a) b -->*
  S4 a (3+b).
Proof.
  es.
Qed.

Lemma Incs4 a b:
  S4 a b -->*
  S4 0 (a*3+b).
Proof.
  gen b.
  ind a Inc4.
Qed.


Lemma Ov3_1_0 b:
  S3 1 (b*2) -->*
  S4 (5+b) 1.
Proof.
  es.
Qed.

Lemma Ov1_1 a n:
  LC a {{{ (hR,R) }}} d2^^(n) *>  d1 *> d0 *> d2^^3 *> 0inf -->+
  S2 a (n+1) 13.
Proof.
  es.
Qed.

Lemma Ov1_0 a n:
  LC a {{{ (hR,R) }}} d2^^(n) *> 0inf -->+
  S2 a n 1.
Proof.
  es.
Qed.

Lemma BigStep1_3 n:
  S1 (n*2+3) -->+
  S4 0 (3^n*36+n*9+46).
Proof.
  unfold S1.
  epose proof (sideRLs_concat_1 (RIncs1 _) (LIncs _ _)) as I1.
  follow I1. clear I1.
  follow10 Ov1_1.
  follow Incs2.
  follow Ov2.
  replace ((3^n*8-1)*2+5) with ((3^n*8+1)*2+1) by lia.
  follow Incs3.
  follow (Ov3_1_0 (3^n*12+n*3+10)).
  follow Incs4.
  finish.
Qed.

Lemma BigStep1_3' n:
  n>=1 ->
  S1 (1+n*2) -->+
  S4 0 (3^n*12+n*9+37).
Proof.
  intros.
  replace n with (S(n-1)) by lia.
  cbn[Nat.pow].
  applys_eq (BigStep1_3 (n-1)); flia.
Qed.

Lemma BigStep1_0' n:
  S1 (0+n*2) -->+
  S4 0 (3^n*18+n*9+37).
Proof.
  rewrite Nat.add_comm.
  unfold S1.
  epose proof (sideRLs_concat_1 (RIncs0 _) (LIncs _ _)) as I1.
  follow I1. clear I1.
  follow10 Ov1_0.
  follow Incs2.
  follow Ov2.
  replace ((3^n*4-1)*2+5) with ((3^n*4+1)*2+1) by lia.
  follow Incs3.
  follow (Ov3_1_0 (3^n*6+n*3+7)).
  follow Incs4.
  finish.
Qed.

Lemma Ov4_0 b:
  b>=1 ->
  S4 0 (0+b*2) -->+
  S1 (b-1).
Proof.
  intros.
  remember (b-1) as b'.
  replace b with (1+b') by lia.
  es.
Qed.

Definition S5 a b :=
  0inf <* <[1;0;1] <* <[1;1;0;1]^^(a) <* <[0;1]^^b |> 0inf.

Lemma Inc5 a b:
  S5 (1+a) b -->*
  S5 a (3+b).
Proof.
  es.
Qed.

Lemma Incs5 a b:
  S5 a b -->*
  S5 0 (a*3+b).
Proof.
  gen b.
  ind a Inc5.
Qed.

Lemma Ov4_1 b:
  S4 0 (1+b*2) -->+
  S5 0 (b*3+10).
Proof.
  mid10 (S5 (3+b) 1).
  1: es.
  follow Incs5.
  finish.
Qed.

Lemma Ov5_0 b:
  S5 0 (0+b*2) -->+
  S5 0 (b*3+4).
Proof.
  mid10 (S5 (1+b) 1).
  1: es.
  follow Incs5.
  finish.
Qed.

Lemma Ov5_1 b:
  b>=2 ->
  S5 0 (1+b*2) -->+
  S1 (b-2).
Proof.
  intros.
  remember (b-2) as b'.
  replace b with (2+b') by lia.
  es.
Qed.

Definition S' '(n,tp) :=
match tp with
| O => S1 n
| S O => S4 0 n
| _ => S5 0 n
end.

Close Scope sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (7,0)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(n,tp) =>
  match tp with
  | 0 => n>=3
  | 1 => n>=8
  | _ => n>=10
  end).
  2: lia.
  intros [n tp] HP.
  unfold S'.
  destruct tp as [|[|]].
  - divmod2_cases n.
    + eexists (_,1); split.
      1: apply BigStep1_0'.
      lia.
    + eexists (_,1); split.
      1: rewrite Nat.add_comm.
      1: apply BigStep1_3'; lia.
      lia.
  - divmod2_cases n.
    + eexists (_,0); split.
      1: apply Ov4_0; lia.
      lia.
    + eexists (_,2); split.
      1: rewrite Nat.add_comm.
      1: apply Ov4_1; lia.
      lia.
  - divmod2_cases n.
    + eexists (_,2); split.
      1: apply Ov5_0; lia.
      lia.
    + eexists (_,0); split.
      1: rewrite Nat.add_comm.
      1: apply Ov5_1; lia.
      lia.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB0LD_0LC0LA_1RC0RD_0LE1RF_1RA0RA_0RE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,[0]).
Notation hL := (A,[0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d0 := [1;1;0;0].
Notation d1 := [1;0;0;0].
Notation d2 := [1;0;1;0].

Lemma RIncs0 n:
  sideRLs tm (hRL^^(3^n*4-1)) (d0^^(n*2+0)*>d2*>d1*>0inf) (d2^^(n*2+3)*>0inf).
Proof.
  induction n.
  - esx.
  - cbn[Nat.mul].
    do 2 rewrite <-Nat.add_assoc.
    do 2 rewrite <-(lpow_add' _ 2).
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    cbn[Nat.pow].
    replace (3*3^n*4-1) with ((3^n*2-1)*6+5) by lia.
    replace (3^n*4-1) with ((3^n*2-1)*2+1) by lia.
    apply segRLs_addmul_v2; esx.
Qed.

Lemma RIncs1 n:
  sideRLs tm (hRL^^(3^n*8-1)) (d0^^(n*2+3)*>d2*>d1*>0inf) (d2^^(n*2)*>d1*>d0*>d2^^3*>0inf).
Proof.
  induction n.
  - esx.
  - cbn[Nat.mul].
    rewrite <-Nat.add_assoc.
    do 2 rewrite <-(lpow_add' _ 2).
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    cbn[Nat.pow].
    replace (3*3^n*8-1) with ((3^n*4-4)*6+23) by lia.
    replace (3^n*8-1) with ((3^n*4-4)*2+7) by lia.
    apply segRLs_addmul_v2; esx.
Qed.

Definition LC a :=
  0inf <* <[1;0;1;0;1;1;0;1;1;0] <* <[1;0]^^a <* <[1;1;0;1].

Definition tm' := flip tm.

Lemma LIncs n a:
  sideRLs tm' (hLR^^n) (LC a) (LC (n*2+a)).
Proof.
  unfold LC.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Definition S1 n :=
  LC 5 {{{ (hR,R) }}} d0^^n *> d2 *> d1 *> 0inf.

Notation "l |> r" := (l {{A}}> r) (at level 30).

Definition S2 a b c :=
  LC a <* <[1;1;0;1]^^b <* <[0;1]^^c |> 0inf.

Lemma Inc2 a b c:
  S2 a (1+b) c -->*
  S2 a b (3+c).
Proof.
  es.
Qed.

Lemma Incs2 a b c:
  S2 a b c -->*
  S2 a 0 (b*3+c).
Proof.
  gen c.
  ind b Inc2.
Qed.

Definition S3 a b :=
  0inf <* <[1;0;1;0;1;1;0;1;1;0] <* <[1;0]^^a <* <[1;1] <* <[0;1]^^b |> 0inf.

Lemma Inc3 a b:
  S3 (2+a) b -->*
  S3 a (3+b).
Proof.
  es.
Qed.

Lemma Incs3 n a b:
  S3 (n*2+a) b -->*
  S3 a (n*3+b).
Proof.
  gen a b.
  ind n Inc3.
Qed.

Lemma Ov2 a c:
  S2 a 0 c -->*
  S3 a (1+c).
Proof.
  es.
Qed.

Definition S4 a b :=
  0inf <* <[1;0] <* <[1;1;0;1]^^(1+a) <* <[0;1]^^b |> 0inf.

Lemma Inc4 a b:
  S4 (1+a) b -->*
  S4 a (3+b).
Proof.
  es.
Qed.

Lemma Incs4 a b:
  S4 a b -->*
  S4 0 (a*3+b).
Proof.
  gen b.
  ind a Inc4.
Qed.


Lemma Ov3_1_0 b:
  S3 1 (b*2) -->*
  S4 (5+b) 1.
Proof.
  es.
Qed.

Lemma Ov1_1 a n:
  LC a {{{ (hR,R) }}} d2^^(n) *>  d1 *> d0 *> d2^^3 *> 0inf -->+
  S2 a (n+1) 13.
Proof.
  es.
Qed.

Lemma Ov1_0 a n:
  LC a {{{ (hR,R) }}} d2^^(n) *> 0inf -->+
  S2 a n 1.
Proof.
  es.
Qed.

Lemma BigStep1_3 n:
  S1 (n*2+3) -->+
  S4 0 (3^n*36+n*9+46).
Proof.
  unfold S1.
  epose proof (sideRLs_concat_1 (RIncs1 _) (LIncs _ _)) as I1.
  follow I1. clear I1.
  follow10 Ov1_1.
  follow Incs2.
  follow Ov2.
  replace ((3^n*8-1)*2+5) with ((3^n*8+1)*2+1) by lia.
  follow Incs3.
  follow (Ov3_1_0 (3^n*12+n*3+10)).
  follow Incs4.
  finish.
Qed.

Lemma BigStep1_3' n:
  n>=1 ->
  S1 (1+n*2) -->+
  S4 0 (3^n*12+n*9+37).
Proof.
  intros.
  replace n with (S(n-1)) by lia.
  cbn[Nat.pow].
  applys_eq (BigStep1_3 (n-1)); flia.
Qed.

Lemma BigStep1_0' n:
  S1 (0+n*2) -->+
  S4 0 (3^n*18+n*9+37).
Proof.
  rewrite Nat.add_comm.
  unfold S1.
  epose proof (sideRLs_concat_1 (RIncs0 _) (LIncs _ _)) as I1.
  follow I1. clear I1.
  follow10 Ov1_0.
  follow Incs2.
  follow Ov2.
  replace ((3^n*4-1)*2+5) with ((3^n*4+1)*2+1) by lia.
  follow Incs3.
  follow (Ov3_1_0 (3^n*6+n*3+7)).
  follow Incs4.
  finish.
Qed.

Lemma Ov4_0 b:
  b>=1 ->
  S4 0 (0+b*2) -->+
  S1 (b-1).
Proof.
  intros.
  remember (b-1) as b'.
  replace b with (1+b') by lia.
  es.
Qed.

Definition S5 a b :=
  0inf <* <[1;0;1] <* <[1;1;0;1]^^(a) <* <[0;1]^^b |> 0inf.

Lemma Inc5 a b:
  S5 (1+a) b -->*
  S5 a (3+b).
Proof.
  es.
Qed.

Lemma Incs5 a b:
  S5 a b -->*
  S5 0 (a*3+b).
Proof.
  gen b.
  ind a Inc5.
Qed.

Lemma Ov4_1 b:
  S4 0 (1+b*2) -->+
  S5 0 (b*3+10).
Proof.
  mid10 (S5 (3+b) 1).
  1: es.
  follow Incs5.
  finish.
Qed.

Lemma Ov5_0 b:
  S5 0 (0+b*2) -->+
  S5 0 (b*3+4).
Proof.
  mid10 (S5 (1+b) 1).
  1: es.
  follow Incs5.
  finish.
Qed.

Lemma Ov5_1 b:
  b>=2 ->
  S5 0 (1+b*2) -->+
  S1 (b-2).
Proof.
  intros.
  remember (b-2) as b'.
  replace b with (2+b') by lia.
  es.
Qed.

Definition S' '(n,tp) :=
match tp with
| O => S1 n
| S O => S4 0 n
| _ => S5 0 n
end.

Close Scope sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (22,0)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(n,tp) =>
  match tp with
  | 0 => n>=3
  | 1 => n>=8
  | _ => n>=10
  end).
  2: lia.
  intros [n tp] HP.
  unfold S'.
  destruct tp as [|[|]].
  - divmod2_cases n.
    + eexists (_,1); split.
      1: apply BigStep1_0'.
      lia.
    + eexists (_,1); split.
      1: rewrite Nat.add_comm.
      1: apply BigStep1_3'; lia.
      lia.
  - divmod2_cases n.
    + eexists (_,0); split.
      1: apply Ov4_0; lia.
      lia.
    + eexists (_,2); split.
      1: rewrite Nat.add_comm.
      1: apply Ov4_1; lia.
      lia.
  - divmod2_cases n.
    + eexists (_,2); split.
      1: apply Ov5_0; lia.
      lia.
    + eexists (_,0); split.
      1: rewrite Nat.add_comm.
      1: apply Ov5_1; lia.
      lia.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB0LE_0RC1RA_1LC0LD_0RA1LF_0LA1LE_---0LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (B,[]).
Notation hL := (E,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d0 := [1;1].
Notation d1 := [1;0].
Notation dw := [1;0;0;1].

Definition LC n := 0inf <* <[1;0;1] <* <[1;1;0;1]^^n.

Definition tm' := flip tm.

Lemma LIncs n a:
  sideRLs tm' (hLR^^n) (LC a) (LC (n+a)).
Proof.
  unfold LC.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Lemma RIncs_O r:
  sideRLs tm (hRL^^0) r r.
Proof.
  esx.
Qed.

Lemma RIncs_S0 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+1)) (d0*>r) (d1*>r').
Proof.
  intros.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  apply segRLs_addmul''; esx.
Qed.

Lemma RIncs_S1 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+0)) (d1*>r) (d1*>r').
Proof.
  intros.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  apply segRLs_addmul''; esx.
Qed.

Lemma RIncs_Sw n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^n) (dw*>r) (dw*>r').
Proof.
  intros.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  apply segRLs_wall''; esx.
Qed.

Lemma RIncs_S0_01 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n+1)) (d0*>[0;1]*>r) (dw*>r').
Proof.
  replace (n+1) with (n*1+1) by lia.
  intros.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  apply segRLs_addmul''; esx.
Qed.

Lemma RIncs_S0s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(2^k*(n+1)-1)) (d0^^k*>r) (d1^^k*>r').
Proof.
  intros.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  rewrite Nat.mul_comm.
  eapply BC.IncsOvs.
  1: solve_seg.
  1: solve_seg.
  1: solve_seg.
Qed.

Lemma RIncs_S1s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(2^k*n)) (d1^^k*>r) (d1^^k*>r').
Proof.
  intros.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  rewrite Nat.mul_comm.
  eapply BC.Ovs.
  2: solve_seg.
  2: solve_seg.
  1: solve_seg.
Qed.

Lemma RIncs_Su n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+1)) ((dw++[0;0])*>r) ((dw++d1)*>r').
Proof.
  intros.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  apply segRLs_addmul''; esx.
Qed.

Lemma RIncs_Sus k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(2^k*(n+1)-1)) ((dw++[0;0])^^k*>r) ((dw++d1)^^k*>r').
Proof.
  intros.
  induction k.
  - applys_eq H; flia.
  - cbn[lpow].
    rewrite Str_app_assoc.
    rewrite (Str_app_assoc (dw++d1)).
    eapply segRLs_sideRLs_concat.
    2: apply IHk.
    cbn[Nat.pow].
    replace (2*2^k*(n+1)-1) with ((2^k*(n+1)-1)*2+1) by lia.
    apply segRLs_addmul''; esx.
Qed.

Lemma RIncs_Sus' k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(2^k*n)) ((dw++d1)^^k*>r) ((dw++d1)^^k*>r').
Proof.
  intros.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  rewrite Nat.mul_comm.
  eapply BC.Ovs.
  2: solve_seg.
  2: solve_seg.
  1: solve_seg.
Qed.

Notation "l |> r" := (l {{{ (hR,R) }}} r) (at level 30).

Lemma Incs a n r r':
  sideRLs tm (hRL^^n) r r' ->
  LC a |> r -->*
  LC (n+a) |> r'.
Proof.
  intros.
  epose proof (sideRLs_concat_1 H (LIncs _ _)) as I1.
  apply I1.
Qed.

Lemma dw111_00 r:
  sideRLs tm (hRL^^1) (dw*>d1*>d1*>d1*>[0;0]*>r) (d1*>[0;0]*>[0;1]*>d1*>d1*>d0*>r).
Proof.
  esx.
Qed.

Lemma dw111_0inf:
  sideRLs tm (hRL^^1) (dw*>d1*>d1*>d1*>0inf) (d1*>[0;0]*>[0;1]*>d1*>d1*>d0*>0inf).
Proof.
  esx.
Qed.

Ltac solve_RIncs_1 :=
match goal with
| |- sideRLs _ _ ?r _ =>
  match r with
  | d0^^_ *> _ => apply RIncs_S0s
  | d1^^_ *> _ => apply RIncs_S1s
  | d0 *> [0;1] *> _ => apply RIncs_S0_01
  | d0 *> _ => apply RIncs_S0
  | d1 *> _ => apply RIncs_S1
  | dw *> d1*>d1*>d1*>[0;0]*>_ => apply dw111_00
  | dw *> d1*>d1*>d1*>0inf => apply dw111_0inf
  | dw *> _ => apply RIncs_Sw
  | [0;0] *> _ => apply RIncs_O
  | 0inf => apply RIncs_O
  | (dw++d1)^^_ *> _ => apply RIncs_Sus'
  | (dw++[0;0])^^_ *> _ => apply RIncs_Sus
  | (dw++[0;0]) *> _ => apply RIncs_Su
  end
end.

Ltac solve_RIncs :=
repeat solve_RIncs_1.

Lemma Rst2 a b r:
  LC a |> d1 ^^ (2+b*3) *> d1 *> [0; 0] *> r -->*
  LC 0 |> d0^^(a*2+2) *> dw *> d1 *> (dw++[0;0])^^b *> d1 *> d0 *> r.
Proof.
  unfold LC.
  es.
Qed.

Lemma Rst3 l b r:
  halts tm (l |> d1 ^^ b *> dw *> d1 *> dw *> d1 *> d1 *> [0; 0] *> r).
Proof.
  esx.
Qed.

Lemma init:
  c0 -->*
  LC 0 {{{ (hR,R) }}} d0^^8 *> dw *> d1 *> d1 *> d0 *> 0inf.
Proof.
  esx.
Qed.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2:{
  follow init.
  follow Incs.
  1: solve_RIncs.
  simpl_small_nat 100.
  follow Incs.
  1: solve_RIncs.
  change (d1^^8) with (d1^^(2+2*3)).
  follow Rst2.
  follow Incs.
  1: solve_RIncs.
  simpl_small_nat 100.
  repeat rewrite Nat.add_0_r.
  repeat rewrite Nat.mul_1_r.
  follow Incs.
  1: solve_RIncs.
  simpl_small_nat 100.
  cbn[lpow].
  rewrite app_nil_r.
  repeat rewrite Str_app_assoc.
  follow Incs.
  1: solve_RIncs.
  simpl_small_nat 100.
  finish.
  }
  apply Rst3.
Qed.

End TM3.


Module TM4.
Definition tm := Eval compute in (TM_from_str "1RB1RD_1LC1LA_1RA0LB_1LB0RE_0RF1RA_---1LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (D,<[1;1]).
Notation hL := (B,[0;1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d0 := [1;1;1;1;0;1].
Notation d1 := [1;1;1;1;1;1].
Notation dw := [0;1].

Definition LC n := 0inf <* <[1;0]^^n.

Definition tm' := flip tm.

Lemma LIncs n a:
  sideRLs tm' (hLR^^n) (LC a) (LC (n+a)).
Proof.
  unfold LC.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Lemma RIncs_O r:
  sideRLs tm (hRL^^0) r r.
Proof.
  esx.
Qed.

Lemma RIncs_S0 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+1)) (d0*>r) (d1*>r').
Proof.
  intros.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  apply segRLs_addmul''; esx.
Qed.

Lemma RIncs_S1 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+0)) (d1*>r) (d1*>r').
Proof.
  intros.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  apply segRLs_addmul''; esx.
Qed.

Lemma RIncs_S0s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(2^k*(n+1)-1)) (d0^^k*>r) (d1^^k*>r').
Proof.
  intros.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  rewrite Nat.mul_comm.
  eapply BC.IncsOvs.
  1: solve_seg.
  1: solve_seg.
  1: solve_seg.
Qed.

Lemma RIncs_S1s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(2^k*n)) (d1^^k*>r) (d1^^k*>r').
Proof.
  intros.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  rewrite Nat.mul_comm.
  eapply BC.Ovs.
  2: solve_seg.
  2: solve_seg.
  1: solve_seg.
Qed.

Lemma RIncs_Sw n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^n) (dw*>r) (dw*>r').
Proof.
  intros.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  apply segRLs_wall''; esx.
Qed.

Notation "l |> r" := (l {{{ (hR,R) }}} r) (at level 30).

Lemma Incs a n r r':
  sideRLs tm (hRL^^n) r r' ->
  LC a |> r -->*
  LC (n+a) |> r'.
Proof.
  intros.
  epose proof (sideRLs_concat_1 H (LIncs _ _)) as I1.
  apply I1.
Qed.

Ltac solve_RIncs_1 :=
match goal with
| |- sideRLs _ _ ?r _ =>
  match r with
  | d0^^_ *> _ => apply RIncs_S0s
  | d1^^_ *> _ => apply RIncs_S1s
  | d0 *> _ => apply RIncs_S0
  | d1 *> _ => apply RIncs_S1
  | dw *> _ => apply RIncs_Sw
  | 0inf => apply RIncs_O
  end
end.

Ltac solve_RIncs :=
repeat solve_RIncs_1.

Lemma init:
  c0 -->*
  LC 2 |> d0^^4 *> d1 *> d0^^4 *> d1 *> 0inf.
Proof.
  esx.
Qed.

Lemma Rst1 a b:
  LC (2+a*3) |> d1^^(2+b) *> 0inf -->*
  LC 2 |> d0^^(1+a) *> dw *> d1 *> d0^^b *> d1 *> 0inf.
Proof.
  unfold LC.
  es.
Qed.

Lemma Rst2 a b c:
  LC (2+a*3) |> d1^^(2+b) *> dw *> d1 ^^ (1+c) *> 0inf -->+
  LC 2 |> d0^^(1+a) *> dw *> d1 *> d0^^b *> d1 *> dw *> d0^^c *> d1 *> 0inf.
Proof.
  unfold LC.
  es.
Qed.

Lemma Rst3 a b c d:
  LC (0+a*3) |> d1^^b *> dw *> d1^^(1+c) *> dw *> d1^^(1+d) *> 0inf -->*
  LC 2 |> d0^^(a+b) *> d1 *> d0^^c *> d1 *> dw *> d0^^d *> d1 *> 0inf.
Proof.
  unfold LC.
  es.
Qed.

Definition S2 '(a,b,c) :=
  LC (2+(1+a*2)*3) |> d1^^(2+(0+b*2)) *> dw *> d1 ^^ (1+(1+c*2)) *> 0inf.

Definition S3 '(a,b,c,d) :=
  LC (0+(1+a*2)*3) |> d1^^(0+b*2) *> dw *> d1^^(1+(1+c*2)) *> dw *> d1^^(1+(1+d*2)) *> 0inf.

Ltac R_mod m :=
  match goal with
  | |- ?a = _ =>
    eassert (X:_) by (eapply (div_mod' a m _); rw_mod_1);
    rewrite X in *;
    clear X
  end.

Ltac feq :=
repeat
match goal with
| |- ?a = _ + _ * ?m => R_mod m; do 2 f_equal
| |- @eq nat _ _ => idtac
| _ => f_equal
end.

Lemma S2_S a b c:
  b<>O ->
  c<>O ->
  exists a' b' c' d', S2 (a,b,c) -->+ S3 (a',b',c',d') /\ (b'<>O/\c'<>O/\d'<>O).
Proof.
  eexists _,_,_,_; split.
  - unfold S2,S3.
    follow10 Rst2.
    follow Incs.
    1: solve_RIncs.
    rw_lpow_add.
    finish.
    feq.
    + replace (0+b*2+1+1) with (1+(1+b*2)) by lia.
      reflexivity.
    + replace (1+c*2+1) with (1+(1+c*2)) by lia.
      reflexivity.
  - lia.
  Unshelve.
  all: solve_ge.
Qed.

Lemma S3_S a b c d:
  b<>O ->
  c<>O ->
  d<>O ->
  exists a' b' c', S3 (a,b,c,d) -->* S2 (a',b',c') /\ (b'<>O /\ c'<>O).
Proof.
  intros.
  eexists _,_,_; split.
  - unfold S2,S3.
    follow Rst3.
    follow Incs.
    1: solve_RIncs.
    rw_lpow_add.
    finish.
    feq.
    + replace (1 + a * 2 + (0 + b * 2) + (1 + c * 2 + 1 + 1)) with (0+(2+a+b+c)*2) by lia.
      reflexivity.
    + replace (1+d*2+1) with (1+(1+d*2)) by lia.
      reflexivity.
  - lia.
  Unshelve.
  all: solve_ge.
Qed.

Ltac R_mod' :=
match goal with
| |- LC ?b |> _ -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Ltac R_mod'' :=
match goal with
| |- LC (_+?b*3) |> _ -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 2 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S2 (_,82,4)).
  1:{
  follow init.
  follow Incs.
  1: solve_RIncs.
  rw_lpow_add.
  simpl_small_nat 100.
  R_mod'.
  follow Rst1.
  simpl_small_nat 500.
  follow Incs.
  1: solve_RIncs.
  rw_lpow_add.
  simpl_small_nat 300.
  R_mod'.
  R_mod''.
  unfold S2.
  apply evstep_refl'.
  feq.
  }
  eapply progress_nonhalt_cond with (P:=fun '(a,b,c) => b<>O/\c<>O).
  2: lia.
  intros [[a b] c] HP.
  epose proof (S2_S _ _ _ _ _) as [a' [b' [c' [d' [I1 I2]]]]].
  epose proof (S3_S _ _ _ _ _ _ _) as [a'' [b'' [c'' [I3 I4]]]].
  eexists (_,_,_); split.
  - follow10 I1.
    apply I3.
  - lia.
  Unshelve.
  all: lia.
Qed.

End TM4.


Module TM5.
Definition tm := Eval compute in (TM_from_str "1LB1LD_1RC0LA_0RF1RD_1RA1RE_1LA0RC_---1LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[1;1]).
Notation hL := (A,[0;1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d0 := [1;1;1;1;0;1].
Notation d1 := [1;1;1;1;1;1].
Notation dw := [0;1].

Definition LC n := 0inf <* <[1;1] <* <[1;0]^^n.

Definition tm' := flip tm.

Lemma LIncs n a:
  sideRLs tm' (hLR^^n) (LC a) (LC (n+a)).
Proof.
  unfold LC.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Lemma RIncs_O r:
  sideRLs tm (hRL^^0) r r.
Proof.
  esx.
Qed.

Lemma RIncs_S0 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+1)) (d0*>r) (d1*>r').
Proof.
  intros.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  apply segRLs_addmul''; esx.
Qed.

Lemma RIncs_S1 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+0)) (d1*>r) (d1*>r').
Proof.
  intros.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  apply segRLs_addmul''; esx.
Qed.

Lemma RIncs_S0s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(2^k*(n+1)-1)) (d0^^k*>r) (d1^^k*>r').
Proof.
  intros.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  rewrite Nat.mul_comm.
  eapply BC.IncsOvs.
  1: solve_seg.
  1: solve_seg.
  1: solve_seg.
Qed.

Lemma RIncs_S1s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(2^k*n)) (d1^^k*>r) (d1^^k*>r').
Proof.
  intros.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  rewrite Nat.mul_comm.
  eapply BC.Ovs.
  2: solve_seg.
  2: solve_seg.
  1: solve_seg.
Qed.

Lemma RIncs_Sw n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^n) (dw*>r) (dw*>r').
Proof.
  intros.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  apply segRLs_wall''; esx.
Qed.

Notation "l |> r" := (l {{{ (hR,R) }}} r) (at level 30).

Lemma Incs a n r r':
  sideRLs tm (hRL^^n) r r' ->
  LC a |> r -->*
  LC (n+a) |> r'.
Proof.
  intros.
  epose proof (sideRLs_concat_1 H (LIncs _ _)) as I1.
  apply I1.
Qed.

Ltac solve_RIncs_1 :=
match goal with
| |- sideRLs _ _ ?r _ =>
  match r with
  | d0^^_ *> _ => apply RIncs_S0s
  | d1^^_ *> _ => apply RIncs_S1s
  | d0 *> _ => apply RIncs_S0
  | d1 *> _ => apply RIncs_S1
  | dw *> _ => apply RIncs_Sw
  | 0inf => apply RIncs_O
  end
end.

Ltac solve_RIncs :=
repeat solve_RIncs_1.

Lemma init:
  c0 -->*
  LC 2 |> d0^^4 *> d1 *> d0^^4 *> d1 *> 0inf.
Proof.
  esx.
Qed.

Lemma Rst1 a b:
  LC (2+a*3) |> d1^^(2+b) *> 0inf -->*
  LC 2 |> d0^^(1+a) *> dw *> d1 *> d0^^b *> d1 *> 0inf.
Proof.
  unfold LC.
  es.
Qed.

Lemma Rst2 a b c:
  LC (2+a*3) |> d1^^(2+b) *> dw *> d1 ^^ (1+c) *> 0inf -->+
  LC 2 |> d0^^(1+a) *> dw *> d1 *> d0^^b *> d1 *> dw *> d0^^c *> d1 *> 0inf.
Proof.
  unfold LC.
  es.
Qed.

Lemma Rst3 a b c d:
  LC (0+a*3) |> d1^^b *> dw *> d1^^(1+c) *> dw *> d1^^(1+d) *> 0inf -->*
  LC 2 |> d0^^(a+b) *> d1 *> d0^^c *> d1 *> dw *> d0^^d *> d1 *> 0inf.
Proof.
  unfold LC.
  es.
Qed.

Definition S2 '(a,b,c) :=
  LC (2+(1+a*2)*3) |> d1^^(2+(0+b*2)) *> dw *> d1 ^^ (1+(1+c*2)) *> 0inf.

Definition S3 '(a,b,c,d) :=
  LC (0+(1+a*2)*3) |> d1^^(0+b*2) *> dw *> d1^^(1+(1+c*2)) *> dw *> d1^^(1+(1+d*2)) *> 0inf.

Ltac R_mod m :=
  match goal with
  | |- ?a = _ =>
    eassert (X:_) by (eapply (div_mod' a m _); rw_mod_1);
    rewrite X in *;
    clear X
  end.

Ltac feq :=
repeat
match goal with
| |- ?a = _ + _ * ?m => R_mod m; do 2 f_equal
| |- @eq nat _ _ => idtac
| _ => f_equal
end.

Lemma S2_S a b c:
  b<>O ->
  c<>O ->
  exists a' b' c' d', S2 (a,b,c) -->+ S3 (a',b',c',d') /\ (b'<>O/\c'<>O/\d'<>O).
Proof.
  eexists _,_,_,_; split.
  - unfold S2,S3.
    follow10 Rst2.
    follow Incs.
    1: solve_RIncs.
    rw_lpow_add.
    finish.
    feq.
    + replace (0+b*2+1+1) with (1+(1+b*2)) by lia.
      reflexivity.
    + replace (1+c*2+1) with (1+(1+c*2)) by lia.
      reflexivity.
  - lia.
  Unshelve.
  all: solve_ge.
Qed.

Lemma S3_S a b c d:
  b<>O ->
  c<>O ->
  d<>O ->
  exists a' b' c', S3 (a,b,c,d) -->* S2 (a',b',c') /\ (b'<>O /\ c'<>O).
Proof.
  intros.
  eexists _,_,_; split.
  - unfold S2,S3.
    follow Rst3.
    follow Incs.
    1: solve_RIncs.
    rw_lpow_add.
    finish.
    feq.
    + replace (1 + a * 2 + (0 + b * 2) + (1 + c * 2 + 1 + 1)) with (0+(2+a+b+c)*2) by lia.
      reflexivity.
    + replace (1+d*2+1) with (1+(1+d*2)) by lia.
      reflexivity.
  - lia.
  Unshelve.
  all: solve_ge.
Qed.

Ltac R_mod' :=
match goal with
| |- LC ?b |> _ -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Ltac R_mod'' :=
match goal with
| |- LC (_+?b*3) |> _ -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 2 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S2 (_,82,4)).
  1:{
  follow init.
  follow Incs.
  1: solve_RIncs.
  rw_lpow_add.
  simpl_small_nat 100.
  R_mod'.
  follow Rst1.
  simpl_small_nat 500.
  follow Incs.
  1: solve_RIncs.
  rw_lpow_add.
  simpl_small_nat 300.
  R_mod'.
  R_mod''.
  unfold S2.
  apply evstep_refl'.
  feq.
  }
  eapply progress_nonhalt_cond with (P:=fun '(a,b,c) => b<>O/\c<>O).
  2: lia.
  intros [[a b] c] HP.
  epose proof (S2_S _ _ _ _ _) as [a' [b' [c' [d' [I1 I2]]]]].
  epose proof (S3_S _ _ _ _ _ _ _) as [a'' [b'' [c'' [I3 I4]]]].
  eexists (_,_,_); split.
  - follow10 I1.
    apply I3.
  - lia.
  Unshelve.
  all: lia.
Qed.

End TM5.


