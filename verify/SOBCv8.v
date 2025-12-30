From BusyCoq Require Import Individual62.

Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import BinaryCounter_v2 NatMod Longitudinal NatMod_v2.
From BusyCoq Require DivModCases.



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

Lemma sideRLs_add tm h a b r r':
  sideRLs tm (h^^a) r r' ->
  a>=b ->
  sideRLs tm (h^^(a-b+b)) r r'.
Proof.
  intros.
  applys_eq H; flia.
Qed.

Ltac R_mod'' a b :=
  eassert (X:_) by (eapply (div_mod'' a b _); rw_mod_1);
  rewrite X in *;
  clear X.

Ltac R_mod' a b :=
  eassert (X:_) by (eapply (div_mod' a b _); rw_mod_1);
  rewrite X in *;
  clear X.

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


Ltac stepn' n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; try reflexivity.

Module TM6.
Definition tm := Eval compute in (TM_from_str "1LB1RC_1LC1LD_1RD0RE_0LB0RE_0RF1RA_---1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[1;0]).
Notation hL := (B,[0;1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d0 := [1;1;1;1;0;1].
Notation d1 := [1;1;1;1;1;1].
Notation dw := [0;1].
Notation du := [1;1;0;1].

Definition LC n := 0inf <* <[1] <* <[0;1]^^n.

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

Inductive RD :=
| D0s(n:Nexpr)
| D1s(n:Nexpr)
| D0 | D1
| Dw
| Du.

Inductive RDH :=
| RH0 | RH1 | RH2.

Inductive RC :=
| RC_S(a:RD)(r:RC)
| RC_O(a:RDH).

Notation rh0 := ([1;1;1;1;1] *> 0inf).
Notation rh1 := ([1] *> 0inf).
Notation rh2 := ([1;1;1] *> 0inf).

Lemma RIncs_rh0:
  sideRLs tm (hRL^^2) rh0 (d1*>rh1).
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


Lemma pow4_mod3 k:
  2^(k*2) mod 3 = 1%nat.
Proof.
  induction k; cbn - [Nat.modulo]; lia.
Qed.

Ltac rw_pa :=
  repeat rewrite Nat.pow_add_r by lia.

Lemma RIncs_Su_0s_0_1w k n r r':
  sideRLs tm (hRL^^(n+2)) r r' ->
  sideRLs tm (hRL^^(n*2^(k*2+2)+2^(k*2+4)/3)) (du*>d0^^(k*2+0)*>d1*>dw*>r) (d1^^(k*2+2)*>r').
Proof.
  intros.
  induction k.
  - cbn[Nat.mul].
    repeat rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply H.
    apply segRLs_addmul; esx.
  - cbn[Nat.mul].
    remember ((n * 2 ^ (2 + k * 2 + 2) + 2 ^ (2 + k * 2 + 4) / 3)) as v1.
    repeat rewrite lpow_add.
    repeat rewrite Str_app_assoc.
    pose proof (pow4_mod3 k).
    replace v1 with (1+((n*2^(k*2+2)+2^(k*2+4)/3)*4+0)) by (subst; rw_pa; lia).
    rewrite lpow_add.
    eapply sideRLs_trans.
    2: eapply segRLs_sideRLs_concat.
    3: rewrite lpow_add'.
    3: apply IHk.
    2: apply segRLs_addmul''; esx.
    esx.
Qed.

Lemma RIncs_Su_0s_1_1w k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2^(k*2+3)+2^(k*2+4)/3)) (du*>d0^^(k*2+1)*>d1*>dw*>r) (d1^^(k*2+3)*>r').
Proof.
  intros.
  induction k.
  - cbn[Nat.mul].
    repeat rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply H.
    apply segRLs_addmul''; esx.
  - cbn[Nat.mul].
    remember ((n * 2 ^ (2 + k * 2 + 3) + 2 ^ (2 + k * 2 + 4) / 3)) as v1.
    repeat rewrite lpow_add.
    repeat rewrite Str_app_assoc.
    pose proof (pow4_mod3 k).
    replace v1 with (1+((n*2^(k*2+3)+2^(k*2+4)/3)*4+0)) by (subst; rw_pa; lia).
    rewrite lpow_add.
    eapply sideRLs_trans.
    2: eapply segRLs_sideRLs_concat.
    3: rewrite lpow_add'.
    3: apply IHk.
    2: apply segRLs_addmul''; esx.
    esx.
Qed.

Lemma RIncs_Su_0s_0_rh0 k:
  sideRLs tm (hRL^^(2^(k*2+2)/3)) (du*>d0^^(k*2+0)*>rh0) (d1^^(k*2+1)*>du*>rh1).
Proof.
  rewrite Nat.add_0_r.
  induction k.
  - esx.
  - cbn[Nat.mul].
    repeat rewrite lpow_add.
    repeat rewrite Str_app_assoc.
    pose proof (pow4_mod3 k).
    replace (2^(2+k*2+2)/3) with (1+(2^(k*2+2)/3*4+0)) by (rw_pa; lia).
    rewrite lpow_add.
    eapply sideRLs_trans.
    2: eapply segRLs_sideRLs_concat.
    3: rewrite lpow_add'.
    3: apply IHk.
    2: apply segRLs_addmul''; esx.
    esx.
Qed.

Lemma RIncs_Su_0s_1_rh0 k:
  sideRLs tm (hRL^^(2^(k*2+2)/3)) (du*>d0^^(k*2+1)*>rh0) (d1^^(k*2+2)*>rh2).
Proof.
  induction k.
  - esx.
  - cbn[Nat.mul].
    repeat rewrite lpow_add.
    repeat rewrite Str_app_assoc.
    pose proof (pow4_mod3 k).
    replace (2^(2+k*2+2)/3) with (1+(2^(k*2+2)/3*4+0)) by (rw_pa; lia).
    rewrite lpow_add.
    eapply sideRLs_trans.
    2: eapply segRLs_sideRLs_concat.
    3: rewrite lpow_add'.
    3: apply IHk.
    2: apply segRLs_addmul''; esx.
    esx.
Qed.

Lemma RIncs_Su_0s_0_rh2 k:
  sideRLs tm (hRL^^(2^(k*2)/3)) (du*>d0^^(k*2+0)*>rh2) (d1^^(k*2)*>du*>rh2).
Proof.
  induction k.
  - esx.
  - cbn[Nat.mul].
    repeat rewrite lpow_add.
    repeat rewrite Str_app_assoc.
    pose proof (pow4_mod3 k).
    replace (2^(2+k*2)/3) with (1+(2^(k*2)/3*4+0)) by (rw_pa; lia).
    rewrite lpow_add.
    eapply sideRLs_trans.
    2: eapply segRLs_sideRLs_concat.
    3: apply IHk.
    2: apply segRLs_addmul''; esx.
    esx.
Qed.

Lemma RIncs_Su_0s_1_rh2 k:
  sideRLs tm (hRL^^(2^(k*2+2)/3)) (du*>d0^^(k*2+1)*>rh2) (d1^^(k*2+2)*>rh1).
Proof.
  induction k.
  - esx.
  - cbn[Nat.mul].
    repeat rewrite lpow_add.
    repeat rewrite Str_app_assoc.
    pose proof (pow4_mod3 k).
    replace (2^(2+k*2+2)/3) with (1+(2^(k*2+2)/3*4+0)) by (rw_pa; lia).
    rewrite lpow_add.
    eapply sideRLs_trans.
    2: rewrite (lpow_add' _ (k*2)).
    2: eapply segRLs_sideRLs_concat.
    3: apply IHk.
    2: apply segRLs_addmul''; esx.
    esx.
Qed.

Notation "l |> r" := (l {{{ (hR,R) }}} r) (at level 30).
Notation "l <2| r" := (l <{{D}} [1;0;1;0;1]%sym *> r) (at level 30).

Lemma Incs a n r r':
  sideRLs tm (hRL^^n) r r' ->
  LC a |> r -->*
  LC (n+a) |> r'.
Proof.
  intros.
  epose proof (sideRLs_concat_1 H (LIncs _ _)) as I1.
  apply I1.
Qed.

Lemma LRst1 n r:
  LC (1+n*3) <2| r -->*
  LC 0 |> d1^^n *> d0 *> r.
Proof.
  unfold LC.
  es.
Qed.

Lemma LRst2 n r:
  LC (2+n*3) <2| r -->*
  LC 0 |> d1^^(n+1) *> dw *> r.
Proof.
  unfold LC.
  es.
Qed.

Lemma LRst0 n r:
  LC (0+n*3) <2| r -->*
  LC 0 |> d1^^(n) *> du *> r.
Proof.
  unfold LC.
  es.
Qed.

Lemma init:
  c0 -->*
  LC 0 |> d1^^448 *> du *> d0^^10 *> rh0.
Proof.
  stepn' 9117316%N.
  repeat rewrite <-const_unfold.
  reflexivity.
Qed.

Import NatModTactics.

Ltac solve_RIncs_1 :=
match goal with
| |- sideRLs _ _ ?r _ =>
  match r with
  | d0^^_ *> _ => apply RIncs_S0s
  | d1^^_ *> _ => apply RIncs_S1s
  | d0 *> _ => apply RIncs_S0
  | d1 *> _ => apply RIncs_S1
  | dw *> _ => apply RIncs_Sw
  | du *> d0^^(?mp.[?x])%Nexpr *> _ => R_mod_v2 mp x 2
  | du *> d0^^(_*2+0) *> rh0 => apply RIncs_Su_0s_0_rh0
  | du *> d0^^(_*2+0) *> d1 *> dw *> _ => apply RIncs_Su_0s_0_1w
  | du *> d0^^(_*2+1) *> [1;1;1] *> 0inf => apply RIncs_Su_0s_1_rh2
  | rh0 => apply RIncs_rh0
  end
end.

Ltac solve_RIncs :=
repeat solve_RIncs_1.

Lemma ROv1 l a:
  l |> d1^^a *> du *> rh1 -->*
  l <2| d0^^a *> rh2.
Proof.
  es.
Qed.

Lemma ROv2 l a:
  l |> d1^^(1+a) *> rh1 -->*
  l <2| d0^^a *> rh0.
Proof.
  es.
Qed.

Lemma ROv3 l a b:
  l |> d1^^(1+a) *> dw *> d1^^(1+b) *> rh1 -->*
  l <2| d0^^a *> d1 *> dw *> d0^^b *> rh0.
Proof.
  es.
Qed.

Lemma ROv2' l a:
  a>=1 ->
  l |> d1^^a *> rh1 -->+
  l <2| d0^^(a-1)%nat *> rh0.
Proof.
  intros.
  remember (a-1)%nat as a'.
  replace a with (1+a')%nat by lia.
  es.
Qed.

Ltac follow' H :=
  eapply evstep_trans; [eapply Peq; [|apply H]; match_Nexpr |].

Definition S' '(a,b) :=
  LC 0 |> d1 ^^ (a*2+1) *> d0 *> d0 ^^ (b*2+1) *> rh0.

Definition P '(a,b) := (a>=1/\b>=1).

Lemma BigStep a b:
  P (a,b) ->
  exists x,
  S' (a,b) -->+
  S' x /\ P x.
Proof.
  intros [Ha Hb].
  eexists (_,a+b+1)%nat; split.
  1:{
  follow Incs.
  1: solve_RIncs.
  rw_lpow_add.
  eapply progress_evstep_trans.
  1: apply ROv2'.
  1: lia.
  match goal with
  | |- LC ?x <2| _ -->* _ => R_mod' x 3
  end.
  follow LRst1.
  match goal with
  | |- _ |> d1^^?x *> _ -->* _ => R_mod'' x 2
  end.
  unfold S'.
  finish.
  }
  split; solve_ge.
  Unshelve.
  all: solve_ge.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof with rw_all.
  eapply multistep_nonhalt with (c':=S' (_,_)).
  1:{
  follow' init...

  follow' Incs.
  1: solve_RIncs.
  rw_lpow_add...
  follow' ROv1...
  follow' LRst0...

  follow' Incs.
  1: solve_RIncs.
  rw_lpow_add...
  follow' ROv2...
  follow' LRst2...

  follow' Incs.
  1: solve_RIncs.
  rw_lpow_add...
  follow' ROv3...
  follow' LRst1...

  follow' Incs.
  1: solve_RIncs.
  rw_lpow_add...
  follow' ROv3...
  follow' LRst0...

  follow' Incs.
  1: solve_RIncs.
  1: apply sideRLs_add.
  1: solve_RIncs.
  1: solve_Nexpr_ge.
  rw_lpow_add...
  follow' ROv2...
  follow' LRst1...

  R_mod_v2 mp (Nvar 0) 2.
  R_mod_v2 mp (Nvar 1) 2.

  unfold S'; finish.
  }
  eapply progress_nonhalt_cond with (P:=P).
  1: intros [a b]; apply BigStep.
  split; solve_Nexpr_ge.
Qed.

End TM6.


Module TM7.
Definition tm := Eval compute in (TM_from_str "1LB0RD_1LC0LA_1RA0LB_1RA0RE_1RF---_0RB0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,[]).
Notation hL := (A,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d0 := [0;0;1;1].
Notation d1 := [0;1;0;1].
Notation d2 := [0;0;0;1].
Notation d0a := [0;0;1;0;1;1].
Notation d1a := [0;1;0;0;1;1].
Notation d2a := [0;0;0;0;1;1].


Definition LC1 n := 0inf <* <[1;0]^^n <* <[0].

Definition tm' := flip tm.

Lemma LIncs1 n a:
  sideRLs tm' (hLR^^n) (LC1 a) (LC1 (n+a)).
Proof.
  unfold LC1.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Notation rh1 := ([0;1] *> 0inf).

Ltac solve_v1 :=
  intros H;
  eapply segRLs_sideRLs_concat; [|apply H];
  apply segRLs_addmul''; esx.

Lemma RIncs_S0 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*3+2)) (d0*>r) (d2*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S1 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*3+1)) (d1*>r) (d2*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S2 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*3+0)) (d2*>r) (d2*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S0s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(3^k*(n+1)-1)) (d0^^k*>r) (d2^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S0 in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Lemma pow3_mod2 a:
  3^a mod 2 = 1%nat.
Proof.
  induction a; cbn[Nat.pow]; lia.
Qed.

Lemma RIncs_S1s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^((3^k*(n*2+1)-1)/2)) (d1^^k*>r) (d2^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S1 in IHk.
    cbn[Nat.pow].
    pose proof (pow3_mod2 k).
    applys_eq IHk; flia.
Qed.

Lemma RIncs_S0a n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*3+2)) (d0a*>r) (d2a*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S1a n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*3+1)) (d1a*>r) (d2a*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S2a n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*3+0)) (d2a*>r) (d2a*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_rh1:
  sideRLs tm (hRL^^1) rh1 0inf.
Proof.
  esx.
Qed.

Lemma RIncs_O r:
  sideRLs tm (hRL^^0) r r.
Proof.
  esx.
Qed.

Notation "l |> r" := (l {{{ (hR,R) }}} r) (at level 30).

Lemma Incs1 a n r r':
  sideRLs tm (hRL^^n) r r' ->
  LC1 a |> r -->*
  LC1 (n+a) |> r'.
Proof.
  intros.
  epose proof (sideRLs_concat_1 H (LIncs1 _ _)) as I1.
  apply I1.
Qed.

Lemma init:
  c0 -->*
  LC1 1 |> d1^^5 *> d1a *> d0^^2 *> d2 *> rh1.
Proof.
  esx.
Qed.

Import NatModTactics.

Ltac solve_RIncs_1 :=
match goal with
| |- sideRLs _ _ ?r _ =>
  match r with
  | d0^^_ *> _ => apply RIncs_S0s
  | d1^^_ *> _ => apply RIncs_S1s
  | d0 *> _ => apply RIncs_S0
  | d1 *> _ => apply RIncs_S1
  | d2 *> _ => apply RIncs_S2
  | d1a *> _ => apply RIncs_S1a
  | rh1 => apply RIncs_rh1
  | [1;1] *> _ => apply RIncs_O
  end
end.

Ltac solve_RIncs :=
repeat solve_RIncs_1.

Ltac follow' H :=
  eapply evstep_trans; [eapply Peq; [|apply H]; match_Nexpr |].

Lemma Rst1 a b c:
  LC1 (2+a*2) |> d2^^b *> d2a *> d2^^c *> 0inf -->*
  LC1 1 |> d1^^a *> d1a *> d0^^b *> d2 *> [1;1] *> d0^^c *> d2 *> rh1.
Proof.
  unfold LC1.
  es.
Qed.

Lemma Rst2 l b c r:
  halts tm (l |> d2^^b *> d2a *> d2^^c *> [1;1] *> r).
Proof.
  esx.
Qed.

Lemma halt: halts tm c0.
Proof with rw_all.
  eapply halts_evstep.
  2:{
  follow' init...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst1...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  finish.
  }
  apply Rst2.
Qed.

End TM7.


Module TM8.
Definition tm := Eval compute in (TM_from_str "1RB---_0RC0LC_1LD0LE_1RE0LC_1LC0RF_1RE0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (A,[]).
Notation hL := (E,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d0 := [0;0;1;1].
Notation d1 := [0;1;0;1].
Notation d2 := [0;0;0;1].
Notation d0a := [0;0;1;0;1;1].
Notation d1a := [0;1;0;0;1;1].
Notation d2a := [0;0;0;0;1;1].


Definition LC1 n := 0inf <* <[1;0]^^n <* <[0].

Definition tm' := flip tm.

Lemma LIncs1 n a:
  sideRLs tm' (hLR^^n) (LC1 a) (LC1 (n+a)).
Proof.
  unfold LC1.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Notation rh1 := ([0;1] *> 0inf).

Ltac solve_v1 :=
  intros H;
  eapply segRLs_sideRLs_concat; [|apply H];
  apply segRLs_addmul''; esx.

Lemma RIncs_S0 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*3+2)) (d0*>r) (d2*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S1 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*3+1)) (d1*>r) (d2*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S2 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*3+0)) (d2*>r) (d2*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S0s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(3^k*(n+1)-1)) (d0^^k*>r) (d2^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S0 in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Lemma pow3_mod2 a:
  3^a mod 2 = 1%nat.
Proof.
  induction a; cbn[Nat.pow]; lia.
Qed.

Lemma RIncs_S1s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^((3^k*(n*2+1)-1)/2)) (d1^^k*>r) (d2^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S1 in IHk.
    cbn[Nat.pow].
    pose proof (pow3_mod2 k).
    applys_eq IHk; flia.
Qed.

Lemma RIncs_S0a n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*3+2)) (d0a*>r) (d2a*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S1a n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*3+1)) (d1a*>r) (d2a*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S2a n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*3+0)) (d2a*>r) (d2a*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_rh1:
  sideRLs tm (hRL^^1) rh1 0inf.
Proof.
  esx.
Qed.

Lemma RIncs_O r:
  sideRLs tm (hRL^^0) r r.
Proof.
  esx.
Qed.

Notation "l |> r" := (l {{{ (hR,R) }}} r) (at level 30).

Lemma Incs1 a n r r':
  sideRLs tm (hRL^^n) r r' ->
  LC1 a |> r -->*
  LC1 (n+a) |> r'.
Proof.
  intros.
  epose proof (sideRLs_concat_1 H (LIncs1 _ _)) as I1.
  apply I1.
Qed.

Lemma init:
  c0 -->*
  LC1 1 |> d1^^2 *> d0^^2 *> d2 *> rh1.
Proof.
  esx.
Qed.

Import NatModTactics.

Ltac solve_RIncs_1 :=
match goal with
| |- sideRLs _ _ ?r _ =>
  match r with
  | d0^^_ *> _ => apply RIncs_S0s
  | d1^^_ *> _ => apply RIncs_S1s
  | d0 *> _ => apply RIncs_S0
  | d1 *> _ => apply RIncs_S1
  | d2 *> _ => apply RIncs_S2
  | d1a *> _ => apply RIncs_S1a
  | rh1 => apply RIncs_rh1
  | [1;1] *> _ => apply RIncs_O
  end
end.

Ltac solve_RIncs :=
repeat solve_RIncs_1.

Ltac follow' H :=
  eapply evstep_trans; [eapply Peq; [|apply H]; match_Nexpr |].

Lemma Rst1 a b:
  LC1 (2+a*2) |> d2^^b *> 0inf -->*
  LC1 1 |> d1^^a *> d1a *> d0^^b *> d2 *> rh1.
Proof.
  unfold LC1.
  es.
Qed.

Lemma Rst2 a b c:
  LC1 (2+a*2) |> d2^^b *> d2a *> d2^^c *> 0inf -->*
  LC1 1 |> d1^^a *> d1a *> d0^^b *> d2 *> [1;1] *> d0^^c *> d2 *> rh1.
Proof.
  unfold LC1.
  es.
Qed.

Lemma Rst3 l b c r:
  halts tm (l |> d2^^b *> d2a *> d2^^c *> [1;1] *> r).
Proof.
  esx.
Qed.

Lemma halt: halts tm c0.
Proof with rw_all.
  eapply halts_evstep.
  2:{
  follow' init...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst1...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst2...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  finish.
  }
  apply Rst3.
Qed.

End TM8.


Module TM9.
Definition tm := Eval compute in (TM_from_str "1RB0RC_1LC1RA_1RA1LD_0LC0LE_0LF0LB_---0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (A,<[1;1]).
Notation hL := (E,[0;1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d0 := [1;1].
Notation d1 := [0;1].
Notation dw := [1;0;0;1].


Definition LC1 n := 0inf <* <[1;0;1;1]^^(1+n) <* <[1].

Definition tm' := flip tm.

Lemma LIncs1 n a:
  sideRLs tm' (hLR^^n) (LC1 a) (LC1 (n+a)).
Proof.
  unfold LC1.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Ltac solve_v1 :=
  intros H;
  eapply segRLs_sideRLs_concat; [|apply H];
  apply segRLs_addmul''; esx.

Lemma RIncs_S0 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+1)) (d0*>r) (d1*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S1 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+0)) (d1*>r) (d1*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_Sw n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^n) (dw*>r) (dw*>r').
Proof.
  intros.
  replace n with (n*1+0) by lia.
  gen H.
  solve_v1.
Qed.

Notation dw00 := [1;0;0;1;1;1;1;1].
Notation dw11 := [1;0;0;1;0;1;0;1].

Lemma RIncs_Sw00 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*4+3)) (dw00*>r) (dw11*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_Sw00s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(4^k*(n+1)-1)) (dw00^^k*>r) (dw11^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_Sw00 in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Lemma RIncs_S0s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(2^k*(n+1)-1)) (d0^^k*>r) (d1^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S0 in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Lemma RIncs_S1s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(2^k*n)) (d1^^k*>r) (d1^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S1 in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Notation rh1 := ([1] *> 0inf).

Lemma RIncs_O r:
  sideRLs tm (hRL^^0) r r.
Proof.
  esx.
Qed.

Notation "l |> r" := (l {{{ (hR,R) }}} r) (at level 30).

Lemma Incs1 a n r r':
  sideRLs tm (hRL^^n) r r' ->
  LC1 a |> r -->*
  LC1 (n+a) |> r'.
Proof.
  intros.
  epose proof (sideRLs_concat_1 H (LIncs1 _ _)) as I1.
  apply I1.
Qed.

Lemma init:
  c0 -->*
  LC1 1 |> dw00^^2 *> d0 *> dw00 *> d0 *> rh1.
Proof.
  esx.
Qed.

Import NatModTactics.

Lemma Rst1 a:
  LC1 (0+a*2) |> dw11^^2 *> d1 *> dw11 *> d1 *> rh1 -->*
  LC1 1 |> dw00^^a *> d0 *> dw00 *> d0^^5 *> dw00 *> d0^^2 *> rh1.
Proof.
  unfold LC1.
  es.
Qed.

Lemma Rst2 a b:
  halts tm (LC1 (0+a*2) |> dw11^^(0+b*2) *> d1 *> dw11 *> d1^^5 *> dw11 *> d1^^2 *> rh1).
Proof.
  esx.
Qed.

Ltac solve_RIncs_1 :=
match goal with
| |- sideRLs _ _ ?r _ =>
  match r with
  | dw00^^_ *> _ => apply RIncs_Sw00s
  | d0^^_ *> _ => apply RIncs_S0s
  | d1^^_ *> _ => apply RIncs_S1s
  | d0 *> _ => apply RIncs_S0
  | d1 *> _ => apply RIncs_S1
  | dw *> _ => apply RIncs_Sw
  | dw00 *> _ => apply RIncs_Sw00
  | rh1 => apply RIncs_O
  end
end.

Ltac solve_RIncs :=
repeat solve_RIncs_1.

Ltac follow' H :=
  eapply evstep_trans; [eapply Peq; [|apply H]; match_Nexpr |].

Ltac followh H :=
  eapply Peq; [|apply H]; match_Nexpr.

Lemma halt: halts tm c0.
Proof with rw_all.
  eapply halts_evstep.
  2:{
  follow' init...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst1...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  finish.
  }
  followh Rst2.
Qed.

End TM9.


Module TM10.
Definition tm := Eval compute in (TM_from_str "1LB0RD_1LC1LB_0LD0LF_0RE0LD_1RA1RE_0LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (A,[]).
Notation hL := (C,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d0 := [1;1;0;0;1;1;0;0].
Notation d1 := [1;1;1;0;1;1;0;0].
Notation d2 := [1;1;1;1;1;1;1;1].


Definition LC1 n := 0inf <* <[0;0;1]^^n.

Definition tm' := flip tm.

Lemma LIncs1 n a:
  sideRLs tm' (hLR^^n) (LC1 a) (LC1 (n+a)).
Proof.
  unfold LC1.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Ltac solve_v1 :=
  intros H;
  eapply segRLs_sideRLs_concat; [|apply H];
  apply segRLs_addmul''; esx.

Lemma RIncs_S0 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*3+2)) (d0*>r) (d2*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S1 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*3+1)) (d1*>r) (d2*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S2 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*3+0)) (d2*>r) (d2*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S0s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(3^k*(n+1)-1)) (d0^^k*>r) (d2^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S0 in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Lemma pow3_mod2 a:
  3^a mod 2 = 1%nat.
Proof.
  induction a; cbn[Nat.pow]; lia.
Qed.

Lemma RIncs_S1s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^((3^k*(n*2+1)-1)/2)) (d1^^k*>r) (d2^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S1 in IHk.
    cbn[Nat.pow].
    pose proof (pow3_mod2 k).
    applys_eq IHk; flia.
Qed.

Lemma RIncs_S2s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(3^k*n)) (d2^^k*>r) (d2^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S2 in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Notation du := [1;1;1;1;1;1;0;0].

Lemma RIncs_Su r:
  sideRLs tm (hRL^^2) (du*>r) ([1;1;1;0;1;1;1;0]*>r).
Proof.
  esx.
Qed.

Notation "l |> r" := (l {{{ (hR,R) }}} r) (at level 30).

Lemma Incs1 a n r r':
  sideRLs tm (hRL^^n) r r' ->
  LC1 a |> r -->*
  LC1 (n+a) |> r'.
Proof.
  intros.
  epose proof (sideRLs_concat_1 H (LIncs1 _ _)) as I1.
  apply I1.
Qed.

Definition rh1 := ([1;1;1;1;1;0;0] *> d0 *> [1;1;1] *> 0inf).
Definition rh2 := ([1]^^5 *> 0inf).

Lemma RIncs_rh1:
  sideRLs tm (hRL^^15) rh1 (d2^^2 *> rh2).
Proof.
  esx.
Qed.

Lemma init:
  c0 -->*
  LC1 1 |> d0^^7 *> d1 *> d0 *> rh1.
Proof.
  esx.
Qed.

Lemma Rst1 a b:
  LC1 (5+a*8) |> d2^^b *> rh2 -->*
  LC1 1 |> d2^^(a*3+1) *> du *> d0^^b *> [1]^^6 *> 0inf.
Proof.
  unfold LC1,rh2.
  es.
Qed.

Lemma Rst2 l b c r:
  halts tm (l |> d2^^b *> [1;1;1;0;1;1;1;0] *> d0^^(1+c) *> r).
Proof.
  esx.
Qed.

Import NatModTactics.

Ltac solve_RIncs_1 :=
match goal with
| |- sideRLs _ _ ?r _ =>
  match r with
  | d0^^_ *> _ => apply RIncs_S0s
  | d1^^_ *> _ => apply RIncs_S1s
  | d2^^_ *> _ => apply RIncs_S2s
  | d0 *> _ => apply RIncs_S0
  | d1 *> _ => apply RIncs_S1
  | d2 *> _ => apply RIncs_S2
  | du *> _ => apply RIncs_Su
  | rh1 => apply RIncs_rh1
  end
end.

Ltac solve_RIncs :=
repeat solve_RIncs_1.

Ltac follow' H :=
  eapply evstep_trans; [eapply Peq; [|apply H]; match_Nexpr |].

Ltac followh H :=
  eapply Peq; [|apply H]; match_Nexpr.

Lemma halt: halts tm c0.
Proof with rw_all.
  eapply halts_evstep.
  2:{
  follow' init...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst1...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  finish.
  }
  followh Rst2.
Qed.

End TM10.


Module TM11.
Definition tm := Eval compute in (TM_from_str "1LB0RD_1LC1LB_0LD0LF_0RE1RA_1RA1RE_0LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (A,[]).
Notation hL := (C,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d0 := [1;1;0;0;1;1;0;0].
Notation d1 := [1;1;1;0;1;1;0;0].
Notation d2 := [1;1;1;1;1;1;1;1].


Definition LC1 n := 0inf <* <[0;0;1]^^n.

Definition tm' := flip tm.

Lemma LIncs1 n a:
  sideRLs tm' (hLR^^n) (LC1 a) (LC1 (n+a)).
Proof.
  unfold LC1.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Ltac solve_v1 :=
  intros H;
  eapply segRLs_sideRLs_concat; [|apply H];
  apply segRLs_addmul''; esx.

Lemma RIncs_S0 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*3+2)) (d0*>r) (d2*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S1 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*3+1)) (d1*>r) (d2*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S2 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*3+0)) (d2*>r) (d2*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S0s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(3^k*(n+1)-1)) (d0^^k*>r) (d2^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S0 in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Lemma pow3_mod2 a:
  3^a mod 2 = 1%nat.
Proof.
  induction a; cbn[Nat.pow]; lia.
Qed.

Lemma RIncs_S1s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^((3^k*(n*2+1)-1)/2)) (d1^^k*>r) (d2^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S1 in IHk.
    cbn[Nat.pow].
    pose proof (pow3_mod2 k).
    applys_eq IHk; flia.
Qed.

Lemma RIncs_S2s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(3^k*n)) (d2^^k*>r) (d2^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S2 in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Notation du := [1;1;1;1;1;1;0;0].

Lemma RIncs_Su r:
  sideRLs tm (hRL^^2) (du*>r) ([1;1;1;0;1;1;1;0]*>r).
Proof.
  esx.
Qed.

Notation "l |> r" := (l {{{ (hR,R) }}} r) (at level 30).

Lemma Incs1 a n r r':
  sideRLs tm (hRL^^n) r r' ->
  LC1 a |> r -->*
  LC1 (n+a) |> r'.
Proof.
  intros.
  epose proof (sideRLs_concat_1 H (LIncs1 _ _)) as I1.
  apply I1.
Qed.

Definition rh1 := ([1;1;1;1;1;0;0] *> d0 *> [1;1;1] *> 0inf).
Definition rh2 := ([1]^^5 *> 0inf).

Lemma RIncs_rh1:
  sideRLs tm (hRL^^15) rh1 (d2^^2 *> rh2).
Proof.
  esx.
Qed.

Lemma init:
  c0 -->*
  LC1 1 |> d0^^7 *> d1 *> d0 *> rh1.
Proof.
  esx.
Qed.

Lemma Rst1 a b:
  LC1 (5+a*8) |> d2^^b *> rh2 -->*
  LC1 1 |> d2^^(a*3+1) *> du *> d0^^b *> [1]^^6 *> 0inf.
Proof.
  unfold LC1,rh2.
  es.
Qed.

Lemma Rst2 l b c r:
  halts tm (l |> d2^^b *> [1;1;1;0;1;1;1;0] *> d0^^(1+c) *> r).
Proof.
  esx.
Qed.

Import NatModTactics.

Ltac solve_RIncs_1 :=
match goal with
| |- sideRLs _ _ ?r _ =>
  match r with
  | d0^^_ *> _ => apply RIncs_S0s
  | d1^^_ *> _ => apply RIncs_S1s
  | d2^^_ *> _ => apply RIncs_S2s
  | d0 *> _ => apply RIncs_S0
  | d1 *> _ => apply RIncs_S1
  | d2 *> _ => apply RIncs_S2
  | du *> _ => apply RIncs_Su
  | rh1 => apply RIncs_rh1
  end
end.

Ltac solve_RIncs :=
repeat solve_RIncs_1.

Ltac follow' H :=
  eapply evstep_trans; [eapply Peq; [|apply H]; match_Nexpr |].

Ltac followh H :=
  eapply Peq; [|apply H]; match_Nexpr.

Lemma halt: halts tm c0.
Proof with rw_all.
  eapply halts_evstep.
  2:{
  follow' init...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst1...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  finish.
  }
  followh Rst2.
Qed.

End TM11.


Module TM12.
Definition tm := Eval compute in (TM_from_str "1LB1LA_0LC0LF_0RD1RE_1RE1RD_1LA0RC_0LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,[]).
Notation hL := (B,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d0 := [1;1;0;0;1;1;0;0].
Notation d1 := [1;1;1;0;1;1;0;0].
Notation d2 := [1;1;1;1;1;1;1;1].


Definition LC1 n := 0inf <* <[0;0;1]^^n.

Definition tm' := flip tm.

Lemma LIncs1 n a:
  sideRLs tm' (hLR^^n) (LC1 a) (LC1 (n+a)).
Proof.
  unfold LC1.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Ltac solve_v1 :=
  intros H;
  eapply segRLs_sideRLs_concat; [|apply H];
  apply segRLs_addmul''; esx.

Lemma RIncs_S0 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*3+2)) (d0*>r) (d2*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S1 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*3+1)) (d1*>r) (d2*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S2 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*3+0)) (d2*>r) (d2*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S0s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(3^k*(n+1)-1)) (d0^^k*>r) (d2^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S0 in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Lemma pow3_mod2 a:
  3^a mod 2 = 1%nat.
Proof.
  induction a; cbn[Nat.pow]; lia.
Qed.

Lemma RIncs_S1s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^((3^k*(n*2+1)-1)/2)) (d1^^k*>r) (d2^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S1 in IHk.
    cbn[Nat.pow].
    pose proof (pow3_mod2 k).
    applys_eq IHk; flia.
Qed.

Lemma RIncs_S2s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(3^k*n)) (d2^^k*>r) (d2^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S2 in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Notation du := [1;1;0;0;1;1;1;0;1;1;0;0].

Lemma RIncs_Su r:
  sideRLs tm (hRL^^1) (du*>r) ([1;1;1;0;1;1;1;0;1;1;0;0]*>r).
Proof.
  esx.
Qed.

Notation "l |> r" := (l {{{ (hR,R) }}} r) (at level 30).

Lemma Incs1 a n r r':
  sideRLs tm (hRL^^n) r r' ->
  LC1 a |> r -->*
  LC1 (n+a) |> r'.
Proof.
  intros.
  epose proof (sideRLs_concat_1 H (LIncs1 _ _)) as I1.
  apply I1.
Qed.

Definition rh1 := ([1;1;0;0;1;0;0;1;1;1;0] *> d0^^2 *> [1]^^6 *> 0inf).
Definition rh2 := ([1] *> 0inf).

Lemma RIncs_rh1:
  sideRLs tm (hRL^^77) rh1 (d2^^4 *> rh2).
Proof.
  esx.
Qed.

Lemma RIncs_O r:
  sideRLs tm (hRL^^0) r r.
Proof.
  esx.
Qed.

Lemma init:
  c0 -->*
  LC1 2 |> d0^^6 *> rh1.
Proof.
  esx.
Qed.


Lemma Rst1 a b:
  LC1 (7+a*8) |> d2^^(1+b) *> rh2 -->*
  LC1 1 |> d2^^(2+a*3) *> [1;1] *> d0^^(1+b) *> [1]^^6 *> 0inf.
Proof.
  unfold LC1,rh2.
  es.
Qed.

Lemma Rst2 a b c r:
  LC1 (1+a*8) |> d2^^b *> [1;1] *> d0^^(1+c) *> r -->*
  LC1 1 |> d2^^(a*3) *> d0^^b *> du *> d0^^c *> r.
Proof.
  unfold LC1.
  es.
Qed.

Lemma Rst3 l b r:
  halts tm (l |> d2^^b *> [1;1;1;0;1;1;1;0;1;1;0;0] *> r).
Proof.
  esx.
Qed.

Import NatModTactics.

Ltac solve_RIncs_1 :=
match goal with
| |- sideRLs _ _ ?r _ =>
  match r with
  | d0^^_ *> _ => apply RIncs_S0s
  | d1^^_ *> _ => apply RIncs_S1s
  | d2^^_ *> _ => apply RIncs_S2s
  | d0 *> _ => apply RIncs_S0
  | d1 *> _ => apply RIncs_S1
  | d2 *> _ => apply RIncs_S2
  | du *> _ => apply RIncs_Su
  | rh1 => apply RIncs_rh1
  | _ => apply RIncs_O
  end
end.

Ltac solve_RIncs :=
repeat solve_RIncs_1.

Ltac follow' H :=
  eapply evstep_trans; [eapply Peq; [|apply H]; match_Nexpr |].

Ltac followh H :=
  eapply Peq; [|apply H]; match_Nexpr.

Lemma halt: halts tm c0.
Proof with rw_all.
  eapply halts_evstep.
  2:{
  follow' init...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst1...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst2...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  finish.
  }
  followh Rst3.
Qed.

End TM12.


Module TM13.
Definition tm := Eval compute in (TM_from_str "1LB1LA_0LC0LF_0RD0LC_1RE1RD_1LA0RC_0LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,[]).
Notation hL := (B,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d0 := [1;1;0;0;1;1;0;0].
Notation d1 := [1;1;1;0;1;1;0;0].
Notation d2 := [1;1;1;1;1;1;1;1].


Definition LC1 n := 0inf <* <[0;0;1]^^n.

Definition tm' := flip tm.

Lemma LIncs1 n a:
  sideRLs tm' (hLR^^n) (LC1 a) (LC1 (n+a)).
Proof.
  unfold LC1.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Ltac solve_v1 :=
  intros H;
  eapply segRLs_sideRLs_concat; [|apply H];
  apply segRLs_addmul''; esx.

Lemma RIncs_S0 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*3+2)) (d0*>r) (d2*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S1 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*3+1)) (d1*>r) (d2*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S2 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*3+0)) (d2*>r) (d2*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S0s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(3^k*(n+1)-1)) (d0^^k*>r) (d2^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S0 in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Lemma pow3_mod2 a:
  3^a mod 2 = 1%nat.
Proof.
  induction a; cbn[Nat.pow]; lia.
Qed.

Lemma RIncs_S1s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^((3^k*(n*2+1)-1)/2)) (d1^^k*>r) (d2^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S1 in IHk.
    cbn[Nat.pow].
    pose proof (pow3_mod2 k).
    applys_eq IHk; flia.
Qed.

Lemma RIncs_S2s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(3^k*n)) (d2^^k*>r) (d2^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S2 in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Notation du := [1;1;0;0;1;1;1;0;1;1;0;0].

Lemma RIncs_Su r:
  sideRLs tm (hRL^^1) (du*>r) ([1;1;1;0;1;1;1;0;1;1;0;0]*>r).
Proof.
  esx.
Qed.

Notation "l |> r" := (l {{{ (hR,R) }}} r) (at level 30).

Lemma Incs1 a n r r':
  sideRLs tm (hRL^^n) r r' ->
  LC1 a |> r -->*
  LC1 (n+a) |> r'.
Proof.
  intros.
  epose proof (sideRLs_concat_1 H (LIncs1 _ _)) as I1.
  apply I1.
Qed.

Definition rh1 := ([1;1;0;0;1;0;0;1;1;1;0] *> d0^^2 *> [1]^^6 *> 0inf).
Definition rh2 := ([1] *> 0inf).

Lemma RIncs_rh1:
  sideRLs tm (hRL^^77) rh1 (d2^^4 *> rh2).
Proof.
  esx.
Qed.

Lemma RIncs_O r:
  sideRLs tm (hRL^^0) r r.
Proof.
  esx.
Qed.

Lemma init:
  c0 -->*
  LC1 2 |> d0^^6 *> rh1.
Proof.
  esx.
Qed.


Lemma Rst1 a b:
  LC1 (7+a*8) |> d2^^(1+b) *> rh2 -->*
  LC1 1 |> d2^^(2+a*3) *> [1;1] *> d0^^(1+b) *> [1]^^6 *> 0inf.
Proof.
  unfold LC1,rh2.
  es.
Qed.

Lemma Rst2 a b c r:
  LC1 (1+a*8) |> d2^^b *> [1;1] *> d0^^(1+c) *> r -->*
  LC1 1 |> d2^^(a*3) *> d0^^b *> du *> d0^^c *> r.
Proof.
  unfold LC1.
  es.
Qed.

Lemma Rst3 l b r:
  halts tm (l |> d2^^b *> [1;1;1;0;1;1;1;0;1;1;0;0] *> r).
Proof.
  esx.
Qed.

Import NatModTactics.

Ltac solve_RIncs_1 :=
match goal with
| |- sideRLs _ _ ?r _ =>
  match r with
  | d0^^_ *> _ => apply RIncs_S0s
  | d1^^_ *> _ => apply RIncs_S1s
  | d2^^_ *> _ => apply RIncs_S2s
  | d0 *> _ => apply RIncs_S0
  | d1 *> _ => apply RIncs_S1
  | d2 *> _ => apply RIncs_S2
  | du *> _ => apply RIncs_Su
  | rh1 => apply RIncs_rh1
  | _ => apply RIncs_O
  end
end.

Ltac solve_RIncs :=
repeat solve_RIncs_1.

Ltac follow' H :=
  eapply evstep_trans; [eapply Peq; [|apply H]; match_Nexpr |].

Ltac followh H :=
  eapply Peq; [|apply H]; match_Nexpr.

Lemma halt: halts tm c0.
Proof with rw_all.
  eapply halts_evstep.
  2:{
  follow' init...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst1...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst2...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  finish.
  }
  followh Rst3.
Qed.

End TM13.


Module TM14.
Definition tm := Eval compute in (TM_from_str "1LB1LA_0LC0LB_1RC0RD_1LE0RF_1RA---_1RE0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (D,<[0]).
Notation hL := (B,[1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d0 := [1;1;1;1;0;0;0;1].
Notation d1 := [1;1;1;1;1;0;0;1].
Notation d2 := [1;1;1;1;1;1;1;1].


Definition LC1 n := 0inf <* <[1;1;0] <* <[1]^^n.

Definition tm' := flip tm.

Lemma LIncs1 n a:
  sideRLs tm' (hLR^^n) (LC1 a) (LC1 (n*3+a)).
Proof.
  unfold LC1.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Definition LC2 n := 0inf <* <[1]^^n.

Lemma LIncs2 n a:
  sideRLs tm' (hLR^^n) (LC2 a) (LC2 (n*2+a)).
Proof.
  unfold LC2.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Ltac solve_v1 :=
  intros H;
  eapply segRLs_sideRLs_concat; [|apply H];
  apply segRLs_addmul''; esx.

Lemma RIncs_S0 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*3+2)) (d0*>r) (d2*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S1 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*3+1)) (d1*>r) (d2*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S2 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*3+0)) (d2*>r) (d2*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S0s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(3^k*(n+1)-1)) (d0^^k*>r) (d2^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S0 in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Lemma pow3_mod2 a:
  3^a mod 2 = 1%nat.
Proof.
  induction a; cbn[Nat.pow]; lia.
Qed.

Lemma RIncs_S1s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^((3^k*(n*2+1)-1)/2)) (d1^^k*>r) (d2^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S1 in IHk.
    cbn[Nat.pow].
    pose proof (pow3_mod2 k).
    applys_eq IHk; flia.
Qed.

Lemma RIncs_S2s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(3^k*n)) (d2^^k*>r) (d2^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S2 in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Notation "l |> r" := (l {{{ (hR,R) }}} r) (at level 30).

Lemma Incs1 a n r r':
  sideRLs tm (hRL^^n) r r' ->
  LC1 a |> r -->*
  LC1 (n*3+a) |> r'.
Proof.
  intros.
  epose proof (sideRLs_concat_1 H (LIncs1 _ _)) as I1.
  apply I1.
Qed.

Lemma Incs2 a n r r':
  sideRLs tm (hRL^^n) r r' ->
  LC2 a |> r -->*
  LC2 (n*2+a) |> r'.
Proof.
  intros.
  epose proof (sideRLs_concat_1 H (LIncs2 _ _)) as I1.
  apply I1.
Qed.

Definition rh1 := (
  [0]^^3 *> [1]^^5 *> [0]^^3 *> [1]^^10 *> 
  [0]^^3 *> [1]^^9 *> [0]^^7 *> [1]^^10 *> 
  [0]^^3 *> [1]^^5 *> [0]^^3 *> [1]^^10 *> 
  0inf).

Lemma RIncs_O r:
  sideRLs tm (hRL^^0) r r.
Proof.
  esx.
Qed.

Notation dx := [0;0;0;0;0;0;0;1; 1;1;1;1;1;1;1;1].

Ltac stepn' n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; try reflexivity.

Lemma init:
  c0 -->*
  LC1 6 |> d0^^60 *> d2 *> dx^^2 *> rh1.
Proof.
  stepn' 133400%N.
Qed.

Notation dy := [1;1;1;1;0;0;0;0;0;0;1].

Lemma RIncs_Sy r:
  sideRLs tm (hRL^^2) (dy *> r) (d2 *> [1;0;1] *> r).
Proof.
  esx.
Qed.

Lemma Rst1 a b c r:
  LC1 (6+a*8) |> d2^^(2+b) *> dx^^(1+c) *> r -->*
  LC2 6 |> d0^^a *> dy *> d1 *> d0^^b *> [1]^^5 *> [0]^^6 *> [1]^^9 *> dx^^c *> r.
Proof.
  unfold LC1,LC2.
  es.
Qed.

Lemma Rst2 l b r:
  halts tm (l |> d2^^b *> [1;0;1] *> r).
Proof.
  esx.
Qed.

Import NatModTactics.

Ltac solve_RIncs_1 :=
match goal with
| |- sideRLs _ _ ?r _ =>
  match r with
  | d0^^_ *> _ => apply RIncs_S0s
  | d1^^_ *> _ => apply RIncs_S1s
  | d2^^_ *> _ => apply RIncs_S2s
  | d0 *> _ => apply RIncs_S0
  | d1 *> _ => apply RIncs_S1
  | d2 *> _ => apply RIncs_S2
  | dy *> _ => apply RIncs_Sy
  | _ => apply RIncs_O
  end
end.

Ltac solve_RIncs :=
repeat solve_RIncs_1.

Ltac follow' H :=
  eapply evstep_trans; [eapply Peq; [|apply H]; match_Nexpr |].

Ltac followh H :=
  eapply Peq; [|apply H]; match_Nexpr.

Lemma halt: halts tm c0.
Proof with rw_all.
  eapply halts_evstep.
  2:{
  follow' init...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst1...

  follow' Incs2.
  1: solve_RIncs.
  rw_lpow_add...
  finish.
  }
  followh Rst2.
Qed.

End TM14.


Module TM15.
Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC0LA_1RD0RB_1RA0RB_0LF1LA_---0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (B,<[]).
Notation hL := (A,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d3 := [1;0;1;0;0;1;0;1].
Notation d4 := [0;0;1;0;0;1;0;1].
Notation du := [0;0;1;1;0;0;1;1].


Definition LC1 n := 0inf <* <[1;0]^^n.

Definition tm' := flip tm.

Lemma LIncs1 n a:
  sideRLs tm' (hLR^^n) (LC1 a) (LC1 (n+a)).
Proof.
  unfold LC1.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Ltac solve_v1 :=
  intros H;
  eapply segRLs_sideRLs_concat; [|apply H];
  apply segRLs_addmul''; esx.

Notation d4a := [0;0;1;0;0;1].
Notation d0a := [0;0;0;0;0;1].

Lemma RIncs_S0a n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*5+4)) (d0a*>r) (d4a*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S2a n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*5+2)) ([0]*>[0;0;1;0;1]*>r) (d4a*>r').
Proof.
  rewrite <-Str_app_assoc.
  solve_v1.
Qed.

Lemma RIncs_S3 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*5+1)) (d3*>r) (d4*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S4 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*5+0)) (d4*>r) (d4*>r').
Proof.
  solve_v1.
Qed.

Lemma pow5_mod4 a:
  5^a mod 4 = 1%nat.
Proof.
  induction a; cbn[Nat.pow]; lia.
Qed.

Lemma RIncs_S3s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^((5^k*(n*4+1)-1)/4)) (d3^^k*>r) (d4^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S3 in IHk.
    cbn[Nat.pow].
    pose proof (pow5_mod4 k).
    applys_eq IHk; flia.
Qed.

Lemma RIncs_Sus k n r r':
  sideRLs tm (hRL^^n) ([0] *> r) r' ->
  sideRLs tm (hRL^^(5^k*(n+1)-1)) ([0] *> du^^k *> r) (d4^^k *> r').
Proof.
  intros.
  induction k.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    cbn[Nat.pow].
    replace (5*5^k*(n+1)-1) with (4+((5^k*(n+1)-1)*5+0)) by lia. 
    rewrite lpow_add.
    eapply sideRLs_trans.
    2: eapply @segRLs_sideRLs_concat with (w1:=d4).
    3: apply IHk.
    2: apply segRLs_addmul''; esx.
    esx.
Qed.

Notation "l |> r" := (l {{{ (hR,R) }}} r) (at level 30).

Lemma Incs1 a n r r':
  sideRLs tm (hRL^^n) r r' ->
  LC1 a |> r -->*
  LC1 (n+a) |> r'.
Proof.
  intros.
  epose proof (sideRLs_concat_1 H (LIncs1 _ _)) as I1.
  apply I1.
Qed.

Notation da := [0;0;1;1;0;0;1;0].

Lemma RIncs_Sa n r r':
  sideRLs tm (hRL^^(n+1)) ([0]*>r) r' ->
  sideRLs tm (hRL^^(n*5+4)) ([0]*>da*>r) (d4*>r').
Proof.
  intros.
  replace (n*5+4) with (2+(n*5+2)) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: eapply @segRLs_sideRLs_concat with (w1:=[0;0;1;0;1;0;0;1]).
  3: apply H.
  1: esx.
  apply segRLs_addmul; esx.
Qed.

Notation da2 := [0;0;0;1;0;0;1;0].

Lemma RIncs_Sa2 n r r':
  sideRLs tm (hRL^^(n+1)) ([0]*>r) r' ->
  sideRLs tm (hRL^^(n*5+6)) ([0]*>da2*>r) (d4*>r').
Proof.
  intros.
  replace (n*5+6) with (4+(n*5+2)) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: eapply @segRLs_sideRLs_concat with (w1:=[0;0;1;0;1;0;0;1]).
  3: apply H.
  1: esx.
  apply segRLs_addmul; esx.
Qed.

Notation db := [1;1;0;1;0;0;1;0].
Notation d4' := [0;1;0;0;1;0;0;1].

Lemma RIncs_Sb n r r':
  sideRLs tm (hRL^^n) ([0]*>r) r' ->
  sideRLs tm (hRL^^(n*5+1)) ([0]*>db*>r) (d4'*>r').
Proof.
  intros.
  replace (n*5+1) with (1+(n*5+0)) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: eapply @segRLs_sideRLs_concat with (w1:=d4').
  3: apply H.
  1: esx.
  apply segRLs_addmul''; esx.
Qed.

Notation dw := [0;1].

Lemma RIncs_Sw n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^n) ([0]*>[1]*>r) (dw*>r').
Proof.
  rewrite <-Str_app_assoc.
  intro H.
  replace n with (n*1+0) by lia.
  gen H.
  solve_v1.
Qed.

Definition rh1 := ([1;0;0;0;0;0;1;1;0;0;1] *> 0inf).

Lemma RIncs_O r:
  sideRLs tm (hRL^^0) r r.
Proof.
  esx.
Qed.

Definition rh2 := (0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0inf).
Lemma RIncs_rh1:
  sideRLs tm (hRL^^19) ([0]*>rh1) (rh2).
Proof.
  esx.
Qed.

Ltac stepn' n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; try reflexivity.

Lemma init:
  c0 -->*
  LC1 2 |> [0] *> du^^22 *> da*>db*>rh1.
Proof.
  stepn' 17961%N.
Qed.

Lemma Rst1 a b:
  LC1 (1+a*4) |> d4^^(1+b)*>d4'*>rh2 -->*
  LC1 2 |> [0] *> du^^a *> [0;0;1;0;1] *> d3^^b *> [0]*>da2*>db*>rh1.
Proof.
  unfold LC1.
  es.
Qed.

Lemma Rst2 a b c:
  LC1 (3+a*4) |> d4^^b *> d4a *> d4^^(1+c) *> d4' *> rh2 -->*
  LC1 2 |> [0] *> du^^a *> da *> [1] *> d3^^b *> d0a *> d3^^c *> [0]*>da2*>db*>rh1.
Proof.
  unfold LC1.
  es.
Qed.

Lemma Rst3 a b c d:
  halts tm (LC1 (0+a*4) |> d4^^(1+b) *> dw *> d4^^c *> d4a *> d4^^(1+d) *> d4' *> rh2).
Proof.
  unfold LC1.
  esx.
Qed.

Import NatModTactics.

Ltac solve_RIncs_1 :=
match goal with
| |- sideRLs _ _ ?r _ =>
  match r with
  | [0] *> du^^_ *> _ => apply RIncs_Sus
  | d3^^_ *> _ => apply RIncs_S3s
  | [0] *> da *> _ => apply RIncs_Sa
  | [0] *> da2 *> _ => apply RIncs_Sa2
  | [0] *> db *> _ => apply RIncs_Sb
  | d0a *> _ => apply RIncs_S0a
  | [0] *> [0;0;1;0;1] *> _ => apply RIncs_S2a
  | [0] *> [1] *> _ => apply RIncs_Sw
  | [0] *> rh1 => apply RIncs_rh1
  end
end.

Ltac solve_RIncs :=
repeat solve_RIncs_1.

Ltac follow' H :=
  eapply evstep_trans; [eapply Peq; [|apply H]; match_Nexpr |].

Ltac followh H :=
  eapply Peq; [|apply H]; match_Nexpr.

Lemma halt: halts tm c0.
Proof with rw_all.
  eapply halts_evstep.
  2:{
  follow' init...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst1...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst2...

  follow' Incs1.
  1: solve_RIncs.
  1: apply sideRLs_add.
  1: solve_RIncs.
  1: solve_Nexpr_ge.
  rw_lpow_add...
  finish.
  }
  followh Rst3.
Qed.

End TM15.


Module TM16.
Definition tm := Eval compute in (TM_from_str "1RB0LD_1LC0RF_1RF1LD_1LE---_0LC0LE_0RA0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (A,<[]).
Notation hL := (D,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d0 := [1;0;0;1].
Notation d7 := [0;1;1;0].

Definition LC1 n := 0inf <* <[1;0;1;0]^^n <* <[0].

Definition tm' := flip tm.

Lemma LIncs1 n a:
  sideRLs tm' (hLR^^n) (LC1 a) (LC1 (n+a)).
Proof.
  unfold LC1.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Ltac solve_v1 :=
  intros H;
  eapply segRLs_sideRLs_concat; [|apply H];
  apply segRLs_addmul''; esx.

Lemma RIncs_S0 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*8+7)) (d0*>r) (d7*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S0s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(8^k*(n+1)-1)) (d0^^k*>r) (d7^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S0 in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Notation "l |> r" := (l {{{ (hR,R) }}} r) (at level 30).

Lemma Incs1 a n r r':
  sideRLs tm (hRL^^n) r r' ->
  LC1 a |> r -->*
  LC1 (n+a) |> r'.
Proof.
  intros.
  epose proof (sideRLs_concat_1 H (LIncs1 _ _)) as I1.
  apply I1.
Qed.

Definition rh1 := ([0;0;1;1;1;1;1;0;1;1;1] *> 0inf).

Lemma RIncs_O r:
  sideRLs tm (hRL^^0) r r.
Proof.
  esx.
Qed.

Lemma RIncs_10 r:
  sideRLs tm (hRL^^3) ([1;0]*>r) ([0;1]*>r).
Proof.
  esx.
Qed.

Lemma init:
  c0 -->*
  LC1 1 |> d0^^5 *> [1;0]*>rh1.
Proof.
  esx.
Qed.

Definition rh3 := [1;1;1;1;1;1;1;0;0;1;0;1;1]*>0inf.
Lemma Rst1 a b:
  LC1 (1+a) |> d7^^b *> [0;1] *> rh1 -->*
  LC1 1 |> d0^^a *> [1;0] *> [0;0;1] *> d0^^b *> rh3.
Proof.
  unfold LC1.
  es.
Qed.

Lemma Rst2 l a b:
  halts tm (l |> d7^^a *> [0;1] *> [0;0;1] *> d0^^b *> rh3).
Proof.
  esx.
Qed.

Import NatModTactics.

Ltac solve_RIncs_1 :=
match goal with
| |- sideRLs _ _ ?r _ =>
  match r with
  | d0^^_ *> _ => apply RIncs_S0s
  | [1;0] *> _ => apply RIncs_10
  end
end.

Ltac solve_RIncs :=
repeat solve_RIncs_1.

Ltac follow' H :=
  eapply evstep_trans; [eapply Peq; [|apply H]; match_Nexpr |].

Ltac followh H :=
  eapply Peq; [|apply H]; match_Nexpr.

Lemma halt: halts tm c0.
Proof with rw_all.
  eapply halts_evstep.
  2:{
  follow' init...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst1...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  finish.
  }
  followh Rst2.
Qed.

End TM16.


Module TM17.
Definition tm := Eval compute in (TM_from_str "1LB---_0LC0LB_1RD1LA_0RE0RB_1RF0LA_1LC0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[]).
Notation hL := (A,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d0 := [1;0;0;1].
Notation d7 := [0;1;1;0].

Definition LC1 n := 0inf <* <[1;0;1;0]^^n <* <[0].

Definition tm' := flip tm.

Lemma LIncs1 n a:
  sideRLs tm' (hLR^^n) (LC1 a) (LC1 (n+a)).
Proof.
  unfold LC1.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Ltac solve_v1 :=
  intros H;
  eapply segRLs_sideRLs_concat; [|apply H];
  apply segRLs_addmul''; esx.

Lemma RIncs_S0 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*8+7)) (d0*>r) (d7*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S0s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(8^k*(n+1)-1)) (d0^^k*>r) (d7^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S0 in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Notation "l |> r" := (l {{{ (hR,R) }}} r) (at level 30).

Lemma Incs1 a n r r':
  sideRLs tm (hRL^^n) r r' ->
  LC1 a |> r -->*
  LC1 (n+a) |> r'.
Proof.
  intros.
  epose proof (sideRLs_concat_1 H (LIncs1 _ _)) as I1.
  apply I1.
Qed.

Definition rh1 := ([0;0;1;1;1;1;1;0;1;1;1] *> 0inf).

Lemma RIncs_O r:
  sideRLs tm (hRL^^0) r r.
Proof.
  esx.
Qed.

Lemma RIncs_10 r:
  sideRLs tm (hRL^^3) ([1;0]*>r) ([0;1]*>r).
Proof.
  esx.
Qed.

Lemma init:
  c0 -->*
  LC1 1 |> d0^^6 *> [1;0]*>rh1.
Proof.
  esx.
Qed.

Definition rh3 := [1;1;1;1;1;1;1;0;0;1;0;1;1]*>0inf.
Lemma Rst1 a b:
  LC1 (1+a) |> d7^^b *> [0;1] *> rh1 -->*
  LC1 1 |> d0^^a *> [1;0] *> [0;0;1] *> d0^^b *> rh3.
Proof.
  unfold LC1.
  es.
Qed.

Lemma Rst2 l a b:
  halts tm (l |> d7^^a *> [0;1] *> [0;0;1] *> d0^^b *> rh3).
Proof.
  esx.
Qed.

Import NatModTactics.

Ltac solve_RIncs_1 :=
match goal with
| |- sideRLs _ _ ?r _ =>
  match r with
  | d0^^_ *> _ => apply RIncs_S0s
  | [1;0] *> _ => apply RIncs_10
  end
end.

Ltac solve_RIncs :=
repeat solve_RIncs_1.

Ltac follow' H :=
  eapply evstep_trans; [eapply Peq; [|apply H]; match_Nexpr |].

Ltac followh H :=
  eapply Peq; [|apply H]; match_Nexpr.

Lemma halt: halts tm c0.
Proof with rw_all.
  eapply halts_evstep.
  2:{
  follow' init...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst1...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  finish.
  }
  followh Rst2.
Qed.

End TM17.


Module TM18.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1LC0RE_1LF0LD_1LA0LF_0RB0RD_0LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (B,<[0;0]).
Notation hL := (A,[0;1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d0 := [0;1;1;0;1;0;0;1;0].
Notation d1 := [1;1;1;0;1;0;0;1;0].
Notation d3 := [1;1;1;1;1;0;0;1;0].
Notation d0' := [0;1;0;0;1;1;0;1;1].
Notation d1' := [1;1;0;0;1;1;0;1;1].


Definition LC1 n := 0inf <* <[1;0;0;0;1;0]^^n <* <[1;0;0].

Definition tm' := flip tm.

Lemma LIncs1 n a:
  sideRLs tm' (hLR^^n) (LC1 a) (LC1 (n+a)).
Proof.
  unfold LC1.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Ltac solve_v1 :=
  intros H;
  eapply segRLs_sideRLs_concat; [|apply H];
  apply segRLs_addmul''; esx.

Lemma RIncs_S0 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*4+3)) (d0*>r) (d3*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S1 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*4+2)) (d1*>r) (d3*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S3 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*4+0)) (d3*>r) (d3*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S0' n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+1)) (d0'*>r) (d1'*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S1' n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+0)) (d1'*>r) (d1'*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S0's k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(2^k*(n+1)-1)) (d0'^^k*>r) (d1'^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S0' in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Lemma RIncs_S1's k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(2^k*n)) (d1'^^k*>r) (d1'^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S1' in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Lemma pow4_mod3 a:
  4^a mod 3 = 1%nat.
Proof.
  induction a; cbn[Nat.pow]; lia.
Qed.

Lemma RIncs_S0s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(4^k*(n+1)-1)) (d0^^k*>r) (d3^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S0 in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Lemma RIncs_S1s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^((4^k*(n*3+2)-2)/3)) (d1^^k*>r) (d3^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S1 in IHk.
    cbn[Nat.pow].
    pose proof (pow4_mod3 k).
    applys_eq IHk; flia.
Qed.

Lemma RIncs_O r:
  sideRLs tm (hRL^^0) r r.
Proof.
  esx.
Qed.

Notation "l |> r" := (l {{{ (hR,R) }}} r) (at level 30).

Lemma Incs1 a n r r':
  sideRLs tm (hRL^^n) r r' ->
  LC1 a |> r -->*
  LC1 (n+a) |> r'.
Proof.
  intros.
  epose proof (sideRLs_concat_1 H (LIncs1 _ _)) as I1.
  apply I1.
Qed.

Definition rh1 := [1;1;0;0;1;1;0;1;1;1;1;0;0;1;0;0;1;1;0;1;0;0;1;0;1]*>0inf.

Lemma init:
  c0 -->*
  LC1 1 |> d1^^11 *> rh1.
Proof.
  esx.
Qed.

Definition rh2 := (1 >> 1 >> 0 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0inf).

Lemma RIncs_rh1:
  sideRLs tm (hRL^^12) (rh1) (rh2).
Proof.
  esx.
Qed.

Definition rh3 := (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0inf).
Definition rh4 := (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0inf).

Lemma RIncs_rh3:
  sideRLs tm (hRL^^1) (rh3) (rh4).
Proof.
  esx.
Qed.

Definition rh5 := (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0inf).
Definition rh6 := (1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0inf).

Lemma RIncs_rh5:
  sideRLs tm (hRL^^2) (rh5) (rh6).
Proof.
  esx.
Qed.

Definition rh7 := (0>>1>>0>>0>>1>>1>>0>>1>> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 0 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0inf).
Definition rh8 := (d1' *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 0 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0inf).

Lemma RIncs_rh7:
  sideRLs tm (hRL^^3) (rh7) (rh8).
Proof.
  esx.
Qed.

Definition rh9 := ([0;1;0;0;1;1;0;1]*>0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 0 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0inf).
Definition rh10 := (1 >> 1 >> 0 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 0 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0inf).
Lemma RIncs_rh9:
  sideRLs tm (hRL^^7) (rh9) (rh10).
Proof.
  esx.
Qed.

Import NatModTactics.

Ltac solve_RIncs_1 :=
match goal with
| |- sideRLs _ _ ?r _ =>
  match r with
  | d0^^_ *> _ => apply RIncs_S0s
  | d1^^_ *> _ => apply RIncs_S1s
  | d0'^^_ *> _ => apply RIncs_S0's
  | d1'^^_ *> _ => apply RIncs_S1's
  | rh1 => apply RIncs_rh1
  | rh3 => apply RIncs_rh3
  | rh5 => apply RIncs_rh5
  | rh7 => apply RIncs_rh7
  | rh9 => apply RIncs_rh9
  end
end.

Ltac solve_RIncs :=
repeat solve_RIncs_1.

Ltac follow' H :=
  eapply evstep_trans; [eapply Peq; [|apply H]; match_Nexpr |].

Lemma Rst1 a b:
  LC1 a |> d3^^(1+b) *> rh2 -->*
  LC1 (1+a) |> d0^^(1+b) *> rh3.
Proof.
  unfold LC1,rh2,rh3.
  es; er.
  use_shift_rule'.
  es.
Qed.

Definition S2 a b r :=
  0inf <{{D}} [0;1] *> [1;0;1;0;0;1]^^a *> [0;1;0;1;1;1;0] *> [1;1;0;1;0;0;1;0;1]^^b *> r.

Lemma Inc2 a b r:
  S2 (1+a) b r -->*
  S2 a (1+b) r.
Proof.
  es.
Qed.

Lemma Incs2 a b r:
  S2 a b r -->*
  S2 0 (a+b) r.
Proof.
  gen b.
  ind a Inc2.
Qed.

Lemma Rst2 a b:
  LC1 (1+a) |> d3^^(1+b) *> rh4 -->*
  LC1 1 |> d1^^(1+a) *> d1'^^(1+b) *> rh5.
Proof.
  unfold LC1,rh4,rh5.
  do 3 (er; sr).
  epose proof (Incs2 a 0 _) as I1.
  follow I1. clear I1.
  es.
Qed.

Lemma Rst3 a b c:
  LC1 a |> d3^^(b) *> d1'^^(2+c) *> rh6 -->*
  LC1 (1+a) |> d0^^b *> d0'^^c *> rh7.
Proof.
  unfold LC1,rh6,rh7.
  es; er.
  use_shift_rule'.
  es.
Qed.

Lemma Rst4 a b c:
  LC1 a |> d3^^(b) *> d1'^^(1+c) *> rh8 -->*
  LC1 (1+a) |> d0^^b *> d0'^^c *> rh9.
Proof.
  unfold LC1,rh8,rh9.
  es; er.
  use_shift_rule'.
  es.
Qed.

Lemma Rst5 l b c:
  halts tm (l |> d3^^b *> d1'^^c *> rh10).
Proof.
  esx.
Qed.

Lemma halt: halts tm c0.
Proof with rw_all.
  eapply halts_evstep.
  2:{
  follow' init...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst1...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst2...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst3...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst4...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  finish.
  }
  apply Rst5.
Qed.

End TM18.


Module TM20.
Definition tm := Eval compute in (TM_from_str "1RB1RF_0LB1LC_1LD1LF_1RE0LA_---0RA_1RA0RD").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Import DivModCases.

Ltac follow' H :=
  let I1:=fresh "I" in
  epose proof H as I1;
  (eapply evstep_progress_trans || eapply evstep_trans); [| follow I1; clear I1]; [es | ].

Definition P1 n a :=
  forall l a0,
  l <* <[1;1;1;0]^^n <{{F}} [1;1;0;1;0;1;1;0] *> [1;0]^^a0 *> 0inf -->*
  l <{{F}} [1;1;0;1;0] *> [1;0;1;0]^^n *> [1;1;0] *> [1;0]^^(a+a0) *> 0inf.

Definition P2 n a :=
  forall l a0,
  l <* <[1;1;1;0]^^n <{{F}} [1;1;0;1;0;1;0;1;1;0] *> [1;0]^^a0 *> 0inf -->*
  l <{{F}} [1;1;0;1;0;1;0] *> [1;0;1;0]^^n *> [1;1;0] *> [1;0]^^(a+a0) *> 0inf.

Lemma P1_S n a a1:
  P1 n a ->
  P2 n a1 ->
  P1 (1+n) (a+a1).
Proof.
  unfold P1,P2.
  intros HP1 HP2 l a0.
  replace (a+a1+a0) with (a1+a+a0) by lia.
  follow' (HP1 (l<*<[1;1;1;0]) a0).
  follow' (HP2 (l<*<[1;1]) (a+a0)).
  es.
Qed.

Lemma P2_S n a a1:
  P2 n a ->
  P1 (1+n) a1 ->
  P2 (1+n) (1+a+a1).
Proof.
  unfold P1,P2.
  intros HP2 HP1 l a0.
  replace (1+a+a1+a0) with (1+a1+a+a0) by lia.
  follow' (HP2 (l<*<[1;1;1;0]) a0).
  follow' (HP1 (l<*<[1;1]) (1+a+a0)).
  es.
Qed.

Lemma P1_O: P1 0 0.
Proof.
  unfold P1; es.
Qed.

Lemma P2_O: P2 0 0.
Proof.
  unfold P2; es.
Qed.

Lemma init:
  c0 -->*
  0inf <* <[1;0] <* <[1]^^26 <* <[1;1;1;0]^^72 <{{F}} [1;1;0;1;0;1;1;0] *> 0inf.
Proof.
  esx.
Qed.

Lemma BigStep [n a n0 a0 a1]:
  P1 n a ->
  P1 (n+n0+1) a0 ->
  P2 (n0+n) a1 ->
  0inf <* <[1;0] <* <[1]^^(2+n0*4) <* <[1;1;1;0]^^n <{{F}} [1;1;0;1;0;1;1;0] *> 0inf -->*
  0inf <* [1] <{{F}} [1;1;0;1;0] *> [1;0;1;0]^^(n+n0+1) *> [1;1;0] *> [1;0]^^(2+a0*2+a1+a) *> 0inf.
Proof.
  unfold P1,P2.
  intros HP1 HP1' HP2.
  follow' (HP1 (0inf<*<[1;0]<*<[1]^^(2+n0*4)) O).
  follow' (HP1' 0inf (1+a)).
  follow' (HP2 (0inf<*<[1;1;0]) (1+a0+a)).
  follow' (HP1' (0inf<*[1]) (2+a1+a0+a)).
  finish.
Qed.

Lemma Halt x y:
  halts tm (0inf <* [1] <{{F}} [1;1;0;1;0] *> [1;0;1;0]^^x *> [1;1;0] *> [1;0]^^(y*2) *> 0inf).
Proof.
  esx.
Qed.

Close Scope sym.

Lemma P_n n:
  exists a1 a2,
  P1 n a1 /\ P2 n a2 /\
  match mod3 n with
  | mod3eq0 a => a1 mod 2 = 0 /\ a2 mod 2 = 0
  | mod3eq1 a => a1 mod 2 = 0 /\ a2 mod 2 = 1
  | mod3eq2 a => a1 mod 2 = 1 /\ a2 mod 2 = 1
  end.
Proof.
  induction n.
  - exists 0,0; repeat split.
    + apply P1_O.
    + apply P2_O.
  - destruct IHn as [a1 [a2 [HP1 [HP2 I1]]]].
    exists (a1+a2),(1+a2+(a1+a2)); repeat split.
    1,2: auto using P1_S,P2_S.
    destruct (mod3 n),(mod3 (S n)); lia.
Qed.

Ltac c_in x H:=
  eassert (E:x=_) by (vm_compute; reflexivity);
  rewrite E in H;
  clear E.


Lemma halt: halts tm c0.
Proof.
  epose proof (P_n 72) as [a1 [a2 [HP1 [HP2 I1]]]].
  epose proof (P_n (72+6+1)) as [a3 [a4 [HP1' [HP2' I2]]]].
  epose proof (P_n (6+72)) as [a5 [a6 [HP1'' [HP2'' I3]]]].
  c_in (mod3 72) I1.
  c_in (mod3 (72+6+1)) I2.
  c_in (mod3 (6+72)) I3.
  destruct (mod2 a6); try lia.
  destruct (mod2 a1); try lia.
  subst.
  eapply halts_evstep.
  2:{
    follow init.
    follow (BigStep HP1 HP1' HP2'').
    finish.
  }
  clear.
  applys_eq (Halt 79 (1+a3+a+a0)); flia.
Qed.

End TM20.

From BusyCoq Require Import ES_v3.

Lemma lpow_add'_11{T} (a:list T) r:
  a *> a *> r = a^^2 *> r.
Proof.
  cbn.
  repeat rewrite Str_app_assoc.
  reflexivity.
Qed.

Ltac rw_lpow_add ::=
  repeat (
  match goal with
  | |- context[?a^^1 *> _] =>
    rewrite (lpow_1 a)
  | |- context[?a *> ?a^^?y *> ?r] =>
    rewrite (lpow_add'_1x a y r)
  | |- context[?a^^?x *> ?a *> ?r] =>
    rewrite (lpow_add'_x1 a x r)
  | |- context[?a *> ?a *> ?r] =>
    rewrite (lpow_add'_11 a r)
  end ||
  rewrite lpow_add').


Module TM21.
Definition tm := Eval compute in (TM_from_str "1LB---_0LC1LA_0RD0LE_1LE0RE_0LF1LC_1RC1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (D,<[0]).
Notation hL := (F,[0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d0 := [0;0;1;0].
Notation d1 := [1;0;1;0].
Notation dw := [1;1;0].


Definition LC1 n := 0inf <* <[0;0;1]^^n.

Definition tm' := flip tm.

Lemma LIncs1 n a:
  sideRLs tm' (hLR^^n) (LC1 a) (LC1 (n+a)).
Proof.
  unfold LC1.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Ltac solve_v1 :=
  intros H;
  eapply segRLs_sideRLs_concat; [|apply H];
  apply segRLs_addmul''; esx.

Lemma RIncs_S0 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+1)) (d0*>r) (d1*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S1 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+0)) (d1*>r) (d1*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_Sw n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^n) (dw*>r) (dw*>r').
Proof.
  intro H.
  replace n with (n*1+0) by lia.
  gen H.
  solve_v1.
Qed.

Lemma RIncs_Sws k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^n) (dw^^k*>r) (dw^^k*>r').
Proof.
  intro H.
  replace n with (n*1+0) by lia.
  gen H.
  solve_v1.
Qed.

Lemma RIncs_S0s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(2^k*(n+1)-1)) (d0^^k*>r) (d1^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S0 in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Lemma RIncs_S1s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(2^k*n)) (d1^^k*>r) (d1^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S1 in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Lemma RIncs_O r:
  sideRLs tm (hRL^^0) r r.
Proof.
  esx.
Qed.

Notation "l |> r" := (l {{{ (hR,R) }}} r) (at level 30).

Lemma Incs1 a n r r':
  sideRLs tm (hRL^^n) r r' ->
  LC1 a |> r -->*
  LC1 (n+a) |> r'.
Proof.
  intros.
  epose proof (sideRLs_concat_1 H (LIncs1 _ _)) as I1.
  apply I1.
Qed.

Definition rh1 := [1]*>0inf.

Ltac stepn' n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; try reflexivity.

Lemma init:
  c0 -->*
  LC1 2 |> d1*>dw^^4*>d0*>dw*>d0*>d1^^2*>dw*>d0*>dw^^4*>d0*>dw^^4*>d0*>dw*>d1^^3*>dw*>d0*>dw^^4*>d0*>dw^^7*>d1*>dw^^2*>d1*>dw*>d0*>dw^^7*>d0^^2*>d1^^2*>d0*>rh1.
Proof.
  stepn' 18107%N.
  simpl_tape; reflexivity.
Qed.

Lemma RIncs_0 r:
  sideRLs tm (hRL^^1) ([0]*>r) ([1]*>r).
Proof.
  esx.
Qed.

Definition da := (dw++d0++dw^^4++d0++dw^^4++d0++dw++d1^^3).
Definition db := (dw++d1++dw^^4++d1++dw^^4++d1++dw++d1^^3).

Lemma RIncs_Sa n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*64+7)) (da*>r) (db*>r').
Proof.
  unfold da,db.
  intros.
  repeat rewrite Str_app_assoc.
  apply RIncs_S1s with (k:=3) in H.
  apply RIncs_Sw in H.
  apply RIncs_S0 in H.
  apply RIncs_Sws with (k:=4) in H.
  apply RIncs_S0 in H.
  apply RIncs_Sws with (k:=4) in H.
  apply RIncs_S0 in H.
  apply RIncs_Sw in H.
  applys_eq H; flia.
Qed.

Lemma pow64_mod9 a:
  64^a mod 9 = 1%nat.
Proof.
  induction a; cbn[Nat.pow]; lia.
Qed.

Lemma RIncs_Sas k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^((64^k*(n*9+1)-1)/9)) (da^^k*>r) (db^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_Sa in IHk.
    cbn[Nat.pow].
    pose proof (pow64_mod9 k).
    applys_eq IHk; flia.
Qed.


Ltac solve_RIncs_1 :=
match goal with
| |- sideRLs _ _ ?r _ =>
  match r with
  | d0^^_ *> _ => apply RIncs_S0s
  | d1^^_ *> _ => apply RIncs_S1s
  | dw^^_ *> _ => apply RIncs_Sws
  | da^^_ *> _ => apply RIncs_Sas
  | d0 *> _ => apply RIncs_S0
  | d1 *> _ => apply RIncs_S1
  | dw *> _ => apply RIncs_Sw
  | [0] *> _ => apply RIncs_0
  | _ => apply RIncs_O
  end
end.

Ltac solve_RIncs :=
repeat solve_RIncs_1.

Definition rh2 := 0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>1>>0inf.

Lemma Rst1 a:
  LC1 (10+a*18) |> d1*>dw^^4*>d1*>dw*>d1^^3*>dw*>d1*>dw^^4*>d1*>dw^^4*>d1*>dw*>d1^^3*>dw*>d1*>dw^^4*>d1*>dw^^7*>d1*>dw^^2*>d1*>dw*>d1*>dw^^7*>d1^^5*>rh1 -->*
  LC1 3 |> d0*>d1*>dw^^4*>d1*>dw*>d1*>d0*>d1*>da^^a*>dw^^4*>d0*>dw^^2*>d1^^3*>[0]*>rh2.
Proof.
  unfold LC1,rh1,rh2.
  cbn.
  es' a.
Qed.

Definition rh3 b := [1;1;1;1;0;1;0;1;1;1;0;1;0;1;1;1;1;1;1;1;0;1;0;1;1;1;0;1;0;1;1;1;1;1;1;1;0;1;0;1;0;0;0;1;0;0;0;1;0;0;0;1;1;1]^^b*>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>1>>0inf.

Lemma Rst2 a b:
  LC1 (30+a*18) |> d1^^2*>dw^^4*>d1*>dw*>d1^^3*>db^^b*>dw^^4*>d1*>dw^^2*>d1^^3*>[1]*>rh2 -->*
  LC1 6 |> d1*>dw^^4*>d1*>dw*>d0*>d1^^2*>da^^a*>dw*>d0*>dw^^4*>d0*>dw^^7*>d1*>d0*>dw^^4*>d1*>dw^^2*>d0^^3*>1>>0>>1>>1>>1>>rh3 b.
Proof.
  unfold LC1,rh3,rh2.
  cbn.
  es' a b.
Qed.

Definition rh4 b r := [1;1;1;1;0;1;0;1;0;0;0;1;0;0;0;1;0;0;0;1;1;1;1;1;1;1;0;1;0;1;1;1;0;1;0;1;1;1;1;1;1;1;0;1;0;1;1;1;0;1;0;1;1;1]^^b*>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>r.

Lemma Rst3 a b c:
  LC1 (14+a*18) |> d1*>dw^^4*>d1*>dw*>d1^^3*>db^^b*>dw*>d1*>dw^^4*>d1*>dw^^7*>d1^^2*>dw^^4*>d1*>dw^^2*>d1^^3*>1>>0>>1>>1>>1>>rh3 (1+c) -->*
  LC1 6 |> d1*>dw^^4*>d1*>dw*>d0*>d1^^2*>da^^a*>dw^^4*>d0*>dw^^2*>d1^^3*>
  [0]*>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>
  rh4 b (rh3 c).
Proof.
  unfold LC1,rh4,rh3.
  cbn.
  es' a b c.
Qed.

Definition rh5 b r :=
  [1;1;1;1;0;1;0;1;1;1;0;1;0;1;1;1;1;1;1;1;0;1;0;1;1;1;0;1;0;1;1;1;1;1;1;1;0;1;0;1;0;0;0;1;0;0;0;1;0;0;0;1;1;1]^^b*>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>r.

Lemma Rst4 a b c r:
  LC1 (16+a*18) |> d1*>dw^^4*>d1*>dw*>d1^^3*>db^^b*>dw^^4*>d1*>dw^^2*>d1^^3*>
  [1]*>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>
  rh4 (1+c) r -->*
  LC1 1 |> d0*>dw*>d1*>dw^^3*>d0*>dw^^4*>d0*>dw^^4*>d1*>dw*>d1^^3*>da^^a*>dw^^4*>d0*>dw^^2*>d1^^3*>
  [0]*>0>>1>>1>>1>>
  rh5 b (rh4 c r).
Proof.
  unfold LC1,rh5,rh4.
  cbn.
  es' a b c & r.
Qed.

Definition rh6 b r := [1;1;1;1;0;1;0;1;1;1;0;1;0;1;1;1;1;1;1;1;0;1;0;1;1;1;0;1;0;1;1;1;1;1;1;1;0;1;0;1;0;0;0;1;0;0;0;1;0;0;0;1;1;1]^^b*>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>r.

Lemma Rst5 a b c r:
  LC1 (30+a*18) |> d1*>dw*>d1*>dw^^3*>d1*>dw^^4*>d1*>dw^^4*>d1*>dw*>d1^^3*>db^^b*>dw^^4*>d1*>dw^^2*>d1^^3*>
  [1]*>0>>1>>1>>1>>
  rh5 (1+c) r -->*
  LC1 6 |> d1*>dw^^4*>d1*>dw*>d0*>d1^^2*>da^^a*>dw*>d0*>dw^^4*>d0*>dw^^7*>d1*>dw^^2*>d1*>d0^^2*>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>
  rh6 b (rh5 c r).
Proof.
  unfold LC1,rh6,rh5.
  cbn.
  es' a b c & r.
Qed.

Lemma Rst6 a b r:
  halts tm (LC1 (16+a*18) |>
  d1*>dw^^4*>d1*>dw*>d1^^3*>db^^b*>dw*>d1*>dw^^4*>d1*>dw^^7*>d1*>dw^^2*>d1^^3*>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>r).
Proof.
  unfold LC1,rh6.
  cbn.
  es' a b & r.
Qed.

Import NatModTactics.

Ltac follow' H :=
  eapply evstep_trans; [eapply Peq; [|apply H]; match_Nexpr |].

Lemma halt: halts tm c0.
Proof with rw_all.
  eapply halts_evstep.
  2:{
  follow' init.

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst1...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst2...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst3...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst4...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst5...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  finish.
  }
  eapply Peq; [|apply Rst6].
  match_Nexpr.
Time Qed.

End TM21.


Module TM22.
Definition tm := Eval compute in (TM_from_str "1RB---_1LC1LD_0LD0RD_1RF1LE_0LF1LA_0RB0LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (B,<[0]).
Notation hL := (D,[0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d0 := [0;0;1;0].
Notation d1 := [1;0;1;0].
Notation dw := [1;1;0].


Definition LC1 n := 0inf <* <[0;0;1]^^n.

Definition tm' := flip tm.

Lemma LIncs1 n a:
  sideRLs tm' (hLR^^n) (LC1 a) (LC1 (n+a)).
Proof.
  unfold LC1.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Ltac solve_v1 :=
  intros H;
  eapply segRLs_sideRLs_concat; [|apply H];
  apply segRLs_addmul''; esx.

Lemma RIncs_S0 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+1)) (d0*>r) (d1*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S1 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+0)) (d1*>r) (d1*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_Sw n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^n) (dw*>r) (dw*>r').
Proof.
  intro H.
  replace n with (n*1+0) by lia.
  gen H.
  solve_v1.
Qed.

Lemma RIncs_Sws k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^n) (dw^^k*>r) (dw^^k*>r').
Proof.
  intro H.
  replace n with (n*1+0) by lia.
  gen H.
  solve_v1.
Qed.

Lemma RIncs_S0s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(2^k*(n+1)-1)) (d0^^k*>r) (d1^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S0 in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Lemma RIncs_S1s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(2^k*n)) (d1^^k*>r) (d1^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S1 in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Lemma RIncs_O r:
  sideRLs tm (hRL^^0) r r.
Proof.
  esx.
Qed.

Notation "l |> r" := (l {{{ (hR,R) }}} r) (at level 30).

Lemma Incs1 a n r r':
  sideRLs tm (hRL^^n) r r' ->
  LC1 a |> r -->*
  LC1 (n+a) |> r'.
Proof.
  intros.
  epose proof (sideRLs_concat_1 H (LIncs1 _ _)) as I1.
  apply I1.
Qed.

Definition rh1 := [1]*>0inf.

Lemma init:
  c0 -->*
  LC1 2 |> d1*>dw^^4*>d0*>dw*>d0*>d1^^2*>dw*>d0*>dw^^4*>d0*>dw^^4*>d0*>dw*>d1^^3*>dw*>d0*>dw^^4*>d0*>dw^^7*>d1*>dw^^2*>d1*>dw*>d0*>dw^^7*>d0^^2*>d1^^2*>d0*>rh1.
Proof.
  esx.
Qed.

Lemma RIncs_0 r:
  sideRLs tm (hRL^^1) ([0]*>r) ([1]*>r).
Proof.
  esx.
Qed.

Definition da := (dw++d0++dw^^4++d0++dw^^4++d0++dw++d1^^3).
Definition db := (dw++d1++dw^^4++d1++dw^^4++d1++dw++d1^^3).

Lemma RIncs_Sa n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*64+7)) (da*>r) (db*>r').
Proof.
  unfold da,db.
  intros.
  repeat rewrite Str_app_assoc.
  apply RIncs_S1s with (k:=3) in H.
  apply RIncs_Sw in H.
  apply RIncs_S0 in H.
  apply RIncs_Sws with (k:=4) in H.
  apply RIncs_S0 in H.
  apply RIncs_Sws with (k:=4) in H.
  apply RIncs_S0 in H.
  apply RIncs_Sw in H.
  applys_eq H; flia.
Qed.

Lemma pow64_mod9 a:
  64^a mod 9 = 1%nat.
Proof.
  induction a; cbn[Nat.pow]; lia.
Qed.

Lemma RIncs_Sas k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^((64^k*(n*9+1)-1)/9)) (da^^k*>r) (db^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_Sa in IHk.
    cbn[Nat.pow].
    pose proof (pow64_mod9 k).
    applys_eq IHk; flia.
Qed.


Ltac solve_RIncs_1 :=
match goal with
| |- sideRLs _ _ ?r _ =>
  match r with
  | d0^^_ *> _ => apply RIncs_S0s
  | d1^^_ *> _ => apply RIncs_S1s
  | dw^^_ *> _ => apply RIncs_Sws
  | da^^_ *> _ => apply RIncs_Sas
  | d0 *> _ => apply RIncs_S0
  | d1 *> _ => apply RIncs_S1
  | dw *> _ => apply RIncs_Sw
  | [0] *> _ => apply RIncs_0
  | _ => apply RIncs_O
  end
end.

Ltac solve_RIncs :=
repeat solve_RIncs_1.

Definition rh2 := 0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>1>>0inf.

Lemma Rst1 a:
  LC1 (10+a*18) |> d1*>dw^^4*>d1*>dw*>d1^^3*>dw*>d1*>dw^^4*>d1*>dw^^4*>d1*>dw*>d1^^3*>dw*>d1*>dw^^4*>d1*>dw^^7*>d1*>dw^^2*>d1*>dw*>d1*>dw^^7*>d1^^5*>rh1 -->*
  LC1 3 |> d0*>d1*>dw^^4*>d1*>dw*>d1*>d0*>d1*>da^^a*>dw^^4*>d0*>dw^^2*>d1^^3*>[0]*>rh2.
Proof.
  unfold LC1,rh1,rh2.
  cbn.
  es' a.
Qed.

Definition rh3 b := [1;1;1;1;0;1;0;1;1;1;0;1;0;1;1;1;1;1;1;1;0;1;0;1;1;1;0;1;0;1;1;1;1;1;1;1;0;1;0;1;0;0;0;1;0;0;0;1;0;0;0;1;1;1]^^b*>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>1>>0inf.

Lemma Rst2 a b:
  LC1 (30+a*18) |> d1^^2*>dw^^4*>d1*>dw*>d1^^3*>db^^b*>dw^^4*>d1*>dw^^2*>d1^^3*>[1]*>rh2 -->*
  LC1 1 |> d0*>dw^^3*>d0*>dw^^4*>d0*>dw*>d1^^3*>da^^a*>dw*>d0*>dw^^4*>d0*>dw^^7*>d1*>d0*>dw^^4*>d1*>dw^^2*>d0^^3*>1>>0>>1>>1>>1>>
  rh3 b.
Proof.
  unfold LC1,rh3,rh2.
  cbn.
  es' a b.
Qed.

Lemma Rst3 a b c:
  halts tm (LC1 (34+a*18) |> d1*>dw^^3*>d1*>dw^^4*>d1*>dw*>d1^^3*>db^^b*>dw*>d1*>dw^^4*>d1*>dw^^7*>d1^^2*>dw^^4*>d1*>dw^^2*>d1^^3*>1>>0>>1>>1>>1>>rh3 (1+c)).
Proof.
  unfold LC1,rh3.
  cbn.
  es' a b c.
Qed.

Import NatModTactics.

Ltac follow' H :=
  eapply evstep_trans; [eapply Peq; [|apply H]; match_Nexpr |].

Lemma halt: halts tm c0.
Proof with rw_all.
  eapply halts_evstep.
  2:{
  follow' init.

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst1...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst2...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  finish.
  }
  eapply Peq; [|apply Rst3].
  match_Nexpr.
Time Qed.

End TM22.


Module TM23.
Definition tm := Eval compute in (TM_from_str "1LB---_0LC1LA_0RD0LE_1LE1RC_0LF0RF_1RC1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (D,<[0]).
Notation hL := (F,[0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d0 := [0;0;1;0].
Notation d1 := [1;0;1;0].
Notation dw := [1;1;0].


Definition LC1 n := 0inf <* <[0;0;1]^^n.

Definition tm' := flip tm.

Lemma LIncs1 n a:
  sideRLs tm' (hLR^^n) (LC1 a) (LC1 (n+a)).
Proof.
  unfold LC1.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Ltac solve_v1 :=
  intros H;
  eapply segRLs_sideRLs_concat; [|apply H];
  apply segRLs_addmul''; esx.

Lemma RIncs_S0 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+1)) (d0*>r) (d1*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S1 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+0)) (d1*>r) (d1*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_Sw n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^n) (dw*>r) (dw*>r').
Proof.
  intro H.
  replace n with (n*1+0) by lia.
  gen H.
  solve_v1.
Qed.

Lemma RIncs_Sws k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^n) (dw^^k*>r) (dw^^k*>r').
Proof.
  intro H.
  replace n with (n*1+0) by lia.
  gen H.
  solve_v1.
Qed.

Lemma RIncs_S0s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(2^k*(n+1)-1)) (d0^^k*>r) (d1^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S0 in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Lemma RIncs_S1s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(2^k*n)) (d1^^k*>r) (d1^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S1 in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Lemma RIncs_O r:
  sideRLs tm (hRL^^0) r r.
Proof.
  esx.
Qed.

Notation "l |> r" := (l {{{ (hR,R) }}} r) (at level 30).

Lemma Incs1 a n r r':
  sideRLs tm (hRL^^n) r r' ->
  LC1 a |> r -->*
  LC1 (n+a) |> r'.
Proof.
  intros.
  epose proof (sideRLs_concat_1 H (LIncs1 _ _)) as I1.
  apply I1.
Qed.

Definition rh1 := [1]*>0inf.

Lemma init:
  c0 -->*
  LC1 2 |> d1*>dw^^4*>d0*>dw*>d0*>d1^^2*>dw*>d0*>dw^^4*>d0*>dw^^4*>d0*>dw*>d1^^3*>dw*>d0*>dw^^4*>d0*>dw^^7*>d1*>dw^^2*>d1*>dw*>d0*>dw^^7*>d0^^2*>d1^^2*>d0*>rh1.
Proof.
  esx.
Qed.

Lemma RIncs_0 r:
  sideRLs tm (hRL^^1) ([0]*>r) ([1]*>r).
Proof.
  esx.
Qed.

Definition da := (dw++d0++dw^^4++d0++dw^^4++d0++dw++d1^^3).
Definition db := (dw++d1++dw^^4++d1++dw^^4++d1++dw++d1^^3).

Lemma RIncs_Sa n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*64+7)) (da*>r) (db*>r').
Proof.
  unfold da,db.
  intros.
  repeat rewrite Str_app_assoc.
  apply RIncs_S1s with (k:=3) in H.
  apply RIncs_Sw in H.
  apply RIncs_S0 in H.
  apply RIncs_Sws with (k:=4) in H.
  apply RIncs_S0 in H.
  apply RIncs_Sws with (k:=4) in H.
  apply RIncs_S0 in H.
  apply RIncs_Sw in H.
  applys_eq H; flia.
Qed.

Lemma pow64_mod9 a:
  64^a mod 9 = 1%nat.
Proof.
  induction a; cbn[Nat.pow]; lia.
Qed.

Lemma RIncs_Sas k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^((64^k*(n*9+1)-1)/9)) (da^^k*>r) (db^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_Sa in IHk.
    cbn[Nat.pow].
    pose proof (pow64_mod9 k).
    applys_eq IHk; flia.
Qed.


Ltac solve_RIncs_1 :=
match goal with
| |- sideRLs _ _ ?r _ =>
  match r with
  | d0^^_ *> _ => apply RIncs_S0s
  | d1^^_ *> _ => apply RIncs_S1s
  | dw^^_ *> _ => apply RIncs_Sws
  | da^^_ *> _ => apply RIncs_Sas
  | d0 *> _ => apply RIncs_S0
  | d1 *> _ => apply RIncs_S1
  | dw *> _ => apply RIncs_Sw
  | [0] *> _ => apply RIncs_0
  | _ => apply RIncs_O
  end
end.

Ltac solve_RIncs :=
repeat solve_RIncs_1.

Definition rh2 := 0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>1>>0inf.

Lemma Rst1 a:
  LC1 (10+a*18) |> d1*>dw^^4*>d1*>dw*>d1^^3*>dw*>d1*>dw^^4*>d1*>dw^^4*>d1*>dw*>d1^^3*>dw*>d1*>dw^^4*>d1*>dw^^7*>d1*>dw^^2*>d1*>dw*>d1*>dw^^7*>d1^^5*>rh1 -->*
  LC1 3 |> d0*>d1*>dw^^4*>d1*>dw*>d1*>d0*>d1*>da^^a*>dw^^4*>d0*>dw^^2*>d1^^3*>[0]*>rh2.
Proof.
  unfold LC1,rh1,rh2.
  cbn.
  es' a.
Qed.

Definition rh3 b := [1;1;1;1;0;1;0;1;1;1;0;1;0;1;1;1;1;1;1;1;0;1;0;1;1;1;0;1;0;1;1;1;1;1;1;1;0;1;0;1;0;0;0;1;0;0;0;1;0;0;0;1;1;1]^^b*>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>1>>0inf.

Lemma Rst2 a b:
  LC1 (30+a*18) |> d1^^2*>dw^^4*>d1*>dw*>d1^^3*>db^^b*>dw^^4*>d1*>dw^^2*>d1^^3*>[1]*>rh2 -->*
  LC1 1 |> d0*>dw^^3*>d0*>dw^^4*>d0*>dw*>d1^^3*>da^^a*>dw*>d0*>dw^^4*>d0*>dw^^7*>d1*>d0*>dw^^4*>d1*>dw^^2*>d0^^3*>1>>0>>1>>1>>1>>
  rh3 b.
Proof.
  unfold LC1,rh3,rh2.
  cbn.
  es' a b.
Qed.

Lemma Rst3 a b c:
  halts tm (LC1 (34+a*18) |> d1*>dw^^3*>d1*>dw^^4*>d1*>dw*>d1^^3*>db^^b*>dw*>d1*>dw^^4*>d1*>dw^^7*>d1^^2*>dw^^4*>d1*>dw^^2*>d1^^3*>1>>0>>1>>1>>1>>rh3 (1+c)).
Proof.
  unfold LC1,rh3.
  cbn.
  es' a b c.
Qed.

Import NatModTactics.

Ltac follow' H :=
  eapply evstep_trans; [eapply Peq; [|apply H]; match_Nexpr |].

Lemma halt: halts tm c0.
Proof with rw_all.
  eapply halts_evstep.
  2:{
  follow' init.

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst1...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst2...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  finish.
  }
  eapply Peq; [|apply Rst3].
  match_Nexpr.
Time Qed.

End TM23.


Module TM24.
Definition tm := Eval compute in (TM_from_str "1LB---_0LC1LA_0RD0LE_1LE0RE_0LF0RE_1RC1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (D,<[0]).
Notation hL := (F,[0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d0 := [0;0;1;0].
Notation d1 := [1;0;1;0].
Notation dw := [1;1;0].


Definition LC1 n := 0inf <* <[0;0;1]^^n.

Definition tm' := flip tm.

Lemma LIncs1 n a:
  sideRLs tm' (hLR^^n) (LC1 a) (LC1 (n+a)).
Proof.
  unfold LC1.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Ltac solve_v1 :=
  intros H;
  eapply segRLs_sideRLs_concat; [|apply H];
  apply segRLs_addmul''; esx.

Lemma RIncs_S0 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+1)) (d0*>r) (d1*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_S1 n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+0)) (d1*>r) (d1*>r').
Proof.
  solve_v1.
Qed.

Lemma RIncs_Sw n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^n) (dw*>r) (dw*>r').
Proof.
  intro H.
  replace n with (n*1+0) by lia.
  gen H.
  solve_v1.
Qed.

Lemma RIncs_Sws k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^n) (dw^^k*>r) (dw^^k*>r').
Proof.
  intro H.
  replace n with (n*1+0) by lia.
  gen H.
  solve_v1.
Qed.

Lemma RIncs_S0s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(2^k*(n+1)-1)) (d0^^k*>r) (d1^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S0 in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Lemma RIncs_S1s k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(2^k*n)) (d1^^k*>r) (d1^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_S1 in IHk.
    cbn[Nat.pow].
    applys_eq IHk; flia.
Qed.

Lemma RIncs_O r:
  sideRLs tm (hRL^^0) r r.
Proof.
  esx.
Qed.

Notation "l |> r" := (l {{{ (hR,R) }}} r) (at level 30).

Lemma Incs1 a n r r':
  sideRLs tm (hRL^^n) r r' ->
  LC1 a |> r -->*
  LC1 (n+a) |> r'.
Proof.
  intros.
  epose proof (sideRLs_concat_1 H (LIncs1 _ _)) as I1.
  apply I1.
Qed.

Definition rh1 := [1]*>0inf.

Lemma init:
  c0 -->*
  LC1 2 |> d1*>dw^^4*>d0*>dw*>d0*>d1^^2*>dw*>d0*>dw^^4*>d0*>dw^^4*>d0*>dw*>d1^^3*>dw*>d0*>dw^^4*>d0*>dw^^7*>d1*>dw^^2*>d1*>dw*>d0*>dw^^7*>d0^^2*>d1^^2*>d0*>rh1.
Proof.
  esx.
Qed.

Lemma RIncs_0 r:
  sideRLs tm (hRL^^1) ([0]*>r) ([1]*>r).
Proof.
  esx.
Qed.

Definition da := (dw++d0++dw^^4++d0++dw^^4++d0++dw++d1^^3).
Definition db := (dw++d1++dw^^4++d1++dw^^4++d1++dw++d1^^3).

Lemma RIncs_Sa n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*64+7)) (da*>r) (db*>r').
Proof.
  unfold da,db.
  intros.
  repeat rewrite Str_app_assoc.
  apply RIncs_S1s with (k:=3) in H.
  apply RIncs_Sw in H.
  apply RIncs_S0 in H.
  apply RIncs_Sws with (k:=4) in H.
  apply RIncs_S0 in H.
  apply RIncs_Sws with (k:=4) in H.
  apply RIncs_S0 in H.
  apply RIncs_Sw in H.
  applys_eq H; flia.
Qed.

Lemma pow64_mod9 a:
  64^a mod 9 = 1%nat.
Proof.
  induction a; cbn[Nat.pow]; lia.
Qed.

Lemma RIncs_Sas k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^((64^k*(n*9+1)-1)/9)) (da^^k*>r) (db^^k*>r').
Proof.
  intros.
  induction k; intros.
  - applys_eq H; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    apply RIncs_Sa in IHk.
    cbn[Nat.pow].
    pose proof (pow64_mod9 k).
    applys_eq IHk; flia.
Qed.


Ltac solve_RIncs_1 :=
match goal with
| |- sideRLs _ _ ?r _ =>
  match r with
  | d0^^_ *> _ => apply RIncs_S0s
  | d1^^_ *> _ => apply RIncs_S1s
  | dw^^_ *> _ => apply RIncs_Sws
  | da^^_ *> _ => apply RIncs_Sas
  | d0 *> _ => apply RIncs_S0
  | d1 *> _ => apply RIncs_S1
  | dw *> _ => apply RIncs_Sw
  | [0] *> _ => apply RIncs_0
  | _ => apply RIncs_O
  end
end.

Ltac solve_RIncs :=
repeat solve_RIncs_1.

Definition rh2 := 0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>1>>0inf.

Lemma Rst1 a:
  LC1 (10+a*18) |> d1*>dw^^4*>d1*>dw*>d1^^3*>dw*>d1*>dw^^4*>d1*>dw^^4*>d1*>dw*>d1^^3*>dw*>d1*>dw^^4*>d1*>dw^^7*>d1*>dw^^2*>d1*>dw*>d1*>dw^^7*>d1^^5*>rh1 -->*
  LC1 3 |> d0*>d1*>dw^^4*>d1*>dw*>d1*>d0*>d1*>da^^a*>dw^^4*>d0*>dw^^2*>d1^^3*>[0]*>rh2.
Proof.
  unfold LC1,rh1,rh2.
  cbn.
  es' a.
Qed.

Definition rh3 b := [1;1;1;1;0;1;0;1;1;1;0;1;0;1;1;1;1;1;1;1;0;1;0;1;1;1;0;1;0;1;1;1;1;1;1;1;0;1;0;1;0;0;0;1;0;0;0;1;0;0;0;1;1;1]^^b*>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>1>>0inf.

Lemma Rst2 a b:
  LC1 (30+a*18) |> d1^^2*>dw^^4*>d1*>dw*>d1^^3*>db^^b*>dw^^4*>d1*>dw^^2*>d1^^3*>[1]*>rh2 -->*
  LC1 6 |> d1*>dw^^4*>d1*>dw*>d0*>d1^^2*>da^^a*>dw*>d0*>dw^^4*>d0*>dw^^7*>d1*>d0*>dw^^4*>d1*>dw^^2*>d0^^3*>1>>0>>1>>1>>1>>rh3 b.
Proof.
  unfold LC1,rh3,rh2.
  cbn.
  es' a b.
Qed.

Definition rh4 b r := [1;1;1;1;0;1;0;1;0;0;0;1;0;0;0;1;0;0;0;1;1;1;1;1;1;1;0;1;0;1;1;1;0;1;0;1;1;1;1;1;1;1;0;1;0;1;1;1;0;1;0;1;1;1]^^b*>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>r.

Lemma Rst3 a b c:
  LC1 (14+a*18) |> d1*>dw^^4*>d1*>dw*>d1^^3*>db^^b*>dw*>d1*>dw^^4*>d1*>dw^^7*>d1^^2*>dw^^4*>d1*>dw^^2*>d1^^3*>1>>0>>1>>1>>1>>rh3 (1+c) -->*
  LC1 6 |> d1*>dw^^4*>d1*>dw*>d0*>d1^^2*>da^^a*>dw^^4*>d0*>dw^^2*>d1^^3*>
  [0]*>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>
  rh4 b (rh3 c).
Proof.
  unfold LC1,rh4,rh3.
  cbn.
  es' a b c.
Qed.

Definition rh5 b r :=
  [1;1;1;1;0;1;0;1;1;1;0;1;0;1;1;1;1;1;1;1;0;1;0;1;1;1;0;1;0;1;1;1;1;1;1;1;0;1;0;1;0;0;0;1;0;0;0;1;0;0;0;1;1;1]^^b*>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>r.

Lemma Rst4 a b c r:
  LC1 (16+a*18) |> d1*>dw^^4*>d1*>dw*>d1^^3*>db^^b*>dw^^4*>d1*>dw^^2*>d1^^3*>
  [1]*>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>1>>1>>
  rh4 (1+c) r -->*
  LC1 1 |> d0*>dw*>d1*>dw^^3*>d0*>dw^^4*>d0*>dw^^4*>d1*>dw*>d1^^3*>da^^a*>dw^^4*>d0*>dw^^2*>d1^^3*>
  [0]*>0>>1>>1>>1>>
  rh5 b (rh4 c r).
Proof.
  unfold LC1,rh5,rh4.
  cbn.
  es' a b c & r.
Qed.

Definition rh6 b r := [1;1;1;1;0;1;0;1;1;1;0;1;0;1;1;1;1;1;1;1;0;1;0;1;1;1;0;1;0;1;1;1;1;1;1;1;0;1;0;1;0;0;0;1;0;0;0;1;0;0;0;1;1;1]^^b*>0>>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>r.

Lemma Rst5 a b c r:
  LC1 (30+a*18) |> d1*>dw*>d1*>dw^^3*>d1*>dw^^4*>d1*>dw^^4*>d1*>dw*>d1^^3*>db^^b*>dw^^4*>d1*>dw^^2*>d1^^3*>
  [1]*>0>>1>>1>>1>>
  rh5 (1+c) r -->*
  LC1 6 |> d1*>dw^^4*>d1*>dw*>d0*>d1^^2*>da^^a*>dw*>d0*>dw^^4*>d0*>dw^^7*>d1*>dw^^2*>d1*>d0^^2*>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>
  rh6 b (rh5 c r).
Proof.
  unfold LC1,rh6,rh5.
  cbn.
  es' a b c & r.
Qed.

Lemma Rst6 a b r:
  halts tm (LC1 (16+a*18) |>
  d1*>dw^^4*>d1*>dw*>d1^^3*>db^^b*>dw*>d1*>dw^^4*>d1*>dw^^7*>d1*>dw^^2*>d1^^3*>1>>0>>1>>1>>1>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>1>>1>>0>>0>>0>>1>>0>>1>>1>>0>>1>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>0>>0>>1>>1>>1>>r).
Proof.
  unfold LC1,rh6.
  cbn.
  es' a b & r.
Qed.

Import NatModTactics.

Ltac follow' H :=
  eapply evstep_trans; [eapply Peq; [|apply H]; match_Nexpr |].

Lemma halt: halts tm c0.
Proof with rw_all.
  eapply halts_evstep.
  2:{
  follow' init.

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst1...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst2...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst3...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst4...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  follow' Rst5...

  follow' Incs1.
  1: solve_RIncs.
  rw_lpow_add...
  finish.
  }
  eapply Peq; [|apply Rst6].
  match_Nexpr.
Time Qed.

End TM24.


Module TM25.
Definition tm := Eval compute in (TM_from_str "1RB0LF_0RC1RB_1LD0RB_1LE---_1RF1LA_0LC0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation hL := (A,[]).
Notation hR := (B,[]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Notation d1 := <[1;1;1].
Notation w0 := <[1;1;1; 1;0;0].
Notation w0' := <[1; 1;0;0; 1;1].
Notation w1 := <[1;1;1; 1;0;1].
Notation w1' := <[1; 1;0;1; 1;1].
Notation w01 := <[1;1;1; 1;0;0; 1;0;1].
Notation w01' := <[1; 1;0;0; 1;0;1; 1;1].
Notation w11 := <[1;1;1; 1;0;1; 1;0;1].
Notation w11' := <[1; 1;0;1; 1;0;1; 1;1].

Ltac am := apply segRLs_addmul_v2; esx.

Lemma d1_Incs n:
  segRLs tm' (hLR^^(n*1+0)) (hLR^^(n*2+0)) d1 d1.
Proof. am. Qed.

Lemma w1_Incs n:
  segRLs tm' (hLR^^(n*1+1)) (hLR^^(n*4+2)) w1' (d1^^2).
Proof. am. Qed.

Lemma w0_Incs1 n:
  segRLs tm' (hLR^^(n*2+1)) (hLR^^(n*2+0)) w0' w0.
Proof. am. Qed.

Lemma w0_Incs2 n:
  segRLs tm' (hLR^^(n*2+2)) (hLR^^(n*2+0)) w0' w1.
Proof. am. Qed.

Lemma w01_Incs n:
  segRLs tm' (hLR^^(n*1+1)) (hLR^^(n*2+0)) w01' (w0<+d1).
Proof. am. Qed.

Lemma w11_Incs n:
  segRLs tm' (hLR^^(n*1+1)) (hLR^^(n*8+2)) w11' (d1^^3).
Proof. am. Qed.

Lemma lh_Incs0 n:
  sideRLs tm' (hLR^^(4+n*4)) (0inf<*<[1;1]) (0inf<*w0^^n<*w01).
Proof.
  eapply sideRLs_trans_add.
  1: esx.
  rewrite lpow_mul.
  sideRLs_ind n.
Qed.

Lemma lh_Incs1 n:
  sideRLs tm' (hLR^^(6+n*4)) (0inf<*<[1;1]) (0inf<*w0^^n<*w11).
Proof.
  eapply sideRLs_trans_add.
  1: esx.
  rewrite lpow_mul.
  sideRLs_ind n.
Qed.

Lemma d1s_Incs k n:
  segRLs tm' (hLR^^n) (hLR^^(n*2^k)) (d1^^k) (d1^^k).
Proof.
  gen n.
  induction k; intros.
  1: applys_eq @segRLs_nil; flia.
  cbn[lpow].
  eapply segRLs_concat.
  2: applys_eq (IHk (n*2)); cbn[Nat.pow]; flia.
  applys_eq (d1_Incs n); flia.
Qed.

Lemma pow4_mod3 k:
  4^(k) mod 3 = 1%nat.
Proof.
  induction k; cbn - [Nat.modulo]; lia.
Qed.

Lemma w1s_Incs k n:
  segRLs tm' (hLR^^(n+1)) (hLR^^(((n*3+1)*4^k+2)/3)) (w1'^^k) (d1^^(k*2)).
Proof.
  gen n.
  induction k; intros.
  1: applys_eq @segRLs_nil; flia.
  cbn[Nat.mul].
  cbn[lpow].
  rewrite (lpow_add _ 2 (k*2)).
  eapply segRLs_concat.
  1: applys_eq (w1_Incs n); flia.
  pose proof (pow4_mod3 k).
  applys_eq (IHk (n*4+1)); cbn[Nat.pow]; flia.
Qed.

Lemma w0s_Incs k n:
  segRLs tm' (hLR^^((n+k)*2)) (hLR^^(n*2)) (w0'^^k) (w1^^k).
Proof.
  gen n.
  induction k; intros.
  1: applys_eq @segRLs_nil; flia.
  cbn[lpow].
  eapply segRLs_concat.
  1: applys_eq (w0_Incs2 (n+k)); flia.
  applys_eq (IHk n); flia.
Qed.

Lemma d1_rot r:
  [1;1]*>d1*>r = d1*>[1;1]*>r.
Proof. trivial. Qed.

Lemma w0_rot r:
  [1;1]*>w0*>r = w0'*>[1;1]*>r.
Proof. trivial. Qed.

Lemma w1_rot r:
  [1;1]*>w1*>r = w1'*>[1;1]*>r.
Proof. trivial. Qed.

Lemma w01_rot r:
  [1;1]*>w01*>r = w01'*>[1;1]*>r.
Proof. trivial. Qed.

Lemma w11_rot r:
  [1;1]*>w11*>r = w11'*>[1;1]*>r.
Proof. trivial. Qed.

Lemma d1s_rot n r:
  [1;1]*>d1^^n*>r = d1^^n*>[1;1]*>r.
Proof. simpl_rotate; trivial. Qed.

Lemma w0s_rot n r:
  [1;1]*>w0^^n*>r = w0'^^n*>[1;1]*>r.
Proof. simpl_rotate; trivial. Qed.

Lemma w1s_rot n r:
  [1;1]*>w1^^n*>r = w1'^^n*>[1;1]*>r.
Proof. simpl_rotate; trivial. Qed.

Ltac rw_rot :=
  repeat (
  rewrite d1s_rot ||
  rewrite w0s_rot ||
  rewrite w1s_rot ||
  rewrite d1_rot ||
  rewrite w0_rot ||
  rewrite w1_rot ||
  rewrite w01_rot ||
  rewrite w11_rot).

Lemma sideRLs_trans_10 tm h r r' r'':
  sideRLs tm h r r' ->
  sideRLs tm [] r' r'' ->
  sideRLs tm h r r''.
Proof.
  intros.
  rewrite <-(app_nil_r h).
  eapply sideRLs_trans; eauto.
Qed.

Lemma LIncs_w01_w0s_0 k n:
  k+3<=n ->
  (n-k) mod 2 = 1%nat ->
  sideRLs tm' (hLR^^n) ([1;1]*>w01*>w0^^k*>0inf) (d1*>w0*>w1^^k*>w01*>w0^^((n-k-3)/2)*>0inf).
Proof.
  intros.
  rw_rot.
  eapply sideRLs_trans_10.
  {
    eapply segRLs_sideRLs_concat.
    1: applys_eq (w01_Incs (n-1)); flia.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (w0s_Incs k (n-1-k)); flia.
    applys_eq (lh_Incs0 ((n-k-3)/2)); flia.
  }
  esx.
Qed.

Lemma LIncs_w01_w0s_1 k n:
  k+4<=n ->
  (n-k) mod 2 = 0%nat ->
  sideRLs tm' (hLR^^n) ([1;1]*>w01*>w0^^k*>0inf) (d1*>w0*>w1^^k*>w11*>w0^^((n-k-4)/2)*>0inf).
Proof.
  intros.
  rw_rot.
  eapply sideRLs_trans_10.
  {
    eapply segRLs_sideRLs_concat.
    1: applys_eq (w01_Incs (n-1)); flia.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (w0s_Incs k (n-1-k)); flia.
    applys_eq (lh_Incs1 ((n-k-4)/2)); flia.
  }
  esx.
Qed.

Lemma LIncs_w11_w0s_0 k n:
  6+k<=n*4 ->
  k mod 2 = 1%nat ->
  sideRLs tm' (hLR^^n) ([1;1]*>w11*>w0^^k*>0inf) (d1^^3*>w1^^k*>w01*>w0^^(n*2-3-k/2)*>0inf).
Proof.
  intros.
  rw_rot.
  eapply sideRLs_trans_10.
  {
    eapply segRLs_sideRLs_concat.
    1: applys_eq (w11_Incs (n-1)); flia.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (w0s_Incs k (n*4-3-k)); flia.
    applys_eq (lh_Incs0 (n*2-3-k/2)); flia.
  }
  esx.
Qed.

Lemma LIncs_w11_w0s_1 k n:
  6+k<=n*4 ->
  k mod 2 = 0%nat ->
  sideRLs tm' (hLR^^n) ([1;1]*>w11*>w0^^k*>0inf) (d1^^3*>w1^^k*>w11*>w0^^(n*2-3-k/2)*>0inf).
Proof.
  intros.
  rw_rot.
  eapply sideRLs_trans_10.
  {
    eapply segRLs_sideRLs_concat.
    1: applys_eq (w11_Incs (n-1)); flia.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (w0s_Incs k (n*4-3-k)); flia.
    applys_eq (lh_Incs1 (n*2-3-k/2)); flia.
  }
  esx.
Qed.

Lemma LIncs_d1s a0 a r r':
  sideRLs tm' (hLR^^(2^a0*2^a)) ([1;1]*>r) r' ->
  sideRLs tm' (hLR^^1) ([1;1]*>d1^^a0*>d1^^a*>r) (d1^^(a0+a)*>r').
Proof.
  intros.
  rewrite <-lpow_add'.
  rw_rot.
  eapply segRLs_sideRLs_concat.
  1: apply d1s_Incs.
  eapply segRLs_sideRLs_concat.
  1: apply d1s_Incs.
  applys_eq H; flia.
Qed.

Lemma LIncs_d1s' a0 a r r':
  sideRLs tm' (hLR^^(((2^a0-1)*4+2)*2^a)) ([1;1]*>r) r' ->
  sideRLs tm' (hLR^^1) ([1;1]*>d1^^a0*>w1*>d1^^a*>r) (d1^^(a0+2+a)*>r').
Proof.
  intros.
  rw_rot.
  eapply sideRLs_trans_10.
  {
    eapply segRLs_sideRLs_concat.
    1: apply d1s_Incs.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (w1_Incs (2^a0-1)); flia.
    eapply segRLs_sideRLs_concat.
    1: apply d1s_Incs.
    apply H.
  }
  esx.
Qed.

Lemma LIncs_w1s n b r r':
  n>=1 ->
  sideRLs tm' (hLR^^(((n*3-2)*4^b+2)/3)) ([1;1]*>r) r' ->
  sideRLs tm' (hLR^^n) ([1;1]*>w1^^b*>r) (d1^^(b*2)*>r').
Proof.
  intros.
  rw_rot.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (w1s_Incs b (n-1)); flia.
  applys_eq H0; flia.
Qed.

Lemma LIncs_w1s' n b r r':
  n>=3 ->
  n mod 2 = 0%nat ->
  sideRLs tm' (hLR^^(((n*3-8)*4^b+2)/3)) ([1;1]*>r) r' ->
  sideRLs tm' (hLR^^n) ([1;1]*>w0*>w1^^b*>r) (w1*>d1^^(b*2)*>r').
Proof.
  intros.
  rw_rot.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (w0_Incs2 ((n-2)/2)); flia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (w1s_Incs b (n-3)); flia.
  applys_eq H1; flia.
Qed.

Definition LC1 (a1:bool) a r := (if a1 then w1 else []) *> d1^^a *> r.
Definition LC2 (b0:bool) b r := (if b0 then w0 else []) *> w1^^b *> r.
Definition LC3 (c1:bool) c := (if c1 then w11 else w01) *> w0^^c *> 0inf.

Lemma LC2_Incs n (b0:bool) b r r':
  n>=3 ->
  n mod 2 = 0%nat ->
  sideRLs tm' (hLR^^(((n*3-8+(if b0 then 0 else 6))*4^b+2)/3)) ([1;1]*>r) r' ->
  sideRLs tm' (hLR^^n) ([1;1]*>LC2 b0 b r) (LC1 b0 (b*2) r').
Proof.
  intros.
  unfold LC2,LC1.
  destruct b0.
  - apply LIncs_w1s'.
    3: applys_eq H1; flia.
    all: lia.
  - apply LIncs_w1s.
    2: applys_eq H1; flia.
    all: lia.
Qed.

Lemma LC1_Incs (a1:bool) a0 a r r':
  sideRLs tm' (hLR^^(if a1 then ((2^a0-1)*4+2)*2^a else 2^a0*2^a)) ([1;1]*>r) r' ->
  sideRLs tm' (hLR^^1) ([1;1]*>d1^^a0*>LC1 a1 a r) (d1^^(a0+a+(if a1 then 2 else 0))*>r').
Proof.
  intros.
  unfold LC1.
  destruct a1.
  - applys_eq (LIncs_d1s' a0 a).
    1: flia.
    applys_eq H; flia.
  - applys_eq (LIncs_d1s a0 a).
    1: flia.
    applys_eq H; flia.
Qed.

Import DivModCases.

Lemma LC3_Incs n (c1:bool) c:
  6+c*2<=n ->
  exists c1' c',
  sideRLs tm' (hLR^^n) ([1;1]*>LC3 c1 c) (d1*>(if c1 then d1^^2 else w0)*>w1^^c*>LC3 c1' c') /\
  1<=c' /\
  n/4<=c'<=n*2.
Proof.
  unfold LC3.
  intros.
  destruct c1.
  - destruct (mod2 c).
    + eexists true,_; split.
      1: apply LIncs_w11_w0s_1; lia.
      lia.
    + eexists false,_; split.
      1: apply LIncs_w11_w0s_0; lia.
      lia.
  - destruct (mod2 (n-c)).
    + eexists true,_; split.
      1: apply LIncs_w01_w0s_1; lia.
      lia.
    + eexists false,_; split.
      1: apply LIncs_w01_w0s_0; lia.
      lia.
Qed.


Notation rh := (d1*>0inf).

Lemma BigStep l l':
  sideRLs tm' (hLR^^1) ([1;1]*>l) l' ->
  l {{{ (hR,R) }}} rh -->+
  l' {{{ (hR,R) }}} rh.
Proof.
  intros.
  mid10 (l <* <[1;1] {{{ (hL,L) }}} rh).
  1: er.
  eapply sideRLs_1,progress_evstep,unflip_evstep in H.
  apply H.
Qed.

Definition Config:Type := bool*nat*nat*bool*nat*bool*nat.

Definition to_config(x:Config) :=
  let '(a1,a0,a,b0,b,c1,c):=x in
  d1^^a0*>LC1 a1 a (LC2 b0 b (LC3 c1 c)) {{{ (hR,R) }}} rh.

Definition P(x:Config):Prop :=
  let '(a1,a0,a,b0,b,c1,c):=x in
  3<=a0 /\
  2<=a /\
  1<=b /\
  1<=c /\
  6+c*2<=((2^a*3-8)*4^b+2)/3 /\
  a0+a+4<=c*2 /\
  True
  .

Lemma pow4_pow2 c:
  4^c = 2^(c*2).
Proof.
  rewrite Nat.mul_comm.
  rewrite Nat.pow_mul_r.
  trivial.
Qed.

Ltac rw_pa := repeat rewrite Nat.pow_add_r in *.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (false,3,3,false,5,false,12)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: unfold P; lia.
  unfold P,to_config.
  intros [[[[[[a1 a0] a] b0] b] c1] c] [HP0 [HP1 [HP2 [HP3 [HP4 [HP5 HP6]]]]]].
  epose proof (LC3_Incs _ c1 c _) as [c1' [c' [I3 I3']]].
  epose proof (LC2_Incs _ b0 b _ _ _ _ I3) as I2.
  epose proof (LC1_Incs a1 a0 a _ _ I2) as I1.
  clear I2 I3.
  exists (b0,a0+a+(if a1 then 2 else 0),b*2+(if c1 then 3 else 1),negb c1,c,c1',c'); split.
  - apply BigStep.
    applys_eq I1.
    destruct a1,b0,c1,c1'; ut; st; reflexivity.
  - shelve.
  Unshelve.
  + etransitivity.
    1: apply HP4.
    destruct a1,b0.
    all: zify_pow2sub1; lia.
  + pose proof (Nat.pow_le_mono_r 2 2 a).
    destruct a1.
    * rewrite Nat.mul_add_distr_r.
      apply (add_ge 0 3).
      2,3: lia.
      remember ((2^a0-1)*4*2^a).
      lia.
    * lia.
  + destruct a.
    1: lia.
    cbn[Nat.pow].
    destruct a1; lia.
  + clear I1.
    repeat split; try lia.
    * destruct I3' as [_ [_ I3']].
      assert (4+c'*2<=2^(b*2+c*2)). {
        assert (I:4+c'*2<=2^(a0+a+b*2+4)). {
          rw_pa.
          rewrite pow4_pow2 in *.
          destruct a1,b0.
          all: zify_pow2sub1; try lia.
        }
        etransitivity.
        1: apply I.
        apply Nat.pow_le_mono_r; lia.
      }
      clear I3'.
      rw_pa.
      rewrite pow4_pow2.
      remember (2^(b*2)-4) as v1.
      replace (2^(b*2)) with (v1+4) in * by (pose proof (Nat.pow_le_mono_r 2 2 (b*2)); lia).
      destruct c1; lia.
    * assert (2^((a0-1)+(a-2)+b*2)<=c'*2). {
        remember (a0-1) as a0'.
        replace a0 with (a0'+1) in * by lia.
        remember (a-2) as a'.
        replace a with (a'+2) in * by lia.
        rw_pa.
        destruct I3' as [_ [I3' _]].
        rewrite pow4_pow2 in *.
        destruct a1,b0.
        all: time (zify_pow2sub1; try lia).
      }
      assert ((a0-1)+(a-2)+b*2+12<=c'*2). {
        etransitivity.
        2: apply H.
        remember ((a0-1)+(a-2)+b*2) as v1.
        assert (4<=v1) by lia.
        remember (v1-4) as v2.
        replace v1 with (v2+4) in * by lia.
        rw_pa.
        clear.
        induction v2; cbn[Nat.pow]; try lia.
      }
      destruct a1,c1; lia.
Qed.

End TM25.


Module TM26.
Definition tm := Eval compute in (TM_from_str "1RB1LE_0RC0RE_1LC0LD_1LA0RE_1RF0LA_---0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation hL := (A,[0;1]).
Notation hR := (B,<[1;0;1]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Notation d0 := <[1;0;1;0].
Notation d1 := <[1;1;1;1].

Inductive LC: nat->nat->nat->side->Prop :=
| LC_O a: LC 0 0 a (0inf<*<[0;1]^^a)
| LC_S0 len n a l:
  LC len n a l ->
  LC (S len) (n+2^len) a (l<*d0)
| LC_S1 len n a l:
  LC len n a l ->
  LC (S len) n a (l<*d1).

Lemma LC_empty len a l:
  LC len 0 a l ->
  l = 0inf<*<[0;1]^^a<*d1^^len.
Proof.
  gen l.
  induction len; intros.
  - inverts H; trivial.
  - inverts H.
    1: lia.
    apply IHlen in H1; subst; trivial.
Qed.

Lemma LC_full len a:
  LC len (2^len-1) a (0inf<*<[0;1]^^a<*d0^^len).
Proof.
  induction len.
  - apply LC_O.
  - apply LC_S0 in IHlen.
    applys_eq IHlen; cbn[Nat.pow]; flia.
Qed.

Lemma LC_lt [len n a l]:
  LC len n a l ->
  n<2^len.
Proof.
  intros H.
  induction H; cbn[Nat.pow]; lia.
Qed.

Lemma LC_Inc_O len n l:
  LC len (S n) 0 l ->
  exists l',
  LC len n 0 l' /\
  sideRLs tm' (hLR^^3) l l'.
Proof.
  gen n l.
  induction len; intros.
  - inverts H.
  - inverts H.
    + destruct n0 as [|n0].
      * eexists; split.
        -- apply LC_S1.
           applys_eq LC_full; flia.
        -- apply LC_empty in H2; subst.
           esx.
      * apply IHlen in H2.
        destruct H2 as [l' [I1 I2]].
        eexists; split.
        -- apply LC_S0 in I1.
           applys_eq I1; flia.
        -- eapply segRLs_sideRLs_concat.
          2: apply I2.
          esx.
    + apply IHlen in H1.
      destruct H1 as [l' [I1 I2]].
      eexists; split.
      * apply LC_S1,I1.
      * eapply segRLs_sideRLs_concat.
        2: apply I2.
        esx.
Qed.

Lemma LC_Inc_S len n a l:
  LC len (S n) (S a) l ->
  exists l',
  LC len n a l' /\
  sideRLs tm' (hLR^^2) l l'.
Proof.
  gen n l.
  induction len; intros.
  - inverts H.
  - inverts H.
    + destruct n0 as [|n0].
      * eexists; split.
        -- apply LC_S1.
           applys_eq LC_full; flia.
        -- apply LC_empty in H2; subst.
           esx.
      * apply IHlen in H2.
        destruct H2 as [l' [I1 I2]].
        eexists; split.
        -- apply LC_S0 in I1.
           applys_eq I1; flia.
        -- eapply segRLs_sideRLs_concat.
          2: apply I2.
          esx.
    + apply IHlen in H1.
      destruct H1 as [l' [I1 I2]].
      eexists; split.
      * apply LC_S1,I1.
      * eapply segRLs_sideRLs_concat.
        2: apply I2.
        esx.
Qed.

Definition RC1 n := [0;1;1;0] *> [1;0;1;0]^^n *> [1;1] *> 0inf.

Definition S' '(l,k) := l {{{ (hL,L) }}} RC1 k.

Lemma Ov len l k:
  LC len 0 0 l ->
  exists l',
  LC (k+1) (2^(k+1)-1) (len*2+3) l' /\
  S' (l,k) -->+
  S' (l',1%nat).
Proof.
  unfold S'.
  intros.
  apply LC_empty in H; subst.
  unfold RC1.
  eexists; split.
  1: apply LC_full.
  es.
Qed.

Lemma Inc_S len n a l k:
  LC len (S n) (S a) l ->
  exists l',
  LC len n a l' /\
  S' (l,k) -->+
  S' (l',2+k).
Proof.
  intros.
  apply LC_Inc_S in H.
  destruct H as [l' [I1 I2]].
  eexists; split.
  1: apply I1.
  unfold S',RC1.
  eapply @sideRLs_split with (ls1:=hLR) in I2.
  destruct I2 as [l0 [I2 I2a]].
  eapply sideRLs_1 in I2,I2a.
  apply unflip_progress in I2,I2a.
  follow10 I2.
  es; er.
  follow100 I2a.
  es.
Qed.

Lemma Inc_O len n l k:
  LC len (S n) O l ->
  exists l',
  LC len n O l' /\
  S' (l,k) -->+
  S' (l',3+k).
Proof.
  intros.
  apply LC_Inc_O in H.
  destruct H as [l' [I1 I2]].
  eexists; split.
  1: apply I1.
  unfold S',RC1.
  eapply @sideRLs_split with (ls1:=hLR) in I2.
  destruct I2 as [l0 [I2 I2a]].
  eapply @sideRLs_split with (ls1:=hLR) in I2a.
  destruct I2a as [l1 [I2a I2b]].
  eapply sideRLs_1 in I2,I2a,I2b.
  apply unflip_progress in I2,I2a,I2b.
  follow10 I2.
  es; er.
  follow100 I2a.
  es; er.
  follow100 I2b.
  es.
Qed.

Ltac rw_pa := repeat rewrite Nat.pow_add_r in *.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (d0^^4*>[1;0]^^5*>0inf,1%nat)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(l,k) => exists len n a, LC len n a l /\ a<=n /\ len*2+3<=2^k+n*2/\k<>O).
  2: {
    eexists _,_,_; split.
    1: apply LC_full.
    lia.
  }
  intros [l k] [len [n [a [I1 I2]]]].
  destruct n.
  {
    destruct a.
    2: lia.
    eapply Ov in I1.
    destruct I1 as [l' [I1 I1a]].
    eexists; split.
    1: apply I1a.
    eexists _,_,_; split.
    1: apply I1.
    rw_pa.
    split.
    1: lia.
    destruct k; [lia|].
    clear.
    induction k; cbn[Nat.pow] in *; lia.
  }
  destruct a.
  {
    eapply Inc_O in I1.
    destruct I1 as [l' [I1 I1a]].
    eexists; split.
    1: apply I1a.
    eexists _,_,_; split.
    1: apply I1.
    rw_pa.
    lia.
  }
  {
    eapply Inc_S in I1.
    destruct I1 as [l' [I1 I1a]].
    eexists; split.
    1: apply I1a.
    eexists _,_,_; split.
    1: apply I1.
    rw_pa.
    lia.
  }
Qed.

End TM26.


