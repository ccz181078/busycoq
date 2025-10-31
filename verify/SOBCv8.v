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


Module TM19.
Definition tm := Eval compute in (TM_from_str "1RB1LF_1RC---_1RD0LF_1RE0RC_1LC1RB_1LC0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (C,<[]).
Notation hL := (F,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d0 := [1;0;1;0].
Notation d1 := [0;0;1;0].
Notation dw := [0;1].


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

Lemma RIncs_1 r:
  sideRLs tm (hRL^^1) ([1]*>r) ([0]*>r).
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

Definition rh1 := [0;1;0;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;1;0;1;0;0;0;0;0;1;0;0;1]*>0inf.

Lemma init:
  c0 -->*
  LC1 2 |> d0^^9 *> dw *> d0 *> d1 *> d0 *> [1] *> [0;0] *> rh1.
Proof.
  esx.
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
  | [1] *> _ => apply RIncs_1
  end
end.

Ltac solve_RIncs :=
repeat solve_RIncs_1.

Lemma Rst1 a b c r:
  LC1 (5+a*6) |> d1^^(2+b) *> dw *> d1^^(1+c) *> [0] *> [0;0] *> r -->+
  LC1 2 |> d0^^(3+a*3) *> dw *> d0 *> d1 *> d0^^b *> [1] *> [0;0] *> dw^^(1+c*2) *> [0] *> dw *> r.
Proof.
  unfold LC1.
  es.
Qed.

Definition S' '(a,b,c,r) :=
  LC1 a |> d1^^(2+b) *> dw *> d1^^(1+c) *> [0] *> [0;0] *> r.

Open Scope nat.

Ltac rw_pa :=
  repeat rewrite Nat.pow_add_r by lia.

Lemma mod_v1 a:
  2^(3+a*6) mod 12 = 8.
Proof.
  induction a.
  1: reflexivity.
  remember (3+a*6) as v1.
  replace (3+S a*6) with (6+v1) by lia.
  rw_pa; lia. 
Qed.

Lemma mod_v2 b:
  (2^(1+b*2)*8-2) mod 12 = 2.
Proof.
  induction b.
  1: reflexivity.
  remember (1+b*2) as v1.
  replace (1+S b*2) with (2+v1) by lia.
  rw_pa; lia.
Qed.

Lemma BigStep a b c r:
  S' (5+a*12,1+b*2,c,r) -->+
  S' ((2^(3+a*6)*(2^(1+b*2)*8-2)-1+2),1+a*6,2+b*2,dw^^(1+c*2)*>[0%sym]*>dw*>r).
Proof.
  unfold S'.
  replace (3+b*2) with (2+(1+b*2)) by lia.
  replace (a*12) with (a*2*6) by lia.
  follow10 Rst1.
  follow Incs1.
  1: solve_RIncs.
  replace (a*2*3) with (a*6) by lia.
  rw_lpow_add.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (7169,7,2,rh1)).
  1:{
  follow init.
  follow Incs1.
  1: solve_RIncs.
  rewrite (lpow_add' d1 1 1).
  rewrite (lpow_add' d1 2 1).
  finish.
  }
  eapply progress_nonhalt_cond with (P:=fun '(a,b,c,r) => a mod 12 = 5 /\ b mod 2 = 1).
  2: split; reflexivity.
  intros [[[a b] c] r] [HPa HPb].
  replace a with (5+a/12*12) by lia.
  replace b with (1+b/2*2) by lia.
  eexists; split.
  1: apply BigStep.
  cbn match.
  split.
  2: lia.
  pose proof (mod_v1 (a/12)) as Ha.
  pose proof (mod_v2 (b/2)) as Hb.
  remember (2^(3+a/12*6)) as v1.
  remember (2^(1+b/2*2)*8-2) as v2.
  replace v1 with (8+v1/12*12) by lia.
  replace v2 with (2+v2/12*12) by lia.
  clear.
  rw_mod_1.
  Unshelve.
  lia.
Qed.

End TM19.


