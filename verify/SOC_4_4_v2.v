From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require ES_v2.
From BusyCoq Require Import Longitudinal BinaryCounter_v2 SimplPow2.

Notation rd0 := [0;0;0;0].
Notation rd1 := [1;0;0;0].

Lemma segRLs_addmul_v2 a1 a2 c1 c2 x h tm w1 w2:
  segRLs tm (h^^c1) (h^^c2) w1 w2 ->
  segRLs tm (h^^a1) (h^^a2) w2 w2 ->
  segRLs tm (h^^(x*a1+c1)) (h^^(x*a2+c2)) w1 w2.
Proof.
  intros.
  rewrite (Nat.add_comm _ c1).
  rewrite (Nat.add_comm _ c2).
  do 2 rewrite lpow_add.
  eapply segRLs_trans.
  1: apply H.
  induction x.
  - constructor.
  - rewrite <-Nat.add_1_r.
    do 2 rewrite Nat.mul_add_distr_r.
    do 2 rewrite lpow_add.
    eapply segRLs_trans.
    1: apply IHx.
    do 2 rewrite Nat.mul_1_l.
    apply H0.
Qed.

Lemma rw_0_0inf:
  [0] *> 0inf = 0inf.
Proof.
  solve_const0_eq.
Qed.

Lemma Str_app_nil(r:side):
  []*>r = r.
Proof.
  reflexivity.
Qed.

Lemma sideRLs_feq2 tm h r r' r'':
  sideRLs tm h r r' ->
  r' = r'' ->
  sideRLs tm h r r''.
Proof.
  congruence.
Qed.

Ltac ssc H := eapply segRLs_sideRLs_concat; [apply H | ].

Ltac flia := unfold DH0; repeat (lia || f_equal).


Module TM1.
Definition tm := Eval compute in (TM_from_str "1LB0RD_1RC0LE_1RD0RB_1RA1RF_1LC1LB_1RD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation ld1 := <[1;1;1;1].
Notation ld0 := <[1;0;1;0].

Definition LC1 a b :=
  0inf <* ld1^^a <* <[1;0;1;1;1;1;1;0] <* ld1^^b <* <[1;0;1;1;1;1;1].

Definition LC0 a b :=
  0inf <* <[1;0] <* ld0^^a <* <[1;0;1;1;1;1;1;0] <* ld1 <* ld0^^b <* <[1;0;1;1;1;1;1].

Definition LC2 a b :=
  0inf <* <[1;1;1] <* ld1^^a <* <[1;0;1;1;1;1;1;0] <* ld1^^b <* <[1;0;1;1;1;1;1].

Definition LC3 a b :=
  0inf <* ld0^^a <* <[1;0;1;0;1;0;1;1] <* ld0^^b <* <[1;0;1;1;1;1;1].

Notation "l <| r" := (l <{{C}} [1;0] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{A}}> r) (at level 30).

Lemma LC1_Ov a b r:
  LC1 a b <| [0;0;0] *> r -->*
  LC0 a b |> r.
Proof.
  unfold LC1,LC0.
  es.
Qed.

Notation hRL := [((A,[1;0]),(C,[1;0]))].
Notation hRLx := [((A,[1;1;1;0;1;0]),(C,[1;0]))].
Notation hLR := [((C,[1;0]),(A,[1;0]))].
Notation hLR' := [((E,[]),(D,[]))].

Ltac ss := solve_seg.

Lemma LC0_Incs a b:
  sideRLs tm' (hLR^^((((1+1)*2^a-1)*2+1)*2^b-1)) (LC0 a b) (LC2 a (b+1)).
Proof.
  unfold LC0,LC2.
  rewrite lpow_add.
  rewrite Str_app_assoc.
  eapply @segRLs_sideRLs_concat with (ls2:=hLR'^^_).
  1: eapply segRLs_wall'.
  1: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.IncsOvs.
  1: ss.
  1: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  2: ss.
  2: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply segRLs_wall.
  1: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.IncsOvs.
  1: ss.
  1: ss.
  1: ss.
  solve_sideRLs.
Qed.

Lemma LC2_Ov a b:
  sideRLs tm' hLR (LC2 a b) (LC3 (a+1) b).
Proof.
  unfold LC2,LC3.
  solve_sideRLs.
Qed.

Lemma LC3_Incs a b:
  sideRLs tm' (hLR^^(((((0+1)*2^a-1)*1+1)+1)*2^b-1)) (LC3 a b) (LC1 a b).
Proof.
  unfold LC3,LC1.
  eapply @segRLs_sideRLs_concat with (ls2:=hLR'^^_).
  1: eapply segRLs_wall'.
  1: ss.
  1: ss.
  Print BC.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.IncsOvs.
  1: ss.
  1: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply segRLs_addmul with (c:=O); esx.
  rewrite Nat.add_0_r.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.IncsOvs.
  1: ss.
  1: ss.
  1: ss.
  solve_sideRLs.
Qed.

Lemma LC_Incs a b:
  sideRLs tm' (hLR^^(((((1+1)*2^a-1)*2+1)*2^b-1)+1+(((((0+1)*2^(a+1)-1)*1+1)+1)*2^(b+1)-1))) (LC0 a b) (LC1 (a+1) (b+1)).
Proof.
  do 2 rewrite lpow_add.
  eapply sideRLs_trans.
  2: apply LC3_Incs.
  eapply sideRLs_trans.
  2: apply LC2_Ov.
  apply LC0_Incs.
Qed.

Lemma LC_Incs' a b:
  sideRLs tm' (hLR^^((2^(a+b+3))+2^b-1)) (LC0 a b) (LC1 (a+1) (b+1)).
Proof.
  applys_eq LC_Incs.
  f_equal.
  rw_pa; zify_pow2sub1; lia.
Qed.



Ltac R_sub n :=
  match goal with
  | |- sideRLs _ (_^^?a) _ _ =>
    rewrite <-(Nat.sub_add n a) by lia'
  end.

Ltac R_m2 :=
  match goal with
  | |- sideRLs _ (_^^?a) _ _ =>
    replace a with (a/2*2) by lia'
  end.

Ltac R_m2a1 :=
  match goal with
  | |- sideRLs _ (_^^?a) _ _ =>
    replace a with (a/2*2+1) by lia'
  end.

Ltac R_x x :=
  match goal with
  | |- sideRLs _ (_^^?a) _ _ =>
    replace a with x by lia'
  end.




Lemma rw_0_rd0 r:
  [0] *> rd0 *> r = rd0 *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_rd1 r:
  [0] *> rd1 *> r = [0;1;0;0] *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_01s n r:
  [0] *> (rd0++rd1)^^n *> r = (rd0++[0;1;0;0])^^n *> [0] *> r.
Proof.
  simpl_rotate; reflexivity.
Qed.

Ltac ss ::= solve_segRLs.

Lemma segRLs_d1_d0 n:
  segRLs tm (hRL^^(n*2+1)) (hRL^^(n+1)) rd1 rd0.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 1 1 n); flia; ss.
Qed.

Lemma segRLs_d1_d1 n:
  segRLs tm (hRL^^(n*2)) (hRL^^(n)) rd1 rd1.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 0 0 n); flia; ss.
Qed.

Lemma segRLs_d0_d0 n:
  segRLs tm (hRL^^(n*2)) (hRL^^(n)) rd0 rd0.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 0 0 n); flia; ss.
Qed.

Lemma segRLs_d0_d1 n:
  segRLs tm (hRL^^(n*2+1)) (hRL^^(n)) rd0 rd1.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 1 0 n); flia; ss.
Qed.

Lemma hRLx_d0 h r r' r0:
  sideRLs tm (hRL^^1) r r0 ->
  sideRLs tm h (rd0*>rd0*>r0) r' ->
  sideRLs tm (hRLx++h) (rd0*>r) r'.
Proof.
  intros.
  eapply sideRLs_trans.
  2: apply H0.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  esx.
Qed.

Lemma hRLx_0100 h r r' r0:
  sideRLs tm (hRLx++[]) r r0 ->
  sideRLs tm h (rd0*>r0) r' ->
  sideRLs tm (hRLx++h) ([0;1;0;0]*>r) r'.
Proof.
  intros.
  eapply sideRLs_trans.
  2: apply H0.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  esx.
Qed.

Lemma hRL_1100 n r r':
  sideRLs tm (hRLx++hRL^^n) r r' ->
  sideRLs tm (hRL^^(n+1)) ([1;1;0;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  change r' with ([]*>r').
  eapply @segRLs_sideRLs_concat.
  2: apply H.
  eapply segRLs_trans.
  1: esx.
  eapply segRLs_nil.
Qed.

Lemma hRL_0100 n r r':
  sideRLs tm (hRL^^n) ([1;1;0;0]*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;1;0;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Ltac rw_0 :=
  repeat (
  rewrite rw_0_rd0 ||
  rewrite rw_0_rd1 ||
  rewrite rw_0_01s ||
  rewrite rw_0_0inf);
  cbn[Nat.add]; cbn[lpow];
  repeat rewrite Str_app_assoc;
  repeat rewrite Str_app_nil.


Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- ?G => idtac G
  end;
  match goal with
  | |- sideRLs _ [] _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ (_^^O) _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ (hRLx++_) (rd0*>_) _ =>
    eapply hRLx_d0; [sscs|]
  | |- sideRLs _ (hRLx++_) ([0;1;0;0]*>_) _ =>
    eapply hRLx_0100; [sscs|]
  | |- sideRLs _ _ ([0;1;0;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_0100
  | |- sideRLs _ _ ([1;1;0;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_1100
  | |- sideRLs _ _ (rd0*>_) _ =>
    (R_m2a1; ssc segRLs_d0_d1) ||
    (R_m2; ssc segRLs_d0_d0)
  | |- sideRLs _ _ (rd1*>_) _ =>
    (R_m2a1; ssc segRLs_d1_d0) ||
    (R_m2; ssc segRLs_d1_d1)
  end; simpl_nat);
  match goal with
  | |- ?G => idtac "fail"; idtac G
  end.

Lemma hRLx_01 n r r':
  sideRLs tm (hRLx++hRL^^n) r r' ->
  sideRLs tm (hRLx++hRL^^(((n+1)*2+1)*2)) (rd0 *> [0;1;0;0] *> r) (rd0*>rd1*>r').
Proof.
  intros.
  sscs.
  applys_eq H; flia.
Qed.

Lemma hRLx_01s k n r r':
  2<=k ->
  sideRLs tm (hRLx++hRL^^(k-2)) r r' ->
  sideRLs tm (hRLx++hRL^^(k*2^(n*2)-2)) ((rd0++[0;1;0;0])^^n*>r) ((rd0++rd1)^^n*>r').
Proof.
  intros.
  induction n.
  - applys_eq H0; flia.
  - cbn[lpow].
    repeat rewrite Str_app_assoc.
    apply hRLx_01 in IHn.
    replace (S n*2) with (n*2+2) by lia.
    rw_pa.
    applys_eq IHn; flia.
Qed.

Inductive RC: nat->side->Prop :=
| RC_5:
    RC 5
  (rd1*>rd1*>rd1*>rd1*>rd1*>rd0*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>0inf)
| RC_6:
    RC 6
  (rd1*>rd1*>rd1*>rd1*>rd1*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>0inf)
| RC_7:
    RC 7
  (rd1*>rd1*>rd1*>rd1*>rd1*>rd1*>rd1*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>0inf)
| RC_8 n:
    RC (n*2+8)
  (rd1*>rd1*>rd1*>rd1*>rd1*>rd1*>rd1*>rd0*>(rd0++rd1)^^n*>rd1*>rd1*>(rd0++rd1)^^(4+n)*>0inf)
| RC_9 n:
    RC (n*2+9)
  (rd1*>rd1*>rd1*>rd1*>rd1*>rd1*>rd1*>rd0*>(rd0++rd1)^^n*>rd0*>rd0*>rd1*>rd1*>(rd0++rd1)^^(4+n)*>0inf)
.

Ltac sscs' := rw_0; sscs; solve_sideRLs.

Lemma RC_Incs n r r':
  RC n r ->
  RC (S n) r' ->
  sideRLs tm (hRL^^((2^(n+3)+1)*2^(n+1)+0)) ([0]*>r) (rd0*>r').
Proof.
  intros I1 I2.
  inverts I1; inverts I2; try lia.
  - sscs'.
  - sscs'.
  - replace n with O by lia.
    sscs'.
  - replace n0 with n in * by lia.
    destruct n as [|[|]].
    + sscs'.
    + sscs'.
    + rw_0.
      eapply sideRLs_feq2; [|shelve].
      repeat rewrite Nat.mul_succ_l.
      sscs.
      replace ((2 ^ (n * 2 + 15) + 1) * 2 ^ (n * 2 + 2) - 2) with
        ((2 ^ (n * 2 + 17) + 4) * 2 ^ (n * 2) - 2) by lia'.
      eapply hRLx_01s; [lia|].
      sscs.
      replace (2 ^ (n * 2 + 3) - 2) with (8 * 2 ^ (n * 2) - 2) by lia'.
      eapply hRLx_01s; [lia|].
      solve_sideRLs.
  - replace n with (S n0) in * by lia.
    clear n.
    rename n0 into n.
    destruct n as [|[|]].
    + sscs'.
    + sscs'.
    + rw_0.
      eapply sideRLs_feq2; [|shelve].
      repeat rewrite Nat.mul_succ_l.
      sscs.
      replace ((2 ^ (n * 2 + 16) + 1) * 2 ^ (n * 2 + 3) - 2) with
        ((2 ^ (n * 2 + 19) + 8) * 2 ^ (n * 2) - 2) by lia'.
      eapply hRLx_01s; [lia|].
      sscs.
      replace (2 ^ (n * 2 + 3) - 2) with (8 * 2 ^ (n * 2) - 2) by lia'.
      eapply hRLx_01s; [lia|].
      solve_sideRLs.
      Unshelve.
      all: st; simpl_rotate; reflexivity.
Qed.

Definition S0 '(n,r) := LC1 n (n+1) <| rd0 *> r.

Lemma BigStep' n r r':
  RC n r ->
  RC (S n) r' ->
  S0 (n,r) -->+
  S0 (S n,r').
Proof.
  intros.
  epose proof (RC_Incs _ _ _ H H0) as I1.
  unfold S0.
  cbn[Str_app].
  follow LC1_Ov.
  epose proof (sideRLs_concat (LC_Incs' n (n+1))) as I2.
  rewrite lrcons_lpow1 in I2 by lia.
  rewrite <-(Nat.add_1_r n).
  eapply I2.
  applys_eq I1.
  rw_pa; flia.
Qed.

Lemma RC_S n r:
  RC n r ->
  exists r', RC (S n) r'.
Proof.
  intros.
  inverts H; eexists; try solve[econstructor].
  - eapply (RC_8 O).
  - applys_eq (RC_9 n0); flia.
  - applys_eq (RC_8 (S n0)); flia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  epose proof (RC_5) as I1.
  match goal with
  | [I1:RC _ ?r|-_] =>
    eapply multistep_nonhalt with (c':=S0 (5,r))
  end.
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(n,r) => RC n r).
  2: apply I1.
  intros [n r] HRC.
  epose proof HRC as HRC'.
  eapply RC_S in HRC'.
  destruct HRC' as [r' I2].
  eexists; split.
  1: apply BigStep'; try eassumption.
  apply I2.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB1LF_1RC0RF_1RE1RD_1RC---_1LF0RC_1RB0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation ld1 := <[1;1;1;1].
Notation ld0 := <[1;0;1;0].

Definition LC1 a b :=
  0inf <* ld1^^a <* <[1;0;1;1;1;1;1;0] <* ld1^^b <* <[1;0;1;1;1;1;1].

Definition LC0 a b :=
  0inf <* <[1;0] <* ld0^^a <* <[1;0;1;1;1;1;1;0] <* ld1 <* ld0^^b <* <[1;0;1;1;1;1;1].

Definition LC2 a b :=
  0inf <* <[1;1;1] <* ld1^^a <* <[1;0;1;1;1;1;1;0] <* ld1^^b <* <[1;0;1;1;1;1;1].

Definition LC3 a b :=
  0inf <* ld0^^a <* <[1;0;1;0;1;0;1;1] <* ld0^^b <* <[1;0;1;1;1;1;1].

Notation "l <| r" := (l <{{B}} [1;0] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{E}}> r) (at level 30).

Lemma LC1_Ov a b r:
  LC1 a b <| [0;0;0] *> r -->*
  LC0 a b |> r.
Proof.
  unfold LC1,LC0.
  es.
Qed.

Notation hRL := [((E,[1;0]),(B,[1;0]))].
Notation hRLx := [((E,[1;1;1;0;1;0]),(B,[1;0]))].
Notation hLR := [((B,[1;0]),(E,[1;0]))].
Notation hLR' := [((A,[]),(C,[]))].

Ltac ss := solve_seg.

Lemma LC0_Incs a b:
  sideRLs tm' (hLR^^((((1+1)*2^a-1)*2+1)*2^b-1)) (LC0 a b) (LC2 a (b+1)).
Proof.
  unfold LC0,LC2.
  rewrite lpow_add.
  rewrite Str_app_assoc.
  eapply @segRLs_sideRLs_concat with (ls2:=hLR'^^_).
  1: eapply segRLs_wall'.
  1: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.IncsOvs.
  1: ss.
  1: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  2: ss.
  2: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply segRLs_wall.
  1: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.IncsOvs.
  1: ss.
  1: ss.
  1: ss.
  solve_sideRLs.
Qed.

Lemma LC2_Ov a b:
  sideRLs tm' hLR (LC2 a b) (LC3 (a+1) b).
Proof.
  unfold LC2,LC3.
  solve_sideRLs.
Qed.

Lemma LC3_Incs a b:
  sideRLs tm' (hLR^^(((((0+1)*2^a-1)*1+1)+1)*2^b-1)) (LC3 a b) (LC1 a b).
Proof.
  unfold LC3,LC1.
  eapply @segRLs_sideRLs_concat with (ls2:=hLR'^^_).
  1: eapply segRLs_wall'.
  1: ss.
  1: ss.
  Print BC.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.IncsOvs.
  1: ss.
  1: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply segRLs_addmul with (c:=O); esx.
  rewrite Nat.add_0_r.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.IncsOvs.
  1: ss.
  1: ss.
  1: ss.
  solve_sideRLs.
Qed.

Lemma LC_Incs a b:
  sideRLs tm' (hLR^^(((((1+1)*2^a-1)*2+1)*2^b-1)+1+(((((0+1)*2^(a+1)-1)*1+1)+1)*2^(b+1)-1))) (LC0 a b) (LC1 (a+1) (b+1)).
Proof.
  do 2 rewrite lpow_add.
  eapply sideRLs_trans.
  2: apply LC3_Incs.
  eapply sideRLs_trans.
  2: apply LC2_Ov.
  apply LC0_Incs.
Qed.

Lemma LC_Incs' a b:
  sideRLs tm' (hLR^^((2^(a+b+3))+2^b-1)) (LC0 a b) (LC1 (a+1) (b+1)).
Proof.
  applys_eq LC_Incs.
  f_equal.
  rw_pa; zify_pow2sub1; lia.
Qed.



Ltac R_sub n :=
  match goal with
  | |- sideRLs _ (_^^?a) _ _ =>
    rewrite <-(Nat.sub_add n a) by lia'
  end.

Ltac R_m2 :=
  match goal with
  | |- sideRLs _ (_^^?a) _ _ =>
    replace a with (a/2*2) by lia'
  end.

Ltac R_m2a1 :=
  match goal with
  | |- sideRLs _ (_^^?a) _ _ =>
    replace a with (a/2*2+1) by lia'
  end.

Ltac R_x x :=
  match goal with
  | |- sideRLs _ (_^^?a) _ _ =>
    replace a with x by lia'
  end.




Lemma rw_0_rd0 r:
  [0] *> rd0 *> r = rd0 *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_rd1 r:
  [0] *> rd1 *> r = [0;1;0;0] *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_01s n r:
  [0] *> (rd0++rd1)^^n *> r = (rd0++[0;1;0;0])^^n *> [0] *> r.
Proof.
  simpl_rotate; reflexivity.
Qed.

Ltac ss ::= solve_segRLs.

Lemma segRLs_d1_d0 n:
  segRLs tm (hRL^^(n*2+1)) (hRL^^(n+1)) rd1 rd0.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 1 1 n); flia; ss.
Qed.

Lemma segRLs_d1_d1 n:
  segRLs tm (hRL^^(n*2)) (hRL^^(n)) rd1 rd1.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 0 0 n); flia; ss.
Qed.

Lemma segRLs_d0_d0 n:
  segRLs tm (hRL^^(n*2)) (hRL^^(n)) rd0 rd0.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 0 0 n); flia; ss.
Qed.

Lemma segRLs_d0_d1 n:
  segRLs tm (hRL^^(n*2+1)) (hRL^^(n)) rd0 rd1.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 1 0 n); flia; ss.
Qed.

Lemma hRLx_d0 h r r' r0:
  sideRLs tm (hRL^^1) r r0 ->
  sideRLs tm h (rd0*>rd0*>r0) r' ->
  sideRLs tm (hRLx++h) (rd0*>r) r'.
Proof.
  intros.
  eapply sideRLs_trans.
  2: apply H0.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  esx.
Qed.

Lemma hRLx_0100 h r r' r0:
  sideRLs tm (hRLx++[]) r r0 ->
  sideRLs tm h (rd0*>r0) r' ->
  sideRLs tm (hRLx++h) ([0;1;0;0]*>r) r'.
Proof.
  intros.
  eapply sideRLs_trans.
  2: apply H0.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  esx.
Qed.

Lemma hRL_1100 n r r':
  sideRLs tm (hRLx++hRL^^n) r r' ->
  sideRLs tm (hRL^^(n+1)) ([1;1;0;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  change r' with ([]*>r').
  eapply @segRLs_sideRLs_concat.
  2: apply H.
  eapply segRLs_trans.
  1: esx.
  eapply segRLs_nil.
Qed.

Lemma hRL_0100 n r r':
  sideRLs tm (hRL^^n) ([1;1;0;0]*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;1;0;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Ltac rw_0 :=
  repeat (
  rewrite rw_0_rd0 ||
  rewrite rw_0_rd1 ||
  rewrite rw_0_01s ||
  rewrite rw_0_0inf);
  cbn[Nat.add]; cbn[lpow];
  repeat rewrite Str_app_assoc;
  repeat rewrite Str_app_nil.


Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- ?G => idtac G
  end;
  match goal with
  | |- sideRLs _ [] _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ (_^^O) _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ (hRLx++_) (rd0*>_) _ =>
    eapply hRLx_d0; [sscs|]
  | |- sideRLs _ (hRLx++_) ([0;1;0;0]*>_) _ =>
    eapply hRLx_0100; [sscs|]
  | |- sideRLs _ _ ([0;1;0;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_0100
  | |- sideRLs _ _ ([1;1;0;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_1100
  | |- sideRLs _ _ (rd0*>_) _ =>
    (R_m2a1; ssc segRLs_d0_d1) ||
    (R_m2; ssc segRLs_d0_d0)
  | |- sideRLs _ _ (rd1*>_) _ =>
    (R_m2a1; ssc segRLs_d1_d0) ||
    (R_m2; ssc segRLs_d1_d1)
  end; simpl_nat);
  match goal with
  | |- ?G => idtac "fail"; idtac G
  end.

Lemma hRLx_01 n r r':
  sideRLs tm (hRLx++hRL^^n) r r' ->
  sideRLs tm (hRLx++hRL^^(((n+1)*2+1)*2)) (rd0 *> [0;1;0;0] *> r) (rd0*>rd1*>r').
Proof.
  intros.
  sscs.
  applys_eq H; flia.
Qed.

Lemma hRLx_01s k n r r':
  2<=k ->
  sideRLs tm (hRLx++hRL^^(k-2)) r r' ->
  sideRLs tm (hRLx++hRL^^(k*2^(n*2)-2)) ((rd0++[0;1;0;0])^^n*>r) ((rd0++rd1)^^n*>r').
Proof.
  intros.
  induction n.
  - applys_eq H0; flia.
  - cbn[lpow].
    repeat rewrite Str_app_assoc.
    apply hRLx_01 in IHn.
    replace (S n*2) with (n*2+2) by lia.
    rw_pa.
    applys_eq IHn; flia.
Qed.

Inductive RC: nat->side->Prop :=
| RC_4:
    RC 4
  (rd1*>rd0*>rd0*>rd1*>rd0*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>0inf)
| RC_5:
    RC 5
  (rd1*>rd0*>rd0*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>0inf)
| RC_6:
    RC 6
  (rd1*>rd0*>rd0*>rd0*>rd0*>rd1*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>0inf)
| RC_7:
    RC 7
  (rd1*>rd0*>rd0*>rd0*>rd0*>rd0*>rd0*>rd1*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>0inf)
| RC_8 n:
    RC (n*2+8)
  (rd1*>rd0*>rd0*>rd0*>rd0*>rd0*>rd1*>(rd0++rd1)^^n*>rd1*>rd1*>(rd0++rd1)^^(5+n)*>0inf)
| RC_9 n:
    RC (n*2+9)
  (rd1*>rd0*>rd0*>rd0*>rd0*>rd0*>rd1*>(rd0++rd1)^^n*>rd0*>rd0*>rd1*>rd1*>(rd0++rd1)^^(5+n)*>0inf)
.

Ltac sscs' := rw_0; sscs; solve_sideRLs.

Lemma RC_Incs n r r':
  RC n r ->
  RC (S n) r' ->
  sideRLs tm (hRL^^((2^(n+5)+1)*2^(n+0)+0)) ([0]*>r) (rd0*>r').
Proof.
  intros I1 I2.
  inverts I1; inverts I2; try lia.
  - sscs'.
  - sscs'.
  - sscs'.
  - replace n with O by lia.
    sscs'.
  - replace n0 with n in * by lia.
    rw_0.
    eapply sideRLs_feq2; [|shelve].
    repeat rewrite Nat.mul_succ_l.
    sscs.
    replace ((2 ^ (n * 2 + 13) + 1) * 2 ^ (n * 2 + 2) - 2) with
      ((2 ^ (n * 2 + 15) + 4) * 2 ^ (n * 2) - 2) by lia'.
    eapply hRLx_01s; [lia|].
    sscs.
    replace (2 ^ (n * 2 + 3) - 2) with (8 * 2 ^ (n * 2) - 2) by lia'.
    eapply hRLx_01s; [lia|].
    solve_sideRLs.
  - replace n with (S n0) in * by lia.
    clear n.
    rename n0 into n.
    rw_0.
    eapply sideRLs_feq2; [|shelve].
    repeat rewrite Nat.mul_succ_l.
    sscs.
    replace ((2 ^ (n * 2 + 14) + 1) * 2 ^ (n * 2 + 3) - 2) with
      ((2 ^ (n * 2 + 17) + 8) * 2 ^ (n * 2) - 2) by lia'.
    eapply hRLx_01s; [lia|].
    sscs.
    replace (2 ^ (n * 2 + 3) - 2) with (8 * 2 ^ (n * 2) - 2) by lia'.
    eapply hRLx_01s; [lia|].
    solve_sideRLs.
    Unshelve.
    all: st; simpl_rotate; reflexivity.
Qed.

Definition S0 '(n,r) := LC1 (n+2) n <| rd0 *> r.

Lemma BigStep' n r r':
  RC n r ->
  RC (S n) r' ->
  S0 (n,r) -->+
  S0 (S n,r').
Proof.
  intros.
  epose proof (RC_Incs _ _ _ H H0) as I1.
  unfold S0.
  cbn[Str_app].
  follow LC1_Ov.
  epose proof (sideRLs_concat (LC_Incs' (n+2) n)) as I2.
  rewrite lrcons_lpow1 in I2 by lia.
  rewrite <-(Nat.add_1_r n).
  replace (n+1+2) with (n+2+1) by lia.
  eapply I2.
  applys_eq I1.
  rw_pa; flia.
Qed.

Lemma RC_S n r:
  RC n r ->
  exists r', RC (S n) r'.
Proof.
  intros.
  inverts H; eexists; try solve[econstructor].
  - eapply (RC_8 O).
  - applys_eq (RC_9 n0); flia.
  - applys_eq (RC_8 (S n0)); flia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  epose proof (RC_4) as I1.
  match goal with
  | [I1:RC _ ?r|-_] =>
    eapply multistep_nonhalt with (c':=S0 (4,r))
  end.
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(n,r) => RC n r).
  2: apply I1.
  intros [n r] HRC.
  epose proof HRC as HRC'.
  eapply RC_S in HRC'.
  destruct HRC' as [r' I2].
  eexists; split.
  1: apply BigStep'; try eassumption.
  apply I2.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB1RF_1LC0RA_1RE0LD_1LE1LC_1RA0RC_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation ld1 := <[1;1;1;1].
Notation ld0 := <[1;0;1;0].

Definition LC1 a b :=
  0inf <* ld1^^a <* <[1;0;1;1;1;1;1;0] <* ld1^^b <* <[1;0;1;1;1;1;1].

Definition LC0 a b :=
  0inf <* <[1;0] <* ld0^^a <* <[1;0;1;1;1;1;1;0] <* ld1 <* ld0^^b <* <[1;0;1;1;1;1;1].

Definition LC2 a b :=
  0inf <* <[1;1;1] <* ld1^^a <* <[1;0;1;1;1;1;1;0] <* ld1^^b <* <[1;0;1;1;1;1;1].

Definition LC3 a b :=
  0inf <* ld0^^a <* <[1;0;1;0;1;0;1;1] <* ld0^^b <* <[1;0;1;1;1;1;1].

Notation "l <| r" := (l <{{E}} [1;0] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{B}}> r) (at level 30).

Lemma LC1_Ov a b r:
  LC1 a b <| [0;0;0] *> r -->*
  LC0 a b |> r.
Proof.
  unfold LC1,LC0.
  es.
Qed.

Notation hRL := [((B,[1;0]),(E,[1;0]))].
Notation hRLx := [((B,[1;1;1;0;1;0]),(E,[1;0]))].
Notation hLR := [((E,[1;0]),(B,[1;0]))].
Notation hLR' := [((D,[]),(A,[]))].

Ltac ss := solve_seg.

Lemma LC0_Incs a b:
  sideRLs tm' (hLR^^((((1+1)*2^a-1)*2+1)*2^b-1)) (LC0 a b) (LC2 a (b+1)).
Proof.
  unfold LC0,LC2.
  rewrite lpow_add.
  rewrite Str_app_assoc.
  eapply @segRLs_sideRLs_concat with (ls2:=hLR'^^_).
  1: eapply segRLs_wall'.
  1: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.IncsOvs.
  1: ss.
  1: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  2: ss.
  2: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply segRLs_wall.
  1: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.IncsOvs.
  1: ss.
  1: ss.
  1: ss.
  solve_sideRLs.
Qed.

Lemma LC2_Ov a b:
  sideRLs tm' hLR (LC2 a b) (LC3 (a+1) b).
Proof.
  unfold LC2,LC3.
  solve_sideRLs.
Qed.

Lemma LC3_Incs a b:
  sideRLs tm' (hLR^^(((((0+1)*2^a-1)*1+1)+1)*2^b-1)) (LC3 a b) (LC1 a b).
Proof.
  unfold LC3,LC1.
  eapply @segRLs_sideRLs_concat with (ls2:=hLR'^^_).
  1: eapply segRLs_wall'.
  1: ss.
  1: ss.
  Print BC.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.IncsOvs.
  1: ss.
  1: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply segRLs_addmul with (c:=O); esx.
  rewrite Nat.add_0_r.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.IncsOvs.
  1: ss.
  1: ss.
  1: ss.
  solve_sideRLs.
Qed.

Lemma LC_Incs a b:
  sideRLs tm' (hLR^^(((((1+1)*2^a-1)*2+1)*2^b-1)+1+(((((0+1)*2^(a+1)-1)*1+1)+1)*2^(b+1)-1))) (LC0 a b) (LC1 (a+1) (b+1)).
Proof.
  do 2 rewrite lpow_add.
  eapply sideRLs_trans.
  2: apply LC3_Incs.
  eapply sideRLs_trans.
  2: apply LC2_Ov.
  apply LC0_Incs.
Qed.

Lemma LC_Incs' a b:
  sideRLs tm' (hLR^^((2^(a+b+3))+2^b-1)) (LC0 a b) (LC1 (a+1) (b+1)).
Proof.
  applys_eq LC_Incs.
  f_equal.
  rw_pa; zify_pow2sub1; lia.
Qed.



Ltac R_sub n :=
  match goal with
  | |- sideRLs _ (_^^?a) _ _ =>
    rewrite <-(Nat.sub_add n a) by lia'
  end.

Ltac R_m2 :=
  match goal with
  | |- sideRLs _ (_^^?a) _ _ =>
    replace a with (a/2*2) by lia'
  end.

Ltac R_m2a1 :=
  match goal with
  | |- sideRLs _ (_^^?a) _ _ =>
    replace a with (a/2*2+1) by lia'
  end.

Ltac R_x x :=
  match goal with
  | |- sideRLs _ (_^^?a) _ _ =>
    replace a with x by lia'
  end.




Lemma rw_0_rd0 r:
  [0] *> rd0 *> r = rd0 *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_rd1 r:
  [0] *> rd1 *> r = [0;1;0;0] *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_01s n r:
  [0] *> (rd0++rd1)^^n *> r = (rd0++[0;1;0;0])^^n *> [0] *> r.
Proof.
  simpl_rotate; reflexivity.
Qed.

Ltac ss ::= solve_segRLs.

Lemma segRLs_d1_d0 n:
  segRLs tm (hRL^^(n*2+1)) (hRL^^(n+1)) rd1 rd0.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 1 1 n); flia; ss.
Qed.

Lemma segRLs_d1_d1 n:
  segRLs tm (hRL^^(n*2)) (hRL^^(n)) rd1 rd1.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 0 0 n); flia; ss.
Qed.

Lemma segRLs_d0_d0 n:
  segRLs tm (hRL^^(n*2)) (hRL^^(n)) rd0 rd0.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 0 0 n); flia; ss.
Qed.

Lemma segRLs_d0_d1 n:
  segRLs tm (hRL^^(n*2+1)) (hRL^^(n)) rd0 rd1.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 1 0 n); flia; ss.
Qed.

Lemma hRLx_d0 h r r' r0:
  sideRLs tm (hRL^^1) r r0 ->
  sideRLs tm h (rd0*>rd0*>r0) r' ->
  sideRLs tm (hRLx++h) (rd0*>r) r'.
Proof.
  intros.
  eapply sideRLs_trans.
  2: apply H0.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  esx.
Qed.

Lemma hRLx_0100 h r r' r0:
  sideRLs tm (hRLx++[]) r r0 ->
  sideRLs tm h (rd0*>r0) r' ->
  sideRLs tm (hRLx++h) ([0;1;0;0]*>r) r'.
Proof.
  intros.
  eapply sideRLs_trans.
  2: apply H0.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  esx.
Qed.

Lemma hRL_1100 n r r':
  sideRLs tm (hRLx++hRL^^n) r r' ->
  sideRLs tm (hRL^^(n+1)) ([1;1;0;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  change r' with ([]*>r').
  eapply @segRLs_sideRLs_concat.
  2: apply H.
  eapply segRLs_trans.
  1: esx.
  eapply segRLs_nil.
Qed.

Lemma hRL_0100 n r r':
  sideRLs tm (hRL^^n) ([1;1;0;0]*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;1;0;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Ltac rw_0 :=
  repeat (
  rewrite rw_0_rd0 ||
  rewrite rw_0_rd1 ||
  rewrite rw_0_01s ||
  rewrite rw_0_0inf);
  cbn[Nat.add]; cbn[lpow];
  repeat rewrite Str_app_assoc;
  repeat rewrite Str_app_nil.


Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- ?G => idtac G
  end;
  match goal with
  | |- sideRLs _ [] _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ (_^^O) _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ (hRLx++_) (rd0*>_) _ =>
    eapply hRLx_d0; [sscs|]
  | |- sideRLs _ (hRLx++_) ([0;1;0;0]*>_) _ =>
    eapply hRLx_0100; [sscs|]
  | |- sideRLs _ _ ([0;1;0;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_0100
  | |- sideRLs _ _ ([1;1;0;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_1100
  | |- sideRLs _ _ (rd0*>_) _ =>
    (R_m2a1; ssc segRLs_d0_d1) ||
    (R_m2; ssc segRLs_d0_d0)
  | |- sideRLs _ _ (rd1*>_) _ =>
    (R_m2a1; ssc segRLs_d1_d0) ||
    (R_m2; ssc segRLs_d1_d1)
  end; simpl_nat);
  match goal with
  | |- ?G => idtac "fail"; idtac G
  end.

Lemma hRLx_01 n r r':
  sideRLs tm (hRLx++hRL^^n) r r' ->
  sideRLs tm (hRLx++hRL^^(((n+1)*2+1)*2)) (rd0 *> [0;1;0;0] *> r) (rd0*>rd1*>r').
Proof.
  intros.
  sscs.
  applys_eq H; flia.
Qed.

Lemma hRLx_01s k n r r':
  2<=k ->
  sideRLs tm (hRLx++hRL^^(k-2)) r r' ->
  sideRLs tm (hRLx++hRL^^(k*2^(n*2)-2)) ((rd0++[0;1;0;0])^^n*>r) ((rd0++rd1)^^n*>r').
Proof.
  intros.
  induction n.
  - applys_eq H0; flia.
  - cbn[lpow].
    repeat rewrite Str_app_assoc.
    apply hRLx_01 in IHn.
    replace (S n*2) with (n*2+2) by lia.
    rw_pa.
    applys_eq IHn; flia.
Qed.


Inductive RC: nat->side->Prop :=
| RC_2:
    RC 2
  (rd0*>rd1*>rd0*>rd0*>rd1*>rd0*>rd0*>rd0*>rd0*>rd1*>0inf)
| RC_3:
    RC 3
  (rd0*>rd0*>rd1*>rd0*>rd1*>rd0*>rd0*>rd0*>rd0*>rd1*>rd0*>rd1*>0inf)
| RC_4:
    RC 4
  (rd0*>rd0*>rd0*>rd1*>rd1*>rd0*>rd0*>rd0*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>0inf)
| RC_5:
    RC 5
  (rd0*>rd0*>rd0*>rd0*>rd0*>rd1*>rd0*>rd0*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>0inf)
| RC_6:
    RC 6
  (rd0*>rd0*>rd0*>rd0*>rd1*>rd1*>rd0*>rd0*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>0inf)
| RC_7:
    RC 7
  (rd0*>rd0*>rd0*>rd0*>rd1*>rd0*>rd1*>rd0*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>0inf)
| RC_8:
    RC 8
  (rd0*>rd0*>rd0*>rd0*>rd1*>rd0*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>0inf)
| RC_9 n:
    RC (n*2+9)
  (rd0*>rd0*>rd0*>rd0*>rd1*>rd0*>rd0*>rd0*>(rd0++rd1)^^n*>rd1*>rd1*>(rd0++rd1)^^(7+n)*>0inf)
| RC_10 n:
    RC (n*2+10)
  (rd0*>rd0*>rd0*>rd0*>rd1*>rd0*>rd0*>rd0*>(rd0++rd1)^^n*>rd0*>rd0*>rd1*>rd1*>(rd0++rd1)^^(7+n)*>0inf)
.

Ltac sscs' := rw_0; sscs; solve_sideRLs.

Lemma RC_Incs n r r':
  RC n r ->
  RC (S n) r' ->
  sideRLs tm (hRL^^((2^(n+8)+1)*2^(n+0)+0)) ([0]*>r) (rd0*>r').
Proof.
  intros I1 I2.
  inverts I1; inverts I2; try lia.
  - sscs'.
  - sscs'.
  - sscs'.
  - sscs'.
  - sscs'.
  - sscs'.
  - replace n with O by lia.
    sscs'.
  - replace n0 with n in * by lia.
    destruct n as [|].
    1: sscs'.
    rw_0.
    eapply sideRLs_feq2; [|shelve].
    repeat rewrite Nat.mul_succ_l.
    sscs.
    replace ((2 ^ (n * 2 + 19) + 1) * 2 ^ (n * 2 + 2) - 2) with
      ((2 ^ (n * 2 + 21) + 4) * 2 ^ (n * 2) - 2) by lia'.
    eapply hRLx_01s; [lia|].
    sscs.
    replace (2 ^ (n * 2 + 3) - 2) with (8 * 2 ^ (n * 2) - 2) by lia'.
    eapply hRLx_01s; [lia|].
    solve_sideRLs.
  - replace n with (S n0) in * by lia.
    clear n.
    rename n0 into n.
    destruct n as [|].
    1: sscs'.
    rw_0.
    eapply sideRLs_feq2; [|shelve].
    repeat rewrite Nat.mul_succ_l.
    sscs.
    replace ((2 ^ (n * 2 + 20) + 1) * 2 ^ (n * 2 + 3) - 2) with
      ((2 ^ (n * 2 + 23) + 8) * 2 ^ (n * 2) - 2) by lia'.
    eapply hRLx_01s; [lia|].
    sscs.
    replace (2 ^ (n * 2 + 3) - 2) with (8 * 2 ^ (n * 2) - 2) by lia'.
    eapply hRLx_01s; [lia|].
    solve_sideRLs.
    Unshelve.
    all: st; simpl_rotate; reflexivity.
Qed.

Definition S0 '(n,r) := LC1 (n+5) n <| rd0 *> r.

Lemma BigStep' n r r':
  RC n r ->
  RC (S n) r' ->
  S0 (n,r) -->+
  S0 (S n,r').
Proof.
  intros.
  epose proof (RC_Incs _ _ _ H H0) as I1.
  unfold S0.
  cbn[Str_app].
  follow LC1_Ov.
  epose proof (sideRLs_concat (LC_Incs' (n+5) n)) as I2.
  rewrite lrcons_lpow1 in I2 by lia.
  rewrite <-(Nat.add_1_r n).
  replace (n+1+5) with (n+5+1) by lia.
  eapply I2.
  applys_eq I1.
  rw_pa; flia.
Qed.

Lemma RC_S n r:
  RC n r ->
  exists r', RC (S n) r'.
Proof.
  intros.
  inverts H; eexists; try solve[econstructor].
  - eapply (RC_9 O).
  - applys_eq (RC_10 n0); flia.
  - applys_eq (RC_9 (S n0)); flia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  epose proof (RC_2) as I1.
  match goal with
  | [I1:RC _ ?r|-_] =>
    eapply multistep_nonhalt with (c':=S0 (2,r))
  end.
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(n,r) => RC n r).
  2: apply I1.
  intros [n r] HRC.
  epose proof HRC as HRC'.
  eapply RC_S in HRC'.
  destruct HRC' as [r' I2].
  eexists; split.
  1: apply BigStep'; try eassumption.
  apply I2.
Qed.

End TM3.


Module TM5.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC0RA_1RE0LD_1LE1LC_1RA0RC_0LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation ld1 := <[1;1;1;1].
Notation ld0 := <[1;0;1;0].

Definition LC1 a b :=
  0inf <* ld1^^a <* <[1;0;1;1;1;1;1;0] <* ld1^^b <* <[1;0;1;1;1;1;1].

Definition LC0 a b :=
  0inf <* <[1;0] <* ld0^^a <* <[1;0;1;1;1;1;1;0] <* ld1 <* ld0^^b <* <[1;0;1;1;1;1;1].

Definition LC2 a b :=
  0inf <* <[1;1;1] <* ld1^^a <* <[1;0;1;1;1;1;1;0] <* ld1^^b <* <[1;0;1;1;1;1;1].

Definition LC3 a b :=
  0inf <* ld0^^a <* <[1;0;1;0;1;0;1;1] <* ld0^^b <* <[1;0;1;1;1;1;1].

Notation "l <| r" := (l <{{E}} [1;0] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{B}}> r) (at level 30).

Lemma LC1_Ov a b r:
  LC1 a b <| [0;0;0] *> r -->*
  LC0 a b |> r.
Proof.
  unfold LC1,LC0.
  es.
Qed.

Notation hRL := [((B,[1;0]),(E,[1;0]))].
Notation hRLx := [((B,[1;1;1;0;1;0]),(E,[1;0]))].
Notation hLR := [((E,[1;0]),(B,[1;0]))].
Notation hLR' := [((D,[]),(A,[]))].

Ltac ss := solve_seg.

Lemma LC0_Incs a b:
  sideRLs tm' (hLR^^((((1+1)*2^a-1)*2+1)*2^b-1)) (LC0 a b) (LC2 a (b+1)).
Proof.
  unfold LC0,LC2.
  rewrite lpow_add.
  rewrite Str_app_assoc.
  eapply @segRLs_sideRLs_concat with (ls2:=hLR'^^_).
  1: eapply segRLs_wall'.
  1: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.IncsOvs.
  1: ss.
  1: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  2: ss.
  2: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply segRLs_wall.
  1: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.IncsOvs.
  1: ss.
  1: ss.
  1: ss.
  solve_sideRLs.
Qed.

Lemma LC2_Ov a b:
  sideRLs tm' hLR (LC2 a b) (LC3 (a+1) b).
Proof.
  unfold LC2,LC3.
  solve_sideRLs.
Qed.

Lemma LC3_Incs a b:
  sideRLs tm' (hLR^^(((((0+1)*2^a-1)*1+1)+1)*2^b-1)) (LC3 a b) (LC1 a b).
Proof.
  unfold LC3,LC1.
  eapply @segRLs_sideRLs_concat with (ls2:=hLR'^^_).
  1: eapply segRLs_wall'.
  1: ss.
  1: ss.
  Print BC.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.IncsOvs.
  1: ss.
  1: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply segRLs_addmul with (c:=O); esx.
  rewrite Nat.add_0_r.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.IncsOvs.
  1: ss.
  1: ss.
  1: ss.
  solve_sideRLs.
Qed.

Lemma LC_Incs a b:
  sideRLs tm' (hLR^^(((((1+1)*2^a-1)*2+1)*2^b-1)+1+(((((0+1)*2^(a+1)-1)*1+1)+1)*2^(b+1)-1))) (LC0 a b) (LC1 (a+1) (b+1)).
Proof.
  do 2 rewrite lpow_add.
  eapply sideRLs_trans.
  2: apply LC3_Incs.
  eapply sideRLs_trans.
  2: apply LC2_Ov.
  apply LC0_Incs.
Qed.

Lemma LC_Incs' a b:
  sideRLs tm' (hLR^^((2^(a+b+3))+2^b-1)) (LC0 a b) (LC1 (a+1) (b+1)).
Proof.
  applys_eq LC_Incs.
  f_equal.
  rw_pa; zify_pow2sub1; lia.
Qed.



Ltac R_sub n :=
  match goal with
  | |- sideRLs _ (_^^?a) _ _ =>
    rewrite <-(Nat.sub_add n a) by lia'
  end.

Ltac R_m2 :=
  match goal with
  | |- sideRLs _ (_^^?a) _ _ =>
    replace a with (a/2*2) by lia'
  end.

Ltac R_m2a1 :=
  match goal with
  | |- sideRLs _ (_^^?a) _ _ =>
    replace a with (a/2*2+1) by lia'
  end.

Ltac R_x x :=
  match goal with
  | |- sideRLs _ (_^^?a) _ _ =>
    replace a with x by lia'
  end.




Lemma rw_0_rd0 r:
  [0] *> rd0 *> r = rd0 *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_rd1 r:
  [0] *> rd1 *> r = [0;1;0;0] *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_01s n r:
  [0] *> (rd0++rd1)^^n *> r = (rd0++[0;1;0;0])^^n *> [0] *> r.
Proof.
  simpl_rotate; reflexivity.
Qed.

Ltac ss ::= solve_segRLs.

Lemma segRLs_d1_d0 n:
  segRLs tm (hRL^^(n*2+1)) (hRL^^(n+1)) rd1 rd0.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 1 1 n); flia; ss.
Qed.

Lemma segRLs_d1_d1 n:
  segRLs tm (hRL^^(n*2)) (hRL^^(n)) rd1 rd1.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 0 0 n); flia; ss.
Qed.

Lemma segRLs_d0_d0 n:
  segRLs tm (hRL^^(n*2)) (hRL^^(n)) rd0 rd0.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 0 0 n); flia; ss.
Qed.

Lemma segRLs_d0_d1 n:
  segRLs tm (hRL^^(n*2+1)) (hRL^^(n)) rd0 rd1.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 1 0 n); flia; ss.
Qed.

Lemma hRLx_d0 h r r' r0:
  sideRLs tm (hRL^^1) r r0 ->
  sideRLs tm h (rd0*>rd0*>r0) r' ->
  sideRLs tm (hRLx++h) (rd0*>r) r'.
Proof.
  intros.
  eapply sideRLs_trans.
  2: apply H0.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  esx.
Qed.

Lemma hRLx_0100 h r r' r0:
  sideRLs tm (hRLx++[]) r r0 ->
  sideRLs tm h (rd0*>r0) r' ->
  sideRLs tm (hRLx++h) ([0;1;0;0]*>r) r'.
Proof.
  intros.
  eapply sideRLs_trans.
  2: apply H0.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  esx.
Qed.

Lemma hRL_1100 n r r':
  sideRLs tm (hRLx++hRL^^n) r r' ->
  sideRLs tm (hRL^^(n+1)) ([1;1;0;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  change r' with ([]*>r').
  eapply @segRLs_sideRLs_concat.
  2: apply H.
  eapply segRLs_trans.
  1: esx.
  eapply segRLs_nil.
Qed.

Lemma hRL_0100 n r r':
  sideRLs tm (hRL^^n) ([1;1;0;0]*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;1;0;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Ltac rw_0 :=
  repeat (
  rewrite rw_0_rd0 ||
  rewrite rw_0_rd1 ||
  rewrite rw_0_01s ||
  rewrite rw_0_0inf);
  cbn[Nat.add]; cbn[lpow];
  repeat rewrite Str_app_assoc;
  repeat rewrite Str_app_nil.


Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- ?G => idtac G
  end;
  match goal with
  | |- sideRLs _ [] _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ (_^^O) _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ (hRLx++_) (rd0*>_) _ =>
    eapply hRLx_d0; [sscs|]
  | |- sideRLs _ (hRLx++_) ([0;1;0;0]*>_) _ =>
    eapply hRLx_0100; [sscs|]
  | |- sideRLs _ _ ([0;1;0;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_0100
  | |- sideRLs _ _ ([1;1;0;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_1100
  | |- sideRLs _ _ (rd0*>_) _ =>
    (R_m2a1; ssc segRLs_d0_d1) ||
    (R_m2; ssc segRLs_d0_d0)
  | |- sideRLs _ _ (rd1*>_) _ =>
    (R_m2a1; ssc segRLs_d1_d0) ||
    (R_m2; ssc segRLs_d1_d1)
  end; simpl_nat);
  match goal with
  | |- ?G => idtac "fail"; idtac G
  end.

Lemma hRLx_01 n r r':
  sideRLs tm (hRLx++hRL^^n) r r' ->
  sideRLs tm (hRLx++hRL^^(((n+1)*2+1)*2)) (rd0 *> [0;1;0;0] *> r) (rd0*>rd1*>r').
Proof.
  intros.
  sscs.
  applys_eq H; flia.
Qed.

Lemma hRLx_01s k n r r':
  2<=k ->
  sideRLs tm (hRLx++hRL^^(k-2)) r r' ->
  sideRLs tm (hRLx++hRL^^(k*2^(n*2)-2)) ((rd0++[0;1;0;0])^^n*>r) ((rd0++rd1)^^n*>r').
Proof.
  intros.
  induction n.
  - applys_eq H0; flia.
  - cbn[lpow].
    repeat rewrite Str_app_assoc.
    apply hRLx_01 in IHn.
    replace (S n*2) with (n*2+2) by lia.
    rw_pa.
    applys_eq IHn; flia.
Qed.


Inductive RC: nat->side->Prop :=
| RC_2:
    RC 2
  (rd0*>rd1*>rd0*>rd0*>rd1*>rd0*>rd0*>rd0*>rd0*>rd1*>0inf)
| RC_3:
    RC 3
  (rd0*>rd0*>rd1*>rd0*>rd1*>rd0*>rd0*>rd0*>rd0*>rd1*>rd0*>rd1*>0inf)
| RC_4:
    RC 4
  (rd0*>rd0*>rd0*>rd1*>rd1*>rd0*>rd0*>rd0*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>0inf)
| RC_5:
    RC 5
  (rd0*>rd0*>rd0*>rd0*>rd0*>rd1*>rd0*>rd0*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>0inf)
| RC_6:
    RC 6
  (rd0*>rd0*>rd0*>rd0*>rd1*>rd1*>rd0*>rd0*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>0inf)
| RC_7:
    RC 7
  (rd0*>rd0*>rd0*>rd0*>rd1*>rd0*>rd1*>rd0*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>0inf)
| RC_8:
    RC 8
  (rd0*>rd0*>rd0*>rd0*>rd1*>rd0*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>0inf)
| RC_9 n:
    RC (n*2+9)
  (rd0*>rd0*>rd0*>rd0*>rd1*>rd0*>rd0*>rd0*>(rd0++rd1)^^n*>rd1*>rd1*>(rd0++rd1)^^(7+n)*>0inf)
| RC_10 n:
    RC (n*2+10)
  (rd0*>rd0*>rd0*>rd0*>rd1*>rd0*>rd0*>rd0*>(rd0++rd1)^^n*>rd0*>rd0*>rd1*>rd1*>(rd0++rd1)^^(7+n)*>0inf)
.

Ltac sscs' := rw_0; sscs; solve_sideRLs.

Lemma RC_Incs n r r':
  RC n r ->
  RC (S n) r' ->
  sideRLs tm (hRL^^((2^(n+8)+1)*2^(n+0)+0)) ([0]*>r) (rd0*>r').
Proof.
  intros I1 I2.
  inverts I1; inverts I2; try lia.
  - sscs'.
  - sscs'.
  - sscs'.
  - sscs'.
  - sscs'.
  - sscs'.
  - replace n with O by lia.
    sscs'.
  - replace n0 with n in * by lia.
    destruct n as [|].
    1: sscs'.
    rw_0.
    eapply sideRLs_feq2; [|shelve].
    repeat rewrite Nat.mul_succ_l.
    sscs.
    replace ((2 ^ (n * 2 + 19) + 1) * 2 ^ (n * 2 + 2) - 2) with
      ((2 ^ (n * 2 + 21) + 4) * 2 ^ (n * 2) - 2) by lia'.
    eapply hRLx_01s; [lia|].
    sscs.
    replace (2 ^ (n * 2 + 3) - 2) with (8 * 2 ^ (n * 2) - 2) by lia'.
    eapply hRLx_01s; [lia|].
    solve_sideRLs.
  - replace n with (S n0) in * by lia.
    clear n.
    rename n0 into n.
    destruct n as [|].
    1: sscs'.
    rw_0.
    eapply sideRLs_feq2; [|shelve].
    repeat rewrite Nat.mul_succ_l.
    sscs.
    replace ((2 ^ (n * 2 + 20) + 1) * 2 ^ (n * 2 + 3) - 2) with
      ((2 ^ (n * 2 + 23) + 8) * 2 ^ (n * 2) - 2) by lia'.
    eapply hRLx_01s; [lia|].
    sscs.
    replace (2 ^ (n * 2 + 3) - 2) with (8 * 2 ^ (n * 2) - 2) by lia'.
    eapply hRLx_01s; [lia|].
    solve_sideRLs.
    Unshelve.
    all: st; simpl_rotate; reflexivity.
Qed.

Definition S0 '(n,r) := LC1 (n+5) n <| rd0 *> r.

Lemma BigStep' n r r':
  RC n r ->
  RC (S n) r' ->
  S0 (n,r) -->+
  S0 (S n,r').
Proof.
  intros.
  epose proof (RC_Incs _ _ _ H H0) as I1.
  unfold S0.
  cbn[Str_app].
  follow LC1_Ov.
  epose proof (sideRLs_concat (LC_Incs' (n+5) n)) as I2.
  rewrite lrcons_lpow1 in I2 by lia.
  rewrite <-(Nat.add_1_r n).
  replace (n+1+5) with (n+5+1) by lia.
  eapply I2.
  applys_eq I1.
  rw_pa; flia.
Qed.

Lemma RC_S n r:
  RC n r ->
  exists r', RC (S n) r'.
Proof.
  intros.
  inverts H; eexists; try solve[econstructor].
  - eapply (RC_9 O).
  - applys_eq (RC_10 n0); flia.
  - applys_eq (RC_9 (S n0)); flia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  epose proof (RC_2) as I1.
  match goal with
  | [I1:RC _ ?r|-_] =>
    eapply multistep_nonhalt with (c':=S0 (2,r))
  end.
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(n,r) => RC n r).
  2: apply I1.
  intros [n r] HRC.
  epose proof HRC as HRC'.
  eapply RC_S in HRC'.
  destruct HRC' as [r' I2].
  eexists; split.
  1: apply BigStep'; try eassumption.
  apply I2.
Qed.

End TM5.


Module TM7.
Definition tm := Eval compute in (TM_from_str "1LB0RD_1RC0LE_1RD0RB_1RA0RF_1LC1LB_0LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation ld1 := <[1;1;1;1].
Notation ld0 := <[1;0;1;0].

Definition LC1 a b :=
  0inf <* ld1^^a <* <[1;0;1;1;1;1;1;0] <* ld1^^b <* <[1;0;1;1;1;1;1].

Definition LC0 a b :=
  0inf <* <[1;0] <* ld0^^a <* <[1;0;1;1;1;1;1;0] <* ld1 <* ld0^^b <* <[1;0;1;1;1;1;1].

Definition LC2 a b :=
  0inf <* <[1;1;1] <* ld1^^a <* <[1;0;1;1;1;1;1;0] <* ld1^^b <* <[1;0;1;1;1;1;1].

Definition LC3 a b :=
  0inf <* ld0^^a <* <[1;0;1;0;1;0;1;1] <* ld0^^b <* <[1;0;1;1;1;1;1].

Notation "l <| r" := (l <{{C}} [1;0] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{A}}> r) (at level 30).

Lemma LC1_Ov a b r:
  LC1 a b <| [0;0;0] *> r -->*
  LC0 a b |> r.
Proof.
  unfold LC1,LC0.
  es.
Qed.

Notation hRL := [((A,[1;0]),(C,[1;0]))].
Notation hRLx := [((A,[1;1;1;0;1;0]),(C,[1;0]))].
Notation hLR := [((C,[1;0]),(A,[1;0]))].
Notation hLR' := [((E,[]),(D,[]))].

Ltac ss := solve_seg.

Lemma LC0_Incs a b:
  sideRLs tm' (hLR^^((((1+1)*2^a-1)*2+1)*2^b-1)) (LC0 a b) (LC2 a (b+1)).
Proof.
  unfold LC0,LC2.
  rewrite lpow_add.
  rewrite Str_app_assoc.
  eapply @segRLs_sideRLs_concat with (ls2:=hLR'^^_).
  1: eapply segRLs_wall'.
  1: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.IncsOvs.
  1: ss.
  1: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  2: ss.
  2: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply segRLs_wall.
  1: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.IncsOvs.
  1: ss.
  1: ss.
  1: ss.
  solve_sideRLs.
Qed.

Lemma LC2_Ov a b:
  sideRLs tm' hLR (LC2 a b) (LC3 (a+1) b).
Proof.
  unfold LC2,LC3.
  solve_sideRLs.
Qed.

Lemma LC3_Incs a b:
  sideRLs tm' (hLR^^(((((0+1)*2^a-1)*1+1)+1)*2^b-1)) (LC3 a b) (LC1 a b).
Proof.
  unfold LC3,LC1.
  eapply @segRLs_sideRLs_concat with (ls2:=hLR'^^_).
  1: eapply segRLs_wall'.
  1: ss.
  1: ss.
  Print BC.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.IncsOvs.
  1: ss.
  1: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply segRLs_addmul with (c:=O); esx.
  rewrite Nat.add_0_r.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.IncsOvs.
  1: ss.
  1: ss.
  1: ss.
  solve_sideRLs.
Qed.

Lemma LC_Incs a b:
  sideRLs tm' (hLR^^(((((1+1)*2^a-1)*2+1)*2^b-1)+1+(((((0+1)*2^(a+1)-1)*1+1)+1)*2^(b+1)-1))) (LC0 a b) (LC1 (a+1) (b+1)).
Proof.
  do 2 rewrite lpow_add.
  eapply sideRLs_trans.
  2: apply LC3_Incs.
  eapply sideRLs_trans.
  2: apply LC2_Ov.
  apply LC0_Incs.
Qed.

Lemma LC_Incs' a b:
  sideRLs tm' (hLR^^((2^(a+b+3))+2^b-1)) (LC0 a b) (LC1 (a+1) (b+1)).
Proof.
  applys_eq LC_Incs.
  f_equal.
  rw_pa; zify_pow2sub1; lia.
Qed.



Ltac R_sub n :=
  match goal with
  | |- sideRLs _ (_^^?a) _ _ =>
    rewrite <-(Nat.sub_add n a) by lia'
  end.

Ltac R_m2 :=
  match goal with
  | |- sideRLs _ (_^^?a) _ _ =>
    replace a with (a/2*2) by lia'
  end.

Ltac R_m2a1 :=
  match goal with
  | |- sideRLs _ (_^^?a) _ _ =>
    replace a with (a/2*2+1) by lia'
  end.

Ltac R_x x :=
  match goal with
  | |- sideRLs _ (_^^?a) _ _ =>
    replace a with x by lia'
  end.




Lemma rw_0_rd0 r:
  [0] *> rd0 *> r = rd0 *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_rd1 r:
  [0] *> rd1 *> r = [0;1;0;0] *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_01s n r:
  [0] *> (rd0++rd1)^^n *> r = (rd0++[0;1;0;0])^^n *> [0] *> r.
Proof.
  simpl_rotate; reflexivity.
Qed.

Ltac ss ::= solve_segRLs.

Lemma segRLs_d1_d0 n:
  segRLs tm (hRL^^(n*2+1)) (hRL^^(n+1)) rd1 rd0.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 1 1 n); flia; ss.
Qed.

Lemma segRLs_d1_d1 n:
  segRLs tm (hRL^^(n*2)) (hRL^^(n)) rd1 rd1.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 0 0 n); flia; ss.
Qed.

Lemma segRLs_d0_d0 n:
  segRLs tm (hRL^^(n*2)) (hRL^^(n)) rd0 rd0.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 0 0 n); flia; ss.
Qed.

Lemma segRLs_d0_d1 n:
  segRLs tm (hRL^^(n*2+1)) (hRL^^(n)) rd0 rd1.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 1 0 n); flia; ss.
Qed.

Lemma hRLx_d0 h r r' r0:
  sideRLs tm (hRL^^1) r r0 ->
  sideRLs tm h (rd0*>rd0*>r0) r' ->
  sideRLs tm (hRLx++h) (rd0*>r) r'.
Proof.
  intros.
  eapply sideRLs_trans.
  2: apply H0.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  esx.
Qed.

Lemma hRLx_0100 h r r' r0:
  sideRLs tm (hRLx++[]) r r0 ->
  sideRLs tm h (rd0*>r0) r' ->
  sideRLs tm (hRLx++h) ([0;1;0;0]*>r) r'.
Proof.
  intros.
  eapply sideRLs_trans.
  2: apply H0.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  esx.
Qed.

Lemma hRL_1100 n r r':
  sideRLs tm (hRLx++hRL^^n) r r' ->
  sideRLs tm (hRL^^(n+1)) ([1;1;0;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  change r' with ([]*>r').
  eapply @segRLs_sideRLs_concat.
  2: apply H.
  eapply segRLs_trans.
  1: esx.
  eapply segRLs_nil.
Qed.

Lemma hRL_0100 n r r':
  sideRLs tm (hRL^^n) ([1;1;0;0]*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;1;0;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Ltac rw_0 :=
  repeat (
  rewrite rw_0_rd0 ||
  rewrite rw_0_rd1 ||
  rewrite rw_0_01s ||
  rewrite rw_0_0inf);
  cbn[Nat.add]; cbn[lpow];
  repeat rewrite Str_app_assoc;
  repeat rewrite Str_app_nil.


Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- ?G => idtac G
  end;
  match goal with
  | |- sideRLs _ [] _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ (_^^O) _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ (hRLx++_) (rd0*>_) _ =>
    eapply hRLx_d0; [sscs|]
  | |- sideRLs _ (hRLx++_) ([0;1;0;0]*>_) _ =>
    eapply hRLx_0100; [sscs|]
  | |- sideRLs _ _ ([0;1;0;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_0100
  | |- sideRLs _ _ ([1;1;0;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_1100
  | |- sideRLs _ _ (rd0*>_) _ =>
    (R_m2a1; ssc segRLs_d0_d1) ||
    (R_m2; ssc segRLs_d0_d0)
  | |- sideRLs _ _ (rd1*>_) _ =>
    (R_m2a1; ssc segRLs_d1_d0) ||
    (R_m2; ssc segRLs_d1_d1)
  end; simpl_nat);
  match goal with
  | |- ?G => idtac "fail"; idtac G
  end.

Lemma hRLx_01 n r r':
  sideRLs tm (hRLx++hRL^^n) r r' ->
  sideRLs tm (hRLx++hRL^^(((n+1)*2+1)*2)) (rd0 *> [0;1;0;0] *> r) (rd0*>rd1*>r').
Proof.
  intros.
  sscs.
  applys_eq H; flia.
Qed.

Lemma hRLx_01s k n r r':
  2<=k ->
  sideRLs tm (hRLx++hRL^^(k-2)) r r' ->
  sideRLs tm (hRLx++hRL^^(k*2^(n*2)-2)) ((rd0++[0;1;0;0])^^n*>r) ((rd0++rd1)^^n*>r').
Proof.
  intros.
  induction n.
  - applys_eq H0; flia.
  - cbn[lpow].
    repeat rewrite Str_app_assoc.
    apply hRLx_01 in IHn.
    replace (S n*2) with (n*2+2) by lia.
    rw_pa.
    applys_eq IHn; flia.
Qed.

Inductive RC: nat->side->Prop :=
| RC_5:
    RC 5
  (rd1*>rd1*>rd1*>rd1*>rd1*>rd0*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>0inf)
| RC_6:
    RC 6
  (rd1*>rd1*>rd1*>rd1*>rd1*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>0inf)
| RC_7:
    RC 7
  (rd1*>rd1*>rd1*>rd1*>rd1*>rd1*>rd1*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>0inf)
| RC_8 n:
    RC (n*2+8)
  (rd1*>rd1*>rd1*>rd1*>rd1*>rd1*>rd1*>rd0*>(rd0++rd1)^^n*>rd1*>rd1*>(rd0++rd1)^^(4+n)*>0inf)
| RC_9 n:
    RC (n*2+9)
  (rd1*>rd1*>rd1*>rd1*>rd1*>rd1*>rd1*>rd0*>(rd0++rd1)^^n*>rd0*>rd0*>rd1*>rd1*>(rd0++rd1)^^(4+n)*>0inf)
.

Ltac sscs' := rw_0; sscs; solve_sideRLs.

Lemma RC_Incs n r r':
  RC n r ->
  RC (S n) r' ->
  sideRLs tm (hRL^^((2^(n+3)+1)*2^(n+1)+0)) ([0]*>r) (rd0*>r').
Proof.
  intros I1 I2.
  inverts I1; inverts I2; try lia.
  - sscs'.
  - sscs'.
  - replace n with O by lia.
    sscs'.
  - replace n0 with n in * by lia.
    destruct n as [|[|]].
    + sscs'.
    + sscs'.
    + rw_0.
      eapply sideRLs_feq2; [|shelve].
      repeat rewrite Nat.mul_succ_l.
      sscs.
      replace ((2 ^ (n * 2 + 15) + 1) * 2 ^ (n * 2 + 2) - 2) with
        ((2 ^ (n * 2 + 17) + 4) * 2 ^ (n * 2) - 2) by lia'.
      eapply hRLx_01s; [lia|].
      sscs.
      replace (2 ^ (n * 2 + 3) - 2) with (8 * 2 ^ (n * 2) - 2) by lia'.
      eapply hRLx_01s; [lia|].
      solve_sideRLs.
  - replace n with (S n0) in * by lia.
    clear n.
    rename n0 into n.
    destruct n as [|[|]].
    + sscs'.
    + sscs'.
    + rw_0.
      eapply sideRLs_feq2; [|shelve].
      repeat rewrite Nat.mul_succ_l.
      sscs.
      replace ((2 ^ (n * 2 + 16) + 1) * 2 ^ (n * 2 + 3) - 2) with
        ((2 ^ (n * 2 + 19) + 8) * 2 ^ (n * 2) - 2) by lia'.
      eapply hRLx_01s; [lia|].
      sscs.
      replace (2 ^ (n * 2 + 3) - 2) with (8 * 2 ^ (n * 2) - 2) by lia'.
      eapply hRLx_01s; [lia|].
      solve_sideRLs.
      Unshelve.
      all: st; simpl_rotate; reflexivity.
Qed.

Definition S0 '(n,r) := LC1 n (n+1) <| rd0 *> r.

Lemma BigStep' n r r':
  RC n r ->
  RC (S n) r' ->
  S0 (n,r) -->+
  S0 (S n,r').
Proof.
  intros.
  epose proof (RC_Incs _ _ _ H H0) as I1.
  unfold S0.
  cbn[Str_app].
  follow LC1_Ov.
  epose proof (sideRLs_concat (LC_Incs' n (n+1))) as I2.
  rewrite lrcons_lpow1 in I2 by lia.
  rewrite <-(Nat.add_1_r n).
  eapply I2.
  applys_eq I1.
  rw_pa; flia.
Qed.

Lemma RC_S n r:
  RC n r ->
  exists r', RC (S n) r'.
Proof.
  intros.
  inverts H; eexists; try solve[econstructor].
  - eapply (RC_8 O).
  - applys_eq (RC_9 n0); flia.
  - applys_eq (RC_8 (S n0)); flia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  epose proof (RC_5) as I1.
  match goal with
  | [I1:RC _ ?r|-_] =>
    eapply multistep_nonhalt with (c':=S0 (5,r))
  end.
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(n,r) => RC n r).
  2: apply I1.
  intros [n r] HRC.
  epose proof HRC as HRC'.
  eapply RC_S in HRC'.
  destruct HRC' as [r' I2].
  eexists; split.
  1: apply BigStep'; try eassumption.
  apply I2.
Qed.

End TM7.


Module TM8.
Definition tm := Eval compute in (TM_from_str "1LB1LE_1RC0RE_1RF0RD_0LE---_1RB0LA_1LE0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation ld1 := <[1;1;1;1].
Notation ld0 := <[1;0;1;0].

Definition LC1 a b :=
  0inf <* ld1^^a <* <[1;0;1;1;1;1;1;0] <* ld1^^b <* <[1;0;1;1;1;1;1].

Definition LC0 a b :=
  0inf <* <[1;0] <* ld0^^a <* <[1;0;1;1;1;1;1;0] <* ld1 <* ld0^^b <* <[1;0;1;1;1;1;1].

Definition LC2 a b :=
  0inf <* <[1;1;1] <* ld1^^a <* <[1;0;1;1;1;1;1;0] <* ld1^^b <* <[1;0;1;1;1;1;1].

Definition LC3 a b :=
  0inf <* ld0^^a <* <[1;0;1;0;1;0;1;1] <* ld0^^b <* <[1;0;1;1;1;1;1].

Notation "l <| r" := (l <{{B}} [1;0] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{F}}> r) (at level 30).

Lemma LC1_Ov a b r:
  LC1 a b <| [0;0;0] *> r -->*
  LC0 a b |> r.
Proof.
  unfold LC1,LC0.
  es.
Qed.

Notation hRL := [((F,[1;0]),(B,[1;0]))].
Notation hRLx := [((F,[1;1;1;0;1;0]),(B,[1;0]))].
Notation hLR := [((B,[1;0]),(F,[1;0]))].
Notation hLR' := [((A,[]),(C,[]))].

Ltac ss := solve_seg.

Lemma LC0_Incs a b:
  sideRLs tm' (hLR^^((((1+1)*2^a-1)*2+1)*2^b-1)) (LC0 a b) (LC2 a (b+1)).
Proof.
  unfold LC0,LC2.
  rewrite lpow_add.
  rewrite Str_app_assoc.
  eapply @segRLs_sideRLs_concat with (ls2:=hLR'^^_).
  1: eapply segRLs_wall'.
  1: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.IncsOvs.
  1: ss.
  1: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  2: ss.
  2: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply segRLs_wall.
  1: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.IncsOvs.
  1: ss.
  1: ss.
  1: ss.
  solve_sideRLs.
Qed.

Lemma LC2_Ov a b:
  sideRLs tm' hLR (LC2 a b) (LC3 (a+1) b).
Proof.
  unfold LC2,LC3.
  solve_sideRLs.
Qed.

Lemma LC3_Incs a b:
  sideRLs tm' (hLR^^(((((0+1)*2^a-1)*1+1)+1)*2^b-1)) (LC3 a b) (LC1 a b).
Proof.
  unfold LC3,LC1.
  eapply @segRLs_sideRLs_concat with (ls2:=hLR'^^_).
  1: eapply segRLs_wall'.
  1: ss.
  1: ss.
  Print BC.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.IncsOvs.
  1: ss.
  1: ss.
  1: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply segRLs_addmul with (c:=O); esx.
  rewrite Nat.add_0_r.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.IncsOvs.
  1: ss.
  1: ss.
  1: ss.
  solve_sideRLs.
Qed.

Lemma LC_Incs a b:
  sideRLs tm' (hLR^^(((((1+1)*2^a-1)*2+1)*2^b-1)+1+(((((0+1)*2^(a+1)-1)*1+1)+1)*2^(b+1)-1))) (LC0 a b) (LC1 (a+1) (b+1)).
Proof.
  do 2 rewrite lpow_add.
  eapply sideRLs_trans.
  2: apply LC3_Incs.
  eapply sideRLs_trans.
  2: apply LC2_Ov.
  apply LC0_Incs.
Qed.

Lemma LC_Incs' a b:
  sideRLs tm' (hLR^^((2^(a+b+3))+2^b-1)) (LC0 a b) (LC1 (a+1) (b+1)).
Proof.
  applys_eq LC_Incs.
  f_equal.
  rw_pa; zify_pow2sub1; lia.
Qed.



Ltac R_sub n :=
  match goal with
  | |- sideRLs _ (_^^?a) _ _ =>
    rewrite <-(Nat.sub_add n a) by lia'
  end.

Ltac R_m2 :=
  match goal with
  | |- sideRLs _ (_^^?a) _ _ =>
    replace a with (a/2*2) by lia'
  end.

Ltac R_m2a1 :=
  match goal with
  | |- sideRLs _ (_^^?a) _ _ =>
    replace a with (a/2*2+1) by lia'
  end.

Ltac R_x x :=
  match goal with
  | |- sideRLs _ (_^^?a) _ _ =>
    replace a with x by lia'
  end.




Lemma rw_0_rd0 r:
  [0] *> rd0 *> r = rd0 *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_rd1 r:
  [0] *> rd1 *> r = [0;1;0;0] *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_01s n r:
  [0] *> (rd0++rd1)^^n *> r = (rd0++[0;1;0;0])^^n *> [0] *> r.
Proof.
  simpl_rotate; reflexivity.
Qed.

Ltac ss ::= solve_segRLs.

Lemma segRLs_d1_d0 n:
  segRLs tm (hRL^^(n*2+1)) (hRL^^(n+1)) rd1 rd0.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 1 1 n); flia; ss.
Qed.

Lemma segRLs_d1_d1 n:
  segRLs tm (hRL^^(n*2)) (hRL^^(n)) rd1 rd1.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 0 0 n); flia; ss.
Qed.

Lemma segRLs_d0_d0 n:
  segRLs tm (hRL^^(n*2)) (hRL^^(n)) rd0 rd0.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 0 0 n); flia; ss.
Qed.

Lemma segRLs_d0_d1 n:
  segRLs tm (hRL^^(n*2+1)) (hRL^^(n)) rd0 rd1.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 1 0 n); flia; ss.
Qed.

Lemma hRLx_d0 h r r' r0:
  sideRLs tm (hRL^^1) r r0 ->
  sideRLs tm h (rd0*>rd0*>r0) r' ->
  sideRLs tm (hRLx++h) (rd0*>r) r'.
Proof.
  intros.
  eapply sideRLs_trans.
  2: apply H0.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  esx.
Qed.

Lemma hRLx_0100 h r r' r0:
  sideRLs tm (hRLx++[]) r r0 ->
  sideRLs tm h (rd0*>r0) r' ->
  sideRLs tm (hRLx++h) ([0;1;0;0]*>r) r'.
Proof.
  intros.
  eapply sideRLs_trans.
  2: apply H0.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  esx.
Qed.

Lemma hRL_1100 n r r':
  sideRLs tm (hRLx++hRL^^n) r r' ->
  sideRLs tm (hRL^^(n+1)) ([1;1;0;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  change r' with ([]*>r').
  eapply @segRLs_sideRLs_concat.
  2: apply H.
  eapply segRLs_trans.
  1: esx.
  eapply segRLs_nil.
Qed.

Lemma hRL_0100 n r r':
  sideRLs tm (hRL^^n) ([1;1;0;0]*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;1;0;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Ltac rw_0 :=
  repeat (
  rewrite rw_0_rd0 ||
  rewrite rw_0_rd1 ||
  rewrite rw_0_01s ||
  rewrite rw_0_0inf);
  cbn[Nat.add]; cbn[lpow];
  repeat rewrite Str_app_assoc;
  repeat rewrite Str_app_nil.


Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- ?G => idtac G
  end;
  match goal with
  | |- sideRLs _ [] _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ (_^^O) _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ (hRLx++_) (rd0*>_) _ =>
    eapply hRLx_d0; [sscs|]
  | |- sideRLs _ (hRLx++_) ([0;1;0;0]*>_) _ =>
    eapply hRLx_0100; [sscs|]
  | |- sideRLs _ _ ([0;1;0;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_0100
  | |- sideRLs _ _ ([1;1;0;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_1100
  | |- sideRLs _ _ (rd0*>_) _ =>
    (R_m2a1; ssc segRLs_d0_d1) ||
    (R_m2; ssc segRLs_d0_d0)
  | |- sideRLs _ _ (rd1*>_) _ =>
    (R_m2a1; ssc segRLs_d1_d0) ||
    (R_m2; ssc segRLs_d1_d1)
  end; simpl_nat);
  match goal with
  | |- ?G => idtac "fail"; idtac G
  end.

Lemma hRLx_01 n r r':
  sideRLs tm (hRLx++hRL^^n) r r' ->
  sideRLs tm (hRLx++hRL^^(((n+1)*2+1)*2)) (rd0 *> [0;1;0;0] *> r) (rd0*>rd1*>r').
Proof.
  intros.
  sscs.
  applys_eq H; flia.
Qed.

Lemma hRLx_01s k n r r':
  2<=k ->
  sideRLs tm (hRLx++hRL^^(k-2)) r r' ->
  sideRLs tm (hRLx++hRL^^(k*2^(n*2)-2)) ((rd0++[0;1;0;0])^^n*>r) ((rd0++rd1)^^n*>r').
Proof.
  intros.
  induction n.
  - applys_eq H0; flia.
  - cbn[lpow].
    repeat rewrite Str_app_assoc.
    apply hRLx_01 in IHn.
    replace (S n*2) with (n*2+2) by lia.
    rw_pa.
    applys_eq IHn; flia.
Qed.

Inductive RC: nat->side->Prop :=
| RC_4:
    RC 4
  (rd1*>rd0*>rd0*>rd1*>rd0*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>0inf)
| RC_5:
    RC 5
  (rd1*>rd0*>rd0*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>0inf)
| RC_6:
    RC 6
  (rd1*>rd0*>rd0*>rd0*>rd0*>rd1*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>0inf)
| RC_7:
    RC 7
  (rd1*>rd0*>rd0*>rd0*>rd0*>rd0*>rd0*>rd1*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd1*>0inf)
| RC_8 n:
    RC (n*2+8)
  (rd1*>rd0*>rd0*>rd0*>rd0*>rd0*>rd1*>(rd0++rd1)^^n*>rd1*>rd1*>(rd0++rd1)^^(5+n)*>0inf)
| RC_9 n:
    RC (n*2+9)
  (rd1*>rd0*>rd0*>rd0*>rd0*>rd0*>rd1*>(rd0++rd1)^^n*>rd0*>rd0*>rd1*>rd1*>(rd0++rd1)^^(5+n)*>0inf)
.

Ltac sscs' := rw_0; sscs; solve_sideRLs.

Lemma RC_Incs n r r':
  RC n r ->
  RC (S n) r' ->
  sideRLs tm (hRL^^((2^(n+5)+1)*2^(n+0)+0)) ([0]*>r) (rd0*>r').
Proof.
  intros I1 I2.
  inverts I1; inverts I2; try lia.
  - sscs'.
  - sscs'.
  - sscs'.
  - replace n with O by lia.
    sscs'.
  - replace n0 with n in * by lia.
    rw_0.
    eapply sideRLs_feq2; [|shelve].
    repeat rewrite Nat.mul_succ_l.
    sscs.
    replace ((2 ^ (n * 2 + 13) + 1) * 2 ^ (n * 2 + 2) - 2) with
      ((2 ^ (n * 2 + 15) + 4) * 2 ^ (n * 2) - 2) by lia'.
    eapply hRLx_01s; [lia|].
    sscs.
    replace (2 ^ (n * 2 + 3) - 2) with (8 * 2 ^ (n * 2) - 2) by lia'.
    eapply hRLx_01s; [lia|].
    solve_sideRLs.
  - replace n with (S n0) in * by lia.
    clear n.
    rename n0 into n.
    rw_0.
    eapply sideRLs_feq2; [|shelve].
    repeat rewrite Nat.mul_succ_l.
    sscs.
    replace ((2 ^ (n * 2 + 14) + 1) * 2 ^ (n * 2 + 3) - 2) with
      ((2 ^ (n * 2 + 17) + 8) * 2 ^ (n * 2) - 2) by lia'.
    eapply hRLx_01s; [lia|].
    sscs.
    replace (2 ^ (n * 2 + 3) - 2) with (8 * 2 ^ (n * 2) - 2) by lia'.
    eapply hRLx_01s; [lia|].
    solve_sideRLs.
    Unshelve.
    all: st; simpl_rotate; reflexivity.
Qed.

Definition S0 '(n,r) := LC1 (n+2) n <| rd0 *> r.

Lemma BigStep' n r r':
  RC n r ->
  RC (S n) r' ->
  S0 (n,r) -->+
  S0 (S n,r').
Proof.
  intros.
  epose proof (RC_Incs _ _ _ H H0) as I1.
  unfold S0.
  cbn[Str_app].
  follow LC1_Ov.
  epose proof (sideRLs_concat (LC_Incs' (n+2) n)) as I2.
  rewrite lrcons_lpow1 in I2 by lia.
  rewrite <-(Nat.add_1_r n).
  replace (n+1+2) with (n+2+1) by lia.
  eapply I2.
  applys_eq I1.
  rw_pa; flia.
Qed.

Lemma RC_S n r:
  RC n r ->
  exists r', RC (S n) r'.
Proof.
  intros.
  inverts H; eexists; try solve[econstructor].
  - eapply (RC_8 O).
  - applys_eq (RC_9 n0); flia.
  - applys_eq (RC_8 (S n0)); flia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  epose proof (RC_4) as I1.
  match goal with
  | [I1:RC _ ?r|-_] =>
    eapply multistep_nonhalt with (c':=S0 (4,r))
  end.
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(n,r) => RC n r).
  2: apply I1.
  intros [n r] HRC.
  epose proof HRC as HRC'.
  eapply RC_S in HRC'.
  destruct HRC' as [r' I2].
  eexists; split.
  1: apply BigStep'; try eassumption.
  apply I2.
Qed.

End TM8.


