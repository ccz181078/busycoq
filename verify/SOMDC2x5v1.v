From BusyCoq Require Import Individual25.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String List.
From BusyCoq Require Import Longitudinal SimplPow2.



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

Ltac ssc H := eapply segRLs_sideRLs_concat; [apply H | ].




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

Ltac flia := unfold DH0; repeat (lia || f_equal).


Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB3RA4LB2RA2RB_2LA---3LA0LB1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation hL := (B,[0]).
Notation hR := (B,[1]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Lemma LOv1 r:
  0inf <* <[2;2] {{{ (hL,L) }}} r -->*
  0inf <* <[3;2] {{{ (hR,R) }}} [4;3;0] *> [0] *> r.
Proof.
  es.
Qed.

Lemma LOv0 r:
  0inf <* <[3;2] {{{ (hL,L) }}} r -->*
  0inf <* <[2;2] {{{ (hR,R) }}} r.
Proof.
  es.
Qed.

Notation "'ld'" := [4;3;0].
Notation "'d0'" := [0;0].
Notation "'d1'" := [4;0].

Ltac ss := solve_segRLs.

Lemma segRLs_043s n:
  segRLs tm (hRL^^2) (hRL^^(2^n+3)) (ld ++ [0;4;3]^^n) (ld^^(1+n)).
Proof.
  rewrite (lpow_add _ 1 n).
  eapply @segRLs_concat with (ls2:=hRL^^4).
  1: ss.
  induction n.
  1: ss.
  rewrite <-(Nat.add_1_r n).
  do 2 rewrite (lpow_add _ n).
  eapply segRLs_concat.
  1: apply IHn.
  rewrite Nat.pow_add_r.
  applys_eq (segRLs_addmul_v2 1 2 2 1 (2^n+1)); flia; ss.
Qed.

Lemma rw_0_430s n r:
  ld *> [0] *> ld^^n *> r =
  (ld ++ [0;4;3]^^n) *> [0] *> r.
Proof.
  simpl_rotate; reflexivity.
Qed.

Lemma sideRLs_043s n c1 c2 r r':
  c1<c2 ->
  sideRLs tm (hRL^^(2^(n+c1)+3)) r (ld^^(c2-c1-1)*>r') ->
  sideRLs tm (hRL^^2) ((ld++[0;4;3]^^(n+c1)) *> r) (ld^^(n+c2) *> r').
Proof.
  intros.
  replace (n+c2) with (1+(n+c1)+(c2-c1-1)) by lia.
  rewrite <-(lpow_add' _ (1+(n+c1))).
  eapply segRLs_sideRLs_concat.
  1: apply segRLs_043s.
  apply H0.
Qed.

Lemma rw_0_00 r:
  [0] *> d0 *> r = d0 *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_40 r:
  [0] *> d1 *> r = [0;4;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_430 r:
  [0] *> ld *> r = [0;4;3] *> [0] *> r.
Proof. reflexivity. Qed.

Lemma segRLs_040 n:
  segRLs tm (hRL^^(n+6)) (hRL^^(n*2+1)) [0;4;0] ld.
Proof.
  applys_eq (segRLs_addmul_v2 1 2 6 1 n); flia; ss.
Qed.

Lemma segRLs_043 n:
  segRLs tm (hRL^^(n+2)) (hRL^^(n*2+1)) [0;4;3] ld.
Proof.
  applys_eq (segRLs_addmul_v2 1 2 2 1 n); flia; ss.
Qed.

Lemma segRLs_d1_d0 n:
  segRLs tm (hRL^^(n*2+1)) (hRL^^(n+1)) d1 d0.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 1 1 n); flia; ss.
Qed.

Lemma segRLs_d1_d1 n:
  segRLs tm (hRL^^(n*2)) (hRL^^(n)) d1 d1.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 0 0 n); flia; ss.
Qed.

Lemma segRLs_d0_d0 n:
  segRLs tm (hRL^^(n*2)) (hRL^^(n)) d0 d0.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 0 0 n); flia; ss.
Qed.

Lemma segRLs_d0_d1 n:
  segRLs tm (hRL^^(n*2+1)) (hRL^^(n)) d0 d1.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 1 0 n); flia; ss.
Qed.

Lemma segRLs_ld n:
  segRLs tm (hRL^^(n)) (hRL^^(n*2)) ld ld.
Proof.
  applys_eq (segRLs_addmul_v2 1 2 0 0 n); flia; ss.
Qed.

Ltac rw_0 :=
  repeat (
  rewrite rw_0_00 ||
  rewrite rw_0_40 ||
  rewrite rw_0_430 ||
  rewrite rw_0_430s).




Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- sideRLs _ _ (d0*>_) (d1*>_) =>
    R_m2a1; ssc segRLs_d0_d1
  | |- sideRLs _ _ (d0*>_) (d0*>_) =>
    R_m2; ssc segRLs_d0_d0
  | |- sideRLs _ _ (d1*>_) (d0*>_) =>
    R_m2a1; ssc segRLs_d1_d0
  | |- sideRLs _ _ (d1*>_) (d1*>_) =>
    R_m2; ssc segRLs_d1_d1
  | |- sideRLs _ _ (ld*>_) (ld*>_) =>
    ssc segRLs_ld
  | |- sideRLs _ _ ([0;4;0]*>_) _ =>
    R_sub 6; ssc segRLs_040
  | |- sideRLs _ _ ([0;4;3]*>_) _ =>
    R_sub 2%nat; ssc segRLs_043
  end; simpl_nat).

Definition RC i n :=
match i with
| 0%nat => ld^^(n*24+5) *> d1*>d1*>d0*>d0*>d0*> (d0++d0++d1)^^(n*8+0) *> 0inf
| 1%nat => ld^^(n*24+7) *> d0*>d0*>d1*>d1*>d1*>d1*>d0*> (d0++d0++d1)^^(n*8+0) *> 0inf
| 2%nat => ld^^(n*24+8) *> d1*>d1*>ld*>d0*>d0*>d1*>d1*>d1*>d1*>d0*> (d0++d0++d1)^^(n*8+0) *> 0inf
| 3%nat => ld^^(n*24+10) *> d0*>ld*>d0*>d0*>d0*>d1*>d1*>d1*>d0*> (d0++d0++d1)^^(n*8+1) *> 0inf
| 4%nat => ld^^(n*24+11) *> d1*>ld*>d1*>d1*>d1*>ld*>d0*>d1*>d1*>d0*>d1*>d0*> (d0++d0++d1)^^(n*8+1) *> 0inf
| 5 => ld^^(n*24+14) *> d1*>d0*>d1*>ld*>d0*>d0*>d1*>d0*>d1*>d0*> (d0++d0++d1)^^(n*8+2) *> 0inf
| 6 => ld^^(n*24+16) *> d1*>d0*>ld*>d0*>d1*>d0*>d0*>d1*>d0*> (d0++d0++d1)^^(n*8+3) *> 0inf
| 7 => ld^^(n*24+18) *> d1*>ld*>d0*>d0*>d1*>d1*>d0*>d0*> (d0++d0++d1)^^(n*8+4) *> 0inf
| 8 => ld^^(n*24+21) *> d0*>d1*>d0*>d0*>d0*>d0*> (d0++d0++d1)^^(n*8+5) *> 0inf
| 9 => ld^^(n*24+22) *> d1*>ld*>d1*>d1*>d1*>d0*>d1*>d1*>d0*> (d0++d0++d1)^^(n*8+5) *> 0inf
| 10 => ld^^(n*24+25) *> d1*>d0*>d1*>d1*>d0*>d1*>d0*> (d0++d0++d1)^^(n*8+6) *> 0inf
| 11 => ld^^(n*24+27) *> d1*>d0*>d0*>d0*>d1*>d0*> (d0++d0++d1)^^(n*8+7) *> 0inf
| 12 => ld^^(n*24+29) *> d1*>d1*>d0*>d0*>d0*> (d0++d0++d1)^^(n*8+8) *> 0inf
| _ => 0inf
end.

Ltac flia' := rw_pa; flia.

Lemma sideRLs_001s n:
  sideRLs tm (hRL^^(2^(n*3+2))) ((d0++d0++d1)^^n *> 0inf) ((d0++d0++d1)^^(n+1) *> 0inf).
Proof.
  induction n.
  - solve_sideRLs.
  - eapply @segRLs_sideRLs_concat with (w1:=d0++d0++d1) (w2:=d0++d0++d1).
    2: apply IHn.
    replace (S n*3+2) with (n*3+5) by lia.
    applys_eq (segRLs_addmul_v2 8 1 0 0 (2^(n*3+2))); flia'; ss.
Qed.

Lemma sideRLs_001s_neg1 n:
  sideRLs tm (hRL^^(2^(n*3+2)-1)) ((d0++d0++d1)^^n *> 0inf) (d1*>d1*>d0*>(d0++d0++d1)^^n *> 0inf).
Proof.
  destruct n.
  - solve_sideRLs.
  - replace (S n*3+2) with (n*3+5) by lia.
    cbn[lpow].
    repeat rewrite Str_app_assoc.
    sscs.
    applys_eq (sideRLs_001s n).
    1: flia.
    st; simpl_rotate; reflexivity.
Qed.

Lemma sideRLs_001s_neg2 n:
  sideRLs tm (hRL^^(2^(n*3+2)-2)) ((d0++d0++d1)^^n *> 0inf) (d0*>d1*>d0*>(d0++d0++d1)^^n *> 0inf).
Proof.
  destruct n.
  - solve_sideRLs.
  - replace (S n*3+2) with (n*3+5) by lia.
    cbn[lpow].
    repeat rewrite Str_app_assoc.
    sscs.
    applys_eq (sideRLs_001s n).
    1: flia.
    st; simpl_rotate; reflexivity.
Qed.

Lemma sideRLs_001s' n c1:
  sideRLs tm (hRL^^(2^(n*24+(c1*3+2))+0)) ((d0++d0++d1)^^(n*8+c1) *> 0inf) ((d0++d0++d1)^^(n*8+(S c1)) *> 0inf).
Proof.
  rewrite Nat.add_0_r.
  applys_eq (sideRLs_001s (n*8+c1)); flia.
Qed.

Lemma sideRLs_001s'_neg1 n c1:
  sideRLs tm (hRL^^(2^(n*24+(c1*3+2))-1)) ((d0++d0++d1)^^(n*8+c1) *> 0inf) (d1*>d1*>d0*>(d0++d0++d1)^^(n*8+c1) *> 0inf).
Proof.
  applys_eq (sideRLs_001s_neg1 (n*8+c1)); flia.
Qed.

Lemma sideRLs_001s'_neg2 n c1:
  sideRLs tm (hRL^^(2^(n*24+(c1*3+2))-2)) ((d0++d0++d1)^^(n*8+c1) *> 0inf) (d0*>d1*>d0*>(d0++d0++d1)^^(n*8+c1) *> 0inf).
Proof.
  applys_eq (sideRLs_001s_neg2 (n*8+c1)); flia.
Qed.

Lemma nil_Str_app (r:side):
  [] *> r = r.
Proof. reflexivity. Qed.

Ltac solve_RInc :=
  cbn[RC];
  rw_0;
  eapply sideRLs_043s; [lia|];
  cbn[Nat.sub]; cbn[lpow];
  repeat rewrite Str_app_assoc;
  repeat rewrite nil_Str_app;
  sscs;
  solve
  [ applys_eq sideRLs_001s'; flia
  | applys_eq sideRLs_001s'_neg1; flia
  | applys_eq sideRLs_001s'_neg2; flia
  ].

Lemma RIncs i n:
  i<12 ->
  sideRLs tm (hRL^^2) (ld *> [0] *> RC i n) (RC (S i) n).
Proof.
  intros Hi.
  do 12 (destruct i; [solve_RInc|]).
  lia.
Qed.

Lemma LIncs:
  sideRLs tm' (hLR) (0inf<*<[3;2]) (0inf<*<[2;2]).
Proof.
  solve_sideRLs.
Qed.

Definition S0 '(i,n) :=
  0inf <* <[3;2] {{{ (hR,R) }}} ld *> [0] *> RC i n.

Lemma BigStep i n:
  i<12 ->
  S0 (i,n) -->+ S0 (S i,n).
Proof.
  intros Hi.
  unfold S0.
  follow10 (sideRLs_concat LIncs (RIncs i n Hi)).
  apply LOv1.
Qed.

Lemma S0_eq n:
  S0 (12,n) = S0 (O,S n).
Proof.
  unfold S0.
  cbn[RC].
  flia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (0,0)%nat).
  1: cbn; step1s.
  eapply progress_nonhalt_cond with (P:=fun '(i,n) => i<12).
  2: lia.
  intros [i n] Hi.
  assert (i<11\/i=11) as [E|E] by lia.
  - eexists (_,_); split.
    1: apply BigStep; lia.
    lia.
  - eexists (O,S n); split.
    1: rewrite <-S0_eq; subst; apply BigStep; lia.
    lia.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1LB3LB---0LA2LB_2RA4LA3RB1RB1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation "'1'" := S2.
Notation "'2'" := S1.

Notation hL := (A,[0]).
Notation hR := (A,[1]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Lemma LOv1 r:
  0inf <* <[2;2] {{{ (hL,L) }}} r -->*
  0inf <* <[3;2] {{{ (hR,R) }}} [4;3;0] *> [0] *> r.
Proof.
  es.
Qed.

Lemma LOv0 r:
  0inf <* <[3;2] {{{ (hL,L) }}} r -->*
  0inf <* <[2;2] {{{ (hR,R) }}} r.
Proof.
  es.
Qed.

Notation "'ld'" := [4;3;0].
Notation "'d0'" := [0;0].
Notation "'d1'" := [4;0].

Ltac ss := solve_segRLs.

Lemma segRLs_043s n:
  segRLs tm (hRL^^2) (hRL^^(2^n+3)) (ld ++ [0;4;3]^^n) (ld^^(1+n)).
Proof.
  rewrite (lpow_add _ 1 n).
  eapply @segRLs_concat with (ls2:=hRL^^4).
  1: ss.
  induction n.
  1: ss.
  rewrite <-(Nat.add_1_r n).
  do 2 rewrite (lpow_add _ n).
  eapply segRLs_concat.
  1: apply IHn.
  rewrite Nat.pow_add_r.
  applys_eq (segRLs_addmul_v2 1 2 2 1 (2^n+1)); flia; ss.
Qed.

Lemma rw_0_430s n r:
  ld *> [0] *> ld^^n *> r =
  (ld ++ [0;4;3]^^n) *> [0] *> r.
Proof.
  simpl_rotate; reflexivity.
Qed.

Lemma sideRLs_043s n c1 c2 r r':
  c1<c2 ->
  sideRLs tm (hRL^^(2^(n+c1)+3)) r (ld^^(c2-c1-1)*>r') ->
  sideRLs tm (hRL^^2) ((ld++[0;4;3]^^(n+c1)) *> r) (ld^^(n+c2) *> r').
Proof.
  intros.
  replace (n+c2) with (1+(n+c1)+(c2-c1-1)) by lia.
  rewrite <-(lpow_add' _ (1+(n+c1))).
  eapply segRLs_sideRLs_concat.
  1: apply segRLs_043s.
  apply H0.
Qed.

Lemma rw_0_00 r:
  [0] *> d0 *> r = d0 *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_40 r:
  [0] *> d1 *> r = [0;4;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_430 r:
  [0] *> ld *> r = [0;4;3] *> [0] *> r.
Proof. reflexivity. Qed.

Lemma segRLs_040 n:
  segRLs tm (hRL^^(n+6)) (hRL^^(n*2+1)) [0;4;0] ld.
Proof.
  applys_eq (segRLs_addmul_v2 1 2 6 1 n); flia; ss.
Qed.

Lemma segRLs_043 n:
  segRLs tm (hRL^^(n+2)) (hRL^^(n*2+1)) [0;4;3] ld.
Proof.
  applys_eq (segRLs_addmul_v2 1 2 2 1 n); flia; ss.
Qed.

Lemma segRLs_d1_d0 n:
  segRLs tm (hRL^^(n*2+1)) (hRL^^(n+1)) d1 d0.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 1 1 n); flia; ss.
Qed.

Lemma segRLs_d1_d1 n:
  segRLs tm (hRL^^(n*2)) (hRL^^(n)) d1 d1.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 0 0 n); flia; ss.
Qed.

Lemma segRLs_d0_d0 n:
  segRLs tm (hRL^^(n*2)) (hRL^^(n)) d0 d0.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 0 0 n); flia; ss.
Qed.

Lemma segRLs_d0_d1 n:
  segRLs tm (hRL^^(n*2+1)) (hRL^^(n)) d0 d1.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 1 0 n); flia; ss.
Qed.

Lemma segRLs_ld n:
  segRLs tm (hRL^^(n)) (hRL^^(n*2)) ld ld.
Proof.
  applys_eq (segRLs_addmul_v2 1 2 0 0 n); flia; ss.
Qed.

Ltac rw_0 :=
  repeat (
  rewrite rw_0_00 ||
  rewrite rw_0_40 ||
  rewrite rw_0_430 ||
  rewrite rw_0_430s).




Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- sideRLs _ _ (d0*>_) (d1*>_) =>
    R_m2a1; ssc segRLs_d0_d1
  | |- sideRLs _ _ (d0*>_) (d0*>_) =>
    R_m2; ssc segRLs_d0_d0
  | |- sideRLs _ _ (d1*>_) (d0*>_) =>
    R_m2a1; ssc segRLs_d1_d0
  | |- sideRLs _ _ (d1*>_) (d1*>_) =>
    R_m2; ssc segRLs_d1_d1
  | |- sideRLs _ _ (ld*>_) (ld*>_) =>
    ssc segRLs_ld
  | |- sideRLs _ _ ([0;4;0]*>_) _ =>
    R_sub 6; ssc segRLs_040
  | |- sideRLs _ _ ([0;4;3]*>_) _ =>
    R_sub 2%nat; ssc segRLs_043
  end; simpl_nat).

Definition RC i n :=
match i with
| 0%nat => ld^^(n*24+7) *> d1*>d0*>d1*>d1*>d0*>d1*>d0*> (d0++d0++d1)^^(n*8+0) *> 0inf
| 1%nat => ld^^(n*24+9) *> d1*>d0*>d0*>d0*>d1*>d0*> (d0++d0++d1)^^(n*8+1) *> 0inf
| 2%nat => ld^^(n*24+11) *> d1*>d1*>d0*>d0*>d0*> (d0++d0++d1)^^(n*8+2) *> 0inf
| 3%nat => ld^^(n*24+13) *> d0*>d0*>d1*>d1*>d1*>d1*>d0*> (d0++d0++d1)^^(n*8+2) *> 0inf
| 4%nat => ld^^(n*24+14) *> d1*>d1*>ld*>d0*>d0*>d1*>d1*>d1*>d1*>d0*> (d0++d0++d1)^^(n*8+2) *> 0inf
| 5 => ld^^(n*24+16) *> d0*>ld*>d0*>d0*>d0*>d1*>d1*>d1*>d0*> (d0++d0++d1)^^(n*8+3) *> 0inf
| 6 => ld^^(n*24+17) *> d1*>ld*>d1*>d1*>d1*>ld*>d0*>d1*>d1*>d0*>d1*>d0*> (d0++d0++d1)^^(n*8+3) *> 0inf
| 7 => ld^^(n*24+20) *> d1*>d0*>d1*>ld*>d0*>d0*>d1*>d0*>d1*>d0*> (d0++d0++d1)^^(n*8+4) *> 0inf
| 8 => ld^^(n*24+22) *> d1*>d0*>ld*>d0*>d1*>d0*>d0*>d1*>d0*> (d0++d0++d1)^^(n*8+5) *> 0inf
| 9 => ld^^(n*24+24) *> d1*>ld*>d0*>d0*>d1*>d1*>d0*>d0*> (d0++d0++d1)^^(n*8+6) *> 0inf
| 10 => ld^^(n*24+27) *> d0*>d1*>d0*>d0*>d0*>d0*> (d0++d0++d1)^^(n*8+7) *> 0inf
| 11 => ld^^(n*24+28) *> d1*>ld*>d1*>d1*>d1*>d0*>d1*>d1*>d0*> (d0++d0++d1)^^(n*8+7) *> 0inf
| 12 => ld^^(n*24+31) *> d1*>d0*>d1*>d1*>d0*>d1*>d0*> (d0++d0++d1)^^(n*8+8) *> 0inf
| _ => 0inf
end.

Ltac flia' := rw_pa; flia.

Lemma sideRLs_001s n:
  sideRLs tm (hRL^^(2^(n*3+2))) ((d0++d0++d1)^^n *> 0inf) ((d0++d0++d1)^^(n+1) *> 0inf).
Proof.
  induction n.
  - solve_sideRLs.
  - eapply @segRLs_sideRLs_concat with (w1:=d0++d0++d1) (w2:=d0++d0++d1).
    2: apply IHn.
    replace (S n*3+2) with (n*3+5) by lia.
    applys_eq (segRLs_addmul_v2 8 1 0 0 (2^(n*3+2))); flia'; ss.
Qed.

Lemma sideRLs_001s_neg1 n:
  sideRLs tm (hRL^^(2^(n*3+2)-1)) ((d0++d0++d1)^^n *> 0inf) (d1*>d1*>d0*>(d0++d0++d1)^^n *> 0inf).
Proof.
  destruct n.
  - solve_sideRLs.
  - replace (S n*3+2) with (n*3+5) by lia.
    cbn[lpow].
    repeat rewrite Str_app_assoc.
    sscs.
    applys_eq (sideRLs_001s n).
    1: flia.
    st; simpl_rotate; reflexivity.
Qed.

Lemma sideRLs_001s_neg2 n:
  sideRLs tm (hRL^^(2^(n*3+2)-2)) ((d0++d0++d1)^^n *> 0inf) (d0*>d1*>d0*>(d0++d0++d1)^^n *> 0inf).
Proof.
  destruct n.
  - solve_sideRLs.
  - replace (S n*3+2) with (n*3+5) by lia.
    cbn[lpow].
    repeat rewrite Str_app_assoc.
    sscs.
    applys_eq (sideRLs_001s n).
    1: flia.
    st; simpl_rotate; reflexivity.
Qed.

Lemma sideRLs_001s' n c1:
  sideRLs tm (hRL^^(2^(n*24+(c1*3+2))+0)) ((d0++d0++d1)^^(n*8+c1) *> 0inf) ((d0++d0++d1)^^(n*8+(S c1)) *> 0inf).
Proof.
  rewrite Nat.add_0_r.
  applys_eq (sideRLs_001s (n*8+c1)); flia.
Qed.

Lemma sideRLs_001s'_neg1 n c1:
  sideRLs tm (hRL^^(2^(n*24+(c1*3+2))-1)) ((d0++d0++d1)^^(n*8+c1) *> 0inf) (d1*>d1*>d0*>(d0++d0++d1)^^(n*8+c1) *> 0inf).
Proof.
  applys_eq (sideRLs_001s_neg1 (n*8+c1)); flia.
Qed.

Lemma sideRLs_001s'_neg2 n c1:
  sideRLs tm (hRL^^(2^(n*24+(c1*3+2))-2)) ((d0++d0++d1)^^(n*8+c1) *> 0inf) (d0*>d1*>d0*>(d0++d0++d1)^^(n*8+c1) *> 0inf).
Proof.
  applys_eq (sideRLs_001s_neg2 (n*8+c1)); flia.
Qed.

Lemma nil_Str_app (r:side):
  [] *> r = r.
Proof. reflexivity. Qed.

Ltac solve_RInc :=
  cbn[RC];
  rw_0;
  eapply sideRLs_043s; [lia|];
  cbn[Nat.sub]; cbn[lpow];
  repeat rewrite Str_app_assoc;
  repeat rewrite nil_Str_app;
  sscs;
  solve
  [ applys_eq sideRLs_001s'; flia
  | applys_eq sideRLs_001s'_neg1; flia
  | applys_eq sideRLs_001s'_neg2; flia
  ].

Lemma RIncs i n:
  i<12 ->
  sideRLs tm (hRL^^2) (ld *> [0] *> RC i n) (RC (S i) n).
Proof.
  intros Hi.
  do 12 (destruct i; [solve_RInc|]).
  lia.
Qed.

Lemma LIncs:
  sideRLs tm' (hLR) (0inf<*<[3;2]) (0inf<*<[2;2]).
Proof.
  solve_sideRLs.
Qed.

Definition S0 '(i,n) :=
  0inf <* <[3;2] {{{ (hR,R) }}} ld *> [0] *> RC i n.

Lemma BigStep i n:
  i<12 ->
  S0 (i,n) -->+ S0 (S i,n).
Proof.
  intros Hi.
  unfold S0.
  follow10 (sideRLs_concat LIncs (RIncs i n Hi)).
  apply LOv1.
Qed.

Lemma S0_eq n:
  S0 (12,n) = S0 (O,S n).
Proof.
  unfold S0.
  cbn[RC].
  flia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (0,0)%nat).
  1: cbn; step1s.
  eapply progress_nonhalt_cond with (P:=fun '(i,n) => i<12).
  2: lia.
  intros [i n] Hi.
  assert (i<11\/i=11) as [E|E] by lia.
  - eexists (_,_); split.
    1: apply BigStep; lia.
    lia.
  - eexists (O,S n); split.
    1: rewrite <-S0_eq; subst; apply BigStep; lia.
    lia.
Qed.

End TM2.


