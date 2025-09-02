From BusyCoq Require Import Individual33.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require ES_v2.
From BusyCoq Require Import Longitudinal BinaryCounter_v2 SimplPow2.

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

Definition tm := Eval compute in (TM_from_str "1LB2LB1RC_1RA2LB0LB_2RB---0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation ld := [2;2].
Notation rd0 := [2;0;2].
Notation rd1 := [2;0;0].
Notation lh := (0inf<*<[1]).

Notation hR := (A,[]).
Notation hL := (B,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma LOv r:
  lh {{{ (hL,L) }}} r -->*
  lh {{{ (hR,R) }}} [2] *> r.
Proof. es. Qed.

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

Lemma rw_2_ld r:
  [2] *> ld *> r = ld *> [2] *> r.
Proof. reflexivity. Qed.

Lemma rw_2_rd0 r:
  [2] *> rd0 *> r = ld *> [0;2] *> r.
Proof. reflexivity. Qed.

Lemma rw_2_rd1 r:
  [2] *> rd1 *> r = ld *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_ld r:
  [0;0] *> ld *> r = [0;0;2] *> [2] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd0 r:
  [0;0] *> rd0 *> r = [0;0;2] *> [0;2] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd1 r:
  [0;0] *> rd1 *> r = [0;0;2] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_2_lds n r:
  [2] *> ld^^n *> r = ld^^n *> [2] *> r.
Proof.
  simpl_rotate; reflexivity.
Qed.

Ltac rw_0 :=
  let h_0 := fresh "h" in
  match goal with
  | |- sideRLs _ ?h _ _ =>
    remember h as h_0
  end;
  cbn[Nat.add]; cbn[lpow];
  repeat rewrite Str_app_assoc;
  repeat rewrite Str_app_nil;
  subst h_0;
  repeat (
  rewrite rw_2_ld ||
  rewrite rw_2_rd0 ||
  rewrite rw_2_rd1 ||
  rewrite rw_2_lds ||
  rewrite rw_00_ld ||
  rewrite rw_00_rd0 ||
  rewrite rw_00_rd1).

Ltac ss := solve_segRLs.

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

Lemma segRLs_ld n:
  segRLs tm (hRL^^(n)) (hRL^^(n*2)) ld ld.
Proof.
  applys_eq (segRLs_addmul_v2 1 2 0 0 n); flia; ss.
Qed.

Lemma sideRLs_lds n i r r':
  sideRLs tm (hRL^^(2^(i+n)+0)) r r' ->
  sideRLs tm (hRL^^(2^n+0)) (ld^^i*>r) (ld^^i*>r').
Proof.
  gen n.
  induction i; intros.
  - apply H.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    1: apply segRLs_ld.
    specialize (IHi (S n)).
    applys_eq IHi.
    1: cbn[Nat.pow]; flia.
    applys_eq H; flia.
Qed.

Lemma hRL_02 n r r':
  sideRLs tm (hRL^^n) (ld*>r) r' ->
  sideRLs tm (hRL^^(n+2)) ([0;2]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  solve_sideRLs.
Qed.

Lemma hRL_002 n r r':
  sideRLs tm (hRL^^n) (rd0*>r) r' ->
  sideRLs tm (hRL^^(n+2)) ([0;0;2]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  solve_sideRLs.
Qed.

Lemma sideRLs_010s n:
  sideRLs tm (hRL^^(2^(n*3+4))) ((rd0++rd1++rd0)^^n*>[1]*>0inf) ((rd0++rd1++rd0)^^n*>rd0*>rd1*>rd0*>[1]*>0inf).
Proof.
  induction n.
  1: solve_sideRLs.
  cbn[lpow].
  do 2 rewrite (Str_app_assoc (rd0++rd1++rd0)).
  eapply segRLs_sideRLs_concat.
  2: apply IHn.
  replace (S n*3) with (n*3+3) by lia.
  applys_eq (segRLs_addmul_v2 8 1 0 0 (2^(n*3+4))); rw_pa; flia; ss.
Qed.

Lemma sideRLs_010s_v1 n:
  sideRLs tm (hRL^^(2^(n*60+4)+0)) ((rd0++rd1++rd0)^^(n*20)*>[1]*>0inf) ((rd0++rd1++rd0)^^(n*20)*>rd0*>rd1*>rd0*>[1]*>0inf).
Proof.
  rewrite Nat.add_0_r.
  applys_eq (sideRLs_010s (n*20)); flia.
Qed.

Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- sideRLs _ (_^^O) _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ _ ([0;2]*>_) _ =>
    R_sub 2%nat; eapply hRL_02
  | |- sideRLs _ _ ([0;0;2]*>_) _ =>
    R_sub 2%nat; eapply hRL_002
  | |- sideRLs _ _ (ld*>_) _ =>
    ssc segRLs_ld
  | |- sideRLs _ _ (ld^^_*>_) _ =>
    eapply sideRLs_lds
  | |- sideRLs _ _ (_^^_*>_) _ =>
    eapply sideRLs_010s_v1
  | |- sideRLs _ _ (rd0*>_) _ =>
    (R_m2a1; ssc segRLs_d0_d1) ||
    (R_m2; ssc segRLs_d0_d0)
  | |- sideRLs _ _ (rd1*>_) _ =>
    (R_m2a1; ssc segRLs_d1_d0) ||
    (R_m2; ssc segRLs_d1_d1)
  end; simpl_nat).

Definition RC i n :=
match i with
| 0%nat => (ld)^^(17+n*60)*>rd0*>ld*>rd1*>rd0*>rd0*>rd0*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(3+n*20)*>[1]*>0inf
| 1%nat => (ld)^^(20+n*60)*>rd1*>rd0*>rd0*>rd1*>rd0*>rd0*>rd0*>(rd0++rd1++rd0)^^(4+n*20)*>[1]*>0inf
| 2%nat => (ld)^^(21+n*60)*>rd0*>ld*>rd0*>rd0*>rd1*>rd1*>rd1*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(4+n*20)*>[1]*>0inf
| 3 => (ld)^^(24+n*60)*>rd0*>rd0*>rd1*>rd0*>rd1*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(5+n*20)*>[1]*>0inf
| 4 => (ld)^^(26+n*60)*>rd0*>rd1*>rd1*>rd0*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(6+n*20)*>[1]*>0inf
| 5 => (ld)^^(28+n*60)*>rd1*>rd1*>rd1*>rd0*>rd0*>rd0*>(rd0++rd1++rd0)^^(7+n*20)*>[1]*>0inf
| 6 => (ld)^^(29+n*60)*>rd0*>rd1*>rd0*>ld*>rd0*>rd0*>rd0*>rd0*>rd0*>(rd0++rd1++rd0)^^(7+n*20)*>[1]*>0inf
| 7 => (ld)^^(31+n*60)*>rd1*>rd0*>ld*>rd0*>rd1*>rd1*>rd1*>rd1*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(7+n*20)*>[1]*>0inf
| 8 => (ld)^^(32+n*60)*>rd0*>ld*>ld*>rd0*>rd1*>rd0*>rd0*>rd1*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(8+n*20)*>[1]*>0inf
| 9 => (ld)^^(36+n*60)*>rd0*>rd1*>rd0*>rd0*>rd0*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(9+n*20)*>[1]*>0inf
| 10 => (ld)^^(38+n*60)*>rd1*>rd0*>rd1*>rd1*>rd0*>rd0*>rd0*>(rd0++rd1++rd0)^^(10+n*20)*>[1]*>0inf
| 11 => (ld)^^(39+n*60)*>rd0*>ld*>rd1*>rd0*>rd1*>rd1*>rd1*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(10+n*20)*>[1]*>0inf
| 12 => (ld)^^(42+n*60)*>rd1*>rd0*>rd1*>rd0*>rd1*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(11+n*20)*>[1]*>0inf
| 13 => (ld)^^(43+n*60)*>rd0*>ld*>rd1*>rd1*>rd1*>rd0*>rd0*>rd0*>(rd0++rd1++rd0)^^(12+n*20)*>[1]*>0inf
| 14 => (ld)^^(46+n*60)*>rd1*>rd1*>rd1*>rd1*>rd1*>rd1*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(12+n*20)*>[1]*>0inf
| 15 => (ld)^^(47+n*60)*>rd0*>rd1*>rd0*>rd0*>rd0*>rd0*>rd0*>ld*>rd0*>rd0*>rd1*>rd1*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(11+n*20)*>[1]*>0inf
| 16 => (ld)^^(49+n*60)*>rd1*>rd0*>rd1*>rd1*>rd1*>rd1*>ld*>rd0*>rd1*>rd0*>rd1*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(12+n*20)*>[1]*>0inf
| 17 => (ld)^^(50+n*60)*>rd0*>ld*>rd1*>rd0*>rd0*>rd1*>ld*>rd0*>rd1*>rd0*>rd1*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(13+n*20)*>[1]*>0inf
| 18 => (ld)^^(53+n*60)*>rd1*>rd0*>rd0*>rd0*>ld*>rd0*>rd1*>rd0*>rd1*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(14+n*20)*>[1]*>0inf
| 19 => (ld)^^(54+n*60)*>rd0*>ld*>rd0*>rd1*>ld*>rd0*>rd1*>rd1*>rd0*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(15+n*20)*>[1]*>0inf
| 20 => (ld)^^(57+n*60)*>rd0*>rd1*>ld*>rd0*>rd1*>rd0*>rd0*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(16+n*20)*>[1]*>0inf
| 21 => (ld)^^(59+n*60)*>rd1*>ld*>rd0*>rd1*>rd1*>rd1*>rd0*>rd0*>rd0*>(rd0++rd1++rd0)^^(17+n*20)*>[1]*>0inf
| 22 => (ld)^^(60+n*60)*>rd0*>ld*>ld*>rd1*>rd1*>rd1*>rd1*>rd1*>rd1*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(17+n*20)*>[1]*>0inf
| 23 => (ld)^^(64+n*60)*>rd1*>rd1*>rd1*>rd1*>rd0*>rd1*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(18+n*20)*>[1]*>0inf
| 24 => (ld)^^(65+n*60)*>rd0*>rd1*>rd0*>rd0*>ld*>rd1*>rd1*>rd0*>rd1*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(18+n*20)*>[1]*>0inf
| 25 => (ld)^^(67+n*60)*>rd1*>rd0*>rd1*>ld*>rd1*>rd0*>rd0*>rd1*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(19+n*20)*>[1]*>0inf
| 26 => (ld)^^(68+n*60)*>rd0*>ld*>rd1*>ld*>rd1*>rd1*>rd0*>rd0*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(20+n*20)*>[1]*>0inf
| 27 => (ld)^^(71+n*60)*>rd1*>ld*>rd1*>rd1*>rd0*>rd1*>rd0*>rd0*>rd0*>(rd0++rd1++rd0)^^(21+n*20)*>[1]*>0inf
| 28 => (ld)^^(72+n*60)*>rd0*>ld*>rd0*>rd0*>ld*>rd1*>rd0*>rd0*>rd1*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(21+n*20)*>[1]*>0inf
| 29 => (ld)^^(75+n*60)*>rd0*>rd0*>ld*>rd1*>rd0*>rd1*>rd0*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(22+n*20)*>[1]*>0inf
| 30 => (ld)^^(77+n*60)*>rd0*>ld*>rd1*>rd0*>rd0*>rd0*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(23+n*20)*>[1]*>0inf
| _ => 0inf
end.

Ltac sscs' :=
  unshelve (
  eapply sideRLs_feq2; [|shelve];
  rw_0;
  sscs;
  solve_sideRLs);
  simpl_tape; simpl_rotate; reflexivity.

Lemma RC_Incs i n:
  i<30 ->
  sideRLs tm (hRL^^(2^0+0)) ([2]*>RC i n) (RC (S i) n).
Proof.
  intro Hn.
  unfold RC.
  time (do 6 (destruct i; [solve[sscs']|])).
  time (do 6 (destruct i; [solve[sscs']|])).
  time (do 6 (destruct i; [solve[sscs']|])).
  time (do 6 (destruct i; [solve[sscs']|])).
  time (do 6 (destruct i; [solve[sscs']|])).
  lia.
Time Qed.

Definition RC0 n :=
match n with
| 0%nat => (ld)^^(4)*>rd0*>rd0*>rd0*>(rd0++rd1++rd0)^^(0)*>[1]*>0inf
| 1%nat => (ld)^^(6)*>rd0*>rd0*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(0)*>[1]*>0inf
| 2%nat => (ld)^^(8)*>rd0*>rd1*>rd1*>rd1*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(0)*>[1]*>0inf
| 3 => (ld)^^(10)*>rd1*>rd1*>rd0*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(1)*>[1]*>0inf
| 4 => (ld)^^(11)*>rd0*>rd1*>ld*>rd1*>rd0*>rd0*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(1)*>[1]*>0inf
| 5 => (ld)^^(13)*>rd1*>ld*>rd1*>rd0*>rd1*>rd0*>rd0*>rd0*>(rd0++rd1++rd0)^^(2)*>[1]*>0inf
| 6 => (ld)^^(14)*>rd0*>ld*>rd0*>ld*>rd1*>rd0*>rd0*>rd1*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(2)*>[1]*>0inf
| 7 => (ld)^^(17)*>rd0*>ld*>rd1*>rd0*>rd0*>rd0*>rd1*>rd0*>rd0*>(rd0++rd1++rd0)^^(3)*>[1]*>0inf
| _ => 0inf
end.

Lemma RC0_Incs i:
  i<7 ->
  sideRLs tm (hRL^^(2^0+0)) ([2]*>RC0 i) (RC0 (S i)).
Proof.
  intro Hn.
  unfold RC0.
  time (do 7 (destruct i; [solve[sscs']|])).
  lia.
Time Qed.

Lemma RC_eq n:
  RC 30 n = RC 0 (S n).
Proof.
  unfold RC.
  st; simpl_rotate; reflexivity.
Qed.

Lemma RC0_eq:
  RC0 7 = RC 0 0.
Proof.
  unfold RC0,RC.
  st; simpl_rotate; reflexivity.
Qed.

Definition S1 i := lh {{{ (hL,L) }}} RC0 i.
Definition S0 '(i,n) := lh {{{ (hL,L) }}} RC i n.

Lemma BigStep i n:
  i<30 ->
  S0 (i,n) -->+
  S0 (S i,n).
Proof.
  intros Hi.
  unfold S0.
  follow LOv.
  epose proof (@sideRLs_concat tm hR hL [] lh lh _ _) as I1.
  cbn in I1.
  unshelve epose proof (I1 _ (RC_Incs i n Hi)) as I1.
  1: constructor.
  apply I1.
Qed.

Lemma BigStep0 i:
  i<7 ->
  S1 i -->*
  S1 (S i).
Proof.
  intros Hi.
  unfold S0.
  follow LOv.
  epose proof (@sideRLs_concat tm hR hL [] lh lh _ _) as I1.
  cbn in I1.
  unshelve epose proof (I1 _ (RC0_Incs i Hi)) as I1.
  1: constructor.
  apply progress_evstep.
  apply I1.
Qed.

Lemma init i:
  i<=7 ->
  c0 -->* S1 i.
Proof.
  induction i; intros.
  1: es.
  follow IHi. 1: lia.
  apply BigStep0; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (O,O)).
  1: follow (init 7); unfold S1,S0; rewrite RC0_eq; finish.
  eapply progress_nonhalt_cond with (P:=fun '(i,n) => i<30).
  2: lia.
  intros [i n] Hi.
  assert (i<29\/i=29) as [E|E] by lia.
  - exists (S i,n); split.
    1: apply BigStep,Hi.
    lia.
  - eexists (O,S n); split; [|lia].
    follow10 (BigStep i n Hi).
    unfold S0.
    rewrite <-RC_eq.
    finish.
Qed.

End TM1.

