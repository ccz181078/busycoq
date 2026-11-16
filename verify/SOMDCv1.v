From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require ES_v2.
From BusyCoq Require Import Longitudinal SimplPow2.

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

Lemma rw_00_0inf:
  [0;0] *> 0inf = 0inf.
Proof.
  solve_const0_eq.
Qed.

Lemma rw_10_0inf:
  [1;0] *> 0inf = [1;0;0] *> 0inf.
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

Definition tm := Eval compute in (TM_from_str "1RB0LF_0RC1RF_1RD1LF_1LE0RB_0RA0LD_0LE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation ld := [1;0;1;0].
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation lh := (0inf<*<[1;0]).

Notation hR := (D,[1]).
Notation hL := (D,[0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma LOv r:
  lh {{{ (hL,L) }}} r -->*
  lh {{{ (hR,R) }}} [1;0] *> r.
Proof. esx. Qed.


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

Lemma rw_10_ld r:
  [1;0] *> ld *> r = ld *> [1;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_rd0 r:
  [1;0] *> rd0 *> r = rd1 *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_rd1 r:
  [1;0] *> rd1 *> r = ld *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_ld r:
  [0] *> ld *> r = [0;1;0] *> [1;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_rd0 r:
  [0] *> rd0 *> r = rd0 *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_rd1 r:
  [0] *> rd1 *> r = [0;1;0] *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_ld r:
  [0;0] *> ld *> r = [0;0;1;0] *> [1;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd0 r:
  [0;0] *> rd0 *> r = rd0 *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd1 r:
  [0;0] *> rd1 *> r = [0;0;1;0] *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_lds n r:
  [1;0] *> ld^^n *> r = ld^^n *> [1;0] *> r.
Proof.
  simpl_rotate; reflexivity.
Qed.

Lemma rw_0_1s n r:
  [0] *> rd1^^n *> r = [0;1;0]^^n *> [0] *> r.
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
  rewrite rw_10_ld ||
  rewrite rw_10_rd0 ||
  rewrite rw_10_rd1 ||
  rewrite rw_10_lds ||
  rewrite rw_10_0inf ||
  rewrite rw_0_ld ||
  rewrite rw_0_rd0 ||
  rewrite rw_0_rd1 ||
  rewrite rw_0_1s ||
  rewrite rw_0_0inf ||
  rewrite rw_00_ld ||
  rewrite rw_00_rd0 ||
  rewrite rw_00_rd1 ||
  rewrite rw_00_0inf).

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

Lemma hRL_110 n r r':
  sideRLs tm (hRL^^n) (rd1*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([1;1;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma hRL_010 n r r':
  sideRLs tm (hRL^^n) ([1;1;0]*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;1;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma hRL_0010 n r r':
  sideRLs tm (hRL^^n) (ld*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;0;1;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma sideRLs_010s k n r r':
  1<=k ->
  sideRLs tm (hRL^^(2^k-2)) r r' ->
  sideRLs tm (hRL^^(2^(k+n)-2)) ([0;1;0]^^n*>r) (rd1^^n*>r').
Proof.
  intros.
  rewrite (Nat.pow_le_mono_r_iff 2) in H by lia.
  induction n.
  - applys_eq H0; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    rewrite <-(Nat.add_1_r n).
    applys_eq (segRLs_addmul_v2 2 1 2 0 (2^(k+n)-2)); rw_pa; flia; ss.
Qed.

Lemma sideRLs_010s_v1 c n r r':
  1<=c ->
  sideRLs tm (hRL^^(2^(n*3+c)-2)) r r' ->
  sideRLs tm (hRL^^(2^(n*6+c)-2)) ([0;1;0]^^(n*3)*>r) (rd1^^(n*3)*>r').
Proof.
  replace (n*6+c) with (n*3+c+n*3) by lia.
  intros.
  apply sideRLs_010s; [lia|assumption].
Qed.

Lemma sideRLs_010s_v2 c n r r':
  1<=c ->
  sideRLs tm (hRL^^(2^c-2)) r r' ->
  sideRLs tm (hRL^^(2^(n*3+c)-2)) ([0;1;0]^^(n*3)*>r) (rd1^^(n*3)*>r').
Proof.
  replace (n*3+c) with (c+n*3) by lia.
  intros.
  apply sideRLs_010s; [lia|assumption].
Qed.


Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- ?G => idtac G
  end;
  match goal with
  | |- sideRLs _ (_^^O) _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ _ ([0;0;1;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_0010
  | |- sideRLs _ _ ([0;1;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_010
  | |- sideRLs _ _ ([1;1;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_110
  | |- sideRLs _ _ (ld*>_) _ =>
    ssc segRLs_ld
  | |- sideRLs _ _ (ld^^_*>_) _ =>
    eapply sideRLs_lds
  | |- sideRLs _ _ ([0;1;0]^^_*>_) _ =>
    (eapply sideRLs_010s_v1;[lia|]) ||
    (eapply sideRLs_010s_v2;[lia|])
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

Definition RC i n :=
match i with
| 0%nat => (ld)^^(11+n*6)*>rd1*>ld*>(rd1)^^(3+n*3)*>ld*>rd1*>rd0*>(rd1)^^(5+n*3)*>ld*>rd1*>rd1*>0inf
| 1%nat => (ld)^^(12+n*6)*>rd1*>ld*>(rd1)^^(3+n*3)*>ld*>rd0*>(rd1)^^(6+n*3)*>ld*>rd1*>rd1*>rd0*>rd1*>0inf
| 2 => (ld)^^(13+n*6)*>rd1*>ld*>(rd1)^^(4+n*3)*>ld*>rd1*>rd0*>(rd1)^^(4+n*3)*>ld*>rd1*>rd1*>rd1*>rd0*>rd1*>0inf
| 3 => (ld)^^(14+n*6)*>rd1*>ld*>(rd1)^^(4+n*3)*>ld*>rd0*>(rd1)^^(5+n*3)*>ld*>rd1*>rd0*>rd0*>rd0*>rd1*>rd1*>0inf
| 4 => (ld)^^(15+n*6)*>rd1*>ld*>(rd1)^^(5+n*3)*>ld*>rd1*>rd0*>(rd1)^^(3+n*3)*>ld*>rd0*>rd0*>rd1*>rd0*>rd0*>rd1*>rd1*>0inf
| 5 => (ld)^^(16+n*6)*>rd1*>ld*>(rd1)^^(5+n*3)*>ld*>rd0*>(rd1)^^(6+n*3)*>ld*>rd0*>rd0*>rd0*>rd0*>rd1*>rd1*>0inf
| 6 => (ld)^^(17+n*6)*>rd1*>ld*>(rd1)^^(6+n*3)*>ld*>rd1*>rd0*>(rd1)^^(8+n*3)*>ld*>rd1*>rd1*>0inf
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
  i<6 ->
  sideRLs tm (hRL^^(2^0+0)) ([1;0]*>RC i n) (RC (S i) n).
Proof.
  intro Hn.
  unfold RC.
  do 6
  (destruct i; [solve[sscs']|]).
  lia.
Qed.

Lemma RC_eq n:
  RC 6 n = RC 0 (S n).
Proof.
  unfold RC.
  st; simpl_rotate; reflexivity.
Qed.

Definition S0 '(i,n) := lh {{{ (hL,L) }}} RC i n.

Lemma BigStep i n:
  i<6 ->
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

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (O,O)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(i,n) => i<6).
  2: lia.
  intros [i n] Hi.
  assert (i<5\/i=5) as [E|E] by lia.
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


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB0LF_0RC1RF_1RD1LA_1LE0RB_0RA0LD_0LE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation ld := [1;0;1;0].
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation lh := (0inf<*<[1;0]).

Notation hR := (D,[1]).
Notation hL := (D,[0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma LOv r:
  lh {{{ (hL,L) }}} r -->*
  lh {{{ (hR,R) }}} [1;0] *> r.
Proof. esx. Qed.


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

Lemma rw_10_ld r:
  [1;0] *> ld *> r = ld *> [1;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_rd0 r:
  [1;0] *> rd0 *> r = rd1 *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_rd1 r:
  [1;0] *> rd1 *> r = ld *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_ld r:
  [0] *> ld *> r = [0;1;0] *> [1;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_rd0 r:
  [0] *> rd0 *> r = rd0 *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_rd1 r:
  [0] *> rd1 *> r = [0;1;0] *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_ld r:
  [0;0] *> ld *> r = [0;0;1;0] *> [1;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd0 r:
  [0;0] *> rd0 *> r = rd0 *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd1 r:
  [0;0] *> rd1 *> r = [0;0;1;0] *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_lds n r:
  [1;0] *> ld^^n *> r = ld^^n *> [1;0] *> r.
Proof.
  simpl_rotate; reflexivity.
Qed.

Lemma rw_0_1s n r:
  [0] *> rd1^^n *> r = [0;1;0]^^n *> [0] *> r.
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
  rewrite rw_10_ld ||
  rewrite rw_10_rd0 ||
  rewrite rw_10_rd1 ||
  rewrite rw_10_lds ||
  rewrite rw_10_0inf ||
  rewrite rw_0_ld ||
  rewrite rw_0_rd0 ||
  rewrite rw_0_rd1 ||
  rewrite rw_0_1s ||
  rewrite rw_0_0inf ||
  rewrite rw_00_ld ||
  rewrite rw_00_rd0 ||
  rewrite rw_00_rd1 ||
  rewrite rw_00_0inf).

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

Lemma hRL_110 n r r':
  sideRLs tm (hRL^^n) (rd1*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([1;1;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma hRL_010 n r r':
  sideRLs tm (hRL^^n) ([1;1;0]*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;1;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma hRL_0010 n r r':
  sideRLs tm (hRL^^n) (ld*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;0;1;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma sideRLs_010s k n r r':
  1<=k ->
  sideRLs tm (hRL^^(2^k-2)) r r' ->
  sideRLs tm (hRL^^(2^(k+n)-2)) ([0;1;0]^^n*>r) (rd1^^n*>r').
Proof.
  intros.
  rewrite (Nat.pow_le_mono_r_iff 2) in H by lia.
  induction n.
  - applys_eq H0; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    rewrite <-(Nat.add_1_r n).
    applys_eq (segRLs_addmul_v2 2 1 2 0 (2^(k+n)-2)); rw_pa; flia; ss.
Qed.

Lemma sideRLs_010s_v1 c n r r':
  1<=c ->
  sideRLs tm (hRL^^(2^(n*3+c)-2)) r r' ->
  sideRLs tm (hRL^^(2^(n*6+c)-2)) ([0;1;0]^^(n*3)*>r) (rd1^^(n*3)*>r').
Proof.
  replace (n*6+c) with (n*3+c+n*3) by lia.
  intros.
  apply sideRLs_010s; [lia|assumption].
Qed.

Lemma sideRLs_010s_v2 c n r r':
  1<=c ->
  sideRLs tm (hRL^^(2^c-2)) r r' ->
  sideRLs tm (hRL^^(2^(n*3+c)-2)) ([0;1;0]^^(n*3)*>r) (rd1^^(n*3)*>r').
Proof.
  replace (n*3+c) with (c+n*3) by lia.
  intros.
  apply sideRLs_010s; [lia|assumption].
Qed.


Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- ?G => idtac G
  end;
  match goal with
  | |- sideRLs _ (_^^O) _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ _ ([0;0;1;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_0010
  | |- sideRLs _ _ ([0;1;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_010
  | |- sideRLs _ _ ([1;1;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_110
  | |- sideRLs _ _ (ld*>_) _ =>
    ssc segRLs_ld
  | |- sideRLs _ _ (ld^^_*>_) _ =>
    eapply sideRLs_lds
  | |- sideRLs _ _ ([0;1;0]^^_*>_) _ =>
    (eapply sideRLs_010s_v1;[lia|]) ||
    (eapply sideRLs_010s_v2;[lia|])
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

Definition RC i n :=
match i with
| 0%nat => (ld)^^(11+n*6)*>rd1*>ld*>(rd1)^^(3+n*3)*>ld*>rd1*>rd0*>(rd1)^^(5+n*3)*>ld*>rd1*>rd1*>0inf
| 1%nat => (ld)^^(12+n*6)*>rd1*>ld*>(rd1)^^(3+n*3)*>ld*>rd0*>(rd1)^^(6+n*3)*>ld*>rd1*>rd1*>rd0*>rd1*>0inf
| 2 => (ld)^^(13+n*6)*>rd1*>ld*>(rd1)^^(4+n*3)*>ld*>rd1*>rd0*>(rd1)^^(4+n*3)*>ld*>rd1*>rd1*>rd1*>rd0*>rd1*>0inf
| 3 => (ld)^^(14+n*6)*>rd1*>ld*>(rd1)^^(4+n*3)*>ld*>rd0*>(rd1)^^(5+n*3)*>ld*>rd1*>rd0*>rd0*>rd0*>rd1*>rd1*>0inf
| 4 => (ld)^^(15+n*6)*>rd1*>ld*>(rd1)^^(5+n*3)*>ld*>rd1*>rd0*>(rd1)^^(3+n*3)*>ld*>rd0*>rd0*>rd1*>rd0*>rd0*>rd1*>rd1*>0inf
| 5 => (ld)^^(16+n*6)*>rd1*>ld*>(rd1)^^(5+n*3)*>ld*>rd0*>(rd1)^^(6+n*3)*>ld*>rd0*>rd0*>rd0*>rd0*>rd1*>rd1*>0inf
| 6 => (ld)^^(17+n*6)*>rd1*>ld*>(rd1)^^(6+n*3)*>ld*>rd1*>rd0*>(rd1)^^(8+n*3)*>ld*>rd1*>rd1*>0inf
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
  i<6 ->
  sideRLs tm (hRL^^(2^0+0)) ([1;0]*>RC i n) (RC (S i) n).
Proof.
  intro Hn.
  unfold RC.
  do 6
  (destruct i; [solve[sscs']|]).
  lia.
Qed.

Lemma RC_eq n:
  RC 6 n = RC 0 (S n).
Proof.
  unfold RC.
  st; simpl_rotate; reflexivity.
Qed.

Definition S0 '(i,n) := lh {{{ (hL,L) }}} RC i n.

Lemma BigStep i n:
  i<6 ->
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

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (O,O)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(i,n) => i<6).
  2: lia.
  intros [i n] Hi.
  assert (i<5\/i=5) as [E|E] by lia.
  - exists (S i,n); split.
    1: apply BigStep,Hi.
    lia.
  - eexists (O,S n); split; [|lia].
    follow10 (BigStep i n Hi).
    unfold S0.
    rewrite <-RC_eq.
    finish.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB0LF_0RC1RF_1RD0RC_1LE0RB_0RA0LD_0LE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation ld := [1;0;1;0].
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation lh := (0inf<*<[1;0]).

Notation hR := (D,[1]).
Notation hL := (D,[0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma LOv r:
  lh {{{ (hL,L) }}} r -->*
  lh {{{ (hR,R) }}} [1;0] *> r.
Proof. esx. Qed.


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

Lemma rw_10_ld r:
  [1;0] *> ld *> r = ld *> [1;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_rd0 r:
  [1;0] *> rd0 *> r = rd1 *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_rd1 r:
  [1;0] *> rd1 *> r = ld *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_ld r:
  [0] *> ld *> r = [0;1;0] *> [1;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_rd0 r:
  [0] *> rd0 *> r = rd0 *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_rd1 r:
  [0] *> rd1 *> r = [0;1;0] *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_ld r:
  [0;0] *> ld *> r = [0;0;1;0] *> [1;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd0 r:
  [0;0] *> rd0 *> r = rd0 *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd1 r:
  [0;0] *> rd1 *> r = [0;0;1;0] *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_lds n r:
  [1;0] *> ld^^n *> r = ld^^n *> [1;0] *> r.
Proof.
  simpl_rotate; reflexivity.
Qed.

Lemma rw_0_1s n r:
  [0] *> rd1^^n *> r = [0;1;0]^^n *> [0] *> r.
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
  rewrite rw_10_ld ||
  rewrite rw_10_rd0 ||
  rewrite rw_10_rd1 ||
  rewrite rw_10_lds ||
  rewrite rw_10_0inf ||
  rewrite rw_0_ld ||
  rewrite rw_0_rd0 ||
  rewrite rw_0_rd1 ||
  rewrite rw_0_1s ||
  rewrite rw_0_0inf ||
  rewrite rw_00_ld ||
  rewrite rw_00_rd0 ||
  rewrite rw_00_rd1 ||
  rewrite rw_00_0inf).

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

Lemma hRL_110 n r r':
  sideRLs tm (hRL^^n) (rd1*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([1;1;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma hRL_010 n r r':
  sideRLs tm (hRL^^n) ([1;1;0]*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;1;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma hRL_0010 n r r':
  sideRLs tm (hRL^^n) (ld*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;0;1;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma sideRLs_010s k n r r':
  1<=k ->
  sideRLs tm (hRL^^(2^k-2)) r r' ->
  sideRLs tm (hRL^^(2^(k+n)-2)) ([0;1;0]^^n*>r) (rd1^^n*>r').
Proof.
  intros.
  rewrite (Nat.pow_le_mono_r_iff 2) in H by lia.
  induction n.
  - applys_eq H0; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    rewrite <-(Nat.add_1_r n).
    applys_eq (segRLs_addmul_v2 2 1 2 0 (2^(k+n)-2)); rw_pa; flia; ss.
Qed.

Lemma sideRLs_010s_v1 c n r r':
  1<=c ->
  sideRLs tm (hRL^^(2^(n*3+c)-2)) r r' ->
  sideRLs tm (hRL^^(2^(n*6+c)-2)) ([0;1;0]^^(n*3)*>r) (rd1^^(n*3)*>r').
Proof.
  replace (n*6+c) with (n*3+c+n*3) by lia.
  intros.
  apply sideRLs_010s; [lia|assumption].
Qed.

Lemma sideRLs_010s_v2 c n r r':
  1<=c ->
  sideRLs tm (hRL^^(2^c-2)) r r' ->
  sideRLs tm (hRL^^(2^(n*3+c)-2)) ([0;1;0]^^(n*3)*>r) (rd1^^(n*3)*>r').
Proof.
  replace (n*3+c) with (c+n*3) by lia.
  intros.
  apply sideRLs_010s; [lia|assumption].
Qed.


Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- ?G => idtac G
  end;
  match goal with
  | |- sideRLs _ (_^^O) _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ _ ([0;0;1;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_0010
  | |- sideRLs _ _ ([0;1;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_010
  | |- sideRLs _ _ ([1;1;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_110
  | |- sideRLs _ _ (ld*>_) _ =>
    ssc segRLs_ld
  | |- sideRLs _ _ (ld^^_*>_) _ =>
    eapply sideRLs_lds
  | |- sideRLs _ _ ([0;1;0]^^_*>_) _ =>
    (eapply sideRLs_010s_v1;[lia|]) ||
    (eapply sideRLs_010s_v2;[lia|])
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

Definition RC i n :=
match i with
| 0%nat => (ld)^^(11+n*6)*>rd1*>ld*>(rd1)^^(3+n*3)*>ld*>rd1*>rd0*>(rd1)^^(5+n*3)*>ld*>rd1*>rd1*>0inf
| 1%nat => (ld)^^(12+n*6)*>rd1*>ld*>(rd1)^^(3+n*3)*>ld*>rd0*>(rd1)^^(6+n*3)*>ld*>rd1*>rd1*>rd0*>rd1*>0inf
| 2 => (ld)^^(13+n*6)*>rd1*>ld*>(rd1)^^(4+n*3)*>ld*>rd1*>rd0*>(rd1)^^(4+n*3)*>ld*>rd1*>rd1*>rd1*>rd0*>rd1*>0inf
| 3 => (ld)^^(14+n*6)*>rd1*>ld*>(rd1)^^(4+n*3)*>ld*>rd0*>(rd1)^^(5+n*3)*>ld*>rd1*>rd0*>rd0*>rd0*>rd1*>rd1*>0inf
| 4 => (ld)^^(15+n*6)*>rd1*>ld*>(rd1)^^(5+n*3)*>ld*>rd1*>rd0*>(rd1)^^(3+n*3)*>ld*>rd0*>rd0*>rd1*>rd0*>rd0*>rd1*>rd1*>0inf
| 5 => (ld)^^(16+n*6)*>rd1*>ld*>(rd1)^^(5+n*3)*>ld*>rd0*>(rd1)^^(6+n*3)*>ld*>rd0*>rd0*>rd0*>rd0*>rd1*>rd1*>0inf
| 6 => (ld)^^(17+n*6)*>rd1*>ld*>(rd1)^^(6+n*3)*>ld*>rd1*>rd0*>(rd1)^^(8+n*3)*>ld*>rd1*>rd1*>0inf
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
  i<6 ->
  sideRLs tm (hRL^^(2^0+0)) ([1;0]*>RC i n) (RC (S i) n).
Proof.
  intro Hn.
  unfold RC.
  do 6
  (destruct i; [solve[sscs']|]).
  lia.
Qed.

Lemma RC_eq n:
  RC 6 n = RC 0 (S n).
Proof.
  unfold RC.
  st; simpl_rotate; reflexivity.
Qed.

Definition S0 '(i,n) := lh {{{ (hL,L) }}} RC i n.

Lemma BigStep i n:
  i<6 ->
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

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (O,O)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(i,n) => i<6).
  2: lia.
  intros [i n] Hi.
  assert (i<5\/i=5) as [E|E] by lia.
  - exists (S i,n); split.
    1: apply BigStep,Hi.
    lia.
  - eexists (O,S n); split; [|lia].
    follow10 (BigStep i n Hi).
    unfold S0.
    rewrite <-RC_eq.
    finish.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1LB0LA_0LC1LB_1RD0RE_1RE---_1RA1RF_1RB0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation ld := [1;1;1].
Notation rd0 := [1;0;0;1].
Notation rd1 := [1;1;0;0].
Notation lh := (0inf<*<[1;1]).

Notation hR := (E,[]).
Notation hL := (B,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma LOv r:
  lh {{{ (hL,L) }}} r -->*
  lh {{{ (hR,R) }}} [1;1] *> r.
Proof. esx. Qed.


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

Lemma rw_11_ld r:
  [1;1] *> ld *> r = ld *> [1;1] *> r.
Proof. reflexivity. Qed.

Lemma rw_11_rd0 r:
  [1;1] *> rd0 *> r = ld *> [0;0;1] *> r.
Proof. reflexivity. Qed.

Lemma rw_11_rd1 r:
  [1;1] *> rd1 *> r = ld *> [1;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_100_ld r:
  [1;0;0] *> ld *> r = rd0 *> [1;1] *> r.
Proof. reflexivity. Qed.

Lemma rw_100_rd0 r:
  [1;0;0] *> rd0 *> r = rd0 *> [0;0;1] *> r.
Proof. reflexivity. Qed.

Lemma rw_100_rd1 r:
  [1;0;0] *> rd1 *> r = rd0 *> [1;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_11_lds n r:
  [1;1] *> ld^^n *> r = ld^^n *> [1;1] *> r.
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
  rewrite rw_11_lds ||
  rewrite rw_11_ld ||
  rewrite rw_11_rd0 ||
  rewrite rw_11_rd1 ||
  rewrite rw_100_ld ||
  rewrite rw_100_rd0 ||
  rewrite rw_100_rd1).

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

Lemma hRL_001 n r r':
  sideRLs tm (hRL^^n) (ld*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;0;1]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma sideRLs_001s n:
  sideRLs tm (hRL^^(2^(n*3+2))) ((rd0++rd0++rd1)^^n*>0inf) ((rd0++rd0++rd1)^^n*>rd0*>rd0*>rd1*>0inf).
Proof.
  induction n.
  1: esx.
  cbn[lpow].
  do 2 rewrite (Str_app_assoc (rd0++rd0++rd1)).
  eapply segRLs_sideRLs_concat.
  2: apply IHn.
  replace (S n*3) with (n*3+3) by lia.
  applys_eq (segRLs_addmul_v2 8 1 0 0 (2^(n*3+2))); rw_pa; flia; ss.
Qed.

Lemma sideRLs_001s_v1 n:
  sideRLs tm (hRL^^(2^(n*24+2)+0)) ((rd0++rd0++rd1)^^(n*8)*>0inf) ((rd0++rd0++rd1)^^(n*8)*>rd0*>rd0*>rd1*>0inf).
Proof.
  rewrite Nat.add_0_r.
  applys_eq (sideRLs_001s (n*8)); flia.
Qed.

Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- ?G => idtac G
  end;
  match goal with
  | |- sideRLs _ (_^^O) _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ _ ([0;0;1]*>_) _ =>
    R_sub 1%nat; eapply hRL_001
  | |- sideRLs _ _ (ld*>_) _ =>
    ssc segRLs_ld
  | |- sideRLs _ _ (ld^^_*>_) _ =>
    eapply sideRLs_lds
  | |- sideRLs _ _ (_^^_*>_) _ =>
    eapply sideRLs_001s_v1
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

Definition RC i n :=
match i with
| 0%nat => (ld)^^(7+n*24)*>rd0*>rd1*>rd0*>rd1*>rd0*>(rd0++rd0++rd1)^^(1+n*8)*>0inf
| 1%nat => (ld)^^(9+n*24)*>rd1*>rd1*>rd0*>rd0*>(rd0++rd0++rd1)^^(2+n*8)*>0inf
| 2 => (ld)^^(10+n*24)*>rd0*>rd0*>ld*>rd0*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(2+n*8)*>0inf
| 3 => (ld)^^(12+n*24)*>rd0*>ld*>rd0*>rd0*>rd1*>rd0*>(rd0++rd0++rd1)^^(3+n*8)*>0inf
| 4 => (ld)^^(15+n*24)*>rd0*>rd0*>rd0*>rd0*>(rd0++rd0++rd1)^^(4+n*8)*>0inf
| 5 => (ld)^^(17+n*24)*>rd0*>rd1*>rd1*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(4+n*8)*>0inf
| 6 => (ld)^^(19+n*24)*>rd1*>rd0*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(5+n*8)*>0inf
| 7 => (ld)^^(20+n*24)*>rd0*>ld*>rd1*>rd0*>rd0*>(rd0++rd0++rd1)^^(6+n*8)*>0inf
| 8 => (ld)^^(23+n*24)*>rd1*>rd0*>rd1*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(6+n*8)*>0inf
| 9 => (ld)^^(24+n*24)*>rd0*>ld*>rd1*>rd0*>rd1*>rd0*>(rd0++rd0++rd1)^^(7+n*8)*>0inf
| 10 => (ld)^^(27+n*24)*>rd1*>rd0*>rd0*>rd0*>(rd0++rd0++rd1)^^(8+n*8)*>0inf
| 11 => (ld)^^(28+n*24)*>rd0*>ld*>rd0*>rd1*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(8+n*8)*>0inf
| 12 => (ld)^^(31+n*24)*>rd0*>rd1*>rd0*>rd1*>rd0*>(rd0++rd0++rd1)^^(9+n*8)*>0inf
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
  i<12 ->
  sideRLs tm (hRL^^(2^0+0)) ([1;1]*>RC i n) (RC (S i) n).
Proof.
  intro Hn.
  unfold RC.
  do 12
  (destruct i; [solve[sscs']|]).
  lia.
Qed.

Lemma RC_eq n:
  RC 12 n = RC 0 (S n).
Proof.
  unfold RC.
  st; simpl_rotate; reflexivity.
Qed.

Definition S0 '(i,n) := lh {{{ (hL,L) }}} RC i n.

Lemma BigStep i n:
  i<12 ->
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

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (O,O)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(i,n) => i<12).
  2: lia.
  intros [i n] Hi.
  assert (i<11\/i=11) as [E|E] by lia.
  - exists (S i,n); split.
    1: apply BigStep,Hi.
    lia.
  - eexists (O,S n); split; [|lia].
    follow10 (BigStep i n Hi).
    unfold S0.
    rewrite <-RC_eq.
    finish.
Qed.

End TM4.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1RB---_1RC1RF_1LD0LC_0LE1LD_1RA0RB_1RD0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation ld := [1;1;1].
Notation rd0 := [1;0;0;1].
Notation rd1 := [1;1;0;0].
Notation lh := (0inf<*<[1;1]).

Notation hR := (B,[]).
Notation hL := (D,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma LOv r:
  lh {{{ (hL,L) }}} r -->*
  lh {{{ (hR,R) }}} [1;1] *> r.
Proof. esx. Qed.


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

Lemma rw_11_ld r:
  [1;1] *> ld *> r = ld *> [1;1] *> r.
Proof. reflexivity. Qed.

Lemma rw_11_rd0 r:
  [1;1] *> rd0 *> r = ld *> [0;0;1] *> r.
Proof. reflexivity. Qed.

Lemma rw_11_rd1 r:
  [1;1] *> rd1 *> r = ld *> [1;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_100_ld r:
  [1;0;0] *> ld *> r = rd0 *> [1;1] *> r.
Proof. reflexivity. Qed.

Lemma rw_100_rd0 r:
  [1;0;0] *> rd0 *> r = rd0 *> [0;0;1] *> r.
Proof. reflexivity. Qed.

Lemma rw_100_rd1 r:
  [1;0;0] *> rd1 *> r = rd0 *> [1;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_11_lds n r:
  [1;1] *> ld^^n *> r = ld^^n *> [1;1] *> r.
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
  rewrite rw_11_lds ||
  rewrite rw_11_ld ||
  rewrite rw_11_rd0 ||
  rewrite rw_11_rd1 ||
  rewrite rw_100_ld ||
  rewrite rw_100_rd0 ||
  rewrite rw_100_rd1).

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

Lemma hRL_001 n r r':
  sideRLs tm (hRL^^n) (ld*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;0;1]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma sideRLs_001s n:
  sideRLs tm (hRL^^(2^(n*3+2))) ((rd0++rd0++rd1)^^n*>0inf) ((rd0++rd0++rd1)^^n*>rd0*>rd0*>rd1*>0inf).
Proof.
  induction n.
  1: esx.
  cbn[lpow].
  do 2 rewrite (Str_app_assoc (rd0++rd0++rd1)).
  eapply segRLs_sideRLs_concat.
  2: apply IHn.
  replace (S n*3) with (n*3+3) by lia.
  applys_eq (segRLs_addmul_v2 8 1 0 0 (2^(n*3+2))); rw_pa; flia; ss.
Qed.

Lemma sideRLs_001s_v1 n:
  sideRLs tm (hRL^^(2^(n*24+2)+0)) ((rd0++rd0++rd1)^^(n*8)*>0inf) ((rd0++rd0++rd1)^^(n*8)*>rd0*>rd0*>rd1*>0inf).
Proof.
  rewrite Nat.add_0_r.
  applys_eq (sideRLs_001s (n*8)); flia.
Qed.

Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- ?G => idtac G
  end;
  match goal with
  | |- sideRLs _ (_^^O) _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ _ ([0;0;1]*>_) _ =>
    R_sub 1%nat; eapply hRL_001
  | |- sideRLs _ _ (ld*>_) _ =>
    ssc segRLs_ld
  | |- sideRLs _ _ (ld^^_*>_) _ =>
    eapply sideRLs_lds
  | |- sideRLs _ _ (_^^_*>_) _ =>
    eapply sideRLs_001s_v1
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

Definition RC i n :=
match i with
| 0%nat => (ld)^^(10+n*24)*>rd0*>rd1*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(2+n*8)*>0inf
| 1%nat => (ld)^^(12+n*24)*>rd1*>rd0*>rd1*>rd0*>(rd0++rd0++rd1)^^(3+n*8)*>0inf
| 2 => (ld)^^(13+n*24)*>rd0*>ld*>rd1*>rd1*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(3+n*8)*>0inf
| 3 => (ld)^^(16+n*24)*>rd1*>rd1*>rd0*>rd1*>rd0*>(rd0++rd0++rd1)^^(4+n*8)*>0inf
| 4 => (ld)^^(17+n*24)*>rd0*>rd0*>ld*>rd1*>rd1*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(4+n*8)*>0inf
| 5 => (ld)^^(19+n*24)*>rd0*>ld*>rd1*>rd0*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(5+n*8)*>0inf
| 6 => (ld)^^(22+n*24)*>rd1*>rd0*>rd0*>rd1*>rd0*>(rd0++rd0++rd1)^^(6+n*8)*>0inf
| 7 => (ld)^^(23+n*24)*>rd0*>ld*>rd0*>rd0*>rd0*>(rd0++rd0++rd1)^^(7+n*8)*>0inf
| 8 => (ld)^^(26+n*24)*>rd0*>rd0*>rd1*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(7+n*8)*>0inf
| 9 => (ld)^^(28+n*24)*>rd0*>rd0*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(8+n*8)*>0inf
| 10 => (ld)^^(30+n*24)*>rd0*>rd0*>rd1*>rd0*>(rd0++rd0++rd1)^^(9+n*8)*>0inf
| 11 => (ld)^^(32+n*24)*>rd0*>rd0*>rd0*>(rd0++rd0++rd1)^^(10+n*8)*>0inf
| 12 => (ld)^^(34+n*24)*>rd0*>rd1*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(10+n*8)*>0inf
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
  i<12 ->
  sideRLs tm (hRL^^(2^0+0)) ([1;1]*>RC i n) (RC (S i) n).
Proof.
  intro Hn.
  unfold RC.
  do 12
  (destruct i; [solve[sscs']|]).
  lia.
Qed.

Lemma RC_eq n:
  RC 12 n = RC 0 (S n).
Proof.
  unfold RC.
  st; simpl_rotate; reflexivity.
Qed.

Definition S0 '(i,n) := lh {{{ (hL,L) }}} RC i n.

Lemma BigStep i n:
  i<12 ->
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

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (O,O)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(i,n) => i<12).
  2: lia.
  intros [i n] Hi.
  assert (i<11\/i=11) as [E|E] by lia.
  - exists (S i,n); split.
    1: apply BigStep,Hi.
    lia.
  - eexists (O,S n); split; [|lia].
    follow10 (BigStep i n Hi).
    unfold S0.
    rewrite <-RC_eq.
    finish.
Qed.

End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1RB0RC_0LC1LB_1RF0RD_1RE1RA_1LB0LE_1RD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation ld := [1;1;1].
Notation rd0 := [1;0;0;1].
Notation rd1 := [1;1;0;0].
Notation lh := (0inf<*<[1;1]).

Notation hR := (D,[]).
Notation hL := (B,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma LOv r:
  lh {{{ (hL,L) }}} r -->*
  lh {{{ (hR,R) }}} [1;1] *> r.
Proof. esx. Qed.


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

Lemma rw_11_ld r:
  [1;1] *> ld *> r = ld *> [1;1] *> r.
Proof. reflexivity. Qed.

Lemma rw_11_rd0 r:
  [1;1] *> rd0 *> r = ld *> [0;0;1] *> r.
Proof. reflexivity. Qed.

Lemma rw_11_rd1 r:
  [1;1] *> rd1 *> r = ld *> [1;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_100_ld r:
  [1;0;0] *> ld *> r = rd0 *> [1;1] *> r.
Proof. reflexivity. Qed.

Lemma rw_100_rd0 r:
  [1;0;0] *> rd0 *> r = rd0 *> [0;0;1] *> r.
Proof. reflexivity. Qed.

Lemma rw_100_rd1 r:
  [1;0;0] *> rd1 *> r = rd0 *> [1;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_11_lds n r:
  [1;1] *> ld^^n *> r = ld^^n *> [1;1] *> r.
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
  rewrite rw_11_lds ||
  rewrite rw_11_ld ||
  rewrite rw_11_rd0 ||
  rewrite rw_11_rd1 ||
  rewrite rw_100_ld ||
  rewrite rw_100_rd0 ||
  rewrite rw_100_rd1).

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

Lemma hRL_001 n r r':
  sideRLs tm (hRL^^n) (ld*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;0;1]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma sideRLs_001s n:
  sideRLs tm (hRL^^(2^(n*3+2))) ((rd0++rd0++rd1)^^n*>0inf) ((rd0++rd0++rd1)^^n*>rd0*>rd0*>rd1*>0inf).
Proof.
  induction n.
  1: esx.
  cbn[lpow].
  do 2 rewrite (Str_app_assoc (rd0++rd0++rd1)).
  eapply segRLs_sideRLs_concat.
  2: apply IHn.
  replace (S n*3) with (n*3+3) by lia.
  applys_eq (segRLs_addmul_v2 8 1 0 0 (2^(n*3+2))); rw_pa; flia; ss.
Qed.

Lemma sideRLs_001s_v1 n:
  sideRLs tm (hRL^^(2^(n*24+2)+0)) ((rd0++rd0++rd1)^^(n*8)*>0inf) ((rd0++rd0++rd1)^^(n*8)*>rd0*>rd0*>rd1*>0inf).
Proof.
  rewrite Nat.add_0_r.
  applys_eq (sideRLs_001s (n*8)); flia.
Qed.

Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- ?G => idtac G
  end;
  match goal with
  | |- sideRLs _ (_^^O) _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ _ ([0;0;1]*>_) _ =>
    R_sub 1%nat; eapply hRL_001
  | |- sideRLs _ _ (ld*>_) _ =>
    ssc segRLs_ld
  | |- sideRLs _ _ (ld^^_*>_) _ =>
    eapply sideRLs_lds
  | |- sideRLs _ _ (_^^_*>_) _ =>
    eapply sideRLs_001s_v1
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

Definition RC i n :=
match i with
| 0%nat => (ld)^^(9+n*24)*>rd0*>rd1*>rd0*>rd0*>(rd0++rd0++rd1)^^(2+n*8)*>0inf
| 1%nat => (ld)^^(11+n*24)*>rd1*>rd1*>rd1*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(2+n*8)*>0inf
| 2 => (ld)^^(12+n*24)*>rd0*>rd0*>rd0*>rd0*>rd0*>ld*>rd0*>rd1*>rd0*>(rd0++rd0++rd1)^^(2+n*8)*>0inf
| 3 => (ld)^^(14+n*24)*>rd0*>rd1*>rd1*>rd1*>ld*>rd0*>rd0*>rd0*>(rd0++rd0++rd1)^^(3+n*8)*>0inf
| 4 => (ld)^^(16+n*24)*>rd1*>rd0*>rd1*>ld*>rd0*>rd0*>rd0*>(rd0++rd0++rd1)^^(4+n*8)*>0inf
| 5 => (ld)^^(17+n*24)*>rd0*>ld*>rd1*>ld*>rd0*>rd1*>rd1*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(4+n*8)*>0inf
| 6 => (ld)^^(20+n*24)*>rd1*>ld*>rd0*>rd1*>rd0*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(5+n*8)*>0inf
| 7 => (ld)^^(21+n*24)*>rd0*>ld*>ld*>rd1*>rd1*>rd0*>rd1*>rd0*>(rd0++rd0++rd1)^^(6+n*8)*>0inf
| 8 => (ld)^^(25+n*24)*>rd1*>rd1*>rd0*>rd0*>rd0*>(rd0++rd0++rd1)^^(7+n*8)*>0inf
| 9 => (ld)^^(26+n*24)*>rd0*>rd0*>ld*>rd0*>rd1*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(7+n*8)*>0inf
| 10 => (ld)^^(28+n*24)*>rd0*>ld*>rd0*>rd0*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(8+n*8)*>0inf
| 11 => (ld)^^(31+n*24)*>rd0*>rd0*>rd0*>rd1*>rd0*>(rd0++rd0++rd1)^^(9+n*8)*>0inf
| 12 => (ld)^^(33+n*24)*>rd0*>rd1*>rd0*>rd0*>(rd0++rd0++rd1)^^(10+n*8)*>0inf
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
  i<12 ->
  sideRLs tm (hRL^^(2^0+0)) ([1;1]*>RC i n) (RC (S i) n).
Proof.
  intro Hn.
  unfold RC.
  do 12
  (destruct i; [solve[sscs']|]).
  lia.
Qed.

Lemma RC_eq n:
  RC 12 n = RC 0 (S n).
Proof.
  unfold RC.
  st; simpl_rotate; reflexivity.
Qed.

Definition S0 '(i,n) := lh {{{ (hL,L) }}} RC i n.

Lemma BigStep i n:
  i<12 ->
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

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (O,O)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(i,n) => i<12).
  2: lia.
  intros [i n] Hi.
  assert (i<11\/i=11) as [E|E] by lia.
  - exists (S i,n); split.
    1: apply BigStep,Hi.
    lia.
  - eexists (O,S n); split; [|lia].
    follow10 (BigStep i n Hi).
    unfold S0.
    rewrite <-RC_eq.
    finish.
Qed.

End TM6.


Module TM7.

Definition tm := Eval compute in (TM_from_str "1LB0LA_0LC1LB_1RD0RE_1RE---_1RA1RF_0RE0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation ld := [1;1;1].
Notation rd0 := [1;0;0;1].
Notation rd1 := [1;1;0;0].
Notation lh := (0inf<*<[1;1]).

Notation hR := (E,[]).
Notation hL := (B,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma LOv r:
  lh {{{ (hL,L) }}} r -->*
  lh {{{ (hR,R) }}} [1;1] *> r.
Proof. esx. Qed.


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

Lemma rw_11_ld r:
  [1;1] *> ld *> r = ld *> [1;1] *> r.
Proof. reflexivity. Qed.

Lemma rw_11_rd0 r:
  [1;1] *> rd0 *> r = ld *> [0;0;1] *> r.
Proof. reflexivity. Qed.

Lemma rw_11_rd1 r:
  [1;1] *> rd1 *> r = ld *> [1;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_100_ld r:
  [1;0;0] *> ld *> r = rd0 *> [1;1] *> r.
Proof. reflexivity. Qed.

Lemma rw_100_rd0 r:
  [1;0;0] *> rd0 *> r = rd0 *> [0;0;1] *> r.
Proof. reflexivity. Qed.

Lemma rw_100_rd1 r:
  [1;0;0] *> rd1 *> r = rd0 *> [1;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_11_lds n r:
  [1;1] *> ld^^n *> r = ld^^n *> [1;1] *> r.
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
  rewrite rw_11_lds ||
  rewrite rw_11_ld ||
  rewrite rw_11_rd0 ||
  rewrite rw_11_rd1 ||
  rewrite rw_100_ld ||
  rewrite rw_100_rd0 ||
  rewrite rw_100_rd1).

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

Lemma hRL_001 n r r':
  sideRLs tm (hRL^^n) (ld*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;0;1]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma sideRLs_001s n:
  sideRLs tm (hRL^^(2^(n*3+2))) ((rd0++rd0++rd1)^^n*>0inf) ((rd0++rd0++rd1)^^n*>rd0*>rd0*>rd1*>0inf).
Proof.
  induction n.
  1: esx.
  cbn[lpow].
  do 2 rewrite (Str_app_assoc (rd0++rd0++rd1)).
  eapply segRLs_sideRLs_concat.
  2: apply IHn.
  replace (S n*3) with (n*3+3) by lia.
  applys_eq (segRLs_addmul_v2 8 1 0 0 (2^(n*3+2))); rw_pa; flia; ss.
Qed.

Lemma sideRLs_001s_v1 n:
  sideRLs tm (hRL^^(2^(n*24+2)+0)) ((rd0++rd0++rd1)^^(n*8)*>0inf) ((rd0++rd0++rd1)^^(n*8)*>rd0*>rd0*>rd1*>0inf).
Proof.
  rewrite Nat.add_0_r.
  applys_eq (sideRLs_001s (n*8)); flia.
Qed.

Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- ?G => idtac G
  end;
  match goal with
  | |- sideRLs _ (_^^O) _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ _ ([0;0;1]*>_) _ =>
    R_sub 1%nat; eapply hRL_001
  | |- sideRLs _ _ (ld*>_) _ =>
    ssc segRLs_ld
  | |- sideRLs _ _ (ld^^_*>_) _ =>
    eapply sideRLs_lds
  | |- sideRLs _ _ (_^^_*>_) _ =>
    eapply sideRLs_001s_v1
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

Definition RC i n :=
match i with
| 0%nat => (ld)^^(7+n*24)*>rd0*>rd1*>rd0*>rd1*>rd0*>(rd0++rd0++rd1)^^(1+n*8)*>0inf
| 1%nat => (ld)^^(9+n*24)*>rd1*>rd1*>rd0*>rd0*>(rd0++rd0++rd1)^^(2+n*8)*>0inf
| 2 => (ld)^^(10+n*24)*>rd0*>rd0*>ld*>rd0*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(2+n*8)*>0inf
| 3 => (ld)^^(12+n*24)*>rd0*>ld*>rd0*>rd0*>rd1*>rd0*>(rd0++rd0++rd1)^^(3+n*8)*>0inf
| 4 => (ld)^^(15+n*24)*>rd0*>rd0*>rd0*>rd0*>(rd0++rd0++rd1)^^(4+n*8)*>0inf
| 5 => (ld)^^(17+n*24)*>rd0*>rd1*>rd1*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(4+n*8)*>0inf
| 6 => (ld)^^(19+n*24)*>rd1*>rd0*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(5+n*8)*>0inf
| 7 => (ld)^^(20+n*24)*>rd0*>ld*>rd1*>rd0*>rd0*>(rd0++rd0++rd1)^^(6+n*8)*>0inf
| 8 => (ld)^^(23+n*24)*>rd1*>rd0*>rd1*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(6+n*8)*>0inf
| 9 => (ld)^^(24+n*24)*>rd0*>ld*>rd1*>rd0*>rd1*>rd0*>(rd0++rd0++rd1)^^(7+n*8)*>0inf
| 10 => (ld)^^(27+n*24)*>rd1*>rd0*>rd0*>rd0*>(rd0++rd0++rd1)^^(8+n*8)*>0inf
| 11 => (ld)^^(28+n*24)*>rd0*>ld*>rd0*>rd1*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(8+n*8)*>0inf
| 12 => (ld)^^(31+n*24)*>rd0*>rd1*>rd0*>rd1*>rd0*>(rd0++rd0++rd1)^^(9+n*8)*>0inf
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
  i<12 ->
  sideRLs tm (hRL^^(2^0+0)) ([1;1]*>RC i n) (RC (S i) n).
Proof.
  intro Hn.
  unfold RC.
  do 12
  (destruct i; [solve[sscs']|]).
  lia.
Qed.

Lemma RC_eq n:
  RC 12 n = RC 0 (S n).
Proof.
  unfold RC.
  st; simpl_rotate; reflexivity.
Qed.

Definition S0 '(i,n) := lh {{{ (hL,L) }}} RC i n.

Lemma BigStep i n:
  i<12 ->
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

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (O,O)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(i,n) => i<12).
  2: lia.
  intros [i n] Hi.
  assert (i<11\/i=11) as [E|E] by lia.
  - exists (S i,n); split.
    1: apply BigStep,Hi.
    lia.
  - eexists (O,S n); split; [|lia].
    follow10 (BigStep i n Hi).
    unfold S0.
    rewrite <-RC_eq.
    finish.
Qed.

End TM7.


Module TM8.

Definition tm := Eval compute in (TM_from_str "1RB0RC_1RC---_1RD1RF_1LE0LD_0LA1LE_0RC0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation ld := [1;1;1].
Notation rd0 := [1;0;0;1].
Notation rd1 := [1;1;0;0].
Notation lh := (0inf<*<[1;1]).

Notation hR := (C,[]).
Notation hL := (E,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma LOv r:
  lh {{{ (hL,L) }}} r -->*
  lh {{{ (hR,R) }}} [1;1] *> r.
Proof. esx. Qed.


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

Lemma rw_11_ld r:
  [1;1] *> ld *> r = ld *> [1;1] *> r.
Proof. reflexivity. Qed.

Lemma rw_11_rd0 r:
  [1;1] *> rd0 *> r = ld *> [0;0;1] *> r.
Proof. reflexivity. Qed.

Lemma rw_11_rd1 r:
  [1;1] *> rd1 *> r = ld *> [1;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_100_ld r:
  [1;0;0] *> ld *> r = rd0 *> [1;1] *> r.
Proof. reflexivity. Qed.

Lemma rw_100_rd0 r:
  [1;0;0] *> rd0 *> r = rd0 *> [0;0;1] *> r.
Proof. reflexivity. Qed.

Lemma rw_100_rd1 r:
  [1;0;0] *> rd1 *> r = rd0 *> [1;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_11_lds n r:
  [1;1] *> ld^^n *> r = ld^^n *> [1;1] *> r.
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
  rewrite rw_11_lds ||
  rewrite rw_11_ld ||
  rewrite rw_11_rd0 ||
  rewrite rw_11_rd1 ||
  rewrite rw_100_ld ||
  rewrite rw_100_rd0 ||
  rewrite rw_100_rd1).

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

Lemma hRL_001 n r r':
  sideRLs tm (hRL^^n) (ld*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;0;1]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma sideRLs_001s n:
  sideRLs tm (hRL^^(2^(n*3+2))) ((rd0++rd0++rd1)^^n*>0inf) ((rd0++rd0++rd1)^^n*>rd0*>rd0*>rd1*>0inf).
Proof.
  induction n.
  1: esx.
  cbn[lpow].
  do 2 rewrite (Str_app_assoc (rd0++rd0++rd1)).
  eapply segRLs_sideRLs_concat.
  2: apply IHn.
  replace (S n*3) with (n*3+3) by lia.
  applys_eq (segRLs_addmul_v2 8 1 0 0 (2^(n*3+2))); rw_pa; flia; ss.
Qed.

Lemma sideRLs_001s_v1 n:
  sideRLs tm (hRL^^(2^(n*24+2)+0)) ((rd0++rd0++rd1)^^(n*8)*>0inf) ((rd0++rd0++rd1)^^(n*8)*>rd0*>rd0*>rd1*>0inf).
Proof.
  rewrite Nat.add_0_r.
  applys_eq (sideRLs_001s (n*8)); flia.
Qed.

Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- ?G => idtac G
  end;
  match goal with
  | |- sideRLs _ (_^^O) _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ _ ([0;0;1]*>_) _ =>
    R_sub 1%nat; eapply hRL_001
  | |- sideRLs _ _ (ld*>_) _ =>
    ssc segRLs_ld
  | |- sideRLs _ _ (ld^^_*>_) _ =>
    eapply sideRLs_lds
  | |- sideRLs _ _ (_^^_*>_) _ =>
    eapply sideRLs_001s_v1
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

Definition RC i n :=
match i with
| 0%nat => (ld)^^(9+n*24)*>rd0*>rd1*>rd0*>rd0*>(rd0++rd0++rd1)^^(2+n*8)*>0inf
| 1%nat => (ld)^^(11+n*24)*>rd1*>rd1*>rd1*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(2+n*8)*>0inf
| 2 => (ld)^^(12+n*24)*>rd0*>rd0*>rd0*>rd0*>rd0*>ld*>rd0*>rd1*>rd0*>(rd0++rd0++rd1)^^(2+n*8)*>0inf
| 3 => (ld)^^(14+n*24)*>rd0*>rd1*>rd1*>rd1*>ld*>rd0*>rd0*>rd0*>(rd0++rd0++rd1)^^(3+n*8)*>0inf
| 4 => (ld)^^(16+n*24)*>rd1*>rd0*>rd1*>ld*>rd0*>rd0*>rd0*>(rd0++rd0++rd1)^^(4+n*8)*>0inf
| 5 => (ld)^^(17+n*24)*>rd0*>ld*>rd1*>ld*>rd0*>rd1*>rd1*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(4+n*8)*>0inf
| 6 => (ld)^^(20+n*24)*>rd1*>ld*>rd0*>rd1*>rd0*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(5+n*8)*>0inf
| 7 => (ld)^^(21+n*24)*>rd0*>ld*>ld*>rd1*>rd1*>rd0*>rd1*>rd0*>(rd0++rd0++rd1)^^(6+n*8)*>0inf
| 8 => (ld)^^(25+n*24)*>rd1*>rd1*>rd0*>rd0*>rd0*>(rd0++rd0++rd1)^^(7+n*8)*>0inf
| 9 => (ld)^^(26+n*24)*>rd0*>rd0*>ld*>rd0*>rd1*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(7+n*8)*>0inf
| 10 => (ld)^^(28+n*24)*>rd0*>ld*>rd0*>rd0*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(8+n*8)*>0inf
| 11 => (ld)^^(31+n*24)*>rd0*>rd0*>rd0*>rd1*>rd0*>(rd0++rd0++rd1)^^(9+n*8)*>0inf
| 12 => (ld)^^(33+n*24)*>rd0*>rd1*>rd0*>rd0*>(rd0++rd0++rd1)^^(10+n*8)*>0inf
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
  i<12 ->
  sideRLs tm (hRL^^(2^0+0)) ([1;1]*>RC i n) (RC (S i) n).
Proof.
  intro Hn.
  unfold RC.
  do 12
  (destruct i; [solve[sscs']|]).
  lia.
Qed.

Lemma RC_eq n:
  RC 12 n = RC 0 (S n).
Proof.
  unfold RC.
  st; simpl_rotate; reflexivity.
Qed.

Definition S0 '(i,n) := lh {{{ (hL,L) }}} RC i n.

Lemma BigStep i n:
  i<12 ->
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

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (O,O)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(i,n) => i<12).
  2: lia.
  intros [i n] Hi.
  assert (i<11\/i=11) as [E|E] by lia.
  - exists (S i,n); split.
    1: apply BigStep,Hi.
    lia.
  - eexists (O,S n); split; [|lia].
    follow10 (BigStep i n Hi).
    unfold S0.
    rewrite <-RC_eq.
    finish.
Qed.

End TM8.


Module TM9.

Definition tm := Eval compute in (TM_from_str "1RB---_1RC1RF_1LD0LC_0LE1LD_1RA0RB_0RB0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation ld := [1;1;1].
Notation rd0 := [1;0;0;1].
Notation rd1 := [1;1;0;0].
Notation lh := (0inf<*<[1;1]).

Notation hR := (B,[]).
Notation hL := (D,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma LOv r:
  lh {{{ (hL,L) }}} r -->*
  lh {{{ (hR,R) }}} [1;1] *> r.
Proof. esx. Qed.


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

Lemma rw_11_ld r:
  [1;1] *> ld *> r = ld *> [1;1] *> r.
Proof. reflexivity. Qed.

Lemma rw_11_rd0 r:
  [1;1] *> rd0 *> r = ld *> [0;0;1] *> r.
Proof. reflexivity. Qed.

Lemma rw_11_rd1 r:
  [1;1] *> rd1 *> r = ld *> [1;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_100_ld r:
  [1;0;0] *> ld *> r = rd0 *> [1;1] *> r.
Proof. reflexivity. Qed.

Lemma rw_100_rd0 r:
  [1;0;0] *> rd0 *> r = rd0 *> [0;0;1] *> r.
Proof. reflexivity. Qed.

Lemma rw_100_rd1 r:
  [1;0;0] *> rd1 *> r = rd0 *> [1;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_11_lds n r:
  [1;1] *> ld^^n *> r = ld^^n *> [1;1] *> r.
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
  rewrite rw_11_lds ||
  rewrite rw_11_ld ||
  rewrite rw_11_rd0 ||
  rewrite rw_11_rd1 ||
  rewrite rw_100_ld ||
  rewrite rw_100_rd0 ||
  rewrite rw_100_rd1).

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

Lemma hRL_001 n r r':
  sideRLs tm (hRL^^n) (ld*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;0;1]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma sideRLs_001s n:
  sideRLs tm (hRL^^(2^(n*3+2))) ((rd0++rd0++rd1)^^n*>0inf) ((rd0++rd0++rd1)^^n*>rd0*>rd0*>rd1*>0inf).
Proof.
  induction n.
  1: esx.
  cbn[lpow].
  do 2 rewrite (Str_app_assoc (rd0++rd0++rd1)).
  eapply segRLs_sideRLs_concat.
  2: apply IHn.
  replace (S n*3) with (n*3+3) by lia.
  applys_eq (segRLs_addmul_v2 8 1 0 0 (2^(n*3+2))); rw_pa; flia; ss.
Qed.

Lemma sideRLs_001s_v1 n:
  sideRLs tm (hRL^^(2^(n*24+2)+0)) ((rd0++rd0++rd1)^^(n*8)*>0inf) ((rd0++rd0++rd1)^^(n*8)*>rd0*>rd0*>rd1*>0inf).
Proof.
  rewrite Nat.add_0_r.
  applys_eq (sideRLs_001s (n*8)); flia.
Qed.

Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- ?G => idtac G
  end;
  match goal with
  | |- sideRLs _ (_^^O) _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ _ ([0;0;1]*>_) _ =>
    R_sub 1%nat; eapply hRL_001
  | |- sideRLs _ _ (ld*>_) _ =>
    ssc segRLs_ld
  | |- sideRLs _ _ (ld^^_*>_) _ =>
    eapply sideRLs_lds
  | |- sideRLs _ _ (_^^_*>_) _ =>
    eapply sideRLs_001s_v1
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

Definition RC i n :=
match i with
| 0%nat => (ld)^^(10+n*24)*>rd0*>rd1*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(2+n*8)*>0inf
| 1%nat => (ld)^^(12+n*24)*>rd1*>rd0*>rd1*>rd0*>(rd0++rd0++rd1)^^(3+n*8)*>0inf
| 2 => (ld)^^(13+n*24)*>rd0*>ld*>rd1*>rd1*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(3+n*8)*>0inf
| 3 => (ld)^^(16+n*24)*>rd1*>rd1*>rd0*>rd1*>rd0*>(rd0++rd0++rd1)^^(4+n*8)*>0inf
| 4 => (ld)^^(17+n*24)*>rd0*>rd0*>ld*>rd1*>rd1*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(4+n*8)*>0inf
| 5 => (ld)^^(19+n*24)*>rd0*>ld*>rd1*>rd0*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(5+n*8)*>0inf
| 6 => (ld)^^(22+n*24)*>rd1*>rd0*>rd0*>rd1*>rd0*>(rd0++rd0++rd1)^^(6+n*8)*>0inf
| 7 => (ld)^^(23+n*24)*>rd0*>ld*>rd0*>rd0*>rd0*>(rd0++rd0++rd1)^^(7+n*8)*>0inf
| 8 => (ld)^^(26+n*24)*>rd0*>rd0*>rd1*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(7+n*8)*>0inf
| 9 => (ld)^^(28+n*24)*>rd0*>rd0*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(8+n*8)*>0inf
| 10 => (ld)^^(30+n*24)*>rd0*>rd0*>rd1*>rd0*>(rd0++rd0++rd1)^^(9+n*8)*>0inf
| 11 => (ld)^^(32+n*24)*>rd0*>rd0*>rd0*>(rd0++rd0++rd1)^^(10+n*8)*>0inf
| 12 => (ld)^^(34+n*24)*>rd0*>rd1*>rd1*>rd1*>rd0*>(rd0++rd0++rd1)^^(10+n*8)*>0inf
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
  i<12 ->
  sideRLs tm (hRL^^(2^0+0)) ([1;1]*>RC i n) (RC (S i) n).
Proof.
  intro Hn.
  unfold RC.
  do 12
  (destruct i; [solve[sscs']|]).
  lia.
Qed.

Lemma RC_eq n:
  RC 12 n = RC 0 (S n).
Proof.
  unfold RC.
  st; simpl_rotate; reflexivity.
Qed.

Definition S0 '(i,n) := lh {{{ (hL,L) }}} RC i n.

Lemma BigStep i n:
  i<12 ->
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

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (O,O)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(i,n) => i<12).
  2: lia.
  intros [i n] Hi.
  assert (i<11\/i=11) as [E|E] by lia.
  - exists (S i,n); split.
    1: apply BigStep,Hi.
    lia.
  - eexists (O,S n); split; [|lia].
    follow10 (BigStep i n Hi).
    unfold S0.
    rewrite <-RC_eq.
    finish.
Qed.

End TM9.


Module TM10.

Definition tm := Eval compute in (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC0LD_0RD0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation ld := [1;0;1;0].
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation lh := (0inf<*<[1]).

Notation hR := (C,[0]).
Notation hL := (A,[0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma LOv r:
  lh {{{ (hL,L) }}} r -->*
  lh {{{ (hR,R) }}} [1;0] *> r.
Proof. esx. Qed.


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

Lemma rw_10_ld r:
  [1;0] *> ld *> r = ld *> [1;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_rd0 r:
  [1;0] *> rd0 *> r = rd1 *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_rd1 r:
  [1;0] *> rd1 *> r = ld *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_ld r:
  [0] *> ld *> r = [0;1;0] *> [1;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_rd0 r:
  [0] *> rd0 *> r = rd0 *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_rd1 r:
  [0] *> rd1 *> r = [0;1;0] *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_ld r:
  [0;0] *> ld *> r = [0;0;1;0] *> [1;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd0 r:
  [0;0] *> rd0 *> r = rd0 *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd1 r:
  [0;0] *> rd1 *> r = [0;0;1;0] *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_lds n r:
  [1;0] *> ld^^n *> r = ld^^n *> [1;0] *> r.
Proof.
  simpl_rotate; reflexivity.
Qed.

Lemma rw_0_1s n r:
  [0] *> rd1^^n *> r = [0;1;0]^^n *> [0] *> r.
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
  rewrite rw_10_ld ||
  rewrite rw_10_rd0 ||
  rewrite rw_10_rd1 ||
  rewrite rw_10_lds ||
  rewrite rw_10_0inf ||
  rewrite rw_0_ld ||
  rewrite rw_0_rd0 ||
  rewrite rw_0_rd1 ||
  rewrite rw_0_1s ||
  rewrite rw_0_0inf ||
  rewrite rw_00_ld ||
  rewrite rw_00_rd0 ||
  rewrite rw_00_rd1 ||
  rewrite rw_00_0inf).

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

Lemma hRL_110 n r r':
  sideRLs tm (hRL^^n) (rd1*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([1;1;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma hRL_010 n r r':
  sideRLs tm (hRL^^n) ([1;1;0]*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;1;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma hRL_0010 n r r':
  sideRLs tm (hRL^^n) (ld*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;0;1;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma sideRLs_010s k n r r':
  1<=k ->
  sideRLs tm (hRL^^(2^k-2)) r r' ->
  sideRLs tm (hRL^^(2^(k+n)-2)) ([0;1;0]^^n*>r) (rd1^^n*>r').
Proof.
  intros.
  rewrite (Nat.pow_le_mono_r_iff 2) in H by lia.
  induction n.
  - applys_eq H0; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    rewrite <-(Nat.add_1_r n).
    applys_eq (segRLs_addmul_v2 2 1 2 0 (2^(k+n)-2)); rw_pa; flia; ss.
Qed.

Lemma sideRLs_010s_v1 c n r r':
  1<=c ->
  sideRLs tm (hRL^^(2^(n*3+c)-2)) r r' ->
  sideRLs tm (hRL^^(2^(n*6+c)-2)) ([0;1;0]^^(n*3)*>r) (rd1^^(n*3)*>r').
Proof.
  replace (n*6+c) with (n*3+c+n*3) by lia.
  intros.
  apply sideRLs_010s; [lia|assumption].
Qed.

Lemma sideRLs_010s_v2 c n r r':
  1<=c ->
  sideRLs tm (hRL^^(2^c-2)) r r' ->
  sideRLs tm (hRL^^(2^(n*3+c)-2)) ([0;1;0]^^(n*3)*>r) (rd1^^(n*3)*>r').
Proof.
  replace (n*3+c) with (c+n*3) by lia.
  intros.
  apply sideRLs_010s; [lia|assumption].
Qed.


Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- ?G => idtac G
  end;
  match goal with
  | |- sideRLs _ (_^^O) _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ _ ([0;0;1;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_0010
  | |- sideRLs _ _ ([0;1;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_010
  | |- sideRLs _ _ ([1;1;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_110
  | |- sideRLs _ _ (ld*>_) _ =>
    ssc segRLs_ld
  | |- sideRLs _ _ (ld^^_*>_) _ =>
    eapply sideRLs_lds
  | |- sideRLs _ _ ([0;1;0]^^_*>_) _ =>
    (eapply sideRLs_010s_v1;[lia|]) ||
    (eapply sideRLs_010s_v2;[lia|])
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

Definition RC i n :=
match i with
| 0%nat => (ld)^^(11+n*6)*>rd1*>ld*>(rd1)^^(3+n*3)*>ld*>rd1*>rd0*>(rd1)^^(5+n*3)*>ld*>rd1*>rd1*>0inf
| 1%nat => (ld)^^(12+n*6)*>rd1*>ld*>(rd1)^^(3+n*3)*>ld*>rd0*>(rd1)^^(6+n*3)*>ld*>rd1*>rd1*>rd0*>rd1*>0inf
| 2 => (ld)^^(13+n*6)*>rd1*>ld*>(rd1)^^(4+n*3)*>ld*>rd1*>rd0*>(rd1)^^(4+n*3)*>ld*>rd1*>rd1*>rd1*>rd0*>rd1*>0inf
| 3 => (ld)^^(14+n*6)*>rd1*>ld*>(rd1)^^(4+n*3)*>ld*>rd0*>(rd1)^^(5+n*3)*>ld*>rd1*>rd0*>rd0*>rd0*>rd1*>rd1*>0inf
| 4 => (ld)^^(15+n*6)*>rd1*>ld*>(rd1)^^(5+n*3)*>ld*>rd1*>rd0*>(rd1)^^(3+n*3)*>ld*>rd0*>rd0*>rd1*>rd0*>rd0*>rd1*>rd1*>0inf
| 5 => (ld)^^(16+n*6)*>rd1*>ld*>(rd1)^^(5+n*3)*>ld*>rd0*>(rd1)^^(6+n*3)*>ld*>rd0*>rd0*>rd0*>rd0*>rd1*>rd1*>0inf
| 6 => (ld)^^(17+n*6)*>rd1*>ld*>(rd1)^^(6+n*3)*>ld*>rd1*>rd0*>(rd1)^^(8+n*3)*>ld*>rd1*>rd1*>0inf
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
  i<6 ->
  sideRLs tm (hRL^^(2^0+0)) ([1;0]*>RC i n) (RC (S i) n).
Proof.
  intro Hn.
  unfold RC.
  do 6
  (destruct i; [solve[sscs']|]).
  lia.
Qed.

Lemma RC_eq n:
  RC 6 n = RC 0 (S n).
Proof.
  unfold RC.
  st; simpl_rotate; reflexivity.
Qed.

Definition S0 '(i,n) := lh {{{ (hL,L) }}} RC i n.

Lemma BigStep i n:
  i<6 ->
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

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (O,O)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(i,n) => i<6).
  2: lia.
  intros [i n] Hi.
  assert (i<5\/i=5) as [E|E] by lia.
  - exists (S i,n); split.
    1: apply BigStep,Hi.
    lia.
  - eexists (O,S n); split; [|lia].
    follow10 (BigStep i n Hi).
    unfold S0.
    rewrite <-RC_eq.
    finish.
Qed.

End TM10.


Module TM11.

Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD1RC_0LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation ld := [1;0;1;0].
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation lh := (0inf<*<[1]).

Notation hR := (C,[0]).
Notation hL := (A,[0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma LOv r:
  lh {{{ (hL,L) }}} r -->*
  lh {{{ (hR,R) }}} [1;0] *> r.
Proof. esx. Qed.


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

Lemma rw_10_ld r:
  [1;0] *> ld *> r = ld *> [1;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_rd0 r:
  [1;0] *> rd0 *> r = rd1 *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_rd1 r:
  [1;0] *> rd1 *> r = ld *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_ld r:
  [0] *> ld *> r = [0;1;0] *> [1;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_rd0 r:
  [0] *> rd0 *> r = rd0 *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_rd1 r:
  [0] *> rd1 *> r = [0;1;0] *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_ld r:
  [0;0] *> ld *> r = [0;0;1;0] *> [1;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd0 r:
  [0;0] *> rd0 *> r = rd0 *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd1 r:
  [0;0] *> rd1 *> r = [0;0;1;0] *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_lds n r:
  [1;0] *> ld^^n *> r = ld^^n *> [1;0] *> r.
Proof.
  simpl_rotate; reflexivity.
Qed.

Lemma rw_0_1s n r:
  [0] *> rd1^^n *> r = [0;1;0]^^n *> [0] *> r.
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
  rewrite rw_10_ld ||
  rewrite rw_10_rd0 ||
  rewrite rw_10_rd1 ||
  rewrite rw_10_lds ||
  rewrite rw_10_0inf ||
  rewrite rw_0_ld ||
  rewrite rw_0_rd0 ||
  rewrite rw_0_rd1 ||
  rewrite rw_0_1s ||
  rewrite rw_0_0inf ||
  rewrite rw_00_ld ||
  rewrite rw_00_rd0 ||
  rewrite rw_00_rd1 ||
  rewrite rw_00_0inf).

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

Lemma hRL_110 n r r':
  sideRLs tm (hRL^^n) (rd1*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([1;1;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma hRL_010 n r r':
  sideRLs tm (hRL^^n) ([1;1;0]*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;1;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma hRL_0010 n r r':
  sideRLs tm (hRL^^n) (ld*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;0;1;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma sideRLs_010s k n r r':
  1<=k ->
  sideRLs tm (hRL^^(2^k-2)) r r' ->
  sideRLs tm (hRL^^(2^(k+n)-2)) ([0;1;0]^^n*>r) (rd1^^n*>r').
Proof.
  intros.
  rewrite (Nat.pow_le_mono_r_iff 2) in H by lia.
  induction n.
  - applys_eq H0; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    rewrite <-(Nat.add_1_r n).
    applys_eq (segRLs_addmul_v2 2 1 2 0 (2^(k+n)-2)); rw_pa; flia; ss.
Qed.

Lemma sideRLs_010s_v1 c n r r':
  1<=c ->
  sideRLs tm (hRL^^(2^(n*3+c)-2)) r r' ->
  sideRLs tm (hRL^^(2^(n*6+c)-2)) ([0;1;0]^^(n*3)*>r) (rd1^^(n*3)*>r').
Proof.
  replace (n*6+c) with (n*3+c+n*3) by lia.
  intros.
  apply sideRLs_010s; [lia|assumption].
Qed.

Lemma sideRLs_010s_v2 c n r r':
  1<=c ->
  sideRLs tm (hRL^^(2^c-2)) r r' ->
  sideRLs tm (hRL^^(2^(n*3+c)-2)) ([0;1;0]^^(n*3)*>r) (rd1^^(n*3)*>r').
Proof.
  replace (n*3+c) with (c+n*3) by lia.
  intros.
  apply sideRLs_010s; [lia|assumption].
Qed.


Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- ?G => idtac G
  end;
  match goal with
  | |- sideRLs _ (_^^O) _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ _ ([0;0;1;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_0010
  | |- sideRLs _ _ ([0;1;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_010
  | |- sideRLs _ _ ([1;1;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_110
  | |- sideRLs _ _ (ld*>_) _ =>
    ssc segRLs_ld
  | |- sideRLs _ _ (ld^^_*>_) _ =>
    eapply sideRLs_lds
  | |- sideRLs _ _ ([0;1;0]^^_*>_) _ =>
    (eapply sideRLs_010s_v1;[lia|]) ||
    (eapply sideRLs_010s_v2;[lia|])
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

Definition RC i n :=
match i with
| 0%nat => (ld)^^(11+n*6)*>rd1*>ld*>(rd1)^^(3+n*3)*>ld*>rd1*>rd0*>(rd1)^^(5+n*3)*>ld*>rd1*>rd1*>0inf
| 1%nat => (ld)^^(12+n*6)*>rd1*>ld*>(rd1)^^(3+n*3)*>ld*>rd0*>(rd1)^^(6+n*3)*>ld*>rd1*>rd1*>rd0*>rd1*>0inf
| 2 => (ld)^^(13+n*6)*>rd1*>ld*>(rd1)^^(4+n*3)*>ld*>rd1*>rd0*>(rd1)^^(4+n*3)*>ld*>rd1*>rd1*>rd1*>rd0*>rd1*>0inf
| 3 => (ld)^^(14+n*6)*>rd1*>ld*>(rd1)^^(4+n*3)*>ld*>rd0*>(rd1)^^(5+n*3)*>ld*>rd1*>rd0*>rd0*>rd0*>rd1*>rd1*>0inf
| 4 => (ld)^^(15+n*6)*>rd1*>ld*>(rd1)^^(5+n*3)*>ld*>rd1*>rd0*>(rd1)^^(3+n*3)*>ld*>rd0*>rd0*>rd1*>rd0*>rd0*>rd1*>rd1*>0inf
| 5 => (ld)^^(16+n*6)*>rd1*>ld*>(rd1)^^(5+n*3)*>ld*>rd0*>(rd1)^^(6+n*3)*>ld*>rd0*>rd0*>rd0*>rd0*>rd1*>rd1*>0inf
| 6 => (ld)^^(17+n*6)*>rd1*>ld*>(rd1)^^(6+n*3)*>ld*>rd1*>rd0*>(rd1)^^(8+n*3)*>ld*>rd1*>rd1*>0inf
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
  i<6 ->
  sideRLs tm (hRL^^(2^0+0)) ([1;0]*>RC i n) (RC (S i) n).
Proof.
  intro Hn.
  unfold RC.
  do 6
  (destruct i; [solve[sscs']|]).
  lia.
Qed.

Lemma RC_eq n:
  RC 6 n = RC 0 (S n).
Proof.
  unfold RC.
  st; simpl_rotate; reflexivity.
Qed.

Definition S0 '(i,n) := lh {{{ (hL,L) }}} RC i n.

Lemma BigStep i n:
  i<6 ->
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

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (O,O)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(i,n) => i<6).
  2: lia.
  intros [i n] Hi.
  assert (i<5\/i=5) as [E|E] by lia.
  - exists (S i,n); split.
    1: apply BigStep,Hi.
    lia.
  - eexists (O,S n); split; [|lia].
    follow10 (BigStep i n Hi).
    unfold S0.
    rewrite <-RC_eq.
    finish.
Qed.

End TM11.


Module TM12.

Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LA_0RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation ld := [1;0;1;0].
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation lh := (0inf<*<[1]).

Notation hR := (C,[0]).
Notation hL := (A,[0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma LOv r:
  lh {{{ (hL,L) }}} r -->*
  lh {{{ (hR,R) }}} [1;0] *> r.
Proof. esx. Qed.


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

Lemma rw_10_ld r:
  [1;0] *> ld *> r = ld *> [1;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_rd0 r:
  [1;0] *> rd0 *> r = rd1 *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_rd1 r:
  [1;0] *> rd1 *> r = ld *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_ld r:
  [0] *> ld *> r = [0;1;0] *> [1;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_rd0 r:
  [0] *> rd0 *> r = rd0 *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_rd1 r:
  [0] *> rd1 *> r = [0;1;0] *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_ld r:
  [0;0] *> ld *> r = [0;0;1;0] *> [1;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd0 r:
  [0;0] *> rd0 *> r = rd0 *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd1 r:
  [0;0] *> rd1 *> r = [0;0;1;0] *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_lds n r:
  [1;0] *> ld^^n *> r = ld^^n *> [1;0] *> r.
Proof.
  simpl_rotate; reflexivity.
Qed.

Lemma rw_0_1s n r:
  [0] *> rd1^^n *> r = [0;1;0]^^n *> [0] *> r.
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
  rewrite rw_10_ld ||
  rewrite rw_10_rd0 ||
  rewrite rw_10_rd1 ||
  rewrite rw_10_lds ||
  rewrite rw_10_0inf ||
  rewrite rw_0_ld ||
  rewrite rw_0_rd0 ||
  rewrite rw_0_rd1 ||
  rewrite rw_0_1s ||
  rewrite rw_0_0inf ||
  rewrite rw_00_ld ||
  rewrite rw_00_rd0 ||
  rewrite rw_00_rd1 ||
  rewrite rw_00_0inf).

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

Lemma hRL_110 n r r':
  sideRLs tm (hRL^^n) (rd1*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([1;1;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma hRL_010 n r r':
  sideRLs tm (hRL^^n) ([1;1;0]*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;1;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma hRL_0010 n r r':
  sideRLs tm (hRL^^n) (ld*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;0;1;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma sideRLs_010s k n r r':
  1<=k ->
  sideRLs tm (hRL^^(2^k-2)) r r' ->
  sideRLs tm (hRL^^(2^(k+n)-2)) ([0;1;0]^^n*>r) (rd1^^n*>r').
Proof.
  intros.
  rewrite (Nat.pow_le_mono_r_iff 2) in H by lia.
  induction n.
  - applys_eq H0; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    rewrite <-(Nat.add_1_r n).
    applys_eq (segRLs_addmul_v2 2 1 2 0 (2^(k+n)-2)); rw_pa; flia; ss.
Qed.

Lemma sideRLs_010s_v1 c n r r':
  1<=c ->
  sideRLs tm (hRL^^(2^(n*3+c)-2)) r r' ->
  sideRLs tm (hRL^^(2^(n*6+c)-2)) ([0;1;0]^^(n*3)*>r) (rd1^^(n*3)*>r').
Proof.
  replace (n*6+c) with (n*3+c+n*3) by lia.
  intros.
  apply sideRLs_010s; [lia|assumption].
Qed.

Lemma sideRLs_010s_v2 c n r r':
  1<=c ->
  sideRLs tm (hRL^^(2^c-2)) r r' ->
  sideRLs tm (hRL^^(2^(n*3+c)-2)) ([0;1;0]^^(n*3)*>r) (rd1^^(n*3)*>r').
Proof.
  replace (n*3+c) with (c+n*3) by lia.
  intros.
  apply sideRLs_010s; [lia|assumption].
Qed.


Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- ?G => idtac G
  end;
  match goal with
  | |- sideRLs _ (_^^O) _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ _ ([0;0;1;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_0010
  | |- sideRLs _ _ ([0;1;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_010
  | |- sideRLs _ _ ([1;1;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_110
  | |- sideRLs _ _ (ld*>_) _ =>
    ssc segRLs_ld
  | |- sideRLs _ _ (ld^^_*>_) _ =>
    eapply sideRLs_lds
  | |- sideRLs _ _ ([0;1;0]^^_*>_) _ =>
    (eapply sideRLs_010s_v1;[lia|]) ||
    (eapply sideRLs_010s_v2;[lia|])
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

Definition RC i n :=
match i with
| 0%nat => (ld)^^(11+n*6)*>rd1*>ld*>(rd1)^^(3+n*3)*>ld*>rd1*>rd0*>(rd1)^^(5+n*3)*>ld*>rd1*>rd1*>0inf
| 1%nat => (ld)^^(12+n*6)*>rd1*>ld*>(rd1)^^(3+n*3)*>ld*>rd0*>(rd1)^^(6+n*3)*>ld*>rd1*>rd1*>rd0*>rd1*>0inf
| 2 => (ld)^^(13+n*6)*>rd1*>ld*>(rd1)^^(4+n*3)*>ld*>rd1*>rd0*>(rd1)^^(4+n*3)*>ld*>rd1*>rd1*>rd1*>rd0*>rd1*>0inf
| 3 => (ld)^^(14+n*6)*>rd1*>ld*>(rd1)^^(4+n*3)*>ld*>rd0*>(rd1)^^(5+n*3)*>ld*>rd1*>rd0*>rd0*>rd0*>rd1*>rd1*>0inf
| 4 => (ld)^^(15+n*6)*>rd1*>ld*>(rd1)^^(5+n*3)*>ld*>rd1*>rd0*>(rd1)^^(3+n*3)*>ld*>rd0*>rd0*>rd1*>rd0*>rd0*>rd1*>rd1*>0inf
| 5 => (ld)^^(16+n*6)*>rd1*>ld*>(rd1)^^(5+n*3)*>ld*>rd0*>(rd1)^^(6+n*3)*>ld*>rd0*>rd0*>rd0*>rd0*>rd1*>rd1*>0inf
| 6 => (ld)^^(17+n*6)*>rd1*>ld*>(rd1)^^(6+n*3)*>ld*>rd1*>rd0*>(rd1)^^(8+n*3)*>ld*>rd1*>rd1*>0inf
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
  i<6 ->
  sideRLs tm (hRL^^(2^0+0)) ([1;0]*>RC i n) (RC (S i) n).
Proof.
  intro Hn.
  unfold RC.
  do 6
  (destruct i; [solve[sscs']|]).
  lia.
Qed.

Lemma RC_eq n:
  RC 6 n = RC 0 (S n).
Proof.
  unfold RC.
  st; simpl_rotate; reflexivity.
Qed.

Definition S0 '(i,n) := lh {{{ (hL,L) }}} RC i n.

Lemma BigStep i n:
  i<6 ->
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

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (O,O)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(i,n) => i<6).
  2: lia.
  intros [i n] Hi.
  assert (i<5\/i=5) as [E|E] by lia.
  - exists (S i,n); split.
    1: apply BigStep,Hi.
    lia.
  - eexists (O,S n); split; [|lia].
    follow10 (BigStep i n Hi).
    unfold S0.
    rewrite <-RC_eq.
    finish.
Qed.

End TM12.


Module TM13.

Definition tm := Eval compute in (TM_from_str "1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation ld := [1;0;1;0].
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation lh := (0inf<*<[1]).

Notation hR := (C,[0]).
Notation hL := (A,[0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma LOv r:
  lh {{{ (hL,L) }}} r -->*
  lh {{{ (hR,R) }}} [1;0] *> r.
Proof. esx. Qed.


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

Lemma rw_10_ld r:
  [1;0] *> ld *> r = ld *> [1;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_rd0 r:
  [1;0] *> rd0 *> r = rd1 *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_rd1 r:
  [1;0] *> rd1 *> r = ld *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_ld r:
  [0] *> ld *> r = [0;1;0] *> [1;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_rd0 r:
  [0] *> rd0 *> r = rd0 *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_rd1 r:
  [0] *> rd1 *> r = [0;1;0] *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_ld r:
  [0;0] *> ld *> r = [0;0;1;0] *> [1;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd0 r:
  [0;0] *> rd0 *> r = rd0 *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd1 r:
  [0;0] *> rd1 *> r = [0;0;1;0] *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_lds n r:
  [1;0] *> ld^^n *> r = ld^^n *> [1;0] *> r.
Proof.
  simpl_rotate; reflexivity.
Qed.

Lemma rw_0_1s n r:
  [0] *> rd1^^n *> r = [0;1;0]^^n *> [0] *> r.
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
  rewrite rw_10_ld ||
  rewrite rw_10_rd0 ||
  rewrite rw_10_rd1 ||
  rewrite rw_10_lds ||
  rewrite rw_10_0inf ||
  rewrite rw_0_ld ||
  rewrite rw_0_rd0 ||
  rewrite rw_0_rd1 ||
  rewrite rw_0_1s ||
  rewrite rw_0_0inf ||
  rewrite rw_00_ld ||
  rewrite rw_00_rd0 ||
  rewrite rw_00_rd1 ||
  rewrite rw_00_0inf).

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

Lemma hRL_110 n r r':
  sideRLs tm (hRL^^n) (rd1*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([1;1;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma hRL_010 n r r':
  sideRLs tm (hRL^^n) ([1;1;0]*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;1;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma hRL_0010 n r r':
  sideRLs tm (hRL^^n) (ld*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;0;1;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma sideRLs_010s k n r r':
  1<=k ->
  sideRLs tm (hRL^^(2^k-2)) r r' ->
  sideRLs tm (hRL^^(2^(k+n)-2)) ([0;1;0]^^n*>r) (rd1^^n*>r').
Proof.
  intros.
  rewrite (Nat.pow_le_mono_r_iff 2) in H by lia.
  induction n.
  - applys_eq H0; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    rewrite <-(Nat.add_1_r n).
    applys_eq (segRLs_addmul_v2 2 1 2 0 (2^(k+n)-2)); rw_pa; flia; ss.
Qed.

Lemma sideRLs_010s_v1 c n r r':
  1<=c ->
  sideRLs tm (hRL^^(2^(n*3+c)-2)) r r' ->
  sideRLs tm (hRL^^(2^(n*6+c)-2)) ([0;1;0]^^(n*3)*>r) (rd1^^(n*3)*>r').
Proof.
  replace (n*6+c) with (n*3+c+n*3) by lia.
  intros.
  apply sideRLs_010s; [lia|assumption].
Qed.

Lemma sideRLs_010s_v2 c n r r':
  1<=c ->
  sideRLs tm (hRL^^(2^c-2)) r r' ->
  sideRLs tm (hRL^^(2^(n*3+c)-2)) ([0;1;0]^^(n*3)*>r) (rd1^^(n*3)*>r').
Proof.
  replace (n*3+c) with (c+n*3) by lia.
  intros.
  apply sideRLs_010s; [lia|assumption].
Qed.


Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- ?G => idtac G
  end;
  match goal with
  | |- sideRLs _ (_^^O) _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ _ ([0;0;1;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_0010
  | |- sideRLs _ _ ([0;1;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_010
  | |- sideRLs _ _ ([1;1;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_110
  | |- sideRLs _ _ (ld*>_) _ =>
    ssc segRLs_ld
  | |- sideRLs _ _ (ld^^_*>_) _ =>
    eapply sideRLs_lds
  | |- sideRLs _ _ ([0;1;0]^^_*>_) _ =>
    (eapply sideRLs_010s_v1;[lia|]) ||
    (eapply sideRLs_010s_v2;[lia|])
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

Definition RC i n :=
match i with
| 0%nat => (ld)^^(11+n*6)*>rd1*>ld*>(rd1)^^(3+n*3)*>ld*>rd1*>rd0*>(rd1)^^(5+n*3)*>ld*>rd1*>rd1*>0inf
| 1%nat => (ld)^^(12+n*6)*>rd1*>ld*>(rd1)^^(3+n*3)*>ld*>rd0*>(rd1)^^(6+n*3)*>ld*>rd1*>rd1*>rd0*>rd1*>0inf
| 2 => (ld)^^(13+n*6)*>rd1*>ld*>(rd1)^^(4+n*3)*>ld*>rd1*>rd0*>(rd1)^^(4+n*3)*>ld*>rd1*>rd1*>rd1*>rd0*>rd1*>0inf
| 3 => (ld)^^(14+n*6)*>rd1*>ld*>(rd1)^^(4+n*3)*>ld*>rd0*>(rd1)^^(5+n*3)*>ld*>rd1*>rd0*>rd0*>rd0*>rd1*>rd1*>0inf
| 4 => (ld)^^(15+n*6)*>rd1*>ld*>(rd1)^^(5+n*3)*>ld*>rd1*>rd0*>(rd1)^^(3+n*3)*>ld*>rd0*>rd0*>rd1*>rd0*>rd0*>rd1*>rd1*>0inf
| 5 => (ld)^^(16+n*6)*>rd1*>ld*>(rd1)^^(5+n*3)*>ld*>rd0*>(rd1)^^(6+n*3)*>ld*>rd0*>rd0*>rd0*>rd0*>rd1*>rd1*>0inf
| 6 => (ld)^^(17+n*6)*>rd1*>ld*>(rd1)^^(6+n*3)*>ld*>rd1*>rd0*>(rd1)^^(8+n*3)*>ld*>rd1*>rd1*>0inf
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
  i<6 ->
  sideRLs tm (hRL^^(2^0+0)) ([1;0]*>RC i n) (RC (S i) n).
Proof.
  intro Hn.
  unfold RC.
  do 6
  (destruct i; [solve[sscs']|]).
  lia.
Qed.

Lemma RC_eq n:
  RC 6 n = RC 0 (S n).
Proof.
  unfold RC.
  st; simpl_rotate; reflexivity.
Qed.

Definition S0 '(i,n) := lh {{{ (hL,L) }}} RC i n.

Lemma BigStep i n:
  i<6 ->
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

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (O,O)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(i,n) => i<6).
  2: lia.
  intros [i n] Hi.
  assert (i<5\/i=5) as [E|E] by lia.
  - exists (S i,n); split.
    1: apply BigStep,Hi.
    lia.
  - eexists (O,S n); split; [|lia].
    follow10 (BigStep i n Hi).
    unfold S0.
    rewrite <-RC_eq.
    finish.
Qed.

End TM13.


Module TM14.

Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD0RF_0LD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation ld := [1;0;1;0].
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation lh := (0inf<*<[1]).

Notation hR := (C,[0]).
Notation hL := (A,[0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma LOv r:
  lh {{{ (hL,L) }}} r -->*
  lh {{{ (hR,R) }}} [1;0] *> r.
Proof. esx. Qed.


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

Lemma rw_10_ld r:
  [1;0] *> ld *> r = ld *> [1;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_rd0 r:
  [1;0] *> rd0 *> r = rd1 *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_rd1 r:
  [1;0] *> rd1 *> r = ld *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_ld r:
  [0] *> ld *> r = [0;1;0] *> [1;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_rd0 r:
  [0] *> rd0 *> r = rd0 *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_rd1 r:
  [0] *> rd1 *> r = [0;1;0] *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_ld r:
  [0;0] *> ld *> r = [0;0;1;0] *> [1;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd0 r:
  [0;0] *> rd0 *> r = rd0 *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd1 r:
  [0;0] *> rd1 *> r = [0;0;1;0] *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_lds n r:
  [1;0] *> ld^^n *> r = ld^^n *> [1;0] *> r.
Proof.
  simpl_rotate; reflexivity.
Qed.

Lemma rw_0_1s n r:
  [0] *> rd1^^n *> r = [0;1;0]^^n *> [0] *> r.
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
  rewrite rw_10_ld ||
  rewrite rw_10_rd0 ||
  rewrite rw_10_rd1 ||
  rewrite rw_10_lds ||
  rewrite rw_10_0inf ||
  rewrite rw_0_ld ||
  rewrite rw_0_rd0 ||
  rewrite rw_0_rd1 ||
  rewrite rw_0_1s ||
  rewrite rw_0_0inf ||
  rewrite rw_00_ld ||
  rewrite rw_00_rd0 ||
  rewrite rw_00_rd1 ||
  rewrite rw_00_0inf).

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

Lemma hRL_110 n r r':
  sideRLs tm (hRL^^n) (rd1*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([1;1;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma hRL_010 n r r':
  sideRLs tm (hRL^^n) ([1;1;0]*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;1;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma hRL_0010 n r r':
  sideRLs tm (hRL^^n) (ld*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;0;1;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma sideRLs_010s k n r r':
  1<=k ->
  sideRLs tm (hRL^^(2^k-2)) r r' ->
  sideRLs tm (hRL^^(2^(k+n)-2)) ([0;1;0]^^n*>r) (rd1^^n*>r').
Proof.
  intros.
  rewrite (Nat.pow_le_mono_r_iff 2) in H by lia.
  induction n.
  - applys_eq H0; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    rewrite <-(Nat.add_1_r n).
    applys_eq (segRLs_addmul_v2 2 1 2 0 (2^(k+n)-2)); rw_pa; flia; ss.
Qed.

Lemma sideRLs_010s_v1 c n r r':
  1<=c ->
  sideRLs tm (hRL^^(2^(n*3+c)-2)) r r' ->
  sideRLs tm (hRL^^(2^(n*6+c)-2)) ([0;1;0]^^(n*3)*>r) (rd1^^(n*3)*>r').
Proof.
  replace (n*6+c) with (n*3+c+n*3) by lia.
  intros.
  apply sideRLs_010s; [lia|assumption].
Qed.

Lemma sideRLs_010s_v2 c n r r':
  1<=c ->
  sideRLs tm (hRL^^(2^c-2)) r r' ->
  sideRLs tm (hRL^^(2^(n*3+c)-2)) ([0;1;0]^^(n*3)*>r) (rd1^^(n*3)*>r').
Proof.
  replace (n*3+c) with (c+n*3) by lia.
  intros.
  apply sideRLs_010s; [lia|assumption].
Qed.


Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- ?G => idtac G
  end;
  match goal with
  | |- sideRLs _ (_^^O) _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ _ ([0;0;1;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_0010
  | |- sideRLs _ _ ([0;1;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_010
  | |- sideRLs _ _ ([1;1;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_110
  | |- sideRLs _ _ (ld*>_) _ =>
    ssc segRLs_ld
  | |- sideRLs _ _ (ld^^_*>_) _ =>
    eapply sideRLs_lds
  | |- sideRLs _ _ ([0;1;0]^^_*>_) _ =>
    (eapply sideRLs_010s_v1;[lia|]) ||
    (eapply sideRLs_010s_v2;[lia|])
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

Definition RC i n :=
match i with
| 0%nat => (ld)^^(11+n*6)*>rd1*>ld*>(rd1)^^(3+n*3)*>ld*>rd1*>rd0*>(rd1)^^(5+n*3)*>ld*>rd1*>rd1*>0inf
| 1%nat => (ld)^^(12+n*6)*>rd1*>ld*>(rd1)^^(3+n*3)*>ld*>rd0*>(rd1)^^(6+n*3)*>ld*>rd1*>rd1*>rd0*>rd1*>0inf
| 2 => (ld)^^(13+n*6)*>rd1*>ld*>(rd1)^^(4+n*3)*>ld*>rd1*>rd0*>(rd1)^^(4+n*3)*>ld*>rd1*>rd1*>rd1*>rd0*>rd1*>0inf
| 3 => (ld)^^(14+n*6)*>rd1*>ld*>(rd1)^^(4+n*3)*>ld*>rd0*>(rd1)^^(5+n*3)*>ld*>rd1*>rd0*>rd0*>rd0*>rd1*>rd1*>0inf
| 4 => (ld)^^(15+n*6)*>rd1*>ld*>(rd1)^^(5+n*3)*>ld*>rd1*>rd0*>(rd1)^^(3+n*3)*>ld*>rd0*>rd0*>rd1*>rd0*>rd0*>rd1*>rd1*>0inf
| 5 => (ld)^^(16+n*6)*>rd1*>ld*>(rd1)^^(5+n*3)*>ld*>rd0*>(rd1)^^(6+n*3)*>ld*>rd0*>rd0*>rd0*>rd0*>rd1*>rd1*>0inf
| 6 => (ld)^^(17+n*6)*>rd1*>ld*>(rd1)^^(6+n*3)*>ld*>rd1*>rd0*>(rd1)^^(8+n*3)*>ld*>rd1*>rd1*>0inf
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
  i<6 ->
  sideRLs tm (hRL^^(2^0+0)) ([1;0]*>RC i n) (RC (S i) n).
Proof.
  intro Hn.
  unfold RC.
  do 6
  (destruct i; [solve[sscs']|]).
  lia.
Qed.

Lemma RC_eq n:
  RC 6 n = RC 0 (S n).
Proof.
  unfold RC.
  st; simpl_rotate; reflexivity.
Qed.

Definition S0 '(i,n) := lh {{{ (hL,L) }}} RC i n.

Lemma BigStep i n:
  i<6 ->
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

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (O,O)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(i,n) => i<6).
  2: lia.
  intros [i n] Hi.
  assert (i<5\/i=5) as [E|E] by lia.
  - exists (S i,n); split.
    1: apply BigStep,Hi.
    lia.
  - eexists (O,S n); split; [|lia].
    follow10 (BigStep i n Hi).
    unfold S0.
    rewrite <-RC_eq.
    finish.
Qed.

End TM14.


Module TM15.

Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation ld := [1;0;1;0].
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation lh := (0inf<*<[1]).

Notation hR := (C,[0]).
Notation hL := (A,[0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma LOv r:
  lh {{{ (hL,L) }}} r -->*
  lh {{{ (hR,R) }}} [1;0] *> r.
Proof. esx. Qed.


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

Lemma rw_10_ld r:
  [1;0] *> ld *> r = ld *> [1;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_rd0 r:
  [1;0] *> rd0 *> r = rd1 *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_rd1 r:
  [1;0] *> rd1 *> r = ld *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_ld r:
  [0] *> ld *> r = [0;1;0] *> [1;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_rd0 r:
  [0] *> rd0 *> r = rd0 *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0_rd1 r:
  [0] *> rd1 *> r = [0;1;0] *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_ld r:
  [0;0] *> ld *> r = [0;0;1;0] *> [1;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd0 r:
  [0;0] *> rd0 *> r = rd0 *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd1 r:
  [0;0] *> rd1 *> r = [0;0;1;0] *> [0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_lds n r:
  [1;0] *> ld^^n *> r = ld^^n *> [1;0] *> r.
Proof.
  simpl_rotate; reflexivity.
Qed.

Lemma rw_0_1s n r:
  [0] *> rd1^^n *> r = [0;1;0]^^n *> [0] *> r.
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
  rewrite rw_10_ld ||
  rewrite rw_10_rd0 ||
  rewrite rw_10_rd1 ||
  rewrite rw_10_lds ||
  rewrite rw_10_0inf ||
  rewrite rw_0_ld ||
  rewrite rw_0_rd0 ||
  rewrite rw_0_rd1 ||
  rewrite rw_0_1s ||
  rewrite rw_0_0inf ||
  rewrite rw_00_ld ||
  rewrite rw_00_rd0 ||
  rewrite rw_00_rd1 ||
  rewrite rw_00_0inf).

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

Lemma hRL_110 n r r':
  sideRLs tm (hRL^^n) (rd1*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([1;1;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma hRL_010 n r r':
  sideRLs tm (hRL^^n) ([1;1;0]*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;1;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma hRL_0010 n r r':
  sideRLs tm (hRL^^n) (ld*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([0;0;1;0]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma sideRLs_010s k n r r':
  1<=k ->
  sideRLs tm (hRL^^(2^k-2)) r r' ->
  sideRLs tm (hRL^^(2^(k+n)-2)) ([0;1;0]^^n*>r) (rd1^^n*>r').
Proof.
  intros.
  rewrite (Nat.pow_le_mono_r_iff 2) in H by lia.
  induction n.
  - applys_eq H0; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    rewrite <-(Nat.add_1_r n).
    applys_eq (segRLs_addmul_v2 2 1 2 0 (2^(k+n)-2)); rw_pa; flia; ss.
Qed.

Lemma sideRLs_010s_v1 c n r r':
  1<=c ->
  sideRLs tm (hRL^^(2^(n*3+c)-2)) r r' ->
  sideRLs tm (hRL^^(2^(n*6+c)-2)) ([0;1;0]^^(n*3)*>r) (rd1^^(n*3)*>r').
Proof.
  replace (n*6+c) with (n*3+c+n*3) by lia.
  intros.
  apply sideRLs_010s; [lia|assumption].
Qed.

Lemma sideRLs_010s_v2 c n r r':
  1<=c ->
  sideRLs tm (hRL^^(2^c-2)) r r' ->
  sideRLs tm (hRL^^(2^(n*3+c)-2)) ([0;1;0]^^(n*3)*>r) (rd1^^(n*3)*>r').
Proof.
  replace (n*3+c) with (c+n*3) by lia.
  intros.
  apply sideRLs_010s; [lia|assumption].
Qed.


Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- ?G => idtac G
  end;
  match goal with
  | |- sideRLs _ (_^^O) _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ _ ([0;0;1;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_0010
  | |- sideRLs _ _ ([0;1;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_010
  | |- sideRLs _ _ ([1;1;0]*>_) _ =>
    R_sub 1%nat; eapply hRL_110
  | |- sideRLs _ _ (ld*>_) _ =>
    ssc segRLs_ld
  | |- sideRLs _ _ (ld^^_*>_) _ =>
    eapply sideRLs_lds
  | |- sideRLs _ _ ([0;1;0]^^_*>_) _ =>
    (eapply sideRLs_010s_v1;[lia|]) ||
    (eapply sideRLs_010s_v2;[lia|])
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

Definition RC i n :=
match i with
| 0%nat => (ld)^^(11+n*6)*>rd1*>ld*>(rd1)^^(3+n*3)*>ld*>rd1*>rd0*>(rd1)^^(5+n*3)*>ld*>rd1*>rd1*>0inf
| 1%nat => (ld)^^(12+n*6)*>rd1*>ld*>(rd1)^^(3+n*3)*>ld*>rd0*>(rd1)^^(6+n*3)*>ld*>rd1*>rd1*>rd0*>rd1*>0inf
| 2 => (ld)^^(13+n*6)*>rd1*>ld*>(rd1)^^(4+n*3)*>ld*>rd1*>rd0*>(rd1)^^(4+n*3)*>ld*>rd1*>rd1*>rd1*>rd0*>rd1*>0inf
| 3 => (ld)^^(14+n*6)*>rd1*>ld*>(rd1)^^(4+n*3)*>ld*>rd0*>(rd1)^^(5+n*3)*>ld*>rd1*>rd0*>rd0*>rd0*>rd1*>rd1*>0inf
| 4 => (ld)^^(15+n*6)*>rd1*>ld*>(rd1)^^(5+n*3)*>ld*>rd1*>rd0*>(rd1)^^(3+n*3)*>ld*>rd0*>rd0*>rd1*>rd0*>rd0*>rd1*>rd1*>0inf
| 5 => (ld)^^(16+n*6)*>rd1*>ld*>(rd1)^^(5+n*3)*>ld*>rd0*>(rd1)^^(6+n*3)*>ld*>rd0*>rd0*>rd0*>rd0*>rd1*>rd1*>0inf
| 6 => (ld)^^(17+n*6)*>rd1*>ld*>(rd1)^^(6+n*3)*>ld*>rd1*>rd0*>(rd1)^^(8+n*3)*>ld*>rd1*>rd1*>0inf
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
  i<6 ->
  sideRLs tm (hRL^^(2^0+0)) ([1;0]*>RC i n) (RC (S i) n).
Proof.
  intro Hn.
  unfold RC.
  do 6
  (destruct i; [solve[sscs']|]).
  lia.
Qed.

Lemma RC_eq n:
  RC 6 n = RC 0 (S n).
Proof.
  unfold RC.
  st; simpl_rotate; reflexivity.
Qed.

Definition S0 '(i,n) := lh {{{ (hL,L) }}} RC i n.

Lemma BigStep i n:
  i<6 ->
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

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (O,O)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(i,n) => i<6).
  2: lia.
  intros [i n] Hi.
  assert (i<5\/i=5) as [E|E] by lia.
  - exists (S i,n); split.
    1: apply BigStep,Hi.
    lia.
  - eexists (O,S n); split; [|lia].
    follow10 (BigStep i n Hi).
    unfold S0.
    rewrite <-RC_eq.
    finish.
Qed.

End TM15.


Module TM16.

Definition tm := Eval compute in (TM_from_str "1RB0LE_0RC0RF_0LD0RD_1LA0LA_0LC0RB_0RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation ld := [1;0;0;0;1;0;0;0].
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation lh := (0inf<*<[1;0;0;0;0]).
Notation lh0 := (0inf<*<[1;0;0;1;0]).

Notation hR := (B,[1;0;0;1]).
Notation hL := (A,[0;0;0;0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma LOv r:
  lh {{{ (hL,L) }}} r -->*
  lh0 {{{ (hR,R) }}} [1;0;0;0] *> r.
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
Lemma rw_1000_ld r:
  [1;0;0;0] *> [1;0;0;0;1;0;0;0] *> r = [1;0;0;0;1;0;0;0] *> [1;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_1000_rd0 r:
  [1;0;0;0] *> [0;0;0] *> r = [1;0;0] *> [0;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_1000_rd1 r:
  [1;0;0;0] *> [1;0;0] *> r = [1;0;0;0;1;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0000_ld r:
  [0;0;0;0] *> [1;0;0;0;1;0;0;0] *> r = [0;0;0;0;1;0;0;0] *> [1;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0000_rd0 r:
  [0;0;0;0] *> [0;0;0] *> r = [0;0;0] *> [0;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0000_rd1 r:
  [0;0;0;0] *> [1;0;0] *> r = [0;0;0;0;1;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_1000100_ld r:
  [1;0;0;0;1;0;0] *> [1;0;0;0;1;0;0;0] *> r = [1;0;0;0;1;0;0;1] *> [0;0;0] *> [1;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_1000100_rd0 r:
  [1;0;0;0;1;0;0] *> [0;0;0] *> r = [1;0;0;0;1;0;0;0] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_1000100_rd1 r:
  [1;0;0;0;1;0;0] *> [1;0;0] *> r = [1;0;0;0;1;0;0;1] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0000100_ld r:
  [0;0;0;0;1;0;0] *> [1;0;0;0;1;0;0;0] *> r = [0;0;0;0;1;0;0;1] *> [0;0;0] *> [1;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0000100_rd0 r:
  [0;0;0;0;1;0;0] *> [0;0;0] *> r = [0;0;0;0;1;0;0;0] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0000100_rd1 r:
  [0;0;0;0;1;0;0] *> [1;0;0] *> r = [0;0;0;0;1;0;0;1] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_ld r:
  [1;0] *> [1;0;0;0;1;0;0;0] *> r = [1;0;1] *> [0;0;0] *> [1;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_rd0 r:
  [1;0] *> [0;0;0] *> r = [1;0;0] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_rd1 r:
  [1;0] *> [1;0;0] *> r = [1;0;1] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_ld r:
  [0;0] *> [1;0;0;0;1;0;0;0] *> r = [0;0;1] *> [0;0;0] *> [1;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd0 r:
  [0;0] *> [0;0;0] *> r = [0;0;0] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd1 r:
  [0;0] *> [1;0;0] *> r = [0;0;1] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_1000_lds n r:
  [1;0;0;0] *> ld^^n *> r = ld^^n *> [1;0;0;0] *> r.
Proof.
  simpl_rotate; reflexivity.
Qed.

Lemma rw_00_rd1s n r:
  [0;0] *> rd1^^n *> r = [0;0;1]^^n *> [0;0] *> r.
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
  rewrite rw_1000_ld ||
  rewrite rw_1000_rd0 ||
  rewrite rw_1000_rd1 ||
  rewrite rw_0000_ld ||
  rewrite rw_0000_rd0 ||
  rewrite rw_0000_rd1 ||
  rewrite rw_1000100_ld ||
  rewrite rw_1000100_rd0 ||
  rewrite rw_1000100_rd1 ||
  rewrite rw_0000100_ld ||
  rewrite rw_0000100_rd0 ||
  rewrite rw_0000100_rd1 ||
  rewrite rw_10_ld ||
  rewrite rw_10_rd0 ||
  rewrite rw_10_rd1 ||
  rewrite rw_00_ld ||
  rewrite rw_00_rd0 ||
  rewrite rw_00_rd1 ||
  rewrite rw_1000_lds ||
  rewrite rw_00_rd1s).

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

Lemma hRL_00 n s r r':
  sideRLs tm (hRL^^n) ((1::0::s)*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ((0::0::s)*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma hRL_101 n r r':
  sideRLs tm (hRL^^n) (rd0*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([1;0;1]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma hRL_10001001 n r r' r0:
  sideRLs tm (hRL^^1) r r0 ->
  sideRLs tm (hRL^^n) (ld*>r0) r' ->
  sideRLs tm (hRL^^(n+1)) ([1;0;0;0;1;0;0;1]*>r) r'.
Proof.
  intros H H0.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H0.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  esx.
Qed.

Lemma sideRLs_001s k n r r':
  2<=k ->
  sideRLs tm (hRL^^(2^k-3)) r r' ->
  sideRLs tm (hRL^^(2^(k+n)-3)) ([0;0;1]^^n*>r) (rd1^^n*>r').
Proof.
  intros.
  rewrite (Nat.pow_le_mono_r_iff 2) in H by lia.
  induction n.
  - applys_eq H0; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    rewrite <-(Nat.add_1_r n).
    applys_eq (segRLs_addmul_v2 2 1 3 0 (2^(k+n)-3)); rw_pa; flia; ss.
Qed.

Lemma sideRLs_001s_v1 c n r r':
  2<=c ->
  sideRLs tm (hRL^^(2^(n*3+c)-3)) r r' ->
  sideRLs tm (hRL^^(2^(n*6+c)-3)) ([0;0;1]^^(n*3)*>r) (rd1^^(n*3)*>r').
Proof.
  replace (n*6+c) with (n*3+c+n*3) by lia.
  intros.
  apply sideRLs_001s; [lia|assumption].
Qed.

Lemma sideRLs_001s_v2 c n r r':
  2<=c ->
  sideRLs tm (hRL^^(2^c-3)) r r' ->
  sideRLs tm (hRL^^(2^(n*3+c)-3)) ([0;0;1]^^(n*3)*>r) (rd1^^(n*3)*>r').
Proof.
  replace (n*3+c) with (c+n*3) by lia.
  intros.
  apply sideRLs_001s; [lia|assumption].
Qed.

Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- ?G => idtac G
  end;
  match goal with
  | |- sideRLs _ (_^^O) _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ _ ((0::0::_)*>_) _ =>
    R_sub 1%nat; eapply hRL_00
  | |- sideRLs _ _ ([1;0;1]*>_) _ =>
    R_sub 1%nat; eapply hRL_101
  | |- sideRLs _ _ ([1;0;0;0;1;0;0;1]*>_) _ =>
    R_sub 1%nat; eapply hRL_10001001
  | |- sideRLs _ _ (ld*>_) _ =>
    ssc segRLs_ld
  | |- sideRLs _ _ (ld^^_*>_) _ =>
    eapply sideRLs_lds
  | |- sideRLs _ _ ([0;0;1]^^_*>_) _ =>
    (eapply sideRLs_001s_v1;[lia|]) ||
    (eapply sideRLs_001s_v2;[lia|])
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

Definition RC i n :=
match i with
| 0%nat => (ld)^^(10+n*6)*>rd1*>ld*>(rd1)^^(3+n*3)*>ld*>rd1*>rd0*>(rd1)^^(5+n*3)*>ld*>rd1*>rd1*>0inf
| 1%nat => (ld)^^(11+n*6)*>rd1*>ld*>(rd1)^^(3+n*3)*>ld*>rd0*>(rd1)^^(6+n*3)*>ld*>rd1*>rd1*>rd0*>rd1*>0inf
| 2 => (ld)^^(12+n*6)*>rd1*>ld*>(rd1)^^(4+n*3)*>ld*>rd1*>rd0*>(rd1)^^(4+n*3)*>ld*>rd1*>rd1*>rd1*>rd0*>rd1*>0inf
| 3 => (ld)^^(13+n*6)*>rd1*>ld*>(rd1)^^(4+n*3)*>ld*>rd0*>(rd1)^^(5+n*3)*>ld*>rd1*>rd0*>rd0*>rd0*>rd1*>rd1*>0inf
| 4 => (ld)^^(14+n*6)*>rd1*>ld*>(rd1)^^(5+n*3)*>ld*>rd1*>rd0*>(rd1)^^(3+n*3)*>ld*>rd0*>rd0*>rd1*>rd0*>rd0*>rd1*>rd1*>0inf
| 5 => (ld)^^(15+n*6)*>rd1*>ld*>(rd1)^^(5+n*3)*>ld*>rd0*>(rd1)^^(6+n*3)*>ld*>rd0*>rd0*>rd0*>rd0*>rd1*>rd1*>0inf
| 6 => (ld)^^(16+n*6)*>rd1*>ld*>(rd1)^^(6+n*3)*>ld*>rd1*>rd0*>(rd1)^^(8+n*3)*>ld*>rd1*>rd1*>0inf
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
  i<6 ->
  sideRLs tm (hRL^^(2^1+0)) ([1;0;0;0]*>RC i n) (RC (S i) n).
Proof.
  intro Hn.
  unfold RC.
  do 6
  (destruct i; [solve[sscs']|]).
  lia.
Qed.

Lemma RC_eq n:
  RC 6 n = RC 0 (S n).
Proof.
  unfold RC.
  st; simpl_rotate; reflexivity.
Qed.

Definition S0 '(i,n) := lh {{{ (hL,L) }}} RC i n.

Lemma BigStep i n:
  i<6 ->
  S0 (i,n) -->+
  S0 (S i,n).
Proof.
  intros Hi.
  unfold S0.
  follow LOv.
  epose proof (@sideRLs_concat tm hR hL hLR lh0 lh _ _) as I1.
  cbn in I1.
  unshelve epose proof (I1 _ (RC_Incs i n Hi)) as I1.
  1: esx.
  apply I1.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (O,O)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(i,n) => i<6).
  2: lia.
  intros [i n] Hi.
  assert (i<5\/i=5) as [E|E] by lia.
  - exists (S i,n); split.
    1: apply BigStep,Hi.
    lia.
  - eexists (O,S n); split; [|lia].
    follow10 (BigStep i n Hi).
    unfold S0.
    rewrite <-RC_eq.
    finish.
Qed.

End TM16.


Module TM17.

Definition tm := Eval compute in (TM_from_str "1LB0LB_1RC0LF_0RE0RD_0RB---_0LA0RA_0LE0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation ld := [1;0;0;0;1;0;0;0].
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation lh := (0inf<*<[1;0;0;0;0]).
Notation lh0 := (0inf<*<[1;0;0;1;0]).

Notation hR := (C,[1;0;0;1]).
Notation hL := (B,[0;0;0;0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma LOv r:
  lh {{{ (hL,L) }}} r -->*
  lh0 {{{ (hR,R) }}} [1;0;0;0] *> r.
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
Lemma rw_1000_ld r:
  [1;0;0;0] *> [1;0;0;0;1;0;0;0] *> r = [1;0;0;0;1;0;0;0] *> [1;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_1000_rd0 r:
  [1;0;0;0] *> [0;0;0] *> r = [1;0;0] *> [0;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_1000_rd1 r:
  [1;0;0;0] *> [1;0;0] *> r = [1;0;0;0;1;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0000_ld r:
  [0;0;0;0] *> [1;0;0;0;1;0;0;0] *> r = [0;0;0;0;1;0;0;0] *> [1;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0000_rd0 r:
  [0;0;0;0] *> [0;0;0] *> r = [0;0;0] *> [0;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0000_rd1 r:
  [0;0;0;0] *> [1;0;0] *> r = [0;0;0;0;1;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_1000100_ld r:
  [1;0;0;0;1;0;0] *> [1;0;0;0;1;0;0;0] *> r = [1;0;0;0;1;0;0;1] *> [0;0;0] *> [1;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_1000100_rd0 r:
  [1;0;0;0;1;0;0] *> [0;0;0] *> r = [1;0;0;0;1;0;0;0] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_1000100_rd1 r:
  [1;0;0;0;1;0;0] *> [1;0;0] *> r = [1;0;0;0;1;0;0;1] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0000100_ld r:
  [0;0;0;0;1;0;0] *> [1;0;0;0;1;0;0;0] *> r = [0;0;0;0;1;0;0;1] *> [0;0;0] *> [1;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0000100_rd0 r:
  [0;0;0;0;1;0;0] *> [0;0;0] *> r = [0;0;0;0;1;0;0;0] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0000100_rd1 r:
  [0;0;0;0;1;0;0] *> [1;0;0] *> r = [0;0;0;0;1;0;0;1] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_ld r:
  [1;0] *> [1;0;0;0;1;0;0;0] *> r = [1;0;1] *> [0;0;0] *> [1;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_rd0 r:
  [1;0] *> [0;0;0] *> r = [1;0;0] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_rd1 r:
  [1;0] *> [1;0;0] *> r = [1;0;1] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_ld r:
  [0;0] *> [1;0;0;0;1;0;0;0] *> r = [0;0;1] *> [0;0;0] *> [1;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd0 r:
  [0;0] *> [0;0;0] *> r = [0;0;0] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd1 r:
  [0;0] *> [1;0;0] *> r = [0;0;1] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_1000_lds n r:
  [1;0;0;0] *> ld^^n *> r = ld^^n *> [1;0;0;0] *> r.
Proof.
  simpl_rotate; reflexivity.
Qed.

Lemma rw_00_rd1s n r:
  [0;0] *> rd1^^n *> r = [0;0;1]^^n *> [0;0] *> r.
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
  rewrite rw_1000_ld ||
  rewrite rw_1000_rd0 ||
  rewrite rw_1000_rd1 ||
  rewrite rw_0000_ld ||
  rewrite rw_0000_rd0 ||
  rewrite rw_0000_rd1 ||
  rewrite rw_1000100_ld ||
  rewrite rw_1000100_rd0 ||
  rewrite rw_1000100_rd1 ||
  rewrite rw_0000100_ld ||
  rewrite rw_0000100_rd0 ||
  rewrite rw_0000100_rd1 ||
  rewrite rw_10_ld ||
  rewrite rw_10_rd0 ||
  rewrite rw_10_rd1 ||
  rewrite rw_00_ld ||
  rewrite rw_00_rd0 ||
  rewrite rw_00_rd1 ||
  rewrite rw_1000_lds ||
  rewrite rw_00_rd1s).

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

Lemma hRL_00 n s r r':
  sideRLs tm (hRL^^n) ((1::0::s)*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ((0::0::s)*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma hRL_101 n r r':
  sideRLs tm (hRL^^n) (rd0*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([1;0;1]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma hRL_10001001 n r r' r0:
  sideRLs tm (hRL^^1) r r0 ->
  sideRLs tm (hRL^^n) (ld*>r0) r' ->
  sideRLs tm (hRL^^(n+1)) ([1;0;0;0;1;0;0;1]*>r) r'.
Proof.
  intros H H0.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H0.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  esx.
Qed.

Lemma sideRLs_001s k n r r':
  2<=k ->
  sideRLs tm (hRL^^(2^k-3)) r r' ->
  sideRLs tm (hRL^^(2^(k+n)-3)) ([0;0;1]^^n*>r) (rd1^^n*>r').
Proof.
  intros.
  rewrite (Nat.pow_le_mono_r_iff 2) in H by lia.
  induction n.
  - applys_eq H0; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    rewrite <-(Nat.add_1_r n).
    applys_eq (segRLs_addmul_v2 2 1 3 0 (2^(k+n)-3)); rw_pa; flia; ss.
Qed.

Lemma sideRLs_001s_v1 c n r r':
  2<=c ->
  sideRLs tm (hRL^^(2^(n*3+c)-3)) r r' ->
  sideRLs tm (hRL^^(2^(n*6+c)-3)) ([0;0;1]^^(n*3)*>r) (rd1^^(n*3)*>r').
Proof.
  replace (n*6+c) with (n*3+c+n*3) by lia.
  intros.
  apply sideRLs_001s; [lia|assumption].
Qed.

Lemma sideRLs_001s_v2 c n r r':
  2<=c ->
  sideRLs tm (hRL^^(2^c-3)) r r' ->
  sideRLs tm (hRL^^(2^(n*3+c)-3)) ([0;0;1]^^(n*3)*>r) (rd1^^(n*3)*>r').
Proof.
  replace (n*3+c) with (c+n*3) by lia.
  intros.
  apply sideRLs_001s; [lia|assumption].
Qed.

Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- ?G => idtac G
  end;
  match goal with
  | |- sideRLs _ (_^^O) _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ _ ((0::0::_)*>_) _ =>
    R_sub 1%nat; eapply hRL_00
  | |- sideRLs _ _ ([1;0;1]*>_) _ =>
    R_sub 1%nat; eapply hRL_101
  | |- sideRLs _ _ ([1;0;0;0;1;0;0;1]*>_) _ =>
    R_sub 1%nat; eapply hRL_10001001
  | |- sideRLs _ _ (ld*>_) _ =>
    ssc segRLs_ld
  | |- sideRLs _ _ (ld^^_*>_) _ =>
    eapply sideRLs_lds
  | |- sideRLs _ _ ([0;0;1]^^_*>_) _ =>
    (eapply sideRLs_001s_v1;[lia|]) ||
    (eapply sideRLs_001s_v2;[lia|])
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

Definition RC i n :=
match i with
| 0%nat => (ld)^^(10+n*6)*>rd1*>ld*>(rd1)^^(2+n*3)*>ld*>rd1*>rd0*>ld*>rd1*>rd0*>(rd1)^^(5+n*3)*>ld*>rd1*>rd1*>0inf
| 1%nat => (ld)^^(11+n*6)*>rd1*>ld*>(rd1)^^(2+n*3)*>ld*>rd0*>rd1*>ld*>rd0*>(rd1)^^(6+n*3)*>ld*>rd1*>rd1*>rd0*>rd1*>0inf
| 2 => (ld)^^(12+n*6)*>rd1*>ld*>(rd1)^^(3+n*3)*>ld*>rd1*>rd0*>ld*>rd1*>rd0*>(rd1)^^(4+n*3)*>ld*>rd1*>rd1*>rd1*>rd0*>rd1*>0inf
| 3 => (ld)^^(13+n*6)*>rd1*>ld*>(rd1)^^(3+n*3)*>ld*>rd0*>rd1*>ld*>rd0*>(rd1)^^(5+n*3)*>ld*>rd1*>rd0*>rd0*>rd0*>rd1*>rd1*>0inf
| 4 => (ld)^^(14+n*6)*>rd1*>ld*>(rd1)^^(4+n*3)*>ld*>rd1*>rd0*>ld*>rd1*>rd0*>(rd1)^^(3+n*3)*>ld*>rd0*>rd0*>rd1*>rd0*>rd0*>rd1*>rd1*>0inf
| 5 => (ld)^^(15+n*6)*>rd1*>ld*>(rd1)^^(4+n*3)*>ld*>rd0*>rd1*>ld*>rd0*>(rd1)^^(6+n*3)*>ld*>rd0*>rd0*>rd0*>rd0*>rd1*>rd1*>0inf
| 6 => (ld)^^(16+n*6)*>rd1*>ld*>(rd1)^^(5+n*3)*>ld*>rd1*>rd0*>ld*>rd1*>rd0*>(rd1)^^(8+n*3)*>ld*>rd1*>rd1*>0inf
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
  i<6 ->
  sideRLs tm (hRL^^(2^1+0)) ([1;0;0;0]*>RC i n) (RC (S i) n).
Proof.
  intro Hn.
  unfold RC.
  do 2
  (destruct i; [destruct n; cbn[Nat.mul]; sscs'|]).
  do 4
  (destruct i; [solve[sscs']|]).
  lia.
Qed.

Lemma RC_eq n:
  RC 6 n = RC 0 (S n).
Proof.
  unfold RC.
  st; simpl_rotate; reflexivity.
Qed.

Definition S0 '(i,n) := lh {{{ (hL,L) }}} RC i n.

Lemma BigStep i n:
  i<6 ->
  S0 (i,n) -->+
  S0 (S i,n).
Proof.
  intros Hi.
  unfold S0.
  follow LOv.
  epose proof (@sideRLs_concat tm hR hL hLR lh0 lh _ _) as I1.
  cbn in I1.
  unshelve epose proof (I1 _ (RC_Incs i n Hi)) as I1.
  1: esx.
  apply I1.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (O,O)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(i,n) => i<6).
  2: lia.
  intros [i n] Hi.
  assert (i<5\/i=5) as [E|E] by lia.
  - exists (S i,n); split.
    1: apply BigStep,Hi.
    lia.
  - eexists (O,S n); split; [|lia].
    follow10 (BigStep i n Hi).
    unfold S0.
    rewrite <-RC_eq.
    finish.
Qed.

End TM17.


Module TM18.

Definition tm := Eval compute in (TM_from_str "1RB0LE_0RC0RF_0LD0RB_1LA0LA_0LC1LB_0RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation ld := [1;0;0;0;1;0;0;0].
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation lh := (0inf<*<[1;0;0;0;0]).
Notation lh0 := (0inf<*<[1;0;0;1;0]).

Notation hR := (B,[1;0;0;1]).
Notation hL := (A,[0;0;0;0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma LOv r:
  lh {{{ (hL,L) }}} r -->*
  lh0 {{{ (hR,R) }}} [1;0;0;0] *> r.
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
Lemma rw_1000_ld r:
  [1;0;0;0] *> [1;0;0;0;1;0;0;0] *> r = [1;0;0;0;1;0;0;0] *> [1;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_1000_rd0 r:
  [1;0;0;0] *> [0;0;0] *> r = [1;0;0] *> [0;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_1000_rd1 r:
  [1;0;0;0] *> [1;0;0] *> r = [1;0;0;0;1;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0000_ld r:
  [0;0;0;0] *> [1;0;0;0;1;0;0;0] *> r = [0;0;0;0;1;0;0;0] *> [1;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0000_rd0 r:
  [0;0;0;0] *> [0;0;0] *> r = [0;0;0] *> [0;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0000_rd1 r:
  [0;0;0;0] *> [1;0;0] *> r = [0;0;0;0;1;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_1000100_ld r:
  [1;0;0;0;1;0;0] *> [1;0;0;0;1;0;0;0] *> r = [1;0;0;0;1;0;0;1] *> [0;0;0] *> [1;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_1000100_rd0 r:
  [1;0;0;0;1;0;0] *> [0;0;0] *> r = [1;0;0;0;1;0;0;0] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_1000100_rd1 r:
  [1;0;0;0;1;0;0] *> [1;0;0] *> r = [1;0;0;0;1;0;0;1] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0000100_ld r:
  [0;0;0;0;1;0;0] *> [1;0;0;0;1;0;0;0] *> r = [0;0;0;0;1;0;0;1] *> [0;0;0] *> [1;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0000100_rd0 r:
  [0;0;0;0;1;0;0] *> [0;0;0] *> r = [0;0;0;0;1;0;0;0] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0000100_rd1 r:
  [0;0;0;0;1;0;0] *> [1;0;0] *> r = [0;0;0;0;1;0;0;1] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_ld r:
  [1;0] *> [1;0;0;0;1;0;0;0] *> r = [1;0;1] *> [0;0;0] *> [1;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_rd0 r:
  [1;0] *> [0;0;0] *> r = [1;0;0] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_rd1 r:
  [1;0] *> [1;0;0] *> r = [1;0;1] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_ld r:
  [0;0] *> [1;0;0;0;1;0;0;0] *> r = [0;0;1] *> [0;0;0] *> [1;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd0 r:
  [0;0] *> [0;0;0] *> r = [0;0;0] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd1 r:
  [0;0] *> [1;0;0] *> r = [0;0;1] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_1000_lds n r:
  [1;0;0;0] *> ld^^n *> r = ld^^n *> [1;0;0;0] *> r.
Proof.
  simpl_rotate; reflexivity.
Qed.

Lemma rw_00_rd1s n r:
  [0;0] *> rd1^^n *> r = [0;0;1]^^n *> [0;0] *> r.
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
  rewrite rw_1000_ld ||
  rewrite rw_1000_rd0 ||
  rewrite rw_1000_rd1 ||
  rewrite rw_0000_ld ||
  rewrite rw_0000_rd0 ||
  rewrite rw_0000_rd1 ||
  rewrite rw_1000100_ld ||
  rewrite rw_1000100_rd0 ||
  rewrite rw_1000100_rd1 ||
  rewrite rw_0000100_ld ||
  rewrite rw_0000100_rd0 ||
  rewrite rw_0000100_rd1 ||
  rewrite rw_10_ld ||
  rewrite rw_10_rd0 ||
  rewrite rw_10_rd1 ||
  rewrite rw_00_ld ||
  rewrite rw_00_rd0 ||
  rewrite rw_00_rd1 ||
  rewrite rw_1000_lds ||
  rewrite rw_00_rd1s).

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

Lemma hRL_00 n s r r':
  sideRLs tm (hRL^^n) ((1::0::s)*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ((0::0::s)*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma hRL_101 n r r':
  sideRLs tm (hRL^^n) (rd0*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([1;0;1]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma hRL_10001001 n r r' r0:
  sideRLs tm (hRL^^1) r r0 ->
  sideRLs tm (hRL^^n) (ld*>r0) r' ->
  sideRLs tm (hRL^^(n+1)) ([1;0;0;0;1;0;0;1]*>r) r'.
Proof.
  intros H H0.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H0.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  esx.
Qed.

Lemma sideRLs_001s k n r r':
  2<=k ->
  sideRLs tm (hRL^^(2^k-3)) r r' ->
  sideRLs tm (hRL^^(2^(k+n)-3)) ([0;0;1]^^n*>r) (rd1^^n*>r').
Proof.
  intros.
  rewrite (Nat.pow_le_mono_r_iff 2) in H by lia.
  induction n.
  - applys_eq H0; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    rewrite <-(Nat.add_1_r n).
    applys_eq (segRLs_addmul_v2 2 1 3 0 (2^(k+n)-3)); rw_pa; flia; ss.
Qed.

Lemma sideRLs_001s_v1 c n r r':
  2<=c ->
  sideRLs tm (hRL^^(2^(n*3+c)-3)) r r' ->
  sideRLs tm (hRL^^(2^(n*6+c)-3)) ([0;0;1]^^(n*3)*>r) (rd1^^(n*3)*>r').
Proof.
  replace (n*6+c) with (n*3+c+n*3) by lia.
  intros.
  apply sideRLs_001s; [lia|assumption].
Qed.

Lemma sideRLs_001s_v2 c n r r':
  2<=c ->
  sideRLs tm (hRL^^(2^c-3)) r r' ->
  sideRLs tm (hRL^^(2^(n*3+c)-3)) ([0;0;1]^^(n*3)*>r) (rd1^^(n*3)*>r').
Proof.
  replace (n*3+c) with (c+n*3) by lia.
  intros.
  apply sideRLs_001s; [lia|assumption].
Qed.

Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- ?G => idtac G
  end;
  match goal with
  | |- sideRLs _ (_^^O) _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ _ ((0::0::_)*>_) _ =>
    R_sub 1%nat; eapply hRL_00
  | |- sideRLs _ _ ([1;0;1]*>_) _ =>
    R_sub 1%nat; eapply hRL_101
  | |- sideRLs _ _ ([1;0;0;0;1;0;0;1]*>_) _ =>
    R_sub 1%nat; eapply hRL_10001001
  | |- sideRLs _ _ (ld*>_) _ =>
    ssc segRLs_ld
  | |- sideRLs _ _ (ld^^_*>_) _ =>
    eapply sideRLs_lds
  | |- sideRLs _ _ ([0;0;1]^^_*>_) _ =>
    (eapply sideRLs_001s_v1;[lia|]) ||
    (eapply sideRLs_001s_v2;[lia|])
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

Definition RC i n :=
match i with
| 0%nat => (ld)^^(10+n*6)*>rd1*>ld*>(rd1)^^(3+n*3)*>ld*>rd1*>rd0*>(rd1)^^(5+n*3)*>ld*>rd1*>rd1*>0inf
| 1%nat => (ld)^^(11+n*6)*>rd1*>ld*>(rd1)^^(3+n*3)*>ld*>rd0*>(rd1)^^(6+n*3)*>ld*>rd1*>rd1*>rd0*>rd1*>0inf
| 2 => (ld)^^(12+n*6)*>rd1*>ld*>(rd1)^^(4+n*3)*>ld*>rd1*>rd0*>(rd1)^^(4+n*3)*>ld*>rd1*>rd1*>rd1*>rd0*>rd1*>0inf
| 3 => (ld)^^(13+n*6)*>rd1*>ld*>(rd1)^^(4+n*3)*>ld*>rd0*>(rd1)^^(5+n*3)*>ld*>rd1*>rd0*>rd0*>rd0*>rd1*>rd1*>0inf
| 4 => (ld)^^(14+n*6)*>rd1*>ld*>(rd1)^^(5+n*3)*>ld*>rd1*>rd0*>(rd1)^^(3+n*3)*>ld*>rd0*>rd0*>rd1*>rd0*>rd0*>rd1*>rd1*>0inf
| 5 => (ld)^^(15+n*6)*>rd1*>ld*>(rd1)^^(5+n*3)*>ld*>rd0*>(rd1)^^(6+n*3)*>ld*>rd0*>rd0*>rd0*>rd0*>rd1*>rd1*>0inf
| 6 => (ld)^^(16+n*6)*>rd1*>ld*>(rd1)^^(6+n*3)*>ld*>rd1*>rd0*>(rd1)^^(8+n*3)*>ld*>rd1*>rd1*>0inf
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
  i<6 ->
  sideRLs tm (hRL^^(2^1+0)) ([1;0;0;0]*>RC i n) (RC (S i) n).
Proof.
  intro Hn.
  unfold RC.
  do 6
  (destruct i; [solve[sscs']|]).
  lia.
Qed.

Lemma RC_eq n:
  RC 6 n = RC 0 (S n).
Proof.
  unfold RC.
  st; simpl_rotate; reflexivity.
Qed.

Definition S0 '(i,n) := lh {{{ (hL,L) }}} RC i n.

Lemma BigStep i n:
  i<6 ->
  S0 (i,n) -->+
  S0 (S i,n).
Proof.
  intros Hi.
  unfold S0.
  follow LOv.
  epose proof (@sideRLs_concat tm hR hL hLR lh0 lh _ _) as I1.
  cbn in I1.
  unshelve epose proof (I1 _ (RC_Incs i n Hi)) as I1.
  1: esx.
  apply I1.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (O,O)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(i,n) => i<6).
  2: lia.
  intros [i n] Hi.
  assert (i<5\/i=5) as [E|E] by lia.
  - exists (S i,n); split.
    1: apply BigStep,Hi.
    lia.
  - eexists (O,S n); split; [|lia].
    follow10 (BigStep i n Hi).
    unfold S0.
    rewrite <-RC_eq.
    finish.
Qed.

End TM18.


Module TM19.

Definition tm := Eval compute in (TM_from_str "1LB0LB_1RC0LF_0RE0RD_0RB---_0LA0RC_0LE1LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation ld := [1;0;0;0;1;0;0;0].
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation lh := (0inf<*<[1;0;0;0;0]).
Notation lh0 := (0inf<*<[1;0;0;1;0]).

Notation hR := (C,[1;0;0;1]).
Notation hL := (B,[0;0;0;0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma LOv r:
  lh {{{ (hL,L) }}} r -->*
  lh0 {{{ (hR,R) }}} [1;0;0;0] *> r.
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
Lemma rw_1000_ld r:
  [1;0;0;0] *> [1;0;0;0;1;0;0;0] *> r = [1;0;0;0;1;0;0;0] *> [1;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_1000_rd0 r:
  [1;0;0;0] *> [0;0;0] *> r = [1;0;0] *> [0;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_1000_rd1 r:
  [1;0;0;0] *> [1;0;0] *> r = [1;0;0;0;1;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0000_ld r:
  [0;0;0;0] *> [1;0;0;0;1;0;0;0] *> r = [0;0;0;0;1;0;0;0] *> [1;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0000_rd0 r:
  [0;0;0;0] *> [0;0;0] *> r = [0;0;0] *> [0;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0000_rd1 r:
  [0;0;0;0] *> [1;0;0] *> r = [0;0;0;0;1;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_1000100_ld r:
  [1;0;0;0;1;0;0] *> [1;0;0;0;1;0;0;0] *> r = [1;0;0;0;1;0;0;1] *> [0;0;0] *> [1;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_1000100_rd0 r:
  [1;0;0;0;1;0;0] *> [0;0;0] *> r = [1;0;0;0;1;0;0;0] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_1000100_rd1 r:
  [1;0;0;0;1;0;0] *> [1;0;0] *> r = [1;0;0;0;1;0;0;1] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0000100_ld r:
  [0;0;0;0;1;0;0] *> [1;0;0;0;1;0;0;0] *> r = [0;0;0;0;1;0;0;1] *> [0;0;0] *> [1;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0000100_rd0 r:
  [0;0;0;0;1;0;0] *> [0;0;0] *> r = [0;0;0;0;1;0;0;0] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_0000100_rd1 r:
  [0;0;0;0;1;0;0] *> [1;0;0] *> r = [0;0;0;0;1;0;0;1] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_ld r:
  [1;0] *> [1;0;0;0;1;0;0;0] *> r = [1;0;1] *> [0;0;0] *> [1;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_rd0 r:
  [1;0] *> [0;0;0] *> r = [1;0;0] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_10_rd1 r:
  [1;0] *> [1;0;0] *> r = [1;0;1] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_ld r:
  [0;0] *> [1;0;0;0;1;0;0;0] *> r = [0;0;1] *> [0;0;0] *> [1;0;0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd0 r:
  [0;0] *> [0;0;0] *> r = [0;0;0] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_00_rd1 r:
  [0;0] *> [1;0;0] *> r = [0;0;1] *> [0;0] *> r.
Proof. reflexivity. Qed.

Lemma rw_1000_lds n r:
  [1;0;0;0] *> ld^^n *> r = ld^^n *> [1;0;0;0] *> r.
Proof.
  simpl_rotate; reflexivity.
Qed.

Lemma rw_00_rd1s n r:
  [0;0] *> rd1^^n *> r = [0;0;1]^^n *> [0;0] *> r.
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
  rewrite rw_1000_ld ||
  rewrite rw_1000_rd0 ||
  rewrite rw_1000_rd1 ||
  rewrite rw_0000_ld ||
  rewrite rw_0000_rd0 ||
  rewrite rw_0000_rd1 ||
  rewrite rw_1000100_ld ||
  rewrite rw_1000100_rd0 ||
  rewrite rw_1000100_rd1 ||
  rewrite rw_0000100_ld ||
  rewrite rw_0000100_rd0 ||
  rewrite rw_0000100_rd1 ||
  rewrite rw_10_ld ||
  rewrite rw_10_rd0 ||
  rewrite rw_10_rd1 ||
  rewrite rw_00_ld ||
  rewrite rw_00_rd0 ||
  rewrite rw_00_rd1 ||
  rewrite rw_1000_lds ||
  rewrite rw_00_rd1s).

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

Lemma hRL_00 n s r r':
  sideRLs tm (hRL^^n) ((1::0::s)*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ((0::0::s)*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma hRL_101 n r r':
  sideRLs tm (hRL^^n) (rd0*>r) r' ->
  sideRLs tm (hRL^^(n+1)) ([1;0;1]*>r) r'.
Proof.
  intros H.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H.
  esx.
Qed.

Lemma hRL_10001001 n r r' r0:
  sideRLs tm (hRL^^1) r r0 ->
  sideRLs tm (hRL^^n) (ld*>r0) r' ->
  sideRLs tm (hRL^^(n+1)) ([1;0;0;0;1;0;0;1]*>r) r'.
Proof.
  intros H H0.
  rewrite Nat.add_comm,lpow_add.
  eapply sideRLs_trans.
  2: apply H0.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  esx.
Qed.

Lemma sideRLs_001s k n r r':
  2<=k ->
  sideRLs tm (hRL^^(2^k-3)) r r' ->
  sideRLs tm (hRL^^(2^(k+n)-3)) ([0;0;1]^^n*>r) (rd1^^n*>r').
Proof.
  intros.
  rewrite (Nat.pow_le_mono_r_iff 2) in H by lia.
  induction n.
  - applys_eq H0; flia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    rewrite <-(Nat.add_1_r n).
    applys_eq (segRLs_addmul_v2 2 1 3 0 (2^(k+n)-3)); rw_pa; flia; ss.
Qed.

Lemma sideRLs_001s_v1 c n r r':
  2<=c ->
  sideRLs tm (hRL^^(2^(n*3+c)-3)) r r' ->
  sideRLs tm (hRL^^(2^(n*6+c)-3)) ([0;0;1]^^(n*3)*>r) (rd1^^(n*3)*>r').
Proof.
  replace (n*6+c) with (n*3+c+n*3) by lia.
  intros.
  apply sideRLs_001s; [lia|assumption].
Qed.

Lemma sideRLs_001s_v2 c n r r':
  2<=c ->
  sideRLs tm (hRL^^(2^c-3)) r r' ->
  sideRLs tm (hRL^^(2^(n*3+c)-3)) ([0;0;1]^^(n*3)*>r) (rd1^^(n*3)*>r').
Proof.
  replace (n*3+c) with (c+n*3) by lia.
  intros.
  apply sideRLs_001s; [lia|assumption].
Qed.

Ltac sscs :=
  simpl_nat;
  repeat (
  match goal with
  | |- ?G => idtac G
  end;
  match goal with
  | |- sideRLs _ (_^^O) _ _ =>
    solve[eapply sideRLseq_O]
  | |- sideRLs _ _ ((0::0::_)*>_) _ =>
    R_sub 1%nat; eapply hRL_00
  | |- sideRLs _ _ ([1;0;1]*>_) _ =>
    R_sub 1%nat; eapply hRL_101
  | |- sideRLs _ _ ([1;0;0;0;1;0;0;1]*>_) _ =>
    R_sub 1%nat; eapply hRL_10001001
  | |- sideRLs _ _ (ld*>_) _ =>
    ssc segRLs_ld
  | |- sideRLs _ _ (ld^^_*>_) _ =>
    eapply sideRLs_lds
  | |- sideRLs _ _ ([0;0;1]^^_*>_) _ =>
    (eapply sideRLs_001s_v1;[lia|]) ||
    (eapply sideRLs_001s_v2;[lia|])
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

Definition RC i n :=
match i with
| 0%nat => (ld)^^(10+n*6)*>rd1*>ld*>(rd1)^^(2+n*3)*>ld*>rd1*>rd0*>ld*>rd1*>rd0*>(rd1)^^(5+n*3)*>ld*>rd1*>rd1*>0inf
| 1%nat => (ld)^^(11+n*6)*>rd1*>ld*>(rd1)^^(2+n*3)*>ld*>rd0*>rd1*>ld*>rd0*>(rd1)^^(6+n*3)*>ld*>rd1*>rd1*>rd0*>rd1*>0inf
| 2 => (ld)^^(12+n*6)*>rd1*>ld*>(rd1)^^(3+n*3)*>ld*>rd1*>rd0*>ld*>rd1*>rd0*>(rd1)^^(4+n*3)*>ld*>rd1*>rd1*>rd1*>rd0*>rd1*>0inf
| 3 => (ld)^^(13+n*6)*>rd1*>ld*>(rd1)^^(3+n*3)*>ld*>rd0*>rd1*>ld*>rd0*>(rd1)^^(5+n*3)*>ld*>rd1*>rd0*>rd0*>rd0*>rd1*>rd1*>0inf
| 4 => (ld)^^(14+n*6)*>rd1*>ld*>(rd1)^^(4+n*3)*>ld*>rd1*>rd0*>ld*>rd1*>rd0*>(rd1)^^(3+n*3)*>ld*>rd0*>rd0*>rd1*>rd0*>rd0*>rd1*>rd1*>0inf
| 5 => (ld)^^(15+n*6)*>rd1*>ld*>(rd1)^^(4+n*3)*>ld*>rd0*>rd1*>ld*>rd0*>(rd1)^^(6+n*3)*>ld*>rd0*>rd0*>rd0*>rd0*>rd1*>rd1*>0inf
| 6 => (ld)^^(16+n*6)*>rd1*>ld*>(rd1)^^(5+n*3)*>ld*>rd1*>rd0*>ld*>rd1*>rd0*>(rd1)^^(8+n*3)*>ld*>rd1*>rd1*>0inf
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
  i<6 ->
  sideRLs tm (hRL^^(2^1+0)) ([1;0;0;0]*>RC i n) (RC (S i) n).
Proof.
  intro Hn.
  unfold RC.
  do 2
  (destruct i; [destruct n; cbn[Nat.mul]; sscs'|]).
  do 4
  (destruct i; [solve[sscs']|]).
  lia.
Qed.

Lemma RC_eq n:
  RC 6 n = RC 0 (S n).
Proof.
  unfold RC.
  st; simpl_rotate; reflexivity.
Qed.

Definition S0 '(i,n) := lh {{{ (hL,L) }}} RC i n.

Lemma BigStep i n:
  i<6 ->
  S0 (i,n) -->+
  S0 (S i,n).
Proof.
  intros Hi.
  unfold S0.
  follow LOv.
  epose proof (@sideRLs_concat tm hR hL hLR lh0 lh _ _) as I1.
  cbn in I1.
  unshelve epose proof (I1 _ (RC_Incs i n Hi)) as I1.
  1: esx.
  apply I1.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (O,O)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(i,n) => i<6).
  2: lia.
  intros [i n] Hi.
  assert (i<5\/i=5) as [E|E] by lia.
  - exists (S i,n); split.
    1: apply BigStep,Hi.
    lia.
  - eexists (O,S n); split; [|lia].
    follow10 (BigStep i n Hi).
    unfold S0.
    rewrite <-RC_eq.
    finish.
Qed.

End TM19.


