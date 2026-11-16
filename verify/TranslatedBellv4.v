From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import ES_v3.
From BusyCoq Require Import Longitudinal.


Ltac stepn' n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; try reflexivity.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1RC0RB_1LA1RB_---0LE_0LF1LE_1LC1LD").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hL := (C,[1;0;0;1;0;0;1;0;0]).
Notation hR := (C,<[0;0;1;1;0;0;1]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Definition tm' := flip tm.

Definition S1 a b c d := [1;1;0]^^(1+a) *> [1;1;1;1;0]^^(1+b) *> [0;0;0;0] *> [1;1;1;1;0;0;0]^^c *> [1;1;0;0;1;1;1;1;1;1;0;0;1;1;0;0] *> [1;1;0;1;1;0;0]^^d *> [1;1;1;1;1;1;1;1;0;1;1] *> 0inf.

Definition S2 a b c d := [1;1;0]^^(1+a) *> [1;1;1;1;0]^^(1+b) *> [0;0] *> [1;1;1;1;0;0;0]^^c *> [1;1;0;0;1;1;1;1;1;1;0;0;1;1;0;0] *> [1;1;0;1;1;0;0]^^d *> [1;1;1;1;1;1;1;1;0;1;1] *> 0inf.

Ltac use_shift_rule ::= use_shift_rule'.

Lemma Inc1 a b c d:
  sideRLs tm' (hLR^^6) (S1 a (2+b) c d) (S1 (6+a) b (2+c) d).
Proof.
  unfold S1.
  es' a b c d.
Qed.

Lemma Inc2 a b c d:
  sideRLs tm' (hLR^^4) (S2 a b (2+c) d) (S2 (4+a) (4+b) c d).
Proof.
  unfold S2.
  es' a b c d.
Qed.

Lemma Ov1 a c d:
  sideRLs tm' (hLR^^10) (S1 a 1 (1+c) d) ([1;1;0]^^(7+a)*>[0]*>S2 4 4 c d).
Proof.
  unfold S1,S2.
  es' a c d.
Qed.

Lemma Ov2 a b d:
  sideRLs tm' (hLR^^65) (S2 a (17+b) 1 d) (S1 (65+a) b 16 (4+d)).
Proof.
  unfold S1,S2.
  es' a b d.
Qed.

Lemma Incs1 n a b c d:
  sideRLs tm' (hLR^^(n*6)) (S1 a (n*2+b) c d) (S1 (n*6+a) b (n*2+c) d).
Proof.
  gen a b c d.
  induction n; intros.
  1: esx.
  eapply sideRLs_trans_add with (n1:=6) (n2:=n*6).
  2: applys_eq (IHn (6+a) b (2+c) d); flia.
  apply Inc1.
Qed.

Lemma Incs2 n a b c d:
  sideRLs tm' (hLR^^(n*4)) (S2 a b (n*2+c) d) (S2 (n*4+a) (n*4+b) c d).
Proof.
  gen a b c d.
  induction n; intros.
  1: esx.
  eapply sideRLs_trans_add with (n1:=4) (n2:=n*4).
  2: applys_eq (IHn (4+a) (4+b) c d); flia.
  apply Inc2.
Qed.

Definition W n := [1;1;0]^^(3+n)++[0].

Lemma wall n a:
  segRLs tm' (hLR^^n) (hLR^^n) (W a) (W a).
Proof.
  unfold W.
  eapply segRLs_wall''; esx.
Qed.

Definition S1' a n d := S1 a 1 (1+(n*2+15)) d.

Lemma Incs12 a n d:
  sideRLs tm' (hLR^^(n*16+145)) (S1' a n d) (W (4+a)*>S1' (n*16+139) (n*2+7) (4+d)).
Proof.
  unfold S1'.
  replace (n*16+145) with (10+((n+7)*4+(65+(n*12+42)))) by lia.
  eapply sideRLs_trans_add.
  1: apply Ov1.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply wall.
  eapply sideRLs_trans_add.
  1: applys_eq (Incs2 (n+7) 4 4 1 d); flia.
  eapply sideRLs_trans_add.
  1: applys_eq (Ov2 (n*4+32) (n*4+15)); flia.
  applys_eq (Incs1 (n*2+7) (n*4+97) 1); flia.
Qed.

Definition RC a b := [1;0;0]^^a *> [1;0;1;1;1;1;1;1;1;1] *> [1;1;0;1;0]^^(1+b) *> [1;1;1;0] *> 0inf.

Lemma RInc a b:
  sideRLs tm (hRL^^2) (RC a b) (RC a (4+b)).
Proof.
  unfold RC.
  es' a b.
Qed.

Lemma RIncs n a b:
  sideRLs tm (hRL^^(n*2)) (RC a b) (RC a (n*4+b)).
Proof.
  gen b.
  induction n; intros.
  1: esx.
  eapply sideRLs_trans_add with (n1:=2) (n2:=n*2).
  1: apply RInc.
  applys_eq IHn; flia.
Qed.

Inductive LC: side->Prop :=
| LC_O a n d: LC (S1' a n d)
| LC_S n r: LC r -> LC (W n*>r).

Lemma LC_spec l:
  LC l ->
  exists l' n,
  sideRLs tm' (hLR^^(n*2)) l l' /\
  LC l' /\
  n<>O.
Proof.
  intro H.
  induction H.
  - eexists _,(n*24+201); split.
    + replace ((n*24+201)*2) with ((n*16+145)+((n*2+7)*16+145)) by lia.
      eapply sideRLs_trans_add.
      1: apply Incs12.
      eapply segRLs_sideRLs_concat.
      1: apply wall.
      apply Incs12.
    + split.
      1: repeat constructor.
      lia.
  - destruct IHLC as [l' [n' [I1 [I2 I3]]]].
    eexists _,_; repeat split.
    + eapply segRLs_sideRLs_concat.
      1: apply wall.
      apply I1.
    + econstructor.
      apply I2.
    + apply I3.
Qed.

Definition S' '(l,a,b) := l {{{ (hL,L) }}} RC a b.

Lemma lcons_1 n:
  lcons hL (hRL^^n) = (hLR^^n,hL).
Proof.
  induction n; cbn; trivial.
  rewrite IHn; trivial.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':= S' (W 9*>W 10*>W 11*>W 8*>W 11*>W 19*>W 24*>W 31 *>W 59*>S1' 83 0 20,9,593)).
  1: stepn' 6446854%N.
  eapply progress_nonhalt_cond with (P:=fun '(l,a,b) => LC l).
  2: repeat constructor.
  intros [[l a] b] HP.
  eapply LC_spec in HP.
  destruct HP as [l' [n' [I1 [I2 I3]]]].
  unshelve epose proof (sideRLs_concat_v2_L (lcons_1 _) _ I1 (RIncs n' a b)) as I4.
  1: destruct (n'*2) eqn:E; cbn; [lia|congruence].
  eexists (_,_,_); split.
  - apply I4.
  - apply I2.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB0RA_1LC1RA_1LA1RD_---0LE_0LF1LE_1LB1LD").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hL := (B,[1;0;0;1;0;0;1;0;0]).
Notation hR := (B,<[0;0;1;1;0;0;1]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Definition tm' := flip tm.

Definition S1 a b c d := [1;1;0]^^(1+a) *> [1;1;1;1;0]^^(1+b) *> [0;0;0;0] *> [1;1;1;1;0;0;0]^^c *> [1;1;0;0;1;1;1;1;1;1;0;0;1;1;0;0] *> [1;1;0;1;1;0;0]^^d *> [1;1;1;1;1;1;1;1;0;1;1] *> 0inf.

Definition S2 a b c d := [1;1;0]^^(1+a) *> [1;1;1;1;0]^^(1+b) *> [0;0] *> [1;1;1;1;0;0;0]^^c *> [1;1;0;0;1;1;1;1;1;1;0;0;1;1;0;0] *> [1;1;0;1;1;0;0]^^d *> [1;1;1;1;1;1;1;1;0;1;1] *> 0inf.

Ltac use_shift_rule ::= use_shift_rule'.

Lemma Inc1 a b c d:
  sideRLs tm' (hLR^^6) (S1 a (2+b) c d) (S1 (6+a) b (2+c) d).
Proof.
  unfold S1.
  es' a b c d.
Qed.

Lemma Inc2 a b c d:
  sideRLs tm' (hLR^^4) (S2 a b (2+c) d) (S2 (4+a) (4+b) c d).
Proof.
  unfold S2.
  es' a b c d.
Qed.

Lemma Ov1 a c d:
  sideRLs tm' (hLR^^10) (S1 a 1 (1+c) d) ([1;1;0]^^(7+a)*>[0]*>S2 4 4 c d).
Proof.
  unfold S1,S2.
  es' a c d.
Qed.

Lemma Ov2 a b d:
  sideRLs tm' (hLR^^65) (S2 a (17+b) 1 d) (S1 (65+a) b 16 (4+d)).
Proof.
  unfold S1,S2.
  es' a b d.
Qed.

Lemma Incs1 n a b c d:
  sideRLs tm' (hLR^^(n*6)) (S1 a (n*2+b) c d) (S1 (n*6+a) b (n*2+c) d).
Proof.
  gen a b c d.
  induction n; intros.
  1: esx.
  eapply sideRLs_trans_add with (n1:=6) (n2:=n*6).
  2: applys_eq (IHn (6+a) b (2+c) d); flia.
  apply Inc1.
Qed.

Lemma Incs2 n a b c d:
  sideRLs tm' (hLR^^(n*4)) (S2 a b (n*2+c) d) (S2 (n*4+a) (n*4+b) c d).
Proof.
  gen a b c d.
  induction n; intros.
  1: esx.
  eapply sideRLs_trans_add with (n1:=4) (n2:=n*4).
  2: applys_eq (IHn (4+a) (4+b) c d); flia.
  apply Inc2.
Qed.

Definition W n := [1;1;0]^^(3+n)++[0].

Lemma wall n a:
  segRLs tm' (hLR^^n) (hLR^^n) (W a) (W a).
Proof.
  unfold W.
  eapply segRLs_wall''; esx.
Qed.

Definition S1' a n d := S1 a 1 (1+(n*2+15)) d.

Lemma Incs12 a n d:
  sideRLs tm' (hLR^^(n*16+145)) (S1' a n d) (W (4+a)*>S1' (n*16+139) (n*2+7) (4+d)).
Proof.
  unfold S1'.
  replace (n*16+145) with (10+((n+7)*4+(65+(n*12+42)))) by lia.
  eapply sideRLs_trans_add.
  1: apply Ov1.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply wall.
  eapply sideRLs_trans_add.
  1: applys_eq (Incs2 (n+7) 4 4 1 d); flia.
  eapply sideRLs_trans_add.
  1: applys_eq (Ov2 (n*4+32) (n*4+15)); flia.
  applys_eq (Incs1 (n*2+7) (n*4+97) 1); flia.
Qed.

Definition RC a b := [1;0;0]^^a *> [1;0;1;1;1;1;1;1;1;1] *> [1;1;0;1;0]^^(1+b) *> [1;1;1;0] *> 0inf.

Lemma RInc a b:
  sideRLs tm (hRL^^2) (RC a b) (RC a (4+b)).
Proof.
  unfold RC.
  es' a b.
Qed.

Lemma RIncs n a b:
  sideRLs tm (hRL^^(n*2)) (RC a b) (RC a (n*4+b)).
Proof.
  gen b.
  induction n; intros.
  1: esx.
  eapply sideRLs_trans_add with (n1:=2) (n2:=n*2).
  1: apply RInc.
  applys_eq IHn; flia.
Qed.

Inductive LC: side->Prop :=
| LC_O a n d: LC (S1' a n d)
| LC_S n r: LC r -> LC (W n*>r).

Lemma LC_spec l:
  LC l ->
  exists l' n,
  sideRLs tm' (hLR^^(n*2)) l l' /\
  LC l' /\
  n<>O.
Proof.
  intro H.
  induction H.
  - eexists _,(n*24+201); split.
    + replace ((n*24+201)*2) with ((n*16+145)+((n*2+7)*16+145)) by lia.
      eapply sideRLs_trans_add.
      1: apply Incs12.
      eapply segRLs_sideRLs_concat.
      1: apply wall.
      apply Incs12.
    + split.
      1: repeat constructor.
      lia.
  - destruct IHLC as [l' [n' [I1 [I2 I3]]]].
    eexists _,_; repeat split.
    + eapply segRLs_sideRLs_concat.
      1: apply wall.
      apply I1.
    + econstructor.
      apply I2.
    + apply I3.
Qed.

Definition S' '(l,a,b) := l {{{ (hL,L) }}} RC a b.

Lemma lcons_1 n:
  lcons hL (hRL^^n) = (hLR^^n,hL).
Proof.
  induction n; cbn; trivial.
  rewrite IHn; trivial.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':= S' (W 9*>W 10*>W 11*>W 8*>W 11*>W 19*>W 24*>W 31 *>W 59*>S1' 83 0 20,9,599)).
  1: stepn' 6554240%N.
  eapply progress_nonhalt_cond with (P:=fun '(l,a,b) => LC l).
  2: repeat constructor.
  intros [[l a] b] HP.
  eapply LC_spec in HP.
  destruct HP as [l' [n' [I1 [I2 I3]]]].
  unshelve epose proof (sideRLs_concat_v2_L (lcons_1 _) _ I1 (RIncs n' a b)) as I4.
  1: destruct (n'*2) eqn:E; cbn; [lia|congruence].
  eexists (_,_,_); split.
  - apply I4.
  - apply I2.
Qed.

End TM2.


