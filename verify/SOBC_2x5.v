From BusyCoq Require Import Individual25.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import BinaryCounter25_v2.
From BusyCoq Require Import NatMod.

Open Scope list.

Lemma lt_mul2add1 a b:
  a<b ->
  a*2+1<b*2.
Proof. lia. Qed.

Lemma lt_mul2 a b:
  a<b ->
  a*2<b*2.
Proof. lia. Qed.

Lemma lt_pow2sub1 a:
  2^a-1<2^a.
Proof.
  pose proof (Nat.pow_nonzero 2 a).
  lia.
Qed.

Lemma lt_0_pow2 a:
  0<2^a.
Proof.
  pose proof (Nat.pow_nonzero 2 a).
  lia.
Qed.

Ltac solve_pow2_lt :=
  repeat (rewrite pow2_S || rewrite Nat.pow_add_r ||
  apply lt_pow2sub1 ||
  apply lt_0_pow2 ||
  apply lt_sub1 || apply lt_mul2add1 || apply lt_mul2 ||
  apply Nat.mul_lt_mono_pos_r).

Ltac follow00 I :=
  eapply evstep_trans; [ apply I | ].

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB2RA3LA4RB---_2LA3RB3RA1LB3LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Definition LC len n :=
  BinDec [2] [3] len n (0inf <* <[1;3]).

Lemma LC_Inc len n r:
  S n<2^len ->
  LC len (S n) <{{B}} r -->*
  LC len n {{A}}> r.
Proof.
  intros H.
  eapply progress_evstep.
  apply LBinDec_spec with (qL:=[]) (qR:=[]); try assumption.
  es.
Qed.

Definition S0 len n m :=
  LC len n <{{B}} [3] *> [1]^^m *> [1] *> 0inf.

Lemma Inc len n m:
  4+n<2^len ->
  S0 len (4+n) m -->*
  S0 len n (3+m).
Proof.
  intros H.
  cbn[Nat.add].
  unfold S0.
  repeat (follow LC_Inc; try lia; es; er).
Qed.

Lemma Incs {len n m k}:
  n+k*4<2^len ->
  S0 len (n+k*4) m -->*
  S0 len n (k*3+m) /\
  n<2^len.
Proof.
  rewrite Nat.add_comm.
  intros H.
  split. 2: lia.
  gen len n m.
  induction k; intros.
  1: finish.
  change (S k*4+n) with (4+(k*4+n)).
  follow Inc.
  follow IHk.
  1: lia.
  finish.
Qed.

Lemma Ov1 {a b}:
  1<2^a ->
  S0 a 1 b -->*
  S0 (b+a+2+1) ((2^(b+a+2)-1)*2) 2 /\
  ((2^(b+a+2)-1)*2)<2^(b+a+2+1).
Proof.
  intros H.
  pose proof (Nat.pow_nonzero 2 (b+a+2)).
  split.
  2: rewrite pow2_S; lia.
  unfold S0.
  follow LC_Inc; es; er.
  unfold LC.
  rw_Bin.
  2: rewrite pow2_S; lia.
  es.
Qed.

Lemma Ov2 {a b}:
  2<2^a ->
  S0 a 2 b -->*
  S0 (b+a+4) (2^(b+a+4)-1) 1 /\
  (2^(b+a+4)-1)<2^(b+a+4).
Proof.
  intros H.
  pose proof (Nat.pow_nonzero 2 (b+a+4)).
  split.
  2: lia.
  unfold S0.
  do 2 (follow LC_Inc; try lia; es; er).
  unfold LC.
  rw_Bin.
  es.
Qed.

Definition S1 n :=
  0inf <* <[1;3] <* [2]^^n {{A}}> [4;2] *> 0inf.

Lemma Ov3 {a b}:
  3<2^a ->
  S0 a 3 b -->*
  S1 (6+b+a).
Proof.
  intros H.
  unfold S0,S1.
  do 3 (follow LC_Inc; try lia; es; er).
  unfold LC.
  rw_Bin.
  es.
Qed.

Ltac R_mod :=
match goal with
| |- S0 ?a ?b ?c -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 4 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
  mid (S0 3 1 5).
  1: unfold S0; cbn; es.
  epose proof Ov1 as [H P].
  2: follow H.
  1: cbn; lia.
  clear H.
  change (5+3+2) with 10 in *.
  R_mod.
  epose proof (Incs P) as [H P0].
  follow00 H. clear H P.
  epose proof (Ov2 P0) as [H P1].
  follow00 H. clear H P0.
  R_mod.
  epose proof (Incs P1) as [H P2].
  follow00 H. clear H P1.
  epose proof (Ov3 P2) as H.
  follow00 H. clear H P2.
  finish.
  }
  eapply halted_halts.
  constructor.
  Unshelve.
  all:
  pose proof (Nat.pow_nonzero 2 10);
  try lia.
Qed.

End TM1.

Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB3LA4RB0RB2LA_1LB2LA3LA1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Definition LC len n :=
  BinDec <[1;0] <[1;1] len n (0inf <* <[1]).

Lemma LC_Inc len n r:
  S n<2^len ->
  LC len (S n) <{{A}} r -->*
  LC len n {{B}}> r.
Proof.
  intros H.
  eapply progress_evstep.
  apply LBinDec_spec with (qL:=[]) (qR:=[]); try assumption.
  es.
Qed.

Definition S0 len n m :=
  LC len n <{{A}} [3;2]^^m *> [1] *> 0inf.

Lemma Inc len n m:
  3+n<2^len ->
  S0 len (3+n) m -->*
  S0 len n (1+m).
Proof.
  intros H.
  cbn[Nat.add].
  unfold S0.
  repeat (follow LC_Inc; try lia; es; er).
Qed.

Lemma Incs {len n m k}:
  n+k*3<2^len ->
  S0 len (n+k*3) m -->*
  S0 len n (k+m) /\
  n<2^len.
Proof.
  rewrite Nat.add_comm.
  intros H.
  split. 2: lia.
  gen len n m.
  induction k; intros.
  1: finish.
  change (S k*3+n) with (3+(k*3+n)).
  follow Inc.
  follow IHk.
  1: lia.
  finish.
Qed.

Lemma Ov0 {a b}:
  0<2^(a+1) ->
  S0 (a+1) 0 (b+3) -->*
  S0 (a+1+b+1+1+1+1) (((((((2^a-1)*2+1)*2^b-1)*2)*2)*2)*2+1) 3 /\
  (((((((2^a-1)*2+1)*2^b-1)*2)*2)*2)*2+1)<2^(a+1+b+1+1+1+1).
Proof.
  intros H.
  split.
  2: solve_pow2_lt.
  unfold S0.
  unfold LC.
  rw_Bin.
  1: es.
  all: solve_pow2_lt.
Qed.

Lemma Ov2 {a b}:
  2<2^(a+1) ->
  S0 (a+1) 2 (b+3) -->*
  S0 (a+1+b+1+1+1+1) (((((2^a-1)*2+1)*2^b-1)*2*2*2+1)*2+1) 3 /\
  (((((2^a-1)*2+1)*2^b-1)*2*2*2+1)*2+1)<2^(a+1+b+1+1+1+1).
Proof.
  intros H.
  split.
  2: solve_pow2_lt.
  unfold S0.
  Opaque LC.
  follow LC_Inc; es; er.
  follow LC_Inc; try lia.
  Transparent LC.
  unfold LC.
  rw_Bin.
  1: es.
  all: solve_pow2_lt.
Qed.

Definition S1 a b := 0inf <* [1] <* <[1;0]^^a <* <[1;1]^^b <* [1] {{B}}> [4;1] *> 0inf.

Lemma Ov1 {a b}:
  1<2^(a+1) ->
  S0 (a+1) 1 (b+3) -->*
  S1 (a+1) (b+3).
Proof.
  intros H.
  unfold S0.
  follow LC_Inc.
  unfold LC.
  rw_Bin.
  es; er.
Qed.

Definition S0' a b :=
  S0 (a+1) b (3).

Lemma IncsOv0 {a b}:
  0+b*3<2^(a+1) ->
  S0' a (0+b*3) -->*
  S0' (a+b+4) ((((2^a-1)*2+1)*2^b-1)*16+1) /\
  ((((2^a-1)*2+1)*2^b-1)*16+1)<2^(a+b+4+1).
Proof.
  intros P.
  unfold S0'.
  epose proof (Incs P) as [H P0].
  epose proof (Ov0 P0) as [H0 P1].
  split.
  - follow H.
    follow H0.
    finish.
  - applys_eq P1.
    1: lia.
    f_equal; lia.
Qed.

Lemma IncsOv2 {a b}:
  2+b*3<2^(a+1) ->
  S0' a (2+b*3) -->*
  S0' (a+b+4) ((((2^a-1)*2+1)*2^b-1)*16+3) /\
  ((((2^a-1)*2+1)*2^b-1)*16+3)<2^(a+b+4+1).
Proof.
  intros P.
  unfold S0'.
  epose proof (Incs P) as [H P0].
  epose proof (Ov2 P0) as [H0 P1].
  split.
  - follow H.
    follow H0.
    finish.
  - applys_eq P1.
    1: lia.
    f_equal; lia.
Qed.

Lemma IncsOv1 {a b}:
  1+b*3<2^(a+1) ->
  S0' a (1+b*3) -->*
  S1 (a+1) (b+3).
Proof.
  intros P.
  unfold S0'.
  epose proof (Incs P) as [H P0].
  epose proof (Ov1 P0) as H0.
  follow H.
  follow H0.
  finish.
Qed.

Lemma Halt a b:
  halted tm (S1 a b).
Proof.
  constructor.
Qed.

Ltac R_mod :=
match goal with
| |- S0' ?a ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
  mid (S0' 5 45).
  1: es.
  R_mod.
  epose proof IncsOv0 as [H P].
  2: follow00 H.
  1: cbn; lia.
  clear H.
  change (45/3) with 15 in *.
  change (5+15+4) with 24 in *.
  R_mod.
  epose proof (IncsOv0 P) as [H P0].
  follow00 H. clear H P.
  R_mod.
  epose proof (IncsOv2 P0) as [H P1].
  follow00 H. clear H P0.
  R_mod.
  epose proof (IncsOv2 P1) as [H P2].
  follow00 H. clear H P1.
  R_mod.
  epose proof (IncsOv1 P2) as H.
  follow00 H. clear H P2.
  finish.
  }
  apply halted_halts.
  apply Halt.
  Unshelve.
  all: solve_ge.
Qed.

End TM2.

