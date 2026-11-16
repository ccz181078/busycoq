From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import BinaryCounter_v2.
From BusyCoq Require Import NatMod.
From BusyCoq Require Import SimplTape.

Open Scope list.

From BusyCoq Require Import Longitudinal.

Lemma pow4_mod3 m:
  4^m mod 3 = 1%nat.
Proof.
  induction m.
  1: trivial.
  rewrite Nat.pow_succ_r by lia.
  rewrite Nat.Div0.mul_mod by lia.
  rewrite IHm; trivial.
Qed.

Module TM71.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1LC1LB_1RD0LA_1LF0RE_---0RC_1RA1RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[1;1;0].
Notation d1 := <[0;1;0].
Notation "l <| r" := (l <{{B}} r) (at level 30).
Notation "l |> r" := (l {{F}}> r) (at level 30).

Definition LC a len n := BinDec d0 d1 len n (0inf <* <[1;0;0]^^a <* d1).

Lemma LC_Inc a len n r:
  S n<2^len ->
  LC a len (S n) <| r -->*
  LC a len n |> r.
Proof.
  intros H.
  eapply progress_evstep.
  apply LBinDec_spec with (qL:=[]) (qR:=[]); try assumption.
  es.
Qed.

Definition S0 a len n b :=
  LC a len n <| [1]^^b *> 0inf.

Opaque BinDec.

Lemma Inc a len n b:
  S n<2^len ->
  S0 a len (S n) b -->*
  S0 a len n (2+b).
Proof.
  unfold S0,LC.
  intros.
  follow LC_Inc.
  es.
Qed.

Lemma Incs a len n b:
  n<2^len ->
  S0 a len n b -->*
  S0 a len 0 (n*2+b).
Proof.
  gen b.
  induction n; intros.
  1: finish.
  follow Inc.
  follow IHn.
  1: lia.
  finish.
Qed.

Fixpoint f n :=
match n with
| O => O
| S n0 => f n0 + ((2^(n0*2+1)-1)*8+5)
end.

Lemma f_def n:
  f n + n*3 = (4^n/3)*16.
Proof.
  induction n.
  1: trivial.
  cbn[f].
  pose proof (pow4_mod3 n).
  replace (S n) with (n+1) by lia.
  repeat rewrite Nat.pow_add_r.
  rewrite (Nat.mul_comm n 2).
  rewrite Nat.pow_mul_r.
  cbn[Nat.pow].
  cbn[Nat.mul].
  cbn[Nat.add].
  pose proof (Nat.pow_nonzero 4 n).
  remember (4^n) as v1.
  epose proof (Nat.Div0.div_mod v1 3).
  rewrite H in H1.
  replace (v1*4) with (v1+v1*3) by lia.
  rewrite Nat.div_add by lia.
  lia.
Qed.

Lemma f_def' n:
  f n = (4^n/3)*16-n*3.
Proof.
  pose proof (f_def n); lia.
Qed.

Lemma f_ge n:
  4^n/3*16 >= n*3.
Proof.
  pose proof (f_def n) as H.
  lia.
Qed.

Lemma OvIncs a len b:
  S0 (1+a) (len) 0 (3+b) -->*
  S0 a (len+2) 0 (3+(2^len-1)*8+5+b).
Proof.
  mid (S0 a (len+2) (2^(len+2)-1) (2+b)).
  - unfold S0,LC.
    rw_Bin.
    es.
  - epose proof (Nat.pow_nonzero 2 len).
    follow Incs; repeat rewrite Nat.pow_add_r; cbn.
    1: lia.
    finish.
Qed.

Lemma OvIncss a a0 b:
  S0 (a+a0) 1 0 (3+b) -->*
  S0 a0 (1+a*2) 0 (3+(f a)+b).
Proof.
  gen a0 b.
  induction a; intros.
  1: cbn[f]; finish.
  cbn[f].
  specialize (IHa (S a0) b).
  follow IHa.
  follow OvIncs.
  fold Nat.add.
  rewrite (Nat.add_comm 1 (a*2)).
  finish.
Qed.

Lemma OvIncss' a b:
  S0 a 1 0 (3+b) -->*
  S0 0 (1+a*2) 0 (3+(4^a/3*16-a*3)+b).
Proof.
  epose proof (OvIncss a 0 b) as H.
  follow H.
  rewrite f_def'.
  finish.
Qed.

Definition S1 a b :=
  0inf <{{C}} [1;1;0]^^a *> [1]^^b *> 0inf.

Lemma Inc1 a b:
  S1 a (3+b) -->*
  S1 (2+a) b.
Proof.
  unfold S1.
  es.
Qed.

Lemma Incs1 a b n:
  S1 a (n*3+b) -->*
  S1 (n*2+a) b.
Proof.
  gen a b.
  ind n Inc1.
Qed.

Definition S2 a b := S0 0 a 0 b.

Lemma Ov0 a b:
  halts tm (S2 a (0+b*3)).
Proof.
  unfold S2,S0,LC.
  rw_Bin.
  eapply halts_evstep.
  2: {
    mid (S1 (1+a) (b*3+1)).
    1: es.
    follow Incs1.
    unfold S1.
    repeat (step1 || sr).
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

Definition S3 x := S2 (x*2+1) (4^x/3*16-x*3+5).

Lemma Ov1 a b:
  S2 a (1+b*3) -->*
  S3 (b*2+a+1).
Proof.
  unfold S3,S2.
  mid (S0 (1+a+b*2) 1 0 5).
  - unfold S0,LC.
    rw_Bin.
    mid (S1 (1+a) (b*3+2)).
    1: es.
    follow Incs1.
    unfold S1.
    es.
  - follow OvIncss'.
    replace (1+a+b*2) with (b*2+a+1) by lia.
    finish.
Qed.

Lemma div_sub a b c:
  c<>O ->
  a>=b*c ->
  (a-b*c)/c = a/c-b /\
  a/c>=b.
Proof.
  intros.
  replace (a/c) with ((a-b*c+b*c)/c) by (f_equal; lia).
  rewrite Nat.div_add by lia.
  lia.
Qed.

Lemma Ov1' x:
  (4^x/3*16-x*3+5) mod 3 = 1%nat ->
  S3 x -->*
  S3 ((4^x/3*16+5)/3*2+2).
Proof.
  intros H.
  eapply evstep_trans.
  - unfold S3.
    rewrite (div_mod' _ _ _ H).
    apply Ov1.
  - epose proof (f_ge x).
    replace (4^x/3*16-x*3+5) with (4^x/3*16+5-x*3) by lia.
    unshelve epose proof (div_sub (4^x/3*16+5) x 3 _ _) as [I1 I2].
    1,2: lia.
    rewrite I1.
    finish.
Qed.

Lemma Ov2 a b:
  S2 a (2+b*3) -->*
  S3 (b*2+a+2).
Proof.
  unfold S3,S2.
  mid (S0 (2+a+b*2) 1 0 5).
  - unfold S0,LC.
    rw_Bin.
    mid (S1 (1+a) ((b+1)*3+0)).
    1: es.
    follow Incs1.
    unfold S1.
    es.
  - follow OvIncss'.
    replace (2+a+b*2) with (b*2+a+2) by lia.
    finish.
Qed.

Lemma Ov2' x:
  (4^x/3*16-x*3+5) mod 3 = 2%nat ->
  S3 x -->*
  S3 ((4^x/3*16+5)/3*2+3).
Proof.
  intros H.
  eapply evstep_trans.
  - unfold S3.
    rewrite (div_mod' _ _ _ H).
    apply Ov2.
  - epose proof (f_ge x).
    replace (4^x/3*16-x*3+5) with (4^x/3*16+5-x*3) by lia.
    unshelve epose proof (div_sub (4^x/3*16+5) x 3 _ _) as [I1 I2].
    1,2: lia.
    rewrite I1.
    finish.
Qed.

Lemma Ov0' x:
  (4^x/3*16-x*3+5) mod 3 = 0%nat ->
  halts tm (S3 x).
Proof.
  intros H.
  unfold S3.
  rewrite (div_mod' _ _ _ H).
  apply Ov0.
Qed.

Transparent BinDec.

Lemma init: c0 -->* S3 0.
Proof.
  unfold S3,S2,S0; cbn; solve_init.
Qed.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
    follow init.
    eapply evstep_trans.
    1: apply Ov2'.
    1: reflexivity.
    cbn.
    eapply evstep_trans.
    1: apply Ov1'.
    1: reflexivity.
    eapply evstep_trans.
    1: apply Ov2'.
    1: rw_mod; reflexivity.
    eapply evstep_trans.
    1: apply Ov2'.
    1: rw_mod; reflexivity.
    eapply evstep_trans.
    1: apply Ov2'.
    1: rw_mod; reflexivity.
    eapply evstep_trans.
    1: apply Ov1'.
    1: rw_mod; reflexivity.
    eapply evstep_trans.
    1: apply Ov2'.
    1: rw_mod; reflexivity.
    finish.
  }
  apply Ov0'.
  rw_mod. reflexivity.
  Unshelve.
  all: match goal with
       | |- 4^?a/3*16 >= ?a*3 => apply f_ge
       | _ => solve_ge
       end.
Qed.

End TM71.


Module TM72.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1LC1LB_1RD0LA_1RB0RE_---0RC_1RA1RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[1;1;0].
Notation d1 := <[0;1;0].
Notation "l <| r" := (l <{{B}} r) (at level 30).
Notation "l |> r" := (l {{F}}> r) (at level 30).

Definition LC a len n := BinDec d0 d1 len n (0inf <* <[1;0;0]^^a <* d1).

Lemma LC_Inc a len n r:
  S n<2^len ->
  LC a len (S n) <| r -->*
  LC a len n |> r.
Proof.
  intros H.
  eapply progress_evstep.
  apply LBinDec_spec with (qL:=[]) (qR:=[]); try assumption.
  es.
Qed.

Definition S0 a len n b :=
  LC a len n <| [1]^^b *> 0inf.

Opaque BinDec.

Lemma Inc a len n b:
  S n<2^len ->
  S0 a len (S n) b -->*
  S0 a len n (2+b).
Proof.
  unfold S0,LC.
  intros.
  follow LC_Inc.
  es.
Qed.

Lemma Incs a len n b:
  n<2^len ->
  S0 a len n b -->*
  S0 a len 0 (n*2+b).
Proof.
  gen b.
  induction n; intros.
  1: finish.
  follow Inc.
  follow IHn.
  1: lia.
  finish.
Qed.

Fixpoint f n :=
match n with
| O => O
| S n0 => f n0 + ((2^(n0*2+1)-1)*8+5)
end.

Lemma f_def n:
  f n + n*3 = (4^n/3)*16.
Proof.
  induction n.
  1: trivial.
  cbn[f].
  pose proof (pow4_mod3 n).
  replace (S n) with (n+1) by lia.
  repeat rewrite Nat.pow_add_r.
  rewrite (Nat.mul_comm n 2).
  rewrite Nat.pow_mul_r.
  cbn[Nat.pow].
  cbn[Nat.mul].
  cbn[Nat.add].
  pose proof (Nat.pow_nonzero 4 n).
  remember (4^n) as v1.
  epose proof (Nat.Div0.div_mod v1 3).
  rewrite H in H1.
  replace (v1*4) with (v1+v1*3) by lia.
  rewrite Nat.div_add by lia.
  lia.
Qed.

Lemma f_def' n:
  f n = (4^n/3)*16-n*3.
Proof.
  pose proof (f_def n); lia.
Qed.

Lemma f_ge n:
  4^n/3*16 >= n*3.
Proof.
  pose proof (f_def n) as H.
  lia.
Qed.

Lemma OvIncs a len b:
  S0 (1+a) (len) 0 (3+b) -->*
  S0 a (len+2) 0 (3+(2^len-1)*8+5+b).
Proof.
  mid (S0 a (len+2) (2^(len+2)-1) (2+b)).
  - unfold S0,LC.
    rw_Bin.
    es.
  - epose proof (Nat.pow_nonzero 2 len).
    follow Incs; repeat rewrite Nat.pow_add_r; cbn.
    1: lia.
    finish.
Qed.

Lemma OvIncss a a0 b:
  S0 (a+a0) 1 0 (3+b) -->*
  S0 a0 (1+a*2) 0 (3+(f a)+b).
Proof.
  gen a0 b.
  induction a; intros.
  1: cbn[f]; finish.
  cbn[f].
  specialize (IHa (S a0) b).
  follow IHa.
  follow OvIncs.
  fold Nat.add.
  rewrite (Nat.add_comm 1 (a*2)).
  finish.
Qed.

Lemma OvIncss' a b:
  S0 a 1 0 (3+b) -->*
  S0 0 (1+a*2) 0 (3+(4^a/3*16-a*3)+b).
Proof.
  epose proof (OvIncss a 0 b) as H.
  follow H.
  rewrite f_def'.
  finish.
Qed.

Definition S1 a b :=
  0inf <{{C}} [1;1;0]^^a *> [1]^^b *> 0inf.

Lemma Inc1 a b:
  S1 a (3+b) -->*
  S1 (2+a) b.
Proof.
  unfold S1.
  es.
Qed.

Lemma Incs1 a b n:
  S1 a (n*3+b) -->*
  S1 (n*2+a) b.
Proof.
  gen a b.
  ind n Inc1.
Qed.

Definition S2 a b := S0 0 a 0 b.

Lemma Ov0 a b:
  halts tm (S2 a (0+b*3)).
Proof.
  unfold S2,S0,LC.
  rw_Bin.
  eapply halts_evstep.
  2: {
    mid (S1 (1+a) (b*3+1)).
    1: es.
    follow Incs1.
    unfold S1.
    repeat (step1 || sr).
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

Definition S3 x := S2 (x*2+1) (4^x/3*16-x*3+5).

Lemma Ov1 a b:
  S2 a (1+b*3) -->*
  S3 (b*2+a+1).
Proof.
  unfold S3,S2.
  mid (S0 (1+a+b*2) 1 0 5).
  - unfold S0,LC.
    rw_Bin.
    mid (S1 (1+a) (b*3+2)).
    1: es.
    follow Incs1.
    unfold S1.
    es.
  - follow OvIncss'.
    replace (1+a+b*2) with (b*2+a+1) by lia.
    finish.
Qed.

Lemma div_sub a b c:
  c<>O ->
  a>=b*c ->
  (a-b*c)/c = a/c-b /\
  a/c>=b.
Proof.
  intros.
  replace (a/c) with ((a-b*c+b*c)/c) by (f_equal; lia).
  rewrite Nat.div_add by lia.
  lia.
Qed.

Lemma Ov1' x:
  (4^x/3*16-x*3+5) mod 3 = 1%nat ->
  S3 x -->*
  S3 ((4^x/3*16+5)/3*2+2).
Proof.
  intros H.
  eapply evstep_trans.
  - unfold S3.
    rewrite (div_mod' _ _ _ H).
    apply Ov1.
  - epose proof (f_ge x).
    replace (4^x/3*16-x*3+5) with (4^x/3*16+5-x*3) by lia.
    unshelve epose proof (div_sub (4^x/3*16+5) x 3 _ _) as [I1 I2].
    1,2: lia.
    rewrite I1.
    finish.
Qed.

Lemma Ov2 a b:
  S2 a (2+b*3) -->*
  S3 (b*2+a+2).
Proof.
  unfold S3,S2.
  mid (S0 (2+a+b*2) 1 0 5).
  - unfold S0,LC.
    rw_Bin.
    mid (S1 (1+a) ((b+1)*3+0)).
    1: es.
    follow Incs1.
    unfold S1.
    es.
  - follow OvIncss'.
    replace (2+a+b*2) with (b*2+a+2) by lia.
    finish.
Qed.

Lemma Ov2' x:
  (4^x/3*16-x*3+5) mod 3 = 2%nat ->
  S3 x -->*
  S3 ((4^x/3*16+5)/3*2+3).
Proof.
  intros H.
  eapply evstep_trans.
  - unfold S3.
    rewrite (div_mod' _ _ _ H).
    apply Ov2.
  - epose proof (f_ge x).
    replace (4^x/3*16-x*3+5) with (4^x/3*16+5-x*3) by lia.
    unshelve epose proof (div_sub (4^x/3*16+5) x 3 _ _) as [I1 I2].
    1,2: lia.
    rewrite I1.
    finish.
Qed.

Lemma Ov0' x:
  (4^x/3*16-x*3+5) mod 3 = 0%nat ->
  halts tm (S3 x).
Proof.
  intros H.
  unfold S3.
  rewrite (div_mod' _ _ _ H).
  apply Ov0.
Qed.

Transparent BinDec.

Lemma init: c0 -->* S3 0.
Proof.
  unfold S3,S2,S0; cbn; solve_init.
Qed.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
    follow init.
    eapply evstep_trans.
    1: apply Ov2'.
    1: reflexivity.
    cbn.
    eapply evstep_trans.
    1: apply Ov1'.
    1: reflexivity.
    eapply evstep_trans.
    1: apply Ov2'.
    1: rw_mod; reflexivity.
    eapply evstep_trans.
    1: apply Ov2'.
    1: rw_mod; reflexivity.
    eapply evstep_trans.
    1: apply Ov2'.
    1: rw_mod; reflexivity.
    eapply evstep_trans.
    1: apply Ov1'.
    1: rw_mod; reflexivity.
    eapply evstep_trans.
    1: apply Ov2'.
    1: rw_mod; reflexivity.
    finish.
  }
  apply Ov0'.
  rw_mod. reflexivity.
  Unshelve.
  all: match goal with
       | |- 4^?a/3*16 >= ?a*3 => apply f_ge
       | _ => solve_ge
       end.
Qed.

End TM72.


Module TM73.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1LC1LB_1RD0LA_1RF0RE_---0RC_1RA1RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[1;1;0].
Notation d1 := <[0;1;0].
Notation "l <| r" := (l <{{B}} r) (at level 30).
Notation "l |> r" := (l {{F}}> r) (at level 30).

Definition LC a len n := BinDec d0 d1 len n (0inf <* <[1;0;0]^^a <* d1).

Lemma LC_Inc a len n r:
  S n<2^len ->
  LC a len (S n) <| r -->*
  LC a len n |> r.
Proof.
  intros H.
  eapply progress_evstep.
  apply LBinDec_spec with (qL:=[]) (qR:=[]); try assumption.
  es.
Qed.

Definition S0 a len n b :=
  LC a len n <| [1]^^b *> 0inf.

Opaque BinDec.

Lemma Inc a len n b:
  S n<2^len ->
  S0 a len (S n) b -->*
  S0 a len n (2+b).
Proof.
  unfold S0,LC.
  intros.
  follow LC_Inc.
  es.
Qed.

Lemma Incs a len n b:
  n<2^len ->
  S0 a len n b -->*
  S0 a len 0 (n*2+b).
Proof.
  gen b.
  induction n; intros.
  1: finish.
  follow Inc.
  follow IHn.
  1: lia.
  finish.
Qed.

Fixpoint f n :=
match n with
| O => O
| S n0 => f n0 + ((2^(n0*2+1)-1)*8+5)
end.

Lemma f_def n:
  f n + n*3 = (4^n/3)*16.
Proof.
  induction n.
  1: trivial.
  cbn[f].
  pose proof (pow4_mod3 n).
  replace (S n) with (n+1) by lia.
  repeat rewrite Nat.pow_add_r.
  rewrite (Nat.mul_comm n 2).
  rewrite Nat.pow_mul_r.
  cbn[Nat.pow].
  cbn[Nat.mul].
  cbn[Nat.add].
  pose proof (Nat.pow_nonzero 4 n).
  remember (4^n) as v1.
  epose proof (Nat.Div0.div_mod v1 3).
  rewrite H in H1.
  replace (v1*4) with (v1+v1*3) by lia.
  rewrite Nat.div_add by lia.
  lia.
Qed.

Lemma f_def' n:
  f n = (4^n/3)*16-n*3.
Proof.
  pose proof (f_def n); lia.
Qed.

Lemma f_ge n:
  4^n/3*16 >= n*3.
Proof.
  pose proof (f_def n) as H.
  lia.
Qed.

Lemma OvIncs a len b:
  S0 (1+a) (len) 0 (3+b) -->*
  S0 a (len+2) 0 (3+(2^len-1)*8+5+b).
Proof.
  mid (S0 a (len+2) (2^(len+2)-1) (2+b)).
  - unfold S0,LC.
    rw_Bin.
    es.
  - epose proof (Nat.pow_nonzero 2 len).
    follow Incs; repeat rewrite Nat.pow_add_r; cbn.
    1: lia.
    finish.
Qed.

Lemma OvIncss a a0 b:
  S0 (a+a0) 1 0 (3+b) -->*
  S0 a0 (1+a*2) 0 (3+(f a)+b).
Proof.
  gen a0 b.
  induction a; intros.
  1: cbn[f]; finish.
  cbn[f].
  specialize (IHa (S a0) b).
  follow IHa.
  follow OvIncs.
  fold Nat.add.
  rewrite (Nat.add_comm 1 (a*2)).
  finish.
Qed.

Lemma OvIncss' a b:
  S0 a 1 0 (3+b) -->*
  S0 0 (1+a*2) 0 (3+(4^a/3*16-a*3)+b).
Proof.
  epose proof (OvIncss a 0 b) as H.
  follow H.
  rewrite f_def'.
  finish.
Qed.

Definition S1 a b :=
  0inf <{{C}} [1;1;0]^^a *> [1]^^b *> 0inf.

Lemma Inc1 a b:
  S1 a (3+b) -->*
  S1 (2+a) b.
Proof.
  unfold S1.
  es.
Qed.

Lemma Incs1 a b n:
  S1 a (n*3+b) -->*
  S1 (n*2+a) b.
Proof.
  gen a b.
  ind n Inc1.
Qed.

Definition S2 a b := S0 0 a 0 b.

Lemma Ov0 a b:
  halts tm (S2 a (0+b*3)).
Proof.
  unfold S2,S0,LC.
  rw_Bin.
  eapply halts_evstep.
  2: {
    mid (S1 (1+a) (b*3+1)).
    1: es.
    follow Incs1.
    unfold S1.
    repeat (step1 || sr).
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

Definition S3 x := S2 (x*2+1) (4^x/3*16-x*3+5).

Lemma Ov1 a b:
  S2 a (1+b*3) -->*
  S3 (b*2+a+1).
Proof.
  unfold S3,S2.
  mid (S0 (1+a+b*2) 1 0 5).
  - unfold S0,LC.
    rw_Bin.
    mid (S1 (1+a) (b*3+2)).
    1: es.
    follow Incs1.
    unfold S1.
    es.
  - follow OvIncss'.
    replace (1+a+b*2) with (b*2+a+1) by lia.
    finish.
Qed.

Lemma div_sub a b c:
  c<>O ->
  a>=b*c ->
  (a-b*c)/c = a/c-b /\
  a/c>=b.
Proof.
  intros.
  replace (a/c) with ((a-b*c+b*c)/c) by (f_equal; lia).
  rewrite Nat.div_add by lia.
  lia.
Qed.

Lemma Ov1' x:
  (4^x/3*16-x*3+5) mod 3 = 1%nat ->
  S3 x -->*
  S3 ((4^x/3*16+5)/3*2+2).
Proof.
  intros H.
  eapply evstep_trans.
  - unfold S3.
    rewrite (div_mod' _ _ _ H).
    apply Ov1.
  - epose proof (f_ge x).
    replace (4^x/3*16-x*3+5) with (4^x/3*16+5-x*3) by lia.
    unshelve epose proof (div_sub (4^x/3*16+5) x 3 _ _) as [I1 I2].
    1,2: lia.
    rewrite I1.
    finish.
Qed.

Lemma Ov2 a b:
  S2 a (2+b*3) -->*
  S3 (b*2+a+2).
Proof.
  unfold S3,S2.
  mid (S0 (2+a+b*2) 1 0 5).
  - unfold S0,LC.
    rw_Bin.
    mid (S1 (1+a) ((b+1)*3+0)).
    1: es.
    follow Incs1.
    unfold S1.
    es.
  - follow OvIncss'.
    replace (2+a+b*2) with (b*2+a+2) by lia.
    finish.
Qed.

Lemma Ov2' x:
  (4^x/3*16-x*3+5) mod 3 = 2%nat ->
  S3 x -->*
  S3 ((4^x/3*16+5)/3*2+3).
Proof.
  intros H.
  eapply evstep_trans.
  - unfold S3.
    rewrite (div_mod' _ _ _ H).
    apply Ov2.
  - epose proof (f_ge x).
    replace (4^x/3*16-x*3+5) with (4^x/3*16+5-x*3) by lia.
    unshelve epose proof (div_sub (4^x/3*16+5) x 3 _ _) as [I1 I2].
    1,2: lia.
    rewrite I1.
    finish.
Qed.

Lemma Ov0' x:
  (4^x/3*16-x*3+5) mod 3 = 0%nat ->
  halts tm (S3 x).
Proof.
  intros H.
  unfold S3.
  rewrite (div_mod' _ _ _ H).
  apply Ov0.
Qed.

Transparent BinDec.

Lemma init: c0 -->* S3 0.
Proof.
  unfold S3,S2,S0; cbn; solve_init.
Qed.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
    follow init.
    eapply evstep_trans.
    1: apply Ov2'.
    1: reflexivity.
    cbn.
    eapply evstep_trans.
    1: apply Ov1'.
    1: reflexivity.
    eapply evstep_trans.
    1: apply Ov2'.
    1: rw_mod; reflexivity.
    eapply evstep_trans.
    1: apply Ov2'.
    1: rw_mod; reflexivity.
    eapply evstep_trans.
    1: apply Ov2'.
    1: rw_mod; reflexivity.
    eapply evstep_trans.
    1: apply Ov1'.
    1: rw_mod; reflexivity.
    eapply evstep_trans.
    1: apply Ov2'.
    1: rw_mod; reflexivity.
    finish.
  }
  apply Ov0'.
  rw_mod. reflexivity.
  Unshelve.
  all: match goal with
       | |- 4^?a/3*16 >= ?a*3 => apply f_ge
       | _ => solve_ge
       end.
Qed.

End TM73.


Module TM74.

Definition tm := Eval compute in (TM_from_str "1RB1RC_1LC1RE_1LD0LB_1RE1LC_1LE0RF_---1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := [0;1;0;1;0;1].
Notation d1 := [1;1;1;1;1;1].
Notation hR1 := (A,<[0;1]).
Notation hL1 := (D,[1;1]).
Notation hR2 := (C,<[1;1]).
Notation hL2 := (B,[0;1]).
Notation hRL := [(hR1,hL1);(hR2,hL2)].
Notation hRL1 := [(hR1,hL1)].

Notation d0a := [1;1;0;1;0;1;0;1].
Notation d1a := [0;1;1;1;1;1;1;1].

Notation d0b := [0;1;1;1;0;1;0;1;0;1].
Notation d1b := [1;1;0;1;1;1;1;1;1;1].

Notation d0c := [0;1;0;1;1;1;0;1].
Notation d1c := [1;1;1;1;0;1;1;1].

Definition RC n := [1;0]^^n *> 0inf.
Notation hLR1 := [(hL1,hR1)].

Definition tm' := flip tm.

Lemma RIncs n m:
  sideRLs tm' (hLR1^^n) (RC m) (RC (n+m)).
Proof.
  unfold RC.
  induction n.
  - esx.
  - replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHn.
    esx.
Qed.

Notation "l |> r" := (l <* <[0;1] {{A}}> r) (at level 30).

Lemma Incs n m l l':
  sideRLs tm (hRL1^^n) l l' ->
  RC m |> l -->*
  RC (n+m) |> l'.
Proof.
  intros HL.
  apply (sideRLs_concat_1 HL (RIncs _ _)).
Qed.

Lemma d0_Incs k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^((n+1)*2^k-1)) (d0^^k *> r) (d1^^k *> r').
Proof.
  intros H.
  gen n r r'.
  induction k; intros.
  - cbn.
    applys_eq H; f_equal; lia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply (IHk _ _ _ H).
    cbn[Nat.pow].
    pose proof (Nat.pow_nonzero 2 k).
    remember ((n+1)*2^k-1) as v1.
    replace ((n+1)*(2*2^k)-1) with (v1*2+1) by lia.
    apply segRLs_addmul''; esx.
Qed.

Ltac solve_v1 :=
  intros H;
  eapply segRLs_sideRLs_concat; [|apply H];
  apply segRLs_addmul'';
  esx.

Lemma d0a_Inc n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+1)) (d0a *> r) (d1a *> r').
Proof.
  solve_v1.
Qed.

Lemma d0b_Inc n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+1)) (d0b *> r) (d1b *> r').
Proof.
  solve_v1.
Qed.

Lemma d0c_Inc n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+1)) (d0c *> r) (d1c *> r').
Proof.
  solve_v1.
Qed.

Notation d1x := [0;1;1;1;1;1].

Lemma d0_Inc n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL1^^(n*2+1)) (d0 *> r) (d1x *> r').
Proof.
  intros H.
  eapply segRLs_sideRLs_concat; [|apply H].
  replace n with (n+0) by lia.
  replace ((n+0)*2) with (n*2) by lia.
  do 2 rewrite lpow_add.
  rewrite lpow_mul.
  eapply segRLs_trans.
  - eapply segRLs_wall''.
    esx.
  - esx.
Qed.

Lemma lh_Inc r:
  sideRLs tm (hRL^^O) r r.
Proof. esx. Qed.

Ltac follow_Incs :=
  eapply evstep_trans; [
  apply Incs;
  apply d0_Inc;
  repeat
  match goal with
  | |- sideRLs _ _ (d0a*>_) _ => apply d0a_Inc
  | |- sideRLs _ _ (d0b*>_) _ => apply d0b_Inc
  | |- sideRLs _ _ (d0c*>_) _ => apply d0c_Inc
  | |- sideRLs _ _ (d0^^_*>_) _ => apply d0_Incs
  end;
  apply lh_Inc | ].

Lemma init:
  c0 -->*
  RC 1 |> d0 *> d0^^5 *> d0a *> d0c *> d0c *> [0;1;1;1;1] *> 0inf.
Proof.
  esx.
Qed.

Lemma Rst_1 a b:
  RC (2+a*3) |> d1x *> d1 ^^ (S b) *> d1a *> d1c *> d1c *> [0; 1; 1; 1; 1] *> 0inf -->*
  RC 1 |> d0 *> d0^^a *> d0b *> d0^^b *> d0c *> d0^^1 *> d0b *> [1;1;0;1;1;1;1] *> 0inf.
Proof.
  unfold RC.
  es.
Qed.

Lemma Rst_2 a b c:
  RC (2+a*3) |> d1x *>
     d1 ^^ b *>
     d1b *> d1 ^^ c *> d1c *> d1 ^^ 1 *> d1b *> [1; 1; 0; 1; 1; 1; 1] *> 0inf -->*
  RC 1 |> d0 *> d0^^a *> d0b *> d0^^b *> d0a *> d0^^c *> d0c *> d0^^1 *> d0b *> [0;1;1;1;1] *> 0inf.
Proof.
  unfold RC.
  es.
Qed.

Lemma Rst_3 a b c d:
  RC (1+a*3) |> d1x *>
   d1 ^^ b *>
   d1b *>
   d1 ^^ c *>
   d1a *> d1 ^^ d *> d1c *> d1 ^^ 1 *> d1b *> [0; 1; 1; 1; 1] *> 0inf -->*
  RC 1 |> d0 *> d0^^a *> d0a *> d0^^b *> d0a *> d0^^c *> d0a *> d0^^d *> d0c *> d0^^1 *> d0b *> [1;1;1] *> 0inf.
Proof.
  unfold RC.
  es.
Qed.

Lemma Rst_4 n n0 n1 n2 n3:
  n0>=1 ->
  RC (1+n*3) |> d1x *>
   d1 ^^ n0 *>
   d1a *>
   d1 ^^ n1 *>
   d1a *>
   d1 ^^ n2 *> d1a *> d1 ^^ n3 *> d1c *> d1 ^^ 1 *> d1b *> [1; 1; 1] *> 0inf -->*
  RC 1 |> d0 *> d0^^n *> d0a *> d0^^(n0-1) *> d0c *> d0^^n1 *> d0c *> d0^^n2 *> d0c *> d0^^(n3+1) *> d0b *> d0c *> [0;1;0;1;1] *> 0inf.
Proof.
  intros Hn.
  replace n0 with (n0-1+1) by lia.
  rewrite Nat.add_sub.
  unfold RC.
  es.
Qed.

Lemma Rst_5 n n0 n1 n2 n3 n4:
  n0>=1 ->
  n4>=1 ->
   RC (2+n*3)
|> d1x *>
   d1 ^^ n0 *>
   d1a *>
   d1 ^^ n1 *>
   d1c *>
   d1 ^^ n2 *>
   d1c *>
   d1 ^^ n3 *> d1c *> d1 ^^ n4 *> d1b *> d1c *> [0; 1; 0; 1; 1] *> 0inf -->*
  RC 1 |> d0 *> d0^^n *> d0b *> d0^^(n0-1) *> d0c *> d0^^(n1+1) *> d0b *> d0^^n2 *> d0a *> d0^^n3 *> d0a *> d0^^(n4-1) *> d0c *> d0^^1 *> [0;1;1;1;1; 1;1;1;0;1;1] *> 0inf.
Proof.
  intros.
  replace n0 with (n0-1+1) by lia.
  replace n4 with (n4-1+1) by lia.
  repeat rewrite Nat.add_sub.
  unfold RC.
  es.
Qed.

Lemma Rst_6 n n0 n1 n2 n3 n4 n5:
  halts tm (
  RC (2+n*3)
|> d1x *>
   d1 ^^ n0 *>
   d1b *>
   d1 ^^ n1 *>
   d1c *>
   d1 ^^ n2 *>
   d1b *>
   d1 ^^ n3 *>
   d1a *>
   d1 ^^ n4 *>
   d1a *>
   d1 ^^ n5 *> d1c *> d1 ^^ 1 *> [0; 1; 1; 1; 1; 1; 1; 1; 0; 1; 1] *> 0inf).
Proof.
  unfold RC.
  esx.
Qed.


Ltac R_mod :=
match goal with
| |- RC ?b |> _ -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
  follow init.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  follow Rst_1.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  follow Rst_2.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  follow Rst_3.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  eapply evstep_trans.
  1: apply Rst_4; solve_ge.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  eapply evstep_trans.
  1: apply Rst_5; solve_ge.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  finish.
  }
  apply Rst_6.
  Unshelve.
  all: solve_ge.
Qed.

End TM74.


Module TM75.

Definition tm := Eval compute in (TM_from_str "1RB1RC_1LC0RF_1LD0LB_1RE1LC_---1RC_1RA0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := [0;1;0;1;0;1].
Notation d1 := [1;1;1;1;1;1].
Notation hR1 := (A,<[0;1]).
Notation hL1 := (D,[1;1]).
Notation hR2 := (C,<[1;1]).
Notation hL2 := (B,[0;1]).
Notation hRL := [(hR1,hL1);(hR2,hL2)].
Notation hRL1 := [(hR1,hL1)].

Notation d0a := [1;1;0;1;0;1;0;1].
Notation d1a := [0;1;1;1;1;1;1;1].

Notation d0b := [0;1;1;1;0;1;0;1;0;1].
Notation d1b := [1;1;0;1;1;1;1;1;1;1].

Notation d0c := [0;1;0;1;1;1;0;1].
Notation d1c := [1;1;1;1;0;1;1;1].

Definition RC n := [1;0]^^n *> 0inf.
Notation hLR1 := [(hL1,hR1)].

Definition tm' := flip tm.

Lemma RIncs n m:
  sideRLs tm' (hLR1^^n) (RC m) (RC (n+m)).
Proof.
  unfold RC.
  induction n.
  - esx.
  - replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHn.
    esx.
Qed.

Notation "l |> r" := (l <* <[0;1] {{A}}> r) (at level 30).

Lemma Incs n m l l':
  sideRLs tm (hRL1^^n) l l' ->
  RC m |> l -->*
  RC (n+m) |> l'.
Proof.
  intros HL.
  apply (sideRLs_concat_1 HL (RIncs _ _)).
Qed.

Lemma d0_Incs k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^((n+1)*2^k-1)) (d0^^k *> r) (d1^^k *> r').
Proof.
  intros H.
  gen n r r'.
  induction k; intros.
  - cbn.
    applys_eq H; f_equal; lia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply (IHk _ _ _ H).
    cbn[Nat.pow].
    pose proof (Nat.pow_nonzero 2 k).
    remember ((n+1)*2^k-1) as v1.
    replace ((n+1)*(2*2^k)-1) with (v1*2+1) by lia.
    apply segRLs_addmul''; esx.
Qed.

Ltac solve_v1 :=
  intros H;
  eapply segRLs_sideRLs_concat; [|apply H];
  apply segRLs_addmul'';
  esx.

Lemma d0a_Inc n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+1)) (d0a *> r) (d1a *> r').
Proof.
  solve_v1.
Qed.

Lemma d0b_Inc n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+1)) (d0b *> r) (d1b *> r').
Proof.
  solve_v1.
Qed.

Lemma d0c_Inc n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+1)) (d0c *> r) (d1c *> r').
Proof.
  solve_v1.
Qed.

Notation d1x := [0;1;1;1;1;1].

Lemma d0_Inc n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL1^^(n*2+1)) (d0 *> r) (d1x *> r').
Proof.
  intros H.
  eapply segRLs_sideRLs_concat; [|apply H].
  replace n with (n+0) by lia.
  replace ((n+0)*2) with (n*2) by lia.
  do 2 rewrite lpow_add.
  rewrite lpow_mul.
  eapply segRLs_trans.
  - eapply segRLs_wall''.
    esx.
  - esx.
Qed.

Lemma lh_Inc r:
  sideRLs tm (hRL^^O) r r.
Proof. esx. Qed.

Ltac follow_Incs :=
  eapply evstep_trans; [
  apply Incs;
  apply d0_Inc;
  repeat
  match goal with
  | |- sideRLs _ _ (d0a*>_) _ => apply d0a_Inc
  | |- sideRLs _ _ (d0b*>_) _ => apply d0b_Inc
  | |- sideRLs _ _ (d0c*>_) _ => apply d0c_Inc
  | |- sideRLs _ _ (d0^^_*>_) _ => apply d0_Incs
  end;
  apply lh_Inc | ].

Lemma init:
  c0 -->*
  RC 1 |> d0 *> d0^^5 *> d0a *> d0c *> d0c *> [0;1;1;1;1] *> 0inf.
Proof.
  esx.
Qed.

Lemma Rst_1 a b:
  RC (2+a*3) |> d1x *> d1 ^^ (S b) *> d1a *> d1c *> d1c *> [0; 1; 1; 1; 1] *> 0inf -->*
  RC 1 |> d0 *> d0^^a *> d0b *> d0^^b *> d0c *> d0^^1 *> d0b *> [1;1;0;1;1;1;1] *> 0inf.
Proof.
  unfold RC.
  es.
Qed.

Lemma Rst_2 a b c:
  RC (2+a*3) |> d1x *>
     d1 ^^ b *>
     d1b *> d1 ^^ c *> d1c *> d1 ^^ 1 *> d1b *> [1; 1; 0; 1; 1; 1; 1] *> 0inf -->*
  RC 1 |> d0 *> d0^^a *> d0b *> d0^^b *> d0a *> d0^^c *> d0c *> d0^^1 *> d0b *> [0;1;1;1;1] *> 0inf.
Proof.
  unfold RC.
  es.
Qed.

Lemma Rst_3 a b c d:
  RC (1+a*3) |> d1x *>
   d1 ^^ b *>
   d1b *>
   d1 ^^ c *>
   d1a *> d1 ^^ d *> d1c *> d1 ^^ 1 *> d1b *> [0; 1; 1; 1; 1] *> 0inf -->*
  RC 1 |> d0 *> d0^^a *> d0a *> d0^^b *> d0a *> d0^^c *> d0a *> d0^^d *> d0c *> d0^^1 *> d0b *> [1;1;1] *> 0inf.
Proof.
  unfold RC.
  es.
Qed.

Lemma Rst_4 n n0 n1 n2 n3:
  n0>=1 ->
  RC (1+n*3) |> d1x *>
   d1 ^^ n0 *>
   d1a *>
   d1 ^^ n1 *>
   d1a *>
   d1 ^^ n2 *> d1a *> d1 ^^ n3 *> d1c *> d1 ^^ 1 *> d1b *> [1; 1; 1] *> 0inf -->*
  RC 1 |> d0 *> d0^^n *> d0a *> d0^^(n0-1) *> d0c *> d0^^n1 *> d0c *> d0^^n2 *> d0c *> d0^^(n3+1) *> d0b *> d0c *> [0;1;0;1;1] *> 0inf.
Proof.
  intros Hn.
  replace n0 with (n0-1+1) by lia.
  rewrite Nat.add_sub.
  unfold RC.
  es.
Qed.

Lemma Rst_5 n n0 n1 n2 n3 n4:
  n0>=1 ->
  n4>=1 ->
   RC (2+n*3)
|> d1x *>
   d1 ^^ n0 *>
   d1a *>
   d1 ^^ n1 *>
   d1c *>
   d1 ^^ n2 *>
   d1c *>
   d1 ^^ n3 *> d1c *> d1 ^^ n4 *> d1b *> d1c *> [0; 1; 0; 1; 1] *> 0inf -->*
  RC 1 |> d0 *> d0^^n *> d0b *> d0^^(n0-1) *> d0c *> d0^^(n1+1) *> d0b *> d0^^n2 *> d0a *> d0^^n3 *> d0a *> d0^^(n4-1) *> d0c *> d0^^1 *> [0;1;1;1;1; 1;1;1;0;1;1] *> 0inf.
Proof.
  intros.
  replace n0 with (n0-1+1) by lia.
  replace n4 with (n4-1+1) by lia.
  repeat rewrite Nat.add_sub.
  unfold RC.
  es.
Qed.

Lemma Rst_6 n n0 n1 n2 n3 n4 n5:
  halts tm (
  RC (2+n*3)
|> d1x *>
   d1 ^^ n0 *>
   d1b *>
   d1 ^^ n1 *>
   d1c *>
   d1 ^^ n2 *>
   d1b *>
   d1 ^^ n3 *>
   d1a *>
   d1 ^^ n4 *>
   d1a *>
   d1 ^^ n5 *> d1c *> d1 ^^ 1 *> [0; 1; 1; 1; 1; 1; 1; 1; 0; 1; 1] *> 0inf).
Proof.
  unfold RC.
  esx.
Qed.


Ltac R_mod :=
match goal with
| |- RC ?b |> _ -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
  follow init.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  follow Rst_1.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  follow Rst_2.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  follow Rst_3.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  eapply evstep_trans.
  1: apply Rst_4; solve_ge.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  eapply evstep_trans.
  1: apply Rst_5; solve_ge.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  finish.
  }
  apply Rst_6.
  Unshelve.
  all: solve_ge.
Qed.

End TM75.


Module TM76.

Definition tm := Eval compute in (TM_from_str "1RB1RC_1LC0RF_1LD0LB_0RE1LC_---1LF_1RA0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := [0;1;0;1;0;1].
Notation d1 := [1;1;1;1;1;1].
Notation hR1 := (A,<[0;1]).
Notation hL1 := (D,[1;1]).
Notation hR2 := (C,<[1;1]).
Notation hL2 := (B,[0;1]).
Notation hRL := [(hR1,hL1);(hR2,hL2)].
Notation hRL1 := [(hR1,hL1)].

Notation d0a := [1;1;0;1;0;1;0;1].
Notation d1a := [0;1;1;1;1;1;1;1].

Notation d0b := [0;1;1;1;0;1;0;1;0;1].
Notation d1b := [1;1;0;1;1;1;1;1;1;1].

Notation d0c := [0;1;0;1;1;1;0;1].
Notation d1c := [1;1;1;1;0;1;1;1].

Definition RC n := [1;0]^^n *> 0inf.
Notation hLR1 := [(hL1,hR1)].

Definition tm' := flip tm.

Lemma RIncs n m:
  sideRLs tm' (hLR1^^n) (RC m) (RC (n+m)).
Proof.
  unfold RC.
  induction n.
  - esx.
  - replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHn.
    esx.
Qed.

Notation "l |> r" := (l <* <[0;1] {{A}}> r) (at level 30).

Lemma Incs n m l l':
  sideRLs tm (hRL1^^n) l l' ->
  RC m |> l -->*
  RC (n+m) |> l'.
Proof.
  intros HL.
  apply (sideRLs_concat_1 HL (RIncs _ _)).
Qed.

Lemma d0_Incs k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^((n+1)*2^k-1)) (d0^^k *> r) (d1^^k *> r').
Proof.
  intros H.
  gen n r r'.
  induction k; intros.
  - cbn.
    applys_eq H; f_equal; lia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply (IHk _ _ _ H).
    cbn[Nat.pow].
    pose proof (Nat.pow_nonzero 2 k).
    remember ((n+1)*2^k-1) as v1.
    replace ((n+1)*(2*2^k)-1) with (v1*2+1) by lia.
    apply segRLs_addmul''; esx.
Qed.

Ltac solve_v1 :=
  intros H;
  eapply segRLs_sideRLs_concat; [|apply H];
  apply segRLs_addmul'';
  esx.

Lemma d0a_Inc n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+1)) (d0a *> r) (d1a *> r').
Proof.
  solve_v1.
Qed.

Lemma d0b_Inc n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+1)) (d0b *> r) (d1b *> r').
Proof.
  solve_v1.
Qed.

Lemma d0c_Inc n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+1)) (d0c *> r) (d1c *> r').
Proof.
  solve_v1.
Qed.

Notation d1x := [0;1;1;1;1;1].

Lemma d0_Inc n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL1^^(n*2+1)) (d0 *> r) (d1x *> r').
Proof.
  intros H.
  eapply segRLs_sideRLs_concat; [|apply H].
  replace n with (n+0) by lia.
  replace ((n+0)*2) with (n*2) by lia.
  do 2 rewrite lpow_add.
  rewrite lpow_mul.
  eapply segRLs_trans.
  - eapply segRLs_wall''.
    esx.
  - esx.
Qed.

Lemma lh_Inc r:
  sideRLs tm (hRL^^O) r r.
Proof. esx. Qed.

Ltac follow_Incs :=
  eapply evstep_trans; [
  apply Incs;
  apply d0_Inc;
  repeat
  match goal with
  | |- sideRLs _ _ (d0a*>_) _ => apply d0a_Inc
  | |- sideRLs _ _ (d0b*>_) _ => apply d0b_Inc
  | |- sideRLs _ _ (d0c*>_) _ => apply d0c_Inc
  | |- sideRLs _ _ (d0^^_*>_) _ => apply d0_Incs
  end;
  apply lh_Inc | ].

Lemma init:
  c0 -->*
  RC 1 |> d0 *> d0^^5 *> d0a *> d0c *> d0c *> [0;1;1;1;1] *> 0inf.
Proof.
  esx.
Qed.

Lemma Rst_1 a b:
  RC (2+a*3) |> d1x *> d1 ^^ (S b) *> d1a *> d1c *> d1c *> [0; 1; 1; 1; 1] *> 0inf -->*
  RC 1 |> d0 *> d0^^a *> d0b *> d0^^b *> d0c *> d0^^1 *> d0b *> [1;1;0;1;1;1;1] *> 0inf.
Proof.
  unfold RC.
  es.
Qed.

Lemma Rst_2 a b c:
  RC (2+a*3) |> d1x *>
     d1 ^^ b *>
     d1b *> d1 ^^ c *> d1c *> d1 ^^ 1 *> d1b *> [1; 1; 0; 1; 1; 1; 1] *> 0inf -->*
  RC 1 |> d0 *> d0^^a *> d0b *> d0^^b *> d0a *> d0^^c *> d0c *> d0^^1 *> d0b *> [0;1;1;1;1] *> 0inf.
Proof.
  unfold RC.
  es.
Qed.

Lemma Rst_3 a b c d:
  RC (1+a*3) |> d1x *>
   d1 ^^ b *>
   d1b *>
   d1 ^^ c *>
   d1a *> d1 ^^ d *> d1c *> d1 ^^ 1 *> d1b *> [0; 1; 1; 1; 1] *> 0inf -->*
  RC 1 |> d0 *> d0^^a *> d0a *> d0^^b *> d0a *> d0^^c *> d0a *> d0^^d *> d0c *> d0^^1 *> d0b *> [1;1;1] *> 0inf.
Proof.
  unfold RC.
  es.
Qed.

Lemma Rst_4 n n0 n1 n2 n3:
  n0>=1 ->
  RC (1+n*3) |> d1x *>
   d1 ^^ n0 *>
   d1a *>
   d1 ^^ n1 *>
   d1a *>
   d1 ^^ n2 *> d1a *> d1 ^^ n3 *> d1c *> d1 ^^ 1 *> d1b *> [1; 1; 1] *> 0inf -->*
  RC 1 |> d0 *> d0^^n *> d0a *> d0^^(n0-1) *> d0c *> d0^^n1 *> d0c *> d0^^n2 *> d0c *> d0^^(n3+1) *> d0b *> d0c *> [0;1;0;1;1] *> 0inf.
Proof.
  intros Hn.
  replace n0 with (n0-1+1) by lia.
  rewrite Nat.add_sub.
  unfold RC.
  es.
Qed.

Lemma Rst_5 n n0 n1 n2 n3 n4:
  n0>=1 ->
  n4>=1 ->
   RC (2+n*3)
|> d1x *>
   d1 ^^ n0 *>
   d1a *>
   d1 ^^ n1 *>
   d1c *>
   d1 ^^ n2 *>
   d1c *>
   d1 ^^ n3 *> d1c *> d1 ^^ n4 *> d1b *> d1c *> [0; 1; 0; 1; 1] *> 0inf -->*
  RC 1 |> d0 *> d0^^n *> d0b *> d0^^(n0-1) *> d0c *> d0^^(n1+1) *> d0b *> d0^^n2 *> d0a *> d0^^n3 *> d0a *> d0^^(n4-1) *> d0c *> d0^^1 *> [0;1;1;1;1; 1;1;1;0;1;1] *> 0inf.
Proof.
  intros.
  replace n0 with (n0-1+1) by lia.
  replace n4 with (n4-1+1) by lia.
  repeat rewrite Nat.add_sub.
  unfold RC.
  es.
Qed.

Lemma Rst_6 n n0 n1 n2 n3 n4 n5:
  halts tm (
  RC (2+n*3)
|> d1x *>
   d1 ^^ n0 *>
   d1b *>
   d1 ^^ n1 *>
   d1c *>
   d1 ^^ n2 *>
   d1b *>
   d1 ^^ n3 *>
   d1a *>
   d1 ^^ n4 *>
   d1a *>
   d1 ^^ n5 *> d1c *> d1 ^^ 1 *> [0; 1; 1; 1; 1; 1; 1; 1; 0; 1; 1] *> 0inf).
Proof.
  unfold RC.
  esx.
Qed.


Ltac R_mod :=
match goal with
| |- RC ?b |> _ -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
  follow init.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  follow Rst_1.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  follow Rst_2.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  follow Rst_3.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  eapply evstep_trans.
  1: apply Rst_4; solve_ge.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  eapply evstep_trans.
  1: apply Rst_5; solve_ge.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  finish.
  }
  apply Rst_6.
  Unshelve.
  all: solve_ge.
Qed.

End TM76.


Module TM77.

Definition tm := Eval compute in (TM_from_str "1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---1LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := [0;1;0;1;0;1].
Notation d1 := [1;1;1;1;1;1].
Notation hR1 := (A,<[0;1]).
Notation hL1 := (D,[1;1]).
Notation hR2 := (C,<[1;1]).
Notation hL2 := (B,[0;1]).
Notation hRL := [(hR1,hL1);(hR2,hL2)].
Notation hRL1 := [(hR1,hL1)].

Notation d0a := [1;1;0;1;0;1;0;1].
Notation d1a := [0;1;1;1;1;1;1;1].

Notation d0b := [0;1;1;1;0;1;0;1;0;1].
Notation d1b := [1;1;0;1;1;1;1;1;1;1].

Notation d0c := [0;1;0;1;1;1;0;1].
Notation d1c := [1;1;1;1;0;1;1;1].

Definition RC n := [1;0]^^n *> 0inf.
Notation hLR1 := [(hL1,hR1)].

Definition tm' := flip tm.

Lemma RIncs n m:
  sideRLs tm' (hLR1^^n) (RC m) (RC (n+m)).
Proof.
  unfold RC.
  induction n.
  - esx.
  - replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHn.
    esx.
Qed.

Notation "l |> r" := (l <* <[0;1] {{A}}> r) (at level 30).

Lemma Incs n m l l':
  sideRLs tm (hRL1^^n) l l' ->
  RC m |> l -->*
  RC (n+m) |> l'.
Proof.
  intros HL.
  apply (sideRLs_concat_1 HL (RIncs _ _)).
Qed.

Lemma d0_Incs k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^((n+1)*2^k-1)) (d0^^k *> r) (d1^^k *> r').
Proof.
  intros H.
  gen n r r'.
  induction k; intros.
  - cbn.
    applys_eq H; f_equal; lia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply (IHk _ _ _ H).
    cbn[Nat.pow].
    pose proof (Nat.pow_nonzero 2 k).
    remember ((n+1)*2^k-1) as v1.
    replace ((n+1)*(2*2^k)-1) with (v1*2+1) by lia.
    apply segRLs_addmul''; esx.
Qed.

Ltac solve_v1 :=
  intros H;
  eapply segRLs_sideRLs_concat; [|apply H];
  apply segRLs_addmul'';
  esx.

Lemma d0a_Inc n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+1)) (d0a *> r) (d1a *> r').
Proof.
  solve_v1.
Qed.

Lemma d0b_Inc n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+1)) (d0b *> r) (d1b *> r').
Proof.
  solve_v1.
Qed.

Lemma d0c_Inc n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+1)) (d0c *> r) (d1c *> r').
Proof.
  solve_v1.
Qed.

Notation d1x := [0;1;1;1;1;1].

Lemma d0_Inc n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL1^^(n*2+1)) (d0 *> r) (d1x *> r').
Proof.
  intros H.
  eapply segRLs_sideRLs_concat; [|apply H].
  replace n with (n+0) by lia.
  replace ((n+0)*2) with (n*2) by lia.
  do 2 rewrite lpow_add.
  rewrite lpow_mul.
  eapply segRLs_trans.
  - eapply segRLs_wall''.
    esx.
  - esx.
Qed.

Lemma lh_Inc r:
  sideRLs tm (hRL^^O) r r.
Proof. esx. Qed.

Ltac follow_Incs :=
  eapply evstep_trans; [
  apply Incs;
  apply d0_Inc;
  repeat
  match goal with
  | |- sideRLs _ _ (d0a*>_) _ => apply d0a_Inc
  | |- sideRLs _ _ (d0b*>_) _ => apply d0b_Inc
  | |- sideRLs _ _ (d0c*>_) _ => apply d0c_Inc
  | |- sideRLs _ _ (d0^^_*>_) _ => apply d0_Incs
  end;
  apply lh_Inc | ].

Lemma init:
  c0 -->*
  RC 1 |> d0 *> d0^^5 *> d0a *> d0c *> d0c *> [0;1;1;1;1] *> 0inf.
Proof.
  esx.
Qed.

Lemma Rst_1 a b:
  RC (2+a*3) |> d1x *> d1 ^^ (S b) *> d1a *> d1c *> d1c *> [0; 1; 1; 1; 1] *> 0inf -->*
  RC 1 |> d0 *> d0^^a *> d0b *> d0^^b *> d0c *> d0^^1 *> d0b *> [1;1;0;1;1;1;1] *> 0inf.
Proof.
  unfold RC.
  es.
Qed.

Lemma Rst_2 a b c:
  RC (2+a*3) |> d1x *>
     d1 ^^ b *>
     d1b *> d1 ^^ c *> d1c *> d1 ^^ 1 *> d1b *> [1; 1; 0; 1; 1; 1; 1] *> 0inf -->*
  RC 1 |> d0 *> d0^^a *> d0b *> d0^^b *> d0a *> d0^^c *> d0c *> d0^^1 *> d0b *> [0;1;1;1;1] *> 0inf.
Proof.
  unfold RC.
  es.
Qed.

Lemma Rst_3 a b c d:
  RC (1+a*3) |> d1x *>
   d1 ^^ b *>
   d1b *>
   d1 ^^ c *>
   d1a *> d1 ^^ d *> d1c *> d1 ^^ 1 *> d1b *> [0; 1; 1; 1; 1] *> 0inf -->*
  RC 1 |> d0 *> d0^^a *> d0a *> d0^^b *> d0a *> d0^^c *> d0a *> d0^^d *> d0c *> d0^^1 *> d0b *> [1;1;1] *> 0inf.
Proof.
  unfold RC.
  es.
Qed.

Lemma Rst_4 n n0 n1 n2 n3:
  n0>=1 ->
  RC (1+n*3) |> d1x *>
   d1 ^^ n0 *>
   d1a *>
   d1 ^^ n1 *>
   d1a *>
   d1 ^^ n2 *> d1a *> d1 ^^ n3 *> d1c *> d1 ^^ 1 *> d1b *> [1; 1; 1] *> 0inf -->*
  RC 1 |> d0 *> d0^^n *> d0a *> d0^^(n0-1) *> d0c *> d0^^n1 *> d0c *> d0^^n2 *> d0c *> d0^^(n3+1) *> d0b *> d0c *> [0;1;0;1;1] *> 0inf.
Proof.
  intros Hn.
  replace n0 with (n0-1+1) by lia.
  rewrite Nat.add_sub.
  unfold RC.
  es.
Qed.

Lemma Rst_5 n n0 n1 n2 n3 n4:
  n0>=1 ->
  n4>=1 ->
   RC (2+n*3)
|> d1x *>
   d1 ^^ n0 *>
   d1a *>
   d1 ^^ n1 *>
   d1c *>
   d1 ^^ n2 *>
   d1c *>
   d1 ^^ n3 *> d1c *> d1 ^^ n4 *> d1b *> d1c *> [0; 1; 0; 1; 1] *> 0inf -->*
  RC 1 |> d0 *> d0^^n *> d0b *> d0^^(n0-1) *> d0c *> d0^^(n1+1) *> d0b *> d0^^n2 *> d0a *> d0^^n3 *> d0a *> d0^^(n4-1) *> d0c *> d0^^1 *> [0;1;1;1;1; 1;1;1;0;1;1] *> 0inf.
Proof.
  intros.
  replace n0 with (n0-1+1) by lia.
  replace n4 with (n4-1+1) by lia.
  repeat rewrite Nat.add_sub.
  unfold RC.
  es.
Qed.

Lemma Rst_6 n n0 n1 n2 n3 n4 n5:
  halts tm (
  RC (2+n*3)
|> d1x *>
   d1 ^^ n0 *>
   d1b *>
   d1 ^^ n1 *>
   d1c *>
   d1 ^^ n2 *>
   d1b *>
   d1 ^^ n3 *>
   d1a *>
   d1 ^^ n4 *>
   d1a *>
   d1 ^^ n5 *> d1c *> d1 ^^ 1 *> [0; 1; 1; 1; 1; 1; 1; 1; 0; 1; 1] *> 0inf).
Proof.
  unfold RC.
  esx.
Qed.


Ltac R_mod :=
match goal with
| |- RC ?b |> _ -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
  follow init.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  follow Rst_1.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  follow Rst_2.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  follow Rst_3.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  eapply evstep_trans.
  1: apply Rst_4; solve_ge.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  eapply evstep_trans.
  1: apply Rst_5; solve_ge.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  finish.
  }
  apply Rst_6.
  Unshelve.
  all: solve_ge.
Qed.

End TM77.


Module TM78.

Definition tm := Eval compute in (TM_from_str "1RB1RC_1LC1RE_1LD0LB_1RA1LC_1LE0RF_---1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := [0;1;0;1;0;1].
Notation d1 := [1;1;1;1;1;1].
Notation hR1 := (A,<[0;1]).
Notation hL1 := (D,[1;1]).
Notation hR2 := (C,<[1;1]).
Notation hL2 := (B,[0;1]).
Notation hRL := [(hR1,hL1);(hR2,hL2)].
Notation hRL1 := [(hR1,hL1)].

Notation d0a := [1;1;0;1;0;1;0;1].
Notation d1a := [0;1;1;1;1;1;1;1].

Notation d0b := [0;1;1;1;0;1;0;1;0;1].
Notation d1b := [1;1;0;1;1;1;1;1;1;1].

Notation d0c := [0;1;0;1;1;1;0;1].
Notation d1c := [1;1;1;1;0;1;1;1].

Definition RC n := [1;0]^^n *> 0inf.
Notation hLR1 := [(hL1,hR1)].

Definition tm' := flip tm.

Lemma RIncs n m:
  sideRLs tm' (hLR1^^n) (RC m) (RC (n+m)).
Proof.
  unfold RC.
  induction n.
  - esx.
  - replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHn.
    esx.
Qed.

Notation "l |> r" := (l <* <[0;1] {{A}}> r) (at level 30).

Lemma Incs n m l l':
  sideRLs tm (hRL1^^n) l l' ->
  RC m |> l -->*
  RC (n+m) |> l'.
Proof.
  intros HL.
  apply (sideRLs_concat_1 HL (RIncs _ _)).
Qed.

Lemma d0_Incs k n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^((n+1)*2^k-1)) (d0^^k *> r) (d1^^k *> r').
Proof.
  intros H.
  gen n r r'.
  induction k; intros.
  - cbn.
    applys_eq H; f_equal; lia.
  - cbn[lpow].
    do 2 rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply (IHk _ _ _ H).
    cbn[Nat.pow].
    pose proof (Nat.pow_nonzero 2 k).
    remember ((n+1)*2^k-1) as v1.
    replace ((n+1)*(2*2^k)-1) with (v1*2+1) by lia.
    apply segRLs_addmul''; esx.
Qed.

Ltac solve_v1 :=
  intros H;
  eapply segRLs_sideRLs_concat; [|apply H];
  apply segRLs_addmul'';
  esx.

Lemma d0a_Inc n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+1)) (d0a *> r) (d1a *> r').
Proof.
  solve_v1.
Qed.

Lemma d0b_Inc n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+1)) (d0b *> r) (d1b *> r').
Proof.
  solve_v1.
Qed.

Lemma d0c_Inc n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL^^(n*2+1)) (d0c *> r) (d1c *> r').
Proof.
  solve_v1.
Qed.

Notation d1x := [0;1;1;1;1;1].

Lemma d0_Inc n r r':
  sideRLs tm (hRL^^n) r r' ->
  sideRLs tm (hRL1^^(n*2+1)) (d0 *> r) (d1x *> r').
Proof.
  intros H.
  eapply segRLs_sideRLs_concat; [|apply H].
  replace n with (n+0) by lia.
  replace ((n+0)*2) with (n*2) by lia.
  do 2 rewrite lpow_add.
  rewrite lpow_mul.
  eapply segRLs_trans.
  - eapply segRLs_wall''.
    esx.
  - esx.
Qed.

Lemma lh_Inc r:
  sideRLs tm (hRL^^O) r r.
Proof. esx. Qed.

Ltac follow_Incs :=
  eapply evstep_trans; [
  apply Incs;
  apply d0_Inc;
  repeat
  match goal with
  | |- sideRLs _ _ (d0a*>_) _ => apply d0a_Inc
  | |- sideRLs _ _ (d0b*>_) _ => apply d0b_Inc
  | |- sideRLs _ _ (d0c*>_) _ => apply d0c_Inc
  | |- sideRLs _ _ (d0^^_*>_) _ => apply d0_Incs
  end;
  apply lh_Inc | ].

Lemma init:
  c0 -->*
  RC 1 |> d0 *> d0^^5 *> d0a *> d0c *> d0c *> [0;1;1;1;1] *> 0inf.
Proof.
  esx.
Qed.

Lemma Rst_1 a b:
  RC (2+a*3) |> d1x *> d1 ^^ (S b) *> d1a *> d1c *> d1c *> [0; 1; 1; 1; 1] *> 0inf -->*
  RC 1 |> d0 *> d0^^a *> d0b *> d0^^b *> d0c *> d0^^1 *> d0b *> [1;1;0;1;1;1;1] *> 0inf.
Proof.
  unfold RC.
  es.
Qed.

Lemma Rst_2 a b c:
  RC (2+a*3) |> d1x *>
     d1 ^^ b *>
     d1b *> d1 ^^ c *> d1c *> d1 ^^ 1 *> d1b *> [1; 1; 0; 1; 1; 1; 1] *> 0inf -->*
  RC 1 |> d0 *> d0^^a *> d0b *> d0^^b *> d0a *> d0^^c *> d0c *> d0^^1 *> d0b *> [0;1;1;1;1] *> 0inf.
Proof.
  unfold RC.
  es.
Qed.

Lemma Rst_3 a b c d:
  RC (1+a*3) |> d1x *>
   d1 ^^ b *>
   d1b *>
   d1 ^^ c *>
   d1a *> d1 ^^ d *> d1c *> d1 ^^ 1 *> d1b *> [0; 1; 1; 1; 1] *> 0inf -->*
  RC 1 |> d0 *> d0^^a *> d0a *> d0^^b *> d0a *> d0^^c *> d0a *> d0^^d *> d0c *> d0^^1 *> d0b *> [1;1;1] *> 0inf.
Proof.
  unfold RC.
  es.
Qed.

Lemma Rst_4 n n0 n1 n2 n3:
  n0>=1 ->
  RC (1+n*3) |> d1x *>
   d1 ^^ n0 *>
   d1a *>
   d1 ^^ n1 *>
   d1a *>
   d1 ^^ n2 *> d1a *> d1 ^^ n3 *> d1c *> d1 ^^ 1 *> d1b *> [1; 1; 1] *> 0inf -->*
  RC 1 |> d0 *> d0^^n *> d0a *> d0^^(n0-1) *> d0c *> d0^^n1 *> d0c *> d0^^n2 *> d0c *> d0^^(n3+1) *> d0b *> d0c *> [0;1;0;1;1] *> 0inf.
Proof.
  intros Hn.
  replace n0 with (n0-1+1) by lia.
  rewrite Nat.add_sub.
  unfold RC.
  es.
Qed.

Lemma Rst_5 n n0 n1 n2 n3 n4:
  n0>=1 ->
  n4>=1 ->
   RC (2+n*3)
|> d1x *>
   d1 ^^ n0 *>
   d1a *>
   d1 ^^ n1 *>
   d1c *>
   d1 ^^ n2 *>
   d1c *>
   d1 ^^ n3 *> d1c *> d1 ^^ n4 *> d1b *> d1c *> [0; 1; 0; 1; 1] *> 0inf -->*
  RC 1 |> d0 *> d0^^n *> d0b *> d0^^(n0-1) *> d0c *> d0^^(n1+1) *> d0b *> d0^^n2 *> d0a *> d0^^n3 *> d0a *> d0^^(n4-1) *> d0c *> d0^^1 *> [0;1;1;1;1; 1;1;1;0;1;1] *> 0inf.
Proof.
  intros.
  replace n0 with (n0-1+1) by lia.
  replace n4 with (n4-1+1) by lia.
  repeat rewrite Nat.add_sub.
  unfold RC.
  es.
Qed.

Lemma Rst_6 n n0 n1 n2 n3 n4 n5:
  halts tm (
  RC (2+n*3)
|> d1x *>
   d1 ^^ n0 *>
   d1b *>
   d1 ^^ n1 *>
   d1c *>
   d1 ^^ n2 *>
   d1b *>
   d1 ^^ n3 *>
   d1a *>
   d1 ^^ n4 *>
   d1a *>
   d1 ^^ n5 *> d1c *> d1 ^^ 1 *> [0; 1; 1; 1; 1; 1; 1; 1; 0; 1; 1] *> 0inf).
Proof.
  unfold RC.
  esx.
Qed.


Ltac R_mod :=
match goal with
| |- RC ?b |> _ -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
  follow init.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  follow Rst_1.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  follow Rst_2.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  follow Rst_3.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  eapply evstep_trans.
  1: apply Rst_4; solve_ge.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  eapply evstep_trans.
  1: apply Rst_5; solve_ge.
  follow_Incs.
  simpl_small_nat 600.
  R_mod.
  finish.
  }
  apply Rst_6.
  Unshelve.
  all: solve_ge.
Qed.

End TM78.


