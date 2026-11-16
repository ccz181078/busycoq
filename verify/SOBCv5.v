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

Module TM9.

Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC0RF_1RD1RC_1LE0RC_1LA1LE_---0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[1;1;0].
Notation d1 := <[0;1;0].
Notation "l <| r" := (l <{{E}} r) (at level 30).
Notation "l |> r" := (l {{C}}> r) (at level 30).

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
  0inf <{{A}} [1;1;0]^^a *> [1]^^b *> 0inf.

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

Lemma Ov1 a b:
  S2 a (1+b*3) -->*
  S2 ((b * 2 + a + 1) * 2 + 1)
    ((4 ^ (b * 2 + a + 1) / 3 * 16 - (b * 2 + a + 1) * 3) + 5).
Proof.
  unfold S2.
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

Lemma Ov2 a b:
  S2 a (2+b*3) -->*
  S2 ((b * 2 + a + 2) * 2 + 1)
    ((4 ^ (b * 2 + a + 2) / 3 * 16 - (b * 2 + a + 2) * 3) + 5).
Proof.
  unfold S2.
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

Transparent BinDec.

Lemma init: c0 -->* S2 5 79.
Proof.
  unfold S2,S0; cbn; solve_init.
Qed.

Ltac R_mod :=
match goal with
| |- S2 ?a ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
    follow init.
    R_mod.
    change (79/3) with 26.
    follow Ov1.
    R_mod.
    finish.
  }
  apply Ov0.
  Unshelve.
  all: match goal with
       | |- 4^?a/3*16 >= ?a*3 => apply f_ge
       | _ => solve_ge
       end.
Qed.

End TM9.


Module TM10.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1RC1RB_1LD0RB_1LE1LD_1RA0LC_---0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[1;1;0].
Notation d1 := <[0;1;0].
Notation "l <| r" := (l <{{D}} r) (at level 30).
Notation "l |> r" := (l {{B}}> r) (at level 30).

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
  0inf <{{E}} [1;1;0]^^a *> [1]^^b *> 0inf.

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

Lemma Ov1 a b:
  S2 a (1+b*3) -->*
  S2 ((b * 2 + a + 1) * 2 + 1)
    ((4 ^ (b * 2 + a + 1) / 3 * 16 - (b * 2 + a + 1) * 3) + 5).
Proof.
  unfold S2.
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

Lemma Ov2 a b:
  S2 a (2+b*3) -->*
  S2 ((b * 2 + a + 2) * 2 + 1)
    ((4 ^ (b * 2 + a + 2) / 3 * 16 - (b * 2 + a + 2) * 3) + 5).
Proof.
  unfold S2.
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

Transparent BinDec.

Lemma init: c0 -->* S2 5 79.
Proof.
  unfold S2,S0; cbn; solve_init.
Qed.

Ltac R_mod :=
match goal with
| |- S2 ?a ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
    follow init.
    R_mod.
    change (79/3) with 26.
    follow Ov1.
    R_mod.
    finish.
  }
  apply Ov0.
  Unshelve.
  all: match goal with
       | |- 4^?a/3*16 >= ?a*3 => apply f_ge
       | _ => solve_ge
       end.
Qed.

End TM10.


Module TM11.

Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC0RF_1LD1LC_1RA0LB_---0RD_1RB1RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[1;1;0].
Notation d1 := <[0;1;0].
Notation "l <| r" := (l <{{C}} r) (at level 30).
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
  0inf <{{D}} [1;1;0]^^a *> [1]^^b *> 0inf.

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

Lemma Ov1 a b:
  S2 a (1+b*3) -->*
  S2 ((b * 2 + a + 1) * 2 + 1)
    ((4 ^ (b * 2 + a + 1) / 3 * 16 - (b * 2 + a + 1) * 3) + 4).
Proof.
  unfold S2.
  mid (S0 (1+a+b*2) 1 0 4).
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

Lemma Ov2 a b:
  S2 a (2+b*3) -->*
  S2 ((b * 2 + a + 2) * 2 + 1)
  ((4 ^ (b * 2 + a + 2) / 3 * 16 - (b * 2 + a + 2) * 3) + 4).
Proof.
  unfold S2.
  mid (S0 (2+a+b*2) 1 0 4).
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

Transparent BinDec.

Lemma init: c0 -->* S2 3 17.
Proof.
  unfold S2,S0; cbn; solve_init.
Qed.

Ltac R_mod :=
match goal with
| |- S2 ?a ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
    follow init.
    R_mod.
    change (17/3) with 5.
    follow Ov2.
    R_mod.
    change (5*2+3+2) with 15.
    follow Ov1.
    R_mod.
    finish.
  }
  apply Ov0.
  Unshelve.
  all: match goal with
       | |- 4^?a/3*16 >= ?a*3 => apply f_ge
       | _ => solve_ge
       end.
Qed.

End TM11.


Module TM12.

Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC0RF_1LA1LC_1LC0RE_1RD1RE_---0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[1;1;0].
Notation d1 := <[0;1;0].
Notation "l <| r" := (l <{{C}} r) (at level 30).
Notation "l |> r" := (l {{E}}> r) (at level 30).

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
  0inf <{{A}} [1;1;0]^^a *> [1]^^b *> 0inf.

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

Lemma Ov1 a b:
  S2 a (1+b*3) -->*
  S2 ((b * 2 + a + 1) * 2 + 1)
    ((4 ^ (b * 2 + a + 1) / 3 * 16 - (b * 2 + a + 1) * 3) + 5).
Proof.
  unfold S2.
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

Lemma Ov2 a b:
  S2 a (2+b*3) -->*
  S2 ((b * 2 + a + 2) * 2 + 1)
    ((4 ^ (b * 2 + a + 2) / 3 * 16 - (b * 2 + a + 2) * 3) + 5).
Proof.
  unfold S2.
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

Transparent BinDec.

Lemma init: c0 -->* S2 5 79.
Proof.
  unfold S2,S0; cbn; solve_init.
Qed.

Ltac R_mod :=
match goal with
| |- S2 ?a ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
    follow init.
    R_mod.
    change (79/3) with 26.
    follow Ov1.
    R_mod.
    finish.
  }
  apply Ov0.
  Unshelve.
  all: match goal with
       | |- 4^?a/3*16 >= ?a*3 => apply f_ge
       | _ => solve_ge
       end.
Qed.

End TM12.


Module TM13.

Definition tm := Eval compute in (TM_from_str "1RB1RA_1LC0RA_1LD1LC_1RE0LB_0LA0RF_---0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[1;1;0].
Notation d1 := <[0;1;0].
Notation "l <| r" := (l <{{C}} r) (at level 30).
Notation "l |> r" := (l {{A}}> r) (at level 30).

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
  0inf <{{D}} [1;1;0]^^a *> [1]^^b *> 0inf.

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

Lemma Ov1 a b:
  S2 a (1+b*3) -->*
  S2 ((b * 2 + a + 1) * 2 + 1)
    ((4 ^ (b * 2 + a + 1) / 3 * 16 - (b * 2 + a + 1) * 3) + 4).
Proof.
  unfold S2.
  mid (S0 (1+a+b*2) 1 0 4).
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

Lemma Ov2 a b:
  S2 a (2+b*3) -->*
  S2 ((b * 2 + a + 2) * 2 + 1)
  ((4 ^ (b * 2 + a + 2) / 3 * 16 - (b * 2 + a + 2) * 3) + 4).
Proof.
  unfold S2.
  mid (S0 (2+a+b*2) 1 0 4).
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

Transparent BinDec.

Lemma init: c0 -->* S2 3 17.
Proof.
  unfold S2,S0; cbn; solve_init.
Qed.

Ltac R_mod :=
match goal with
| |- S2 ?a ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
    follow init.
    R_mod.
    change (17/3) with 5.
    follow Ov2.
    R_mod.
    change (5*2+3+2) with 15.
    follow Ov1.
    R_mod.
    finish.
  }
  apply Ov0.
  Unshelve.
  all: match goal with
       | |- 4^?a/3*16 >= ?a*3 => apply f_ge
       | _ => solve_ge
       end.
Qed.

End TM13.


Module TM14.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1LC1LB_1RD0LA_0LA0RE_---0RC_1RA1RF").

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
| S n0 => f n0 + ((2^(n0*2+2)-1)*8+5)
end.

Lemma f_def n:
  f n + n*3 = (4^n/3)*32.
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
  f n = (4^n/3)*32-n*3.
Proof.
  pose proof (f_def n); lia.
Qed.

Lemma f_ge n:
  4^n/3*32 >= n*3.
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
  S0 (a+a0) 2 0 (3+b) -->*
  S0 a0 (2+a*2) 0 (3+(f a)+b).
Proof.
  gen a0 b.
  induction a; intros.
  1: cbn[f]; finish.
  cbn[f].
  specialize (IHa (S a0) b).
  follow IHa.
  follow OvIncs.
  fold Nat.add.
  rewrite (Nat.add_comm 2 (a*2)).
  finish.
Qed.

Lemma OvIncss' a b:
  S0 a 2 0 (3+b) -->*
  S0 0 (2+a*2) 0 (3+(4^a/3*32-a*3)+b).
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

Definition S2 a b := S0 0 (2+a) 0 b.

Lemma Ov0 a b:
  halts tm (S2 a (0+b*3)).
Proof.
  unfold S2,S0,LC.
  rw_Bin.
  eapply halts_evstep.
  2: {
    mid (S1 (3+a) (b*3+1)).
    1: es.
    follow Incs1.
    unfold S1.
    repeat (step1 || sr).
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

Lemma Ov1 a b:
  S2 a (1+b*3) -->*
  S2 ((b * 2 + a + 1) * 2)
    ((4 ^ (b * 2 + a + 1) / 3 * 32 - (b * 2 + a + 1) * 3) + 10).
Proof.
  unfold S2.
  mid (S0 (1+a+b*2) 2 0 10).
  - unfold S0,LC.
    rw_Bin.
    mid (S1 (3+a) (b*3+2)).
    1: es.
    follow Incs1.
    unfold S1.
    es.
  - follow OvIncss'.
    replace (1+a+b*2) with (b*2+a+1) by lia.
    finish.
Qed.

Lemma Ov2 a b:
  S2 a (2+b*3) -->*
  S2 ((b * 2 + a + 2) * 2)
    ((4 ^ (b * 2 + a + 2) / 3 * 32 - (b * 2 + a + 2) * 3) + 10).
Proof.
  unfold S2.
  mid (S0 (a+b*2+2) 2 0 10).
  - unfold S0,LC.
    rw_Bin.
    mid (S1 (3+a) ((b+1)*3+0)).
    1: es.
    follow Incs1.
    unfold S1.
    es.
  - follow OvIncss'.
    replace (a+b*2) with (b*2+a) by lia.
    finish.
Qed.

Transparent BinDec.

Lemma init: c0 -->* S2 2 37.
Proof.
  unfold S2,S0; cbn; solve_init.
Qed.

Ltac R_mod :=
match goal with
| |- S2 ?a ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
    follow init.
    R_mod.
    change (37/3) with 12.
    follow Ov1.
    R_mod.
    change (12*2+2+1) with 27.
    follow Ov1.
    R_mod.
    finish.
  }
  apply Ov0.
  Unshelve.
  all: match goal with
       | |- 4^?a/3*32 >= ?a*3 => apply f_ge
       | _ => solve_ge
       end.
Qed.

End TM14.


Module TM15.

Definition tm := Eval compute in (TM_from_str "1LB1LA_1RC0LF_---0RD_0RE0RB_1RF1RE_1LA0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[1;1;0].
Notation d1 := <[0;1;0].
Notation "l <| r" := (l <{{A}} r) (at level 30).
Notation "l |> r" := (l {{E}}> r) (at level 30).

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
| S n0 => f n0 + ((2^(n0*2)-1)*8+5)
end.

Lemma f_def n:
  f n + n*3 = (4^n/3)*8.
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
  f n = (4^n/3)*8-n*3.
Proof.
  pose proof (f_def n); lia.
Qed.

Lemma f_ge n:
  4^n/3*8 >= n*3.
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
  S0 (a+a0) 0 0 (3+b) -->*
  S0 a0 (a*2) 0 (3+(f a)+b).
Proof.
  gen a0 b.
  induction a; intros.
  1: cbn[f]; finish.
  cbn[f].
  specialize (IHa (S a0) b).
  follow IHa.
  follow OvIncs.
  fold Nat.add.
  finish.
Qed.

Lemma OvIncss' a b:
  S0 a 0 0 (3+b) -->*
  S0 0 (a*2) 0 (3+(4^a/3*8-a*3)+b).
Proof.
  epose proof (OvIncss a 0 b) as H.
  follow H.
  rewrite f_def'.
  finish.
Qed.

Definition S1 a b :=
  0inf <{{B}} [1;1;0]^^a *> [1]^^b *> 0inf.

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
  S2 a (0+b*3) -->*
  S2 ((b * 2 + a + 1) * 2)
    ((4 ^ (b * 2 + a + 1) / 3 * 8 - (b * 2 + a + 1) * 3) + 3).
Proof.
  unfold S2.
  mid (S0 (1+a+b*2) 0 0 3).
  - unfold S0,LC.
    rw_Bin.
    mid (S1 (1+a) (b*3+1)).
    1: es.
    follow Incs1.
    unfold S1.
    es.
  - follow OvIncss'.
    replace (1+a+b*2) with (b*2+a+1) by lia.
    finish.
Qed.

Lemma Ov1 a b:
  halts tm (S2 a (1+b*3)).
Proof.
  unfold S2,S0,LC.
  rw_Bin.
  eapply halts_evstep.
  2: {
    mid (S1 (1+a) (b*3+2)).
    1: es.
    follow Incs1.
    unfold S1.
    repeat (step1 || sr).
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

Lemma Ov2 a b:
  halts tm (S2 a (2+b*3)).
Proof.
  unfold S2,S0,LC.
  rw_Bin.
  eapply halts_evstep.
  2: {
    mid (S1 (1+a) (b*3+3)).
    1: es.
    follow Incs1.
    unfold S1.
    repeat (step1 || sr).
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

Transparent BinDec.

Lemma init: c0 -->* S2 6 162.
Proof.
  unfold S2,S0; cbn; solve_init.
Qed.

Ltac R_mod :=
match goal with
| |- S2 ?a ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
    follow init.
    R_mod.
    change (162/3) with 54.
    follow Ov0.
    R_mod.
    finish.
  }
  apply Ov2.
  Unshelve.
  all: match goal with
       | |- 4^?a/3*8 >= ?a*3 => apply f_ge
       | _ => solve_ge
       end.
Qed.

End TM15.


Module TM16.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1LC1LB_1RD0LA_1LA0RE_---0RC_1RA1RF").

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
| S n0 => f n0 + ((2^(n0*2+3)-1)*8+5)
end.

Lemma f_def n:
  f n + n*3 = (4^n/3)*64.
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
  f n = (4^n/3)*64-n*3.
Proof.
  pose proof (f_def n); lia.
Qed.

Lemma f_ge n:
  4^n/3*64 >= n*3.
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
  S0 (a+a0) 3 0 (3+b) -->*
  S0 a0 (3+a*2) 0 (3+(f a)+b).
Proof.
  gen a0 b.
  induction a; intros.
  1: cbn[f]; finish.
  cbn[f].
  specialize (IHa (S a0) b).
  follow IHa.
  follow OvIncs.
  fold Nat.add.
  rewrite (Nat.add_comm 3 (a*2)).
  finish.
Qed.

Lemma OvIncss' a b:
  S0 a 3 0 (3+b) -->*
  S0 0 (3+a*2) 0 (3+(4^a/3*64-a*3)+b).
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

Definition S2 a b := S0 0 (3+a) 0 b.

Lemma Ov0 a b:
  halts tm (S2 a (0+b*3)).
Proof.
  unfold S2,S0,LC.
  rw_Bin.
  eapply halts_evstep.
  2: {
    mid (S1 (4+a) (b*3+1)).
    1: es.
    follow Incs1.
    unfold S1.
    repeat (step1 || sr).
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

Lemma Ov1 a b:
  S2 (a) (1+b*3) -->*
  S2 ((b * 2 + a + 1) * 2)
    ((4 ^ (b * 2 + a + 1) / 3 * 64 - (b * 2 + a + 1) * 3) + 34).
Proof.
  unfold S2.
  mid (S0 (1+a+b*2) 3 0 34).
  - unfold S0,LC.
    rw_Bin.
    mid (S1 (4+a) (b*3+2)).
    1: es.
    follow Incs1.
    unfold S1.
    es.
  - follow OvIncss'.
    replace (1+a+b*2) with (b*2+a+1) by lia.
    finish.
Qed.

Lemma Ov2 a b:
  S2 (a) (2+b*3) -->*
  S2 ((b * 2 + a + 2) * 2)
    ((4 ^ (b * 2 + a + 2) / 3 * 64 - (b * 2 + a + 2) * 3) + 34).
Proof.
  unfold S2.
  mid (S0 (a+b*2+2) 3 0 34).
  - unfold S0,LC.
    rw_Bin.
    mid (S1 (4+a) ((b+1)*3+0)).
    1: es.
    follow Incs1.
    unfold S1.
    es.
  - follow OvIncss'.
    replace (a+b*2) with (b*2+a) by lia.
    finish.
Qed.

Transparent BinDec.

Lemma init: c0 -->* S2 3 173.
Proof.
  unfold S2,S0; cbn; solve_init.
Qed.

Ltac R_mod :=
match goal with
| |- S2 ?a ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
    follow init.
    R_mod.
    change (173/3) with 57.
    follow Ov2.
    R_mod.
    finish.
  }
  apply Ov0.
  Unshelve.
  all: match goal with
       | |- 4^?a/3*8 >= ?a*3 => apply f_ge
       | _ => solve_ge
       end.
Qed.

End TM16.


Module TM17.

Definition tm := Eval compute in (TM_from_str "1RB0LC_0LC0RF_1LE0RD_1RC1RD_1LA1LE_---0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[1;1;0].
Notation d1 := <[0;1;0].
Notation "l <| r" := (l <{{E}} r) (at level 30).
Notation "l |> r" := (l {{D}}> r) (at level 30).

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
| S n0 => f n0 + ((2^(n0*2+2)-1)*8+5)
end.

Lemma f_def n:
  f n + n*3 = (4^n/3)*32.
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
  f n = (4^n/3)*32-n*3.
Proof.
  pose proof (f_def n); lia.
Qed.

Lemma f_ge n:
  4^n/3*32 >= n*3.
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
  S0 (a+a0) 2 0 (3+b) -->*
  S0 a0 (2+a*2) 0 (3+(f a)+b).
Proof.
  gen a0 b.
  induction a; intros.
  1: cbn[f]; finish.
  cbn[f].
  specialize (IHa (S a0) b).
  follow IHa.
  follow OvIncs.
  fold Nat.add.
  rewrite (Nat.add_comm 2 (a*2)).
  finish.
Qed.

Lemma OvIncss' a b:
  S0 a 2 0 (3+b) -->*
  S0 0 (2+a*2) 0 (3+(4^a/3*32-a*3)+b).
Proof.
  epose proof (OvIncss a 0 b) as H.
  follow H.
  rewrite f_def'.
  finish.
Qed.

Definition S1 a b :=
  0inf <{{A}} [1;1;0]^^a *> [1]^^b *> 0inf.

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

Definition S2 a b := S0 0 (2+a) 0 b.

Lemma Ov0 a b:
  halts tm (S2 a (0+b*3)).
Proof.
  unfold S2,S0,LC.
  rw_Bin.
  eapply halts_evstep.
  2: {
    mid (S1 (3+a) (b*3+1)).
    1: es.
    follow Incs1.
    unfold S1.
    repeat (step1 || sr).
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

Lemma Ov1 a b:
  S2 a (1+b*3) -->*
  S2 ((b * 2 + a + 1) * 2)
    ((4 ^ (b * 2 + a + 1) / 3 * 32 - (b * 2 + a + 1) * 3) + 10).
Proof.
  unfold S2.
  mid (S0 (1+a+b*2) 2 0 10).
  - unfold S0,LC.
    rw_Bin.
    mid (S1 (3+a) (b*3+2)).
    1: es.
    follow Incs1.
    unfold S1.
    es.
  - follow OvIncss'.
    replace (1+a+b*2) with (b*2+a+1) by lia.
    finish.
Qed.

Lemma Ov2 a b:
  S2 a (2+b*3) -->*
  S2 ((b * 2 + a + 2) * 2)
    ((4 ^ (b * 2 + a + 2) / 3 * 32 - (b * 2 + a + 2) * 3) + 10).
Proof.
  unfold S2.
  mid (S0 (a+b*2+2) 2 0 10).
  - unfold S0,LC.
    rw_Bin.
    mid (S1 (3+a) ((b+1)*3+0)).
    1: es.
    follow Incs1.
    unfold S1.
    es.
  - follow OvIncss'.
    replace (a+b*2) with (b*2+a) by lia.
    finish.
Qed.

Transparent BinDec.

Lemma init: c0 -->* S2 4 164.
Proof.
  unfold S2,S0; cbn; solve_init.
Qed.

Ltac R_mod :=
match goal with
| |- S2 ?a ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
    follow init.
    R_mod.
    change (164/3) with 54.
    follow Ov2.
    R_mod.
    change (54*2+4+2) with 114.
    follow Ov1.
    R_mod.
    follow Ov1.
    R_mod.
    follow Ov2.
    R_mod.
    finish.
  }
  apply Ov0.
  Unshelve.
  all: try match goal with
       | |- 4^?a/3*32 >= ?a*3 => apply f_ge
       end.
  all: try lia.
Qed.

End TM17.


Module TM18.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1LC1LB_1RD0LA_0LF0RE_---0RC_1RA1RF").

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

Lemma Ov1 a b:
  S2 a (1+b*3) -->*
  S2 ((b * 2 + a + 1) * 2 + 1)
    ((4 ^ (b * 2 + a + 1) / 3 * 16 - (b * 2 + a + 1) * 3) + 4).
Proof.
  unfold S2.
  mid (S0 (1+a+b*2) 1 0 4).
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

Lemma Ov2 a b:
  S2 a (2+b*3) -->*
  S2 ((b * 2 + a + 2) * 2 + 1)
    ((4 ^ (b * 2 + a + 2) / 3 * 16 - (b * 2 + a + 2) * 3) + 4).
Proof.
  unfold S2.
  mid (S0 (2+a+b*2) 1 0 4).
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

Transparent BinDec.

Lemma init: c0 -->* S2 1 4.
Proof.
  unfold S2,S0; cbn; solve_init.
Qed.

Ltac R_mod :=
match goal with
| |- S2 ?a ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
    follow init.
    R_mod.
    change (4/3) with 1%nat.
    follow Ov1.
    change (1*2+1+1) with 4.
    R_mod.
    change (4^4/3) with 85.
    follow Ov2.
    R_mod.
    finish.
  }
  apply Ov0.
  Unshelve.
  all: match goal with
       | |- 4^?a/3*16 >= ?a*3 => apply f_ge
       | _ => solve_ge
       end.
Qed.

End TM18.


Module TM19.

Definition tm := Eval compute in (TM_from_str "1RB0LE_1LC0RD_1LA1LC_---0RA_1LC0RF_1RE1RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[1;1;0].
Notation d1 := <[0;1;0].
Notation "l <| r" := (l <{{C}} r) (at level 30).
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
| S n0 => f n0 + ((2^(n0*2+2)-1)*8+5)
end.

Lemma f_def n:
  f n + n*3 = (4^n/3)*32.
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
  f n = (4^n/3)*32-n*3.
Proof.
  pose proof (f_def n); lia.
Qed.

Lemma f_ge n:
  4^n/3*32 >= n*3.
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
  S0 (a+a0) 2 0 (3+b) -->*
  S0 a0 (2+a*2) 0 (3+(f a)+b).
Proof.
  gen a0 b.
  induction a; intros.
  1: cbn[f]; finish.
  cbn[f].
  specialize (IHa (S a0) b).
  follow IHa.
  follow OvIncs.
  fold Nat.add.
  rewrite (Nat.add_comm 2 (a*2)).
  finish.
Qed.

Lemma OvIncss' a b:
  S0 a 2 0 (3+b) -->*
  S0 0 (2+a*2) 0 (3+(4^a/3*32-a*3)+b).
Proof.
  epose proof (OvIncss a 0 b) as H.
  follow H.
  rewrite f_def'.
  finish.
Qed.

Definition S1 a b :=
  0inf <{{A}} [1;1;0]^^a *> [1]^^b *> 0inf.

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

Definition S2 a b := S0 0 (2+a) 0 b.

Lemma Ov0 a b:
  halts tm (S2 a (0+b*3)).
Proof.
  unfold S2,S0,LC.
  rw_Bin.
  eapply halts_evstep.
  2: {
    mid (S1 (3+a) (b*3+1)).
    1: es.
    follow Incs1.
    unfold S1.
    repeat (step1 || sr).
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

Lemma Ov1 a b:
  S2 a (1+b*3) -->*
  S2 ((b * 2 + a + 2) * 2)
    ((4 ^ (b * 2 + a + 2) / 3 * 32 - (b * 2 + a + 2) * 3) + 8).
Proof.
  unfold S2.
  mid (S0 (2+a+b*2) 2 0 8).
  - unfold S0,LC.
    rw_Bin.
    mid (S1 (3+a) (b*3+2)).
    1: es.
    follow Incs1.
    unfold S1.
    es.
  - follow OvIncss'.
    replace (2+a+b*2) with (b*2+a+2) by lia.
    finish.
Qed.

Lemma Ov2 a b:
  S2 a (2+b*3) -->*
  S2 ((b * 2 + a + 3) * 2)
    ((4 ^ (b * 2 + a + 3) / 3 * 32 - (b * 2 + a + 3) * 3) + 8).
Proof.
  unfold S2.
  mid (S0 (a+b*2+3) 2 0 8).
  - unfold S0,LC.
    rw_Bin.
    mid (S1 (3+a) ((b+1)*3+0)).
    1: es.
    follow Incs1.
    unfold S1.
    es.
  - follow OvIncss'.
    replace (a+b*2) with (b*2+a) by lia.
    finish.
Qed.

Transparent BinDec.

Lemma init: c0 -->* S2 0 8.
Proof.
  unfold S2,S0; cbn; solve_init.
Qed.

Ltac R_mod :=
match goal with
| |- S2 ?a ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
    follow init.
    R_mod.
    change (8/3) with 2.
    follow Ov2.
    R_mod.
    change (2*2+0+3) with 7.
    follow Ov1.
    R_mod.
    follow Ov2.
    R_mod.
    finish.
  }
  apply Ov0.
  Unshelve.
  all: match goal with
       | |- 4^?a/3*32 >= ?a*3 => apply f_ge
       | _ => solve_ge
       end.
Qed.

End TM19.


Module TM20.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1LC1LB_1RD0LA_1RA0RE_---0RC_1RA1RF").

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

Lemma Ov1 a b:
  S2 a (1+b*3) -->*
  S2 ((b * 2 + a + 1) * 2 + 1)
    ((4 ^ (b * 2 + a + 1) / 3 * 16 - (b * 2 + a + 1) * 3) + 4).
Proof.
  unfold S2.
  mid (S0 (1+a+b*2) 1 0 4).
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

Lemma Ov2 a b:
  S2 a (2+b*3) -->*
  S2 ((b * 2 + a + 2) * 2 + 1)
    ((4 ^ (b * 2 + a + 2) / 3 * 16 - (b * 2 + a + 2) * 3) + 4).
Proof.
  unfold S2.
  mid (S0 (2+a+b*2) 1 0 4).
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

Transparent BinDec.

Lemma init: c0 -->* S2 1 4.
Proof.
  unfold S2,S0; cbn; solve_init.
Qed.

Ltac R_mod :=
match goal with
| |- S2 ?a ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
    follow init.
    R_mod.
    change (4/3) with 1%nat.
    follow Ov1.
    change (1*2+1+1) with 4.
    R_mod.
    change (4^4/3) with 85.
    follow Ov2.
    R_mod.
    finish.
  }
  apply Ov0.
  Unshelve.
  all: match goal with
       | |- 4^?a/3*16 >= ?a*3 => apply f_ge
       | _ => solve_ge
       end.
Qed.

End TM20.


Module TM31.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC0LD_1RE0RD_0LB1RA_1RA0RF_---0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[1;0;0].
Notation d1 := <[1;1;1].
Notation "l <| r" := (l <{{D}} [0] *> r) (at level 30).
Notation "l |> r" := (l <* <[1] {{A}}> r) (at level 30).
Notation lh := (0inf <* <[1;1]).

Definition LC l len n := BinDec d0 d1 len n l.

Lemma LC_Inc l len n r:
  S n<2^len ->
  LC l len (S n) <| r -->*
  LC l len n |> r.
Proof.
  intros H.
  eapply progress_evstep.
  apply LBinDec_spec; try assumption.
  es.
Qed.

Definition S0 l len n b :=
  LC l len n <| [1;1;1;1;0] *> [1;1]^^(1+b) *> 0inf.

Opaque BinDec.

Lemma Inc l len n b:
  S n<2^len ->
  S0 l len (S n) b -->*
  S0 l len n (1+b).
Proof.
  unfold S0,LC.
  intros.
  follow LC_Inc.
  es.
Qed.

Lemma Incs l len n b:
  n<2^len ->
  S0 l len n b -->*
  S0 l len 0 (n+b).
Proof.
  gen b.
  induction n; intros.
  1: finish.
  follow Inc.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Ov2 len b:
  S0 lh len 0 (2+b*3) -->+
  S0 lh (len+1+1+b*2+1) (((((2^len-1)*2+1)*2+1)*2^(b*2)-1)*2+1) 0.
Proof.
  unfold S0,LC.
  rw_Bin.
  all: try solve_pow2_lt.
  es.
Qed.

Lemma OvIncs2 len b:
  S0 lh len 0 (2+b*3) -->+
  S0 lh (len+1+1+b*2+1) 0 ((((((2^len-1)*2+1)*2+1)*2^(b*2)-1)*2+1)+0).
Proof.
  follow10 Ov2.
  follow Incs.
  1: solve_pow2_lt.
  finish.
Qed.

Lemma Ov1 len b:
  b>=1 ->
  halts tm (S0 lh len 0 (1+b*3)).
Proof.
  intros Hb.
  replace b with (b-1+1) by lia.
  unfold S0,LC.
  rw_Bin.
  eapply halts_evstep.
  2: {
    repeat (rewrite lpow_add || rewrite lpow_mul).
    repeat (step1 || sr).
    finish.
  }
  eapply halted_halts.
  constructor.
  all: try solve_pow2_lt.
Qed.

Transparent BinDec.

Lemma init: c0-->* S0 lh 2 0 8.
Proof. unfold S0,LC; cbn; solve_init. Qed.

Ltac R_mod :=
match goal with
| |- S0 lh ?a _ ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
    follow init.
    R_mod.
    follow100 OvIncs2.
    R_mod.
    follow100 OvIncs2.
    R_mod.
    finish.
  }
  apply Ov1.
  shelve.
  Unshelve.
  all: solve_ge.
Qed.

End TM31.


Module TM32.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC0LD_1RE0RD_0LB1RA_1RA1RF_---0LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[1;0;0].
Notation d1 := <[1;1;1].
Notation "l <| r" := (l <{{D}} [0] *> r) (at level 30).
Notation "l |> r" := (l <* <[1] {{A}}> r) (at level 30).
Notation lh := (0inf <* <[1;1]).

Definition LC l len n := BinDec d0 d1 len n l.

Lemma LC_Inc l len n r:
  S n<2^len ->
  LC l len (S n) <| r -->*
  LC l len n |> r.
Proof.
  intros H.
  eapply progress_evstep.
  apply LBinDec_spec; try assumption.
  es.
Qed.

Definition S0 l len n b :=
  LC l len n <| [1;1;1;1;0] *> [1;1]^^(1+b) *> 0inf.

Opaque BinDec.

Lemma Inc l len n b:
  S n<2^len ->
  S0 l len (S n) b -->*
  S0 l len n (1+b).
Proof.
  unfold S0,LC.
  intros.
  follow LC_Inc.
  es.
Qed.

Lemma Incs l len n b:
  n<2^len ->
  S0 l len n b -->*
  S0 l len 0 (n+b).
Proof.
  gen b.
  induction n; intros.
  1: finish.
  follow Inc.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Ov2 len b:
  S0 lh len 0 (2+b*3) -->+
  S0 lh (len+1+1+b*2+1) (((((2^len-1)*2+1)*2+1)*2^(b*2)-1)*2+1) 0.
Proof.
  unfold S0,LC.
  rw_Bin.
  all: try solve_pow2_lt.
  es.
Qed.

Lemma OvIncs2 len b:
  S0 lh len 0 (2+b*3) -->+
  S0 lh (len+1+1+b*2+1) 0 ((((((2^len-1)*2+1)*2+1)*2^(b*2)-1)*2+1)+0).
Proof.
  follow10 Ov2.
  follow Incs.
  1: solve_pow2_lt.
  finish.
Qed.

Lemma Ov1 len b:
  b>=1 ->
  halts tm (S0 lh len 0 (1+b*3)).
Proof.
  intros Hb.
  replace b with (b-1+1) by lia.
  unfold S0,LC.
  rw_Bin.
  eapply halts_evstep.
  2: {
    repeat (rewrite lpow_add || rewrite lpow_mul).
    repeat (step1 || sr).
    finish.
  }
  eapply halted_halts.
  constructor.
  all: try solve_pow2_lt.
Qed.

Transparent BinDec.

Lemma init: c0-->* S0 lh 2 0 8.
Proof. unfold S0,LC; cbn; solve_init. Qed.

Ltac R_mod :=
match goal with
| |- S0 lh ?a _ ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
    follow init.
    R_mod.
    follow100 OvIncs2.
    R_mod.
    follow100 OvIncs2.
    R_mod.
    finish.
  }
  apply Ov1.
  shelve.
  Unshelve.
  all: solve_ge.
Qed.

End TM32.


Module TM33.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC0LD_1RE0RD_0LB1RA_1RA1RF_---1RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[1;0;0].
Notation d1 := <[1;1;1].
Notation "l <| r" := (l <{{D}} [0] *> r) (at level 30).
Notation "l |> r" := (l <* <[1] {{A}}> r) (at level 30).
Notation lh := (0inf <* <[1;1]).

Definition LC l len n := BinDec d0 d1 len n l.

Lemma LC_Inc l len n r:
  S n<2^len ->
  LC l len (S n) <| r -->*
  LC l len n |> r.
Proof.
  intros H.
  eapply progress_evstep.
  apply LBinDec_spec; try assumption.
  es.
Qed.

Definition S0 l len n b :=
  LC l len n <| [1;1;1;1;0] *> [1;1]^^(1+b) *> 0inf.

Opaque BinDec.

Lemma Inc l len n b:
  S n<2^len ->
  S0 l len (S n) b -->*
  S0 l len n (1+b).
Proof.
  unfold S0,LC.
  intros.
  follow LC_Inc.
  es.
Qed.

Lemma Incs l len n b:
  n<2^len ->
  S0 l len n b -->*
  S0 l len 0 (n+b).
Proof.
  gen b.
  induction n; intros.
  1: finish.
  follow Inc.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Ov2 len b:
  S0 lh len 0 (2+b*3) -->+
  S0 lh (len+1+1+b*2+1) (((((2^len-1)*2+1)*2+1)*2^(b*2)-1)*2+1) 0.
Proof.
  unfold S0,LC.
  rw_Bin.
  all: try solve_pow2_lt.
  es.
Qed.

Lemma OvIncs2 len b:
  S0 lh len 0 (2+b*3) -->+
  S0 lh (len+1+1+b*2+1) 0 ((((((2^len-1)*2+1)*2+1)*2^(b*2)-1)*2+1)+0).
Proof.
  follow10 Ov2.
  follow Incs.
  1: solve_pow2_lt.
  finish.
Qed.

Lemma Ov1 len b:
  b>=1 ->
  halts tm (S0 lh len 0 (1+b*3)).
Proof.
  intros Hb.
  replace b with (b-1+1) by lia.
  unfold S0,LC.
  rw_Bin.
  eapply halts_evstep.
  2: {
    repeat (rewrite lpow_add || rewrite lpow_mul).
    repeat (step1 || sr).
    finish.
  }
  eapply halted_halts.
  constructor.
  all: try solve_pow2_lt.
Qed.

Transparent BinDec.

Lemma init: c0-->* S0 lh 2 0 8.
Proof. unfold S0,LC; cbn; solve_init. Qed.

Ltac R_mod :=
match goal with
| |- S0 lh ?a _ ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
    follow init.
    R_mod.
    follow100 OvIncs2.
    R_mod.
    follow100 OvIncs2.
    R_mod.
    finish.
  }
  apply Ov1.
  shelve.
  Unshelve.
  all: solve_ge.
Qed.

End TM33.

Inductive DivMod2: nat->Prop :=
| DivMod2_0 a: DivMod2 (a*2+0)
| DivMod2_1 a: DivMod2 (a*2+1)
.

Lemma divmod2_cases a: DivMod2 a.
Proof.
  epose proof (Nat.Div0.div_mod a 2) as H.
  epose proof (Nat.mod_upper_bound a 2) as H0.
  destruct (a mod 2) as [|[|]].
  - applys_eq (DivMod2_0 (a/2)); lia.
  - applys_eq (DivMod2_1 (a/2)); lia.
  - lia.
Qed.

Ltac divmod2 a :=
  epose proof (divmod2_cases a) as Hdm2;
  inverts Hdm2.


Module TM37.

Definition tm := Eval compute in (TM_from_str "1RB0RB_1LC0RA_0LF1LD_0RD0LE_1LC1LC_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[0;1;1;1;0;0].
Notation d1 := <[0;1;1;1;1;1].
Notation "l <| r" := (l <{{C}} [1;0] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{B}}> r) (at level 30).
Notation lh := (0inf <* <[1;1]).

Definition LC l len n := BinDec d0 d1 len n l.

Lemma LC_Inc l len n r:
  S n<2^len ->
  LC l len (S n) <| r -->*
  LC l len n |> r.
Proof.
  intros H.
  eapply progress_evstep.
  apply LBinDec_spec; try assumption.
  es.
Qed.

Definition S0 l len n b :=
  LC l len n <| [1;0]^^(b) *> 0inf.

Opaque BinDec.

Lemma Inc l len n b:
  S n<2^len ->
  S0 l len (S n) b -->*
  S0 l len n (1+b).
Proof.
  unfold S0,LC.
  intros.
  follow LC_Inc.
  es.
Qed.

Lemma Incs l len n b:
  n<2^len ->
  S0 l len n b -->*
  S0 l len 0 (n+b).
Proof.
  gen b.
  induction n; intros.
  1: finish.
  follow Inc.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Ov1 len b:
  S0 lh (len+1) 0 (1+b*3) -->+
  S0 lh (len+1+b+1) ((((2^len-1)*2+1)*2^b-1)*2+1) 2.
Proof.
  unfold S0,LC.
  rw_Bin.
  2,3: solve_pow2_lt.
  es.
Qed.

Lemma OvIncs1 len b:
  S0 lh (len+1) 0 (1+b*3) -->+
  S0 lh (len+1+b+1) 0 (((((2^len-1)*2+1)*2^b-1)*2+1)+2).
Proof.
  follow10 Ov1.
  follow Incs.
  1: solve_pow2_lt.
  finish.
Qed.

Definition S1 a len b m :=
  S0 (lh<*d0^^a<*<[0;1;1;1;0;1;1]) len b m.

Lemma Ov0 len b:
  S0 lh (len+1) 0 (0+b*3) -->+
  S1 len (b+1) ((2^b-1)*2+1) 0.
Proof.
  unfold S1,S0,LC.
  rw_Bin.
  2: solve_pow2_lt.
  es.
Qed.

Lemma Ov0a_S a b m:
  S1 (S a) b 0 m -->*
  S1 a (b+1) ((2^b-1)*2+1) (m+1).
Proof.
  unfold S1,S0,LC.
  rw_Bin.
  2: solve_pow2_lt.
  es.
Qed.

Lemma Ov0a a b m:
  halts tm (S1 a b 0 m).
Proof.
  gen b m.
  induction a; intros.
  - eapply halts_evstep.
    2: {
      unfold S1,S0,LC.
      rw_Bin.
      repeat (step1 || sr).
      finish.
    }
    eapply halted_halts.
    constructor.
  - eapply halts_evstep.
    2: {
      unfold S1.
      follow Ov0a_S.
      unfold S1.
      follow Incs.
      1: solve_pow2_lt.
      finish.
    }
    unfold S1 in IHa.
    apply IHa.
Qed.

Lemma Ov0H len b:
  halts tm (S0 lh (len+1) 0 (0+b*3)).
Proof.
  eapply halts_evstep.
  2: {
    follow100 Ov0.
    follow Incs.
    1: solve_pow2_lt.
    finish.
  }
  apply Ov0a.
Qed.

Lemma init: c0-->* S0 lh (4+1) 0 43.
Proof.
  Transparent BinDec.
  unfold S0,LC; cbn.
  solve_init.
Qed.

Ltac R_mod :=
match goal with
| |- S0 lh ?a _ ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
    follow init.
    R_mod.
    follow100 OvIncs1.
    R_mod.
    finish.
  }
  apply Ov0H.
  Unshelve.
  all: solve_ge.
Qed.

End TM37.


Module TM38.

Definition tm := Eval compute in (TM_from_str "1RB0RB_1LC0RA_0LF1LD_1RD0LE_1LC1LC_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[0;1;1;1;0;0].
Notation d1 := <[0;1;1;1;1;1].
Notation "l <| r" := (l <{{C}} [1;0] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{B}}> r) (at level 30).
Notation lh := (0inf <* <[1;1]).

Definition LC l len n := BinDec d0 d1 len n l.

Lemma LC_Inc l len n r:
  S n<2^len ->
  LC l len (S n) <| r -->*
  LC l len n |> r.
Proof.
  intros H.
  eapply progress_evstep.
  apply LBinDec_spec; try assumption.
  es.
Qed.

Definition S0 l len n b :=
  LC l len n <| [1;0]^^(b) *> 0inf.

Opaque BinDec.

Lemma Inc l len n b:
  S n<2^len ->
  S0 l len (S n) b -->*
  S0 l len n (1+b).
Proof.
  unfold S0,LC.
  intros.
  follow LC_Inc.
  es.
Qed.

Lemma Incs l len n b:
  n<2^len ->
  S0 l len n b -->*
  S0 l len 0 (n+b).
Proof.
  gen b.
  induction n; intros.
  1: finish.
  follow Inc.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Ov1 len b:
  S0 lh (len+1) 0 (1+b*3) -->+
  S0 lh (len+1+b+1) ((((2^len-1)*2+1)*2^b-1)*2+1) 2.
Proof.
  unfold S0,LC.
  rw_Bin.
  2,3: solve_pow2_lt.
  es.
Qed.

Lemma OvIncs1 len b:
  S0 lh (len+1) 0 (1+b*3) -->+
  S0 lh (len+1+b+1) 0 (((((2^len-1)*2+1)*2^b-1)*2+1)+2).
Proof.
  follow10 Ov1.
  follow Incs.
  1: solve_pow2_lt.
  finish.
Qed.

Definition S1 a len b m :=
  S0 (lh<*d0^^a<*<[0;1;1;1;0;1;1]) len b m.

Lemma Ov0 len b:
  S0 lh (len+1) 0 (0+b*3) -->+
  S1 len (b+1) ((2^b-1)*2+1) 0.
Proof.
  unfold S1,S0,LC.
  rw_Bin.
  2: solve_pow2_lt.
  es.
Qed.

Lemma Ov0a_S a b m:
  S1 (S a) b 0 m -->*
  S1 a (b+1) ((2^b-1)*2+1) (m+1).
Proof.
  unfold S1,S0,LC.
  rw_Bin.
  2: solve_pow2_lt.
  es.
Qed.

Lemma Ov0a a b m:
  halts tm (S1 a b 0 m).
Proof.
  gen b m.
  induction a; intros.
  - eapply halts_evstep.
    2: {
      unfold S1,S0,LC.
      rw_Bin.
      repeat (step1 || sr).
      finish.
    }
    eapply halted_halts.
    constructor.
  - eapply halts_evstep.
    2: {
      unfold S1.
      follow Ov0a_S.
      unfold S1.
      follow Incs.
      1: solve_pow2_lt.
      finish.
    }
    unfold S1 in IHa.
    apply IHa.
Qed.

Lemma Ov0H len b:
  halts tm (S0 lh (len+1) 0 (0+b*3)).
Proof.
  eapply halts_evstep.
  2: {
    follow100 Ov0.
    follow Incs.
    1: solve_pow2_lt.
    finish.
  }
  apply Ov0a.
Qed.

Lemma init: c0-->* S0 lh (4+1) 0 43.
Proof.
  Transparent BinDec.
  unfold S0,LC; cbn.
  solve_init.
Qed.

Ltac R_mod :=
match goal with
| |- S0 lh ?a _ ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
    follow init.
    R_mod.
    follow100 OvIncs1.
    R_mod.
    finish.
  }
  apply Ov0H.
  Unshelve.
  all: solve_ge.
Qed.

End TM38.


Module TM39.

Definition tm := Eval compute in (TM_from_str "1RB0RB_1LC0RA_0LE0LD_1LC0LF_1RA---_0RA0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[0;1;1;1;0;0].
Notation d1 := <[0;1;1;1;1;1].
Notation "l <| r" := (l <{{C}} [1;0] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{B}}> r) (at level 30).
Notation lh := (0inf <* <[1;1]).

Definition LC l len n := BinDec d0 d1 len n l.

Lemma LC_Inc l len n r:
  S n<2^len ->
  LC l len (S n) <| r -->*
  LC l len n |> r.
Proof.
  intros H.
  eapply progress_evstep.
  apply LBinDec_spec; try assumption.
  es.
Qed.

Definition S0 l len n b :=
  LC l len n <| [1;0]^^(b) *> 0inf.

Opaque BinDec.

Lemma Inc l len n b:
  S n<2^len ->
  S0 l len (S n) b -->*
  S0 l len n (1+b).
Proof.
  unfold S0,LC.
  intros.
  follow LC_Inc.
  es.
Qed.

Lemma Incs l len n b:
  n<2^len ->
  S0 l len n b -->*
  S0 l len 0 (n+b).
Proof.
  gen b.
  induction n; intros.
  1: finish.
  follow Inc.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Ov1 len b:
  S0 lh (len+1) 0 (1+b*3) -->+
  S0 lh (len+1+b+1) ((((2^len-1)*2+1)*2^b-1)*2+1) 2.
Proof.
  unfold S0,LC.
  rw_Bin.
  2,3: solve_pow2_lt.
  es.
Qed.

Lemma OvIncs1 len b:
  S0 lh (len+1) 0 (1+b*3) -->+
  S0 lh (len+1+b+1) 0 (((((2^len-1)*2+1)*2^b-1)*2+1)+2).
Proof.
  follow10 Ov1.
  follow Incs.
  1: solve_pow2_lt.
  finish.
Qed.

Definition S1 a len b m :=
  S0 (lh<*d0^^a<*<[0;1;1;1;0;1;1]) len b m.

Lemma Ov0 len b:
  S0 lh (len+1) 0 (0+b*3) -->+
  S1 len (b+1) ((2^b-1)*2+1) 0.
Proof.
  unfold S1,S0,LC.
  rw_Bin.
  2: solve_pow2_lt.
  es.
Qed.

Lemma Ov0a_S a b m:
  S1 (S a) b 0 m -->*
  S1 a (b+1) ((2^b-1)*2+1) (m+1).
Proof.
  unfold S1,S0,LC.
  rw_Bin.
  2: solve_pow2_lt.
  es.
Qed.

Lemma Ov0a a b m:
  halts tm (S1 a b 0 m).
Proof.
  gen b m.
  induction a; intros.
  - eapply halts_evstep.
    2: {
      unfold S1,S0,LC.
      rw_Bin.
      repeat (step1 || sr).
      finish.
    }
    eapply halted_halts.
    constructor.
  - eapply halts_evstep.
    2: {
      unfold S1.
      follow Ov0a_S.
      unfold S1.
      follow Incs.
      1: solve_pow2_lt.
      finish.
    }
    unfold S1 in IHa.
    apply IHa.
Qed.

Lemma Ov0H len b:
  halts tm (S0 lh (len+1) 0 (0+b*3)).
Proof.
  eapply halts_evstep.
  2: {
    follow100 Ov0.
    follow Incs.
    1: solve_pow2_lt.
    finish.
  }
  apply Ov0a.
Qed.

Lemma init: c0-->* S0 lh (4+1) 0 43.
Proof.
  Transparent BinDec.
  unfold S0,LC; cbn.
  solve_init.
Qed.

Ltac R_mod :=
match goal with
| |- S0 lh ?a _ ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
    follow init.
    R_mod.
    follow100 OvIncs1.
    R_mod.
    finish.
  }
  apply Ov0H.
  Unshelve.
  all: solve_ge.
Qed.

End TM39.


Module TM50.

Definition tm := Eval compute in (TM_from_str "1LB0LF_1RC1LA_1LD0RC_1RE0LB_1RC0RE_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[0;0].
Notation d1 := <[1;0].
Notation "l <| r" := (l <{{A}} [] *> r) (at level 30).
Notation "l |> r" := (l <* <[] {{C}}> r) (at level 30).

Definition LC l len n := BinDec d0 d1 len n l.

Lemma LC_Inc l len n r:
  S n<2^len ->
  LC l len (S n) <| r -->*
  LC l len n |> r.
Proof.
  intros H.
  eapply progress_evstep.
  apply LBinDec_spec; try assumption.
  es.
Qed.

Definition S0 l len n b :=
  LC l len n <| [1;0] *> [1;1]^^(1+b) *> 0inf.

Opaque BinDec.

Lemma Inc0 l len n b:
  S n<2^len ->
  S0 l len (S n) b -->*
  S0 l len n (1+b).
Proof.
  unfold S0,LC.
  intros.
  follow LC_Inc.
  es.
Qed.

Lemma Incs0 l len n b:
  n<2^len ->
  S0 l len n b -->*
  S0 l len 0 (n+b).
Proof.
  gen b.
  induction n; intros.
  1: finish.
  follow Inc0.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Ov l l' len b:
  (forall r, l <| r -->* l' {{C}}> r) ->
  S0 (l<*<[0;1]) len 0 b -->*
  S0 (l'<*<[1]) (len+1+1+b) ((((2^len-1)*2+1)*2+1)*2^b-1) 0.
Proof.
  intros Hl.
  unfold S0,LC.
  rw_Bin.
  2,3: solve_pow2_lt.
  es; er.
  follow Hl.
  es.
Qed.

Lemma OvIncs {l l' len b}:
  (forall r, l <| r -->* l' {{C}}> r) ->
  exists len' b',
  S0 (l<*<[0;1]) len 0 b -->*
  S0 (l'<*<[1]) len' 0 b'.
Proof.
  intros Hl.
  eexists _,_.
  follow Ov.
  follow Incs0.
  1: solve_pow2_lt.
  finish.
Qed.

Lemma Ov' l l' len b:
  (forall r, l <| r -->* l' {{E}}> r) ->
  S0 (l<*<[0;1]) len 0 b -->*
  S0 (l'<*<[0;1]) len (2^len-1) (b+1).
Proof.
  intros Hl.
  unfold S0,LC.
  rw_Bin.
  es; er.
  follow Hl.
  es.
Qed.

Lemma OvIncs' {l l' len b}:
  (forall r, l <| r -->* l' {{E}}> r) ->
  exists len' b',
  S0 (l<*<[0;1]) len 0 b -->*
  S0 (l'<*<[0;1]) len' 0 b'.
Proof.
  intros Hl.
  eexists _,_.
  follow Ov'.
  follow Incs0.
  1: solve_pow2_lt.
  finish.
Qed.

Lemma OvH l len b:
  halts tm (S0 (l<*<[1;1;0;1]) len 0 b).
Proof.
  unfold S0,LC.
  rw_Bin.
  solve_halt.
Qed.

Transparent BinDec.

Lemma init:
  exists len b,
  c0 -->*
  S0 (0inf<*<[1;0;1;0]<*<[0;1]) len 0 b.
Proof.
  exists 2 6.
  unfold S0,LC; cbn; solve_init.
Qed.

Lemma init1:
  exists len b,
  c0 -->*
  S0 (0inf<*<[1;0;0;0;0]<*<[0;1]) len 0 b.
Proof.
  epose proof init as [len [b I]].
  epose proof (OvIncs _) as [len' [b' I']].
  eexists _,_; follow I; apply I'.
  Unshelve.
  es.
Qed.

Lemma init2:
  exists len b,
  c0 -->*
  S0 (0inf<*<[1;0;0;1]<*<[0;1]) len 0 b.
Proof.
  epose proof init1 as [len [b I]].
  epose proof (OvIncs _) as [len' [b' I']].
  eexists _,_; follow I; apply I'.
  Unshelve.
  es.
Qed.

Lemma init3:
  exists len b,
  c0 -->*
  S0 (0inf<*<[1;0;0;0;1;0]<*<[0;1]) len 0 b.
Proof.
  epose proof init2 as [len [b I]].
  epose proof (OvIncs' _) as [len' [b' I']].
  eexists _,_; follow I; apply I'.
  Unshelve.
  es.
Qed.

Lemma init4:
  exists len b,
  c0 -->*
  S0 (0inf<*<[1;0;1;0;0]<*<[0;1]) len 0 b.
Proof.
  epose proof init3 as [len [b I]].
  epose proof (OvIncs _) as [len' [b' I']].
  eexists _,_; follow I; apply I'.
  Unshelve.
  es.
Qed.

Lemma init5:
  exists len b,
  c0 -->*
  S0 (0inf<*<[1;0;1;1]<*<[0;1]) len 0 b.
Proof.
  epose proof init4 as [len [b I]].
  epose proof (OvIncs _) as [len' [b' I']].
  eexists _,_; follow I; apply I'.
  Unshelve.
  es.
Qed.

Lemma halt: halts tm c0.
Proof.
  epose proof init5 as [a0 [b0 I0]].
  eapply halts_evstep.
  2: apply I0.
  apply OvH.
Qed.

End TM50.


Module TM51.

Definition tm := Eval compute in (TM_from_str "1LB1LF_1RC1LA_1LD0RC_1RE0LB_1RC0RE_1RD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[0;0].
Notation d1 := <[1;0].
Notation "l <| r" := (l <{{A}} [] *> r) (at level 30).
Notation "l |> r" := (l <* <[] {{C}}> r) (at level 30).

Definition LC l len n := BinDec d0 d1 len n l.

Lemma LC_Inc l len n r:
  S n<2^len ->
  LC l len (S n) <| r -->*
  LC l len n |> r.
Proof.
  intros H.
  eapply progress_evstep.
  apply LBinDec_spec; try assumption.
  es.
Qed.

Definition S0 l len n b :=
  LC l len n <| [1;0] *> [1;1]^^(1+b) *> 0inf.

Opaque BinDec.

Lemma Inc0 l len n b:
  S n<2^len ->
  S0 l len (S n) b -->*
  S0 l len n (1+b).
Proof.
  unfold S0,LC.
  intros.
  follow LC_Inc.
  es.
Qed.

Lemma Incs0 l len n b:
  n<2^len ->
  S0 l len n b -->*
  S0 l len 0 (n+b).
Proof.
  gen b.
  induction n; intros.
  1: finish.
  follow Inc0.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Ov l l' len b:
  (forall r, l <| r -->* l' {{C}}> r) ->
  S0 (l<*<[0;1]) len 0 b -->*
  S0 (l'<*<[1]) (len+1+1+b) ((((2^len-1)*2+1)*2+1)*2^b-1) 0.
Proof.
  intros Hl.
  unfold S0,LC.
  rw_Bin.
  2,3: solve_pow2_lt.
  es; er.
  follow Hl.
  es.
Qed.

Lemma OvIncs {l l' len b}:
  (forall r, l <| r -->* l' {{C}}> r) ->
  exists len' b',
  S0 (l<*<[0;1]) len 0 b -->*
  S0 (l'<*<[1]) len' 0 b'.
Proof.
  intros Hl.
  eexists _,_.
  follow Ov.
  follow Incs0.
  1: solve_pow2_lt.
  finish.
Qed.

Lemma Ov' l l' len b:
  (forall r, l <| r -->* l' {{E}}> r) ->
  S0 (l<*<[0;1]) len 0 b -->*
  S0 (l'<*<[0;1]) len (2^len-1) (b+1).
Proof.
  intros Hl.
  unfold S0,LC.
  rw_Bin.
  es; er.
  follow Hl.
  es.
Qed.

Lemma OvIncs' {l l' len b}:
  (forall r, l <| r -->* l' {{E}}> r) ->
  exists len' b',
  S0 (l<*<[0;1]) len 0 b -->*
  S0 (l'<*<[0;1]) len' 0 b'.
Proof.
  intros Hl.
  eexists _,_.
  follow Ov'.
  follow Incs0.
  1: solve_pow2_lt.
  finish.
Qed.

Lemma OvH l len b:
  halts tm (S0 (l<*<[1;1;0;1]) len 0 b).
Proof.
  unfold S0,LC.
  rw_Bin.
  solve_halt.
Qed.

Transparent BinDec.

Lemma init:
  exists len b,
  c0 -->*
  S0 (0inf<*<[1;0;1;0]<*<[0;1]) len 0 b.
Proof.
  exists 2 6.
  unfold S0,LC; cbn; solve_init.
Qed.

Lemma init1:
  exists len b,
  c0 -->*
  S0 (0inf<*<[1;0;0;0;0]<*<[0;1]) len 0 b.
Proof.
  epose proof init as [len [b I]].
  epose proof (OvIncs _) as [len' [b' I']].
  eexists _,_; follow I; apply I'.
  Unshelve.
  es.
Qed.

Lemma init2:
  exists len b,
  c0 -->*
  S0 (0inf<*<[1;0;0;1]<*<[0;1]) len 0 b.
Proof.
  epose proof init1 as [len [b I]].
  epose proof (OvIncs _) as [len' [b' I']].
  eexists _,_; follow I; apply I'.
  Unshelve.
  es.
Qed.

Lemma init3:
  exists len b,
  c0 -->*
  S0 (0inf<*<[1;0;0;0;1;0]<*<[0;1]) len 0 b.
Proof.
  epose proof init2 as [len [b I]].
  epose proof (OvIncs' _) as [len' [b' I']].
  eexists _,_; follow I; apply I'.
  Unshelve.
  es.
Qed.

Lemma init4:
  exists len b,
  c0 -->*
  S0 (0inf<*<[1;0;1;0;0]<*<[0;1]) len 0 b.
Proof.
  epose proof init3 as [len [b I]].
  epose proof (OvIncs _) as [len' [b' I']].
  eexists _,_; follow I; apply I'.
  Unshelve.
  es.
Qed.

Lemma init5:
  exists len b,
  c0 -->*
  S0 (0inf<*<[1;0;1;1]<*<[0;1]) len 0 b.
Proof.
  epose proof init4 as [len [b I]].
  epose proof (OvIncs _) as [len' [b' I']].
  eexists _,_; follow I; apply I'.
  Unshelve.
  es.
Qed.

Lemma halt: halts tm c0.
Proof.
  epose proof init5 as [a0 [b0 I0]].
  eapply halts_evstep.
  2: apply I0.
  apply OvH.
Qed.

End TM51.


Module TM52.

Definition tm := Eval compute in (TM_from_str "1RB---_1RC0LE_1RD0RC_1LB0RD_1RD1LF_1LE1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[0;0].
Notation d1 := <[1;0].
Notation "l <| r" := (l <{{F}} [] *> r) (at level 30).
Notation "l |> r" := (l <* <[] {{D}}> r) (at level 30).

Definition LC l len n := BinDec d0 d1 len n l.

Lemma LC_Inc l len n r:
  S n<2^len ->
  LC l len (S n) <| r -->*
  LC l len n |> r.
Proof.
  intros H.
  eapply progress_evstep.
  apply LBinDec_spec; try assumption.
  es.
Qed.

Definition S0 l len n b :=
  LC l len n <| [1;0] *> [1;1]^^(1+b) *> 0inf.

Opaque BinDec.

Lemma Inc0 l len n b:
  S n<2^len ->
  S0 l len (S n) b -->*
  S0 l len n (1+b).
Proof.
  unfold S0,LC.
  intros.
  follow LC_Inc.
  es.
Qed.

Lemma Incs0 l len n b:
  n<2^len ->
  S0 l len n b -->*
  S0 l len 0 (n+b).
Proof.
  gen b.
  induction n; intros.
  1: finish.
  follow Inc0.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Ov l l' len b:
  (forall r, l <| r -->* l' {{D}}> r) ->
  S0 (l<*<[0;1]) len 0 b -->*
  S0 (l'<*<[1]) (len+1+1+b) ((((2^len-1)*2+1)*2+1)*2^b-1) 0.
Proof.
  intros Hl.
  unfold S0,LC.
  rw_Bin.
  2,3: solve_pow2_lt.
  es; er.
  follow Hl.
  es.
Qed.

Lemma OvIncs {l l' len b}:
  (forall r, l <| r -->* l' {{D}}> r) ->
  exists len' b',
  S0 (l<*<[0;1]) len 0 b -->*
  S0 (l'<*<[1]) len' 0 b'.
Proof.
  intros Hl.
  eexists _,_.
  follow Ov.
  follow Incs0.
  1: solve_pow2_lt.
  finish.
Qed.

Lemma Ov' l l' len b:
  (forall r, l <| r -->* l' {{C}}> r) ->
  S0 (l<*<[0;1]) len 0 b -->*
  S0 (l'<*<[0;1]) len (2^len-1) (b+1).
Proof.
  intros Hl.
  unfold S0,LC.
  rw_Bin.
  es; er.
  follow Hl.
  es.
Qed.

Lemma OvIncs' {l l' len b}:
  (forall r, l <| r -->* l' {{C}}> r) ->
  exists len' b',
  S0 (l<*<[0;1]) len 0 b -->*
  S0 (l'<*<[0;1]) len' 0 b'.
Proof.
  intros Hl.
  eexists _,_.
  follow Ov'.
  follow Incs0.
  1: solve_pow2_lt.
  finish.
Qed.

Lemma OvH l len b:
  halts tm (S0 (l<*<[1;1;0;1]) len 0 b).
Proof.
  unfold S0,LC.
  rw_Bin.
  solve_halt.
Qed.

Transparent BinDec.

Lemma init1:
  exists len b,
  c0 -->*
  S0 (0inf<*<[1;0;0;0;0]<*<[0;1]) len 0 b.
Proof.
  exists 2 2.
  unfold S0,LC; cbn; solve_init.
Qed.

Lemma init2:
  exists len b,
  c0 -->*
  S0 (0inf<*<[1;0;0;1]<*<[0;1]) len 0 b.
Proof.
  epose proof init1 as [len [b I]].
  epose proof (OvIncs _) as [len' [b' I']].
  eexists _,_; follow I; apply I'.
  Unshelve.
  es.
Qed.

Lemma init3:
  exists len b,
  c0 -->*
  S0 (0inf<*<[1;0;0;0;1;0]<*<[0;1]) len 0 b.
Proof.
  epose proof init2 as [len [b I]].
  epose proof (OvIncs' _) as [len' [b' I']].
  eexists _,_; follow I; apply I'.
  Unshelve.
  es.
Qed.

Lemma init4:
  exists len b,
  c0 -->*
  S0 (0inf<*<[1;0;1;0;0]<*<[0;1]) len 0 b.
Proof.
  epose proof init3 as [len [b I]].
  epose proof (OvIncs _) as [len' [b' I']].
  eexists _,_; follow I; apply I'.
  Unshelve.
  es.
Qed.

Lemma init5:
  exists len b,
  c0 -->*
  S0 (0inf<*<[1;0;1;1]<*<[0;1]) len 0 b.
Proof.
  epose proof init4 as [len [b I]].
  epose proof (OvIncs _) as [len' [b' I']].
  eexists _,_; follow I; apply I'.
  Unshelve.
  es.
Qed.

Lemma halt: halts tm c0.
Proof.
  epose proof init5 as [a0 [b0 I0]].
  eapply halts_evstep.
  2: apply I0.
  apply OvH.
Qed.

End TM52.


Module TM54.

Definition tm := Eval compute in (TM_from_str "1LB---_1RC1LB_1RF0RD_1LD1LE_0RE0LB_0RA0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[0;1;1].
Notation d1 := <[1;1;1].
Notation "l <| r" := (l <{{B}} [] *> r) (at level 30).
Notation "l |> r" := (l <* <[] {{F}}> r) (at level 30).

Definition LC l len n := BinDec d0 d1 len n l.

Lemma LC_Inc l len n r:
  S n<2^len ->
  LC l len (S n) <| r -->*
  LC l len n |> r.
Proof.
  intros H.
  eapply progress_evstep.
  apply LBinDec_spec; try assumption.
  es.
Qed.

Definition S0 l len n b :=
  LC l len n <| [1;0] *> [1;1;1]^^(b*2) *> 0inf.

Opaque BinDec.

Lemma Inc0 l len n b:
  S n<2^len ->
  S0 l len (S n) b -->*
  S0 l len n (1+b).
Proof.
  unfold S0,LC.
  intros.
  follow LC_Inc.
  es.
Qed.

Lemma Incs0 l len n b:
  n<2^len ->
  S0 l len n b -->*
  S0 l len 0 (n+b).
Proof.
  gen b.
  induction n; intros.
  1: finish.
  follow Inc0.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Ov_S a b:
  S0 0inf (a+3) 0 b -->*
  S0 (0inf <* d1 <* d0^^(a+1) <* <[1;1]) (b*2+1) (2^(b*2+1)-1) 1.
Proof.
  unfold S0,LC.
  rw_Bin.
  es.
Qed.

Lemma Halt a b m:
  halts tm (S0 (0inf <* d1 <* d0^^(a+1) <* <[1;1]) b 0 (m+1)).
Proof.
  unfold S0,LC.
  rw_Bin.
  solve_halt.
Qed.

Lemma Halt0 a b:
  b<2^(a+3) ->
  halts tm (S0 0inf (a+3) b 1).
Proof.
  intros Hb.
  eapply halts_evstep.
  2: {
    follow Incs0.
    follow Ov_S.
    follow Incs0.
    1: apply lt_pow2sub1.
    finish.
  }
  apply Halt.
Qed.

Lemma init: c0 -->* S0 0inf (0+1+1+9) (((0*2+1)*2+1)*2^9-1) 1.
Proof.
  Transparent BinDec.
  unfold S0,LC.
  rw_Bin.
  2: solve_pow2_lt.
  solve_init.
Qed.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: apply init.
  change (0+1+1+9) with (8+3).
  apply Halt0.
  vm_compute; lia.
Qed.

End TM54.


Module TM55.

Definition tm := Eval compute in (TM_from_str "1RB0RF_0RC---_1LC1LD_0RD0LE_1RF1LE_1RA0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[0;1;1].
Notation d1 := <[1;1;1].
Notation "l <| r" := (l <{{E}} [] *> r) (at level 30).
Notation "l |> r" := (l <* <[] {{A}}> r) (at level 30).

Definition LC l len n := BinDec d0 d1 len n l.

Lemma LC_Inc l len n r:
  S n<2^len ->
  LC l len (S n) <| r -->*
  LC l len n |> r.
Proof.
  intros H.
  eapply progress_evstep.
  apply LBinDec_spec; try assumption.
  es.
Qed.

Definition S0 l len n b :=
  LC l len n <| [1;0] *> [1;1;1]^^(b*2) *> 0inf.

Opaque BinDec.

Lemma Inc0 l len n b:
  S n<2^len ->
  S0 l len (S n) b -->*
  S0 l len n (1+b).
Proof.
  unfold S0,LC.
  intros.
  follow LC_Inc.
  es.
Qed.

Lemma Incs0 l len n b:
  n<2^len ->
  S0 l len n b -->*
  S0 l len 0 (n+b).
Proof.
  gen b.
  induction n; intros.
  1: finish.
  follow Inc0.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Ov_S a b:
  S0 0inf (a+3) 0 b -->*
  S0 (0inf <* d1 <* d0^^(a+1) <* <[1;1]) (b*2+1) (2^(b*2+1)-1) 1.
Proof.
  unfold S0,LC.
  rw_Bin.
  es.
Qed.

Lemma Halt a b m:
  halts tm (S0 (0inf <* d1 <* d0^^(a+1) <* <[1;1]) b 0 (m+1)).
Proof.
  unfold S0,LC.
  rw_Bin.
  solve_halt.
Qed.

Lemma Halt0 a b:
  b<2^(a+3) ->
  halts tm (S0 0inf (a+3) b 1).
Proof.
  intros Hb.
  eapply halts_evstep.
  2: {
    follow Incs0.
    follow Ov_S.
    follow Incs0.
    1: apply lt_pow2sub1.
    finish.
  }
  apply Halt.
Qed.

Lemma init: c0 -->* S0 0inf (0+1+1+9) (((0*2+1)*2+1)*2^9-1) 1.
Proof.
  Transparent BinDec.
  unfold S0,LC.
  rw_Bin.
  2: solve_pow2_lt.
  solve_init.
Qed.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: apply init.
  change (0+1+1+9) with (8+3).
  apply Halt0.
  vm_compute; lia.
Qed.

End TM55.


Module TM56.

Definition tm := Eval compute in (TM_from_str "1RB1LA_1RC0RE_0RD0RB_1LA1LE_1LF0LA_1LD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[0;1;1].
Notation d1 := <[1;1;1].
Notation "l <| r" := (l <{{A}} [] *> r) (at level 30).
Notation "l |> r" := (l <* <[] {{C}}> r) (at level 30).

Definition LC l len n := BinDec d0 d1 len n l.

Lemma LC_Inc l len n r:
  S n<2^len ->
  LC l len (S n) <| r -->*
  LC l len n |> r.
Proof.
  intros H.
  eapply progress_evstep.
  apply LBinDec_spec; try assumption.
  es.
Qed.

Definition S0 l len n b :=
  LC l len n <| [1;0] *> [1;1;1]^^(b) *> 0inf.

Opaque BinDec.

Lemma Inc0 l len n b:
  S n<2^len ->
  S0 l len (S n) b -->*
  S0 l len n (2+b).
Proof.
  unfold S0,LC.
  intros.
  follow LC_Inc.
  es.
Qed.

Lemma Incs0 l len n b:
  n<2^len ->
  S0 l len n b -->*
  S0 l len 0 (n*2+b).
Proof.
  gen b.
  induction n; intros.
  1: finish.
  follow Inc0.
  follow IHn.
  1: lia.
  finish.
Qed.

Definition S1 a b :=
  0inf <* d1 <* d0^^a <{{A}} [1;1;1]^^b *> 0inf.

Lemma S1_Inc a b:
  S1 (2+a) b -->*
  S1 a (3+b).
Proof. es. Qed.

Lemma S1_Incs n a b:
  S1 (n*2+a) b -->*
  S1 a (n*3+b).
Proof.
  gen a b.
  ind n S1_Inc.
Qed.

Lemma Ov1 a b:
  S0 0inf (1+a*2) 0 b -->*
  S0 0inf (0+1+(b+a*3+1)) ((0*2+1)*2^(b+a*3+1)-1) 2.
Proof.
  remember (b+a*3+1) as v1.
  unfold S1,S0,LC.
  rw_Bin.
  2: solve_pow2_lt.
  subst.
  mid (S1 (a*2+0) (b+1)).
  1: es.
  follow S1_Incs.
  es.
Qed.

Lemma Ov0 a b:
  a>=1 ->
  halts tm (S0 0inf (0+a*2) 0 b).
Proof.
  intros Ha.
  destruct a as [|a].
  1: lia.
  eapply halts_evstep.
  2: {
    unfold S0,LC.
    rw_Bin.
    mid (S1 (a*2+1) (b+1)).
    1: es.
    follow S1_Incs.
    unfold S1.
    repeat (step1 || sr).
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

Lemma Ov1Incs a b:
  S0 0inf (1+a*2) 0 b -->*
  S0 0inf ((b+a*3+1)+1) 0 ((2^(b+a*3+1)-1)*2+2).
Proof.
  follow Ov1.
  remember (b+a*3+1) as v1.
  follow Incs0.
  1: solve_pow2_lt.
  finish.
Qed.

Ltac R_mod :=
match goal with
| |- S0 _ ?a _ ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' a 2 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Transparent BinDec.
Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
    mid (S0 0inf 3 0 8).
    1: unfold S0,LC; cbn; solve_init.
    remember 8 as v1.
    change 3 with (1+1*2)%nat.
    subst.
    follow Ov1Incs.
    R_mod.
    follow Ov1Incs.
    R_mod.
    finish.
  }
  eapply Ov0.
  shelve.
  Unshelve.
  all: solve_ge.
Qed.

End TM56.


Module TM59.

Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC0LE_---0RD_1RA1RF_1LA0RF_1RE0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[0;1;1;0;0;1].
Notation d1 := <[0;0;1;0;0;1].
Notation "l <| r" := (l <{{B}} [] *> r) (at level 30).
Notation "l |> r" := (l <* <[] {{C}}> r) (at level 30).

Definition LC l len n := BinDec d0 d1 len n l.

Lemma LC_Inc l len n r:
  S n<2^len ->
  LC l len (S n) <| r -->*
  LC l len n |> r.
Proof.
  intros H.
  eapply progress_evstep.
  apply LBinDec_spec; try assumption.
  es.
Qed.

Notation lh := (0inf <* [1]).

Definition S0 l len n b :=
  LC l len n <| [1] *> [1;0]^^(1+b) *> 0inf.

Opaque BinDec.

Lemma Inc0 l len n b:
  S n<2^len ->
  S0 l len (S n) b -->*
  S0 l len n (2+b).
Proof.
  unfold S0,LC.
  intros.
  follow LC_Inc.
  es.
Qed.

Lemma Incs0 l len n b:
  n<2^len ->
  S0 l len n b -->*
  S0 l len 0 (n*2+b).
Proof.
  gen b.
  induction n; intros.
  1: finish.
  follow Inc0.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Ov1 len b:
  S0 lh (len+1) 0 (1+b*3) -->+
  S0 lh (len+1+b+1) ((((2^len-1)*2+1)*2^b-1)*2+1) 3.
Proof.
  unfold S0,LC.
  rw_Bin.
  2,3: solve_pow2_lt.
  repeat (rewrite lpow_add || rewrite lpow_mul).
  simpl_tape.
  execute_with_shift_rule'.
Qed.

Lemma Ov1Incs len b:
  S0 lh (len+1) 0 (1+b*3) -->+
  S0 lh (len+1+b+1) 0 (((((2^len-1)*2+1)*2^b-1)*2+1)*2+3).
Proof.
  follow10 Ov1.
  follow Incs0.
  1: solve_pow2_lt.
  finish.
Qed.

Lemma Ov2 len b:
  S0 lh (len+1) 0 (2+b*3) -->+
  S0 lh (len+1+b+1) ((((2^len-1)*2+1)*2^b-1)*2+1) 5.
Proof.
  unfold S0,LC.
  rw_Bin.
  2,3: solve_pow2_lt.
  1: es.
Qed.

Lemma Ov2Incs len b:
  S0 lh (len+1) 0 (2+b*3) -->+
  S0 lh (len+1+b+1) 0 (((((2^len-1)*2+1)*2^b-1)*2+1)*2+5).
Proof.
  follow10 Ov2.
  follow Incs0.
  1: solve_pow2_lt.
  finish.
Qed.

Lemma Ov0 len b:
  halts tm (S0 lh (len+1) 0 (0+b*3)).
Proof.
  unfold S0,LC.
  rw_Bin.
  solve_halt.
Qed.

Transparent BinDec.
Lemma init: c0 -->* S0 lh 3 0 13.
Proof.
  1: unfold S0,LC; cbn; solve_init.
Qed.

Ltac R_mod :=
match goal with
| |- S0 _ ?a _ ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
    follow init.
    change (S0 lh 3 0 13) with (S0 lh (2+1) 0 (1+4*3)).
    follow100 Ov1Incs.
    R_mod.
    follow100 Ov2Incs.
    R_mod.
    finish.
  }
  apply Ov0.
  Unshelve.
  all: solve_ge.
Qed.

End TM59.


Module TM60.

Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC0RA_1LA0LB_1RE0LA_---0RF_1RC1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[0;1;1;0;0;1].
Notation d1 := <[0;0;1;0;0;1].
Notation "l <| r" := (l <{{A}} [1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0] {{F}}> r) (at level 30).

Definition LC l len n := BinDec d0 d1 len n l.

Lemma LC_Inc l len n r:
  S n<2^len ->
  LC l len (S n) <| r -->*
  LC l len n |> r.
Proof.
  intros H.
  eapply progress_evstep.
  apply LBinDec_spec; try assumption.
  es.
Qed.

Notation lh := (0inf <* <[1;0;0;1]).

Definition S0 l len n b :=
  LC l len n <| [1;0]^^(1+b) *> 0inf.

Opaque BinDec.

Lemma Inc0 l len n b:
  S n<2^len ->
  S0 l len (S n) b -->*
  S0 l len n (2+b).
Proof.
  unfold S0,LC.
  intros.
  follow LC_Inc.
  es.
Qed.

Lemma Incs0 l len n b:
  n<2^len ->
  S0 l len n b -->*
  S0 l len 0 (n*2+b).
Proof.
  gen b.
  induction n; intros.
  1: finish.
  follow Inc0.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Ov1 len b:
  S0 lh (len+1) 0 (1+b*3) -->+
  S0 lh (len+1+b+1) ((((2^len-1)*2+1)*2^b-1)*2+1) 3.
Proof.
  unfold S0,LC.
  rw_Bin.
  2,3: solve_pow2_lt.
  repeat (rewrite lpow_add || rewrite lpow_mul).
  simpl_tape.
  execute_with_shift_rule'.
Qed.

Lemma Ov1Incs len b:
  S0 lh (len+1) 0 (1+b*3) -->+
  S0 lh (len+1+b+1) 0 (((((2^len-1)*2+1)*2^b-1)*2+1)*2+3).
Proof.
  follow10 Ov1.
  follow Incs0.
  1: solve_pow2_lt.
  finish.
Qed.

Lemma Ov2 len b:
  S0 lh (len+1) 0 (2+b*3) -->+
  S0 lh (len+1+b+1) ((((2^len-1)*2+1)*2^b-1)*2+1) 5.
Proof.
  unfold S0,LC.
  rw_Bin.
  2,3: solve_pow2_lt.
  1: es.
Qed.

Lemma Ov2Incs len b:
  S0 lh (len+1) 0 (2+b*3) -->+
  S0 lh (len+1+b+1) 0 (((((2^len-1)*2+1)*2^b-1)*2+1)*2+5).
Proof.
  follow10 Ov2.
  follow Incs0.
  1: solve_pow2_lt.
  finish.
Qed.

Lemma Ov0 len b:
  halts tm (S0 lh (len+1) 0 (0+b*3)).
Proof.
  unfold S0,LC.
  rw_Bin.
  solve_halt.
Qed.

Transparent BinDec.
Lemma init: c0 -->* S0 lh 3 0 13.
Proof.
  1: unfold S0,LC; cbn; solve_init.
Qed.

Ltac R_mod :=
match goal with
| |- S0 _ ?a _ ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
    follow init.
    change (S0 lh 3 0 13) with (S0 lh (2+1) 0 (1+4*3)).
    follow100 Ov1Incs.
    R_mod.
    follow100 Ov2Incs.
    R_mod.
    finish.
  }
  apply Ov0.
  Unshelve.
  all: solve_ge.
Qed.

End TM60.


Module TM61.

Definition tm := Eval compute in (TM_from_str "1RB1LD_1RC0RF_0RD0RB_0LE0RA_1LA1RC_1RE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[0;1;1;0;1;0].
Notation d1 := <[0;1;1;0;1;1].
Notation "l <| r" := (l <{{A}} [] *> r) (at level 30).
Notation "l |> r" := (l <* <[] {{B}}> r) (at level 30).

Definition LC l len n := BinDec d0 d1 len n l.

Lemma LC_Inc l len n r:
  S n<2^len ->
  LC l len (S n) <| r -->*
  LC l len n |> r.
Proof.
  intros H.
  eapply progress_evstep.
  apply LBinDec_spec; try assumption.
  es.
Qed.

Notation lh := (0inf <* <[1]).

Definition S0 l len n b :=
  LC l len n <| [1;0;1] *> [1;0]^^(b) *> 0inf.

Opaque BinDec.

Lemma Inc0 l len n b:
  S n<2^len ->
  S0 l len (S n) b -->*
  S0 l len n (1+b).
Proof.
  unfold S0,LC.
  intros.
  follow LC_Inc.
  es.
Qed.

Lemma Incs0 l len n b:
  n<2^len ->
  S0 l len n b -->*
  S0 l len 0 (n+b).
Proof.
  gen b.
  induction n; intros.
  1: finish.
  follow Inc0.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Ov2 len b:
  S0 lh (len) 0 (2+b*3) -->+
  S0 lh (len+1+b) (((2^len-1)*2+1)*2^b-1) 2.
Proof.
  unfold S0,LC.
  rw_Bin.
  2: solve_pow2_lt.
  es.
Qed.

Lemma Ov2Incs len b:
  S0 lh (len) 0 (2+b*3) -->*
  S0 lh (len+1+b) 0 ((((2^len-1)*2+1)*2^b-1)+2).
Proof.
  follow100 Ov2.
  follow Incs0.
  1: solve_pow2_lt.
  finish.
Qed.

Lemma Ov1 len b:
  b >= 1 ->
  S0 lh (len) 0 (1+b*3) -->*
  S0 lh (len+1+b) ((((2^len-1)*2+1)*2^b-1)) 1.
Proof.
  intros Hb.
  unfold S0,LC.
  rw_Bin.
  2: solve_pow2_lt.
  destruct b as [|b].
  1: lia.
  es.
Qed.

Lemma Ov1Incs len b:
  b>=1 ->
  S0 lh (len) 0 (1+b*3) -->*
  S0 lh (len+1+b) 0 ((((2^len-1)*2+1)*2^b-1)+1).
Proof.
  intros Hb.
  follow Ov1.
  follow Incs0.
  1: solve_pow2_lt.
  finish.
Qed.

Lemma Ov0 len b:
  b>=2 ->
  halts tm (S0 lh len 0 (0+b*3)).
Proof.
  intros Hb.
  replace b with (b-2+2) by lia.
  unfold S0,LC.
  rw_Bin.
  solve_halt.
Qed.

Transparent BinDec.
Lemma init: c0 -->* S0 lh 4 0 (2+4*3).
Proof.
  1: unfold S0,LC; cbn; solve_init.
Qed.

Ltac R_mod :=
match goal with
| |- S0 _ ?a _ ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
    follow init.
    follow Ov2Incs.
    R_mod.
    follow Ov2Incs.
    R_mod.
    epose proof (Ov1Incs _ _ _) as I.
    follow I; clear I.
    R_mod.
    finish.
  }
  eapply Ov0.
  shelve.
  Unshelve.
  all: solve_ge.
Qed.

End TM61.


Module TM62.

Definition tm := Eval compute in (TM_from_str "1RB0LE_1RC1RB_1RD---_1LA0RF_0LA1RD_1RB0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[1;0;0].
Notation d1 := <[1;1;1].
Notation "l <| r" := (l <{{E}} [0] *> r) (at level 30).
Notation "l |> r" := (l <* <[1] {{D}}> r) (at level 30).

Definition LC l len n := BinDec d0 d1 len n l.

Lemma LC_Inc l len n r:
  S n<2^len ->
  LC l len (S n) <| r -->*
  LC l len n |> r.
Proof.
  intros H.
  eapply progress_evstep.
  apply LBinDec_spec; try assumption.
  es.
Qed.

Opaque BinDec.

Definition RC m := [1;1;1;0;0] *> [1;1;1]^^m *> 0inf.

Definition S0 l len1 a1 b :=
  LC l len1 a1 <| RC (1+b).

Lemma Inc0 l len n b:
  S n<2^len ->
  S0 l len (S n) b -->*
  S0 l len n (1+b).
Proof.
  unfold S0,LC.
  intros.
  follow LC_Inc.
  es.
Qed.

Lemma Incs0 l len n b:
  n<2^len ->
  S0 l len n b -->*
  S0 l len 0 (n+b).
Proof.
  gen b.
  induction n; intros.
  1: finish.
  follow Inc0.
  follow IHn.
  1: lia.
  finish.
Qed.

Notation lh := (0inf <* <[1;1]).
Notation m2 := <[1;0;1;1].
Notation m1 := <[1;0;1].
Notation m0 := <[1;0].

Definition S1 len0 a0 m len1 a1 b :=
  S0 (LC lh len0 a0 <* d0 <* m) len1 a1 b.

Lemma Rst2 len0 a0 a b:
  S a0 < 2^len0 ->
  S1 len0 (S a0) m2 a 0 b -->*
  S1 len0 a0 m1 (a+b+2) 0 (2^b-1).
Proof.
  intros Ha0.
  mid (S1 len0 a0 m1 (a+1+1+b) ((0*2*2+1)*2^b-1) 0).
  - unfold S1,S0,LC.
    rw_Bin.
    2: solve_pow2_lt.
    es; er.
    follow LC_Inc.
    es.
  - mid (S1 len0 a0 m1 (a+1+1+b) 0 ((0*2*2+1)*2^b-1+0)).
    1: unfold S1; follow Incs0.
    1: solve_pow2_lt.
    1: finish.
    finish.
Qed.

Lemma Rst1 len0 a0 a b:
  S a0 < 2^len0 ->
  S1 len0 (S a0) m1 a 0 b -->*
  S1 len0 a0 m0 (a+b+2) 0 (2^b-1).
Proof.
  intros Ha0.
  mid (S1 len0 a0 m0 (a+1+1+b) ((0*2*2+1)*2^b-1) 0).
  - unfold S1,S0,LC.
    rw_Bin.
    2: solve_pow2_lt.
    es; er.
    follow LC_Inc.
    es.
  - mid (S1 len0 a0 m0 (a+1+1+b) 0 ((0*2*2+1)*2^b-1+0)).
    1: unfold S1; follow Incs0.
    1: solve_pow2_lt.
    1: finish.
    finish.
Qed.

Lemma Rst0 len0 a0 a b:
  S a0 < 2^len0 ->
  S1 len0 (S a0) m0 a 0 b -->*
  S1 len0 a0 m2 (a+b+1) 0 (2^b-1).
Proof.
  intros Ha0.
  mid (S1 len0 a0 m2 (a+1+b) ((0*2+1)*2^b-1) 0).
  - unfold S1,S0,LC.
    rw_Bin.
    2: solve_pow2_lt.
    es; er.
    follow LC_Inc.
    es.
  - mid (S1 len0 a0 m2 (a+1+b) 0 ((0*2+1)*2^b-1+0)).
    1: unfold S1; follow Incs0.
    1: solve_pow2_lt.
    1: finish.
    finish.
Qed.

Fixpoint t2 a b :=
match a with
| O => b
| S a0 => 2^(t2 a0 b)-1
end.

Fixpoint st2 a b :=
match a with
| O => O
| S a0 => st2 a0 b
end + t2 a b.

Lemma Rsts n len0 a0 b:
  n*3+a0<2^len0 ->
  S1 len0 (n*3+a0) m2 b 0 (2^b-1) -->*
  S1 len0 a0 m2 (st2 (n*3) b + n*5) 0 (t2 (1+n*3) b).
Proof.
  gen a0.
  induction n; intros.
  - cbn; finish.
  - specialize (IHn (3+a0)).
    follow IHn.
    1: lia.
    cbn.
    follow Rst2.
    1: lia.
    follow Rst1.
    1: lia.
    follow Rst0.
    1: lia.
    finish.
Qed.

Lemma Rsts1 n len0 b:
  1+n*3<2^len0 ->
  S1 len0 (1+n*3) m2 b 0 (2^b-1) -->*
  S1 len0 0 m1 (st2 (1+n*3) b + (n*5+2)) 0 (t2 (2+n*3) b).
Proof.
  intros.
  rewrite Nat.add_comm.
  follow Rsts.
  1: lia.
  follow Rst2.
  1: lia.
  rewrite (Nat.add_comm (n*3) 1).
  cbn.
  finish.
Qed.

Lemma Rsts1_v2 n len0 b:
  n<2^len0 ->
  n mod 3 = 1%nat ->
  S1 len0 n m2 b 0 (2^b-1) -->*
  S1 len0 0 m1 (st2 n b + (n/3*5+2)) 0 (t2 (n+1) b).
Proof.
  intros.
  epose proof (div_mod' n 3 1 H0) as Hn.
  rewrite Hn.
  follow Rsts1.
  1: lia.
  finish.
Qed.

Lemma Rsts2 n len0 b:
  2+n*3<2^len0 ->
  S1 len0 (2+n*3) m2 b 0 (2^b-1) -->*
  S1 len0 0 m0 (st2 (2+n*3) b + (n*5+4)) 0 (t2 (3+n*3) b).
Proof.
  intros.
  rewrite Nat.add_comm.
  follow Rsts.
  1: lia.
  follow Rst2.
  1: lia.
  follow Rst1.
  1: lia.
  rewrite (Nat.add_comm (n*3) 2).
  cbn.
  finish.
Qed.

Lemma Rst1' a0 a b:
  S1 a0 0 m1 a 0 b -->*
  S1 (a0+1+1+a) ((((2^a0-1)*2+1)*2+1)*2^a-1) m2 b 0 (2^b-1).
Proof.
  mid (S1 (a0+1+1+a) ((((2^a0-1)*2+1)*2+1)*2^a-1) m2 b (2^b-1) 0).
  - unfold S1,S0,LC,RC.
    rw_Bin.
    all: try solve_pow2_lt.
    es.
  - mid (S1 (a0+1+1+a) ((((2^a0-1)*2+1)*2+1)*2^a-1) m2 b 0 (2^b-1+0)).
    1: unfold S1; follow Incs0.
    1: solve_pow2_lt.
    1: finish.
    finish.
Qed.

Lemma Rst1'_WF a0 a:
  ((((2^a0-1)*2+1)*2+1)*2^a-1) < 2^(a0+1+1+a).
Proof.
  solve_pow2_lt.
Qed.

Lemma Rst0' a0 a b:
  halts tm (S1 a0 0 m0 a 0 b).
Proof.
  unfold S1,S0,LC,RC.
  rw_Bin.
  all: try solve_pow2_lt.
  solve_halt.
Qed.

Lemma Rsts2H n len0 b:
  n<2^len0 ->
  n mod 3 = 2 ->
  halts tm (S1 len0 n m2 b 0 (2^b-1)).
Proof.
  intros.
  epose proof (div_mod' _ _ _ H0) as Hn.
  rewrite Hn.
  eapply halts_evstep.
  2: apply Rsts2.
  2: lia.
  apply Rst0'.
Qed.

Transparent BinDec.
Lemma init: c0-->* S1 3 7 m2 6 0 63.
Proof.
  unfold S1,S0,LC; cbn.
  solve_init.
Qed.

Lemma t2_mod C a b c d:
  (forall x, t2 (C+x) b mod c = d) ->
  a>=C ->
  t2 a b mod c = d.
Proof.
  intros.
  specialize (H (a-C)).
  applys_eq H.
  repeat (lia || f_equal).
Qed.

Lemma st2_mod C a b c d:
  (forall x, t2 (C+x) b mod c = d) ->
  a>=C ->
  st2 a b mod c = (((st2 C b) mod c) + ((d*(a-C)) mod c)) mod c.
Proof.
  intros Hd Ha.
  rewrite <-Nat.Div0.add_mod.
  replace (st2 a) with (st2 (a-C+C)) by (f_equal; lia).
  induction (a-C).
  - cbn.
    f_equal.
    lia.
  - cbn.
    rewrite Nat.Div0.add_mod.
    rewrite IHn.
    specialize (Hd (S n)).
    replace (C+S n) with (S(n+C)) in Hd by lia.
    cbn[t2] in Hd.
    rewrite Hd.
    rewrite Nat.Div0.add_mod_idemp_l.
    f_equal.
    lia.
Qed.

Lemma mod1 a:
  (a mod 1 = 0)%nat.
Proof.
  epose proof (Nat.mod_upper_bound a 1).
  lia.
Qed.

Notation C := 7%nat.

Ltac le_C a b :=
match a with
| O => idtac
| S ?a0 =>
  match b with
  | O => fail
  | S ?b0 => le_C a0 b0
  end
end.


Lemma t2_S a b: t2 (S a) b = 2^(t2 a b)-1.
Proof. reflexivity. Qed.

Lemma t2_O b: t2 O b = b.
Proof. reflexivity. Qed.

Lemma st2_S a b: st2 (S a) b = st2 a b + t2 (S a) b.
Proof. reflexivity. Qed.

Lemma st2_O b: st2 O b = b.
Proof. reflexivity. Qed.


Ltac rw_mod_1 :=
match goal with
| |- ?G => idtac "rw_mod_1"; idtac G
end;
match goal with
| |- (_ = _) = _ =>
  apply feq2; rw_mod_0
| |- _ mod 1%nat = _ =>
  apply mod1
| |- (t2 ?a ?b) mod ?c = _ =>
  le_C a 7%nat;
  is_nat_const c;
  repeat (rewrite t2_S || rewrite t2_O);
  rw_mod_1
| |- (st2 ?a ?b) mod ?c = _ =>
  le_C a 7%nat;
  is_nat_const c;
  repeat (rewrite st2_S || rewrite st2_O);
  rw_mod_1
| |- (t2 ?a ?b) mod ?c = _ =>
  is_nat_const c;
  etransitivity; [
    apply (t2_mod C);
    [ |shelve];
    intros; cbn[Nat.add];
    repeat (rewrite t2_S || rewrite t2_O);
    rw_mod_1
  | ];
  rw_mod_rec
| |- (st2 ?a ?b) mod ?c = _ =>
  is_nat_const c;
  etransitivity; [
    apply (st2_mod C);
    [ |shelve];
    intros; cbn[Nat.add];
    repeat (rewrite t2_S || rewrite t2_O);
    rw_mod_1
  | ];
  rw_mod_rec
| |- (?a + ?b) mod ?c = _ =>
  is_nat_const c;
  etransitivity; [ apply Nat.Div0.add_mod | ];
  rw_mod_rec
| |- (?a - ?b) mod ?c = _ =>
  is_nat_const c;
  etransitivity; [ apply sub_mod; [ shelve | congruence ] | ];
  rw_mod_rec
| |- (?a * ?b) mod ?c = _ =>
  is_nat_const c;
  etransitivity; [ apply Nat.Div0.mul_mod | ];
  rw_mod_rec
| |- (?a / ?b) mod ?c = _ =>
  idtac "div_mod_comm";
  is_nat_const b;
  is_nat_const c;
  etransitivity; [ eapply div_mod_comm; [ crefl | congruence ] | ];
  rw_mod_rec
| |- (?a ^ ?b) mod ?c = _ =>
  is_nat_const a;
  is_nat_const c;
  (
  (is_nat_const b; idtac "pow_mod_1"; rw_mod_2) +
  ( idtac "pow_mod_2";
    idtac a; idtac b; idtac c;
    etransitivity;
    [ eapply pow_mod;
      [ crefl | | | | | | | | ];
      [ congruence | congruence | | | | | | ];
      [ rw_mod_0 | | | | | ];
      [ rw_mod_0 | | | | ];
      [ rw_mod_0 | | | ];
      [ rw_mod_0 | | ];
      [ shelve | rw_mod_0 ]
    | ];
    rw_mod_rec)
  )
| |- (_ + _ = _) =>
  rw_mod_rec
| |- (_ - _ = _) =>
  rw_mod_rec
| |- (_ * _ = _) =>
  rw_mod_rec
| |- (_ / _ = _) =>
  rw_mod_rec
| |- (_ mod _ = _) =>
  rw_mod_rec
| |- (_ ^ _ = _) =>
  rw_mod_rec
| _ => rw_mod_2
end
with
rw_mod_0 := rw_mod_1
with
rw_mod_rec :=
match goal with
| |- ?G => idtac "rw_mod_rec"; idtac G
end;
etransitivity; [ (apply feq2; rw_mod_0) + reflexivity | ]; rw_mod_2
with
rw_mod_2 :=
match goal with
| |- ?G => idtac "rw_mod_2"; idtac G
end;
etransitivity;
[
match goal with
| |- (_ * 0 = _) =>
  eapply Nat.mul_0_r
| |- (0 * _ = _) =>
  eapply Nat.mul_0_l
| |- (?a * ?b = _) =>
  reflexivity
| |- (?a ^ ?b = _) =>
  reflexivity
| |- ((?a * ?b) mod ?c = _) =>
  no_var a; no_var b; no_var c;
  eapply mul_mod_c; crefl
| |- ((?a ^ ?b) mod ?c = _) =>
  no_var a; no_var b; no_var c;
  eapply pow_mod_c; crefl
| |- (?e = _) =>
  no_var e; crefl
| _ =>
  reflexivity
end
| 
  match goal with
  | |- ?x = _ => idtac "rw_mod_2 ret"; idtac x
  end;
  reflexivity
].

Lemma pow2_gt a:
  a<=2^a-1.
Proof.
  induction a.
  - lia.
  - pose proof (Nat.pow_nonzero 2 a).
    cbn; lia.
Qed.

Lemma t2_ge a b:
  t2 a b >= b.
Proof.
  induction a.
  - cbn; lia.
  - cbn.
    pose proof (pow2_gt (t2 a b)).
    lia.
Qed.

Lemma t2_ge1 a b:
  b >= 1 ->
  t2 a b >= 1.
Proof.
  pose proof (t2_ge a b).
  lia.
Qed.

Ltac R_mod :=
  match goal with
  | |- S1 _ ?a _ _ _ _ -->* _ =>
    eassert (X:_) by (eapply (div_mod' a 3 _); rw_mod_1);
    rewrite X in *;
    clear X
  end.

Ltac rw_mod :=
match goal with
| |- ?e =>
  eassert (e = _) as Hrw by rw_mod_1;
  rewrite Hrw;
  clear Hrw
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
  follow init.
  change 63 with (2^6-1).
  change (S1 3 7) with (S1 3 (1+2*3)).
  follow Rsts1.
  follow Rst1'.
  change (1+2*3) with 7.
  change (2^(3+2)-1) with 31.
  change (2*5+2) with 12.

  epose proof (Rsts1_v2 _ _ _ _) as I.
  eapply evstep_trans.
  1: apply I.
  1: rw_mod; reflexivity.
  clear I.
  follow Rst1'.

  finish.
  }
  apply Rsts2H.
  1: apply Rst1'_WF.
  rw_mod; reflexivity.
  Unshelve.
  all: solve_ge.
  all: repeat
       match goal with
       | |- t2 _ _ >= _ => apply t2_ge1; solve_ge
       end.
  apply Rst1'_WF.
Qed.

End TM62.


Module TM63.

Definition tm := Eval compute in (TM_from_str "1RB---_1LC0RF_1RE0LD_0LC1RB_1RA1RE_1RE0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[1;0;0].
Notation d1 := <[1;1;1].
Notation "l <| r" := (l <{{D}} [0] *> r) (at level 30).
Notation "l |> r" := (l <* <[1] {{B}}> r) (at level 30).

Definition LC l len n := BinDec d0 d1 len n l.

Lemma LC_Inc l len n r:
  S n<2^len ->
  LC l len (S n) <| r -->*
  LC l len n |> r.
Proof.
  intros H.
  eapply progress_evstep.
  apply LBinDec_spec; try assumption.
  es.
Qed.

Opaque BinDec.

Definition RC m := [1;1;1;0;0] *> [1;1;1]^^m *> 0inf.

Definition S0 l len1 a1 b :=
  LC l len1 a1 <| RC (1+b).

Lemma Inc0 l len n b:
  S n<2^len ->
  S0 l len (S n) b -->*
  S0 l len n (1+b).
Proof.
  unfold S0,LC.
  intros.
  follow LC_Inc.
  es.
Qed.

Lemma Incs0 l len n b:
  n<2^len ->
  S0 l len n b -->*
  S0 l len 0 (n+b).
Proof.
  gen b.
  induction n; intros.
  1: finish.
  follow Inc0.
  follow IHn.
  1: lia.
  finish.
Qed.

Notation lh := (0inf <* <[1;1;1;0;1;1]).
Notation m2 := <[1;0;1;1].
Notation m1 := <[1;0;1].
Notation m0 := <[1;0].

Definition S1 len0 a0 m len1 a1 b :=
  S0 (LC lh len0 a0 <* d0 <* m) len1 a1 b.

Lemma Rst2 len0 a0 a b:
  S a0 < 2^len0 ->
  S1 len0 (S a0) m2 a 0 b -->*
  S1 len0 a0 m1 (a+b+2) 0 (2^b-1).
Proof.
  intros Ha0.
  mid (S1 len0 a0 m1 (a+1+1+b) ((0*2*2+1)*2^b-1) 0).
  - unfold S1,S0,LC.
    rw_Bin.
    2: solve_pow2_lt.
    es; er.
    follow LC_Inc.
    es.
  - mid (S1 len0 a0 m1 (a+1+1+b) 0 ((0*2*2+1)*2^b-1+0)).
    1: unfold S1; follow Incs0.
    1: solve_pow2_lt.
    1: finish.
    finish.
Qed.

Lemma Rst1 len0 a0 a b:
  S a0 < 2^len0 ->
  S1 len0 (S a0) m1 a 0 b -->*
  S1 len0 a0 m0 (a+b+2) 0 (2^b-1).
Proof.
  intros Ha0.
  mid (S1 len0 a0 m0 (a+1+1+b) ((0*2*2+1)*2^b-1) 0).
  - unfold S1,S0,LC.
    rw_Bin.
    2: solve_pow2_lt.
    es; er.
    follow LC_Inc.
    es.
  - mid (S1 len0 a0 m0 (a+1+1+b) 0 ((0*2*2+1)*2^b-1+0)).
    1: unfold S1; follow Incs0.
    1: solve_pow2_lt.
    1: finish.
    finish.
Qed.

Lemma Rst0 len0 a0 a b:
  S a0 < 2^len0 ->
  S1 len0 (S a0) m0 a 0 b -->*
  S1 len0 a0 m2 (a+b+1) 0 (2^b-1).
Proof.
  intros Ha0.
  mid (S1 len0 a0 m2 (a+1+b) ((0*2+1)*2^b-1) 0).
  - unfold S1,S0,LC.
    rw_Bin.
    2: solve_pow2_lt.
    es; er.
    follow LC_Inc.
    es.
  - mid (S1 len0 a0 m2 (a+1+b) 0 ((0*2+1)*2^b-1+0)).
    1: unfold S1; follow Incs0.
    1: solve_pow2_lt.
    1: finish.
    finish.
Qed.

Fixpoint t2 a b :=
match a with
| O => b
| S a0 => 2^(t2 a0 b)-1
end.

Fixpoint st2 a b :=
match a with
| O => O
| S a0 => st2 a0 b
end + t2 a b.

Lemma Rsts n len0 a0 b:
  n*3+a0<2^len0 ->
  S1 len0 (n*3+a0) m2 b 0 (2^b-1) -->*
  S1 len0 a0 m2 (st2 (n*3) b + n*5) 0 (t2 (1+n*3) b).
Proof.
  gen a0.
  induction n; intros.
  - cbn; finish.
  - specialize (IHn (3+a0)).
    follow IHn.
    1: lia.
    cbn.
    follow Rst2.
    1: lia.
    follow Rst1.
    1: lia.
    follow Rst0.
    1: lia.
    finish.
Qed.

Lemma Rsts1 n len0 b:
  1+n*3<2^len0 ->
  S1 len0 (1+n*3) m2 b 0 (2^b-1) -->*
  S1 len0 0 m1 (st2 (1+n*3) b + (n*5+2)) 0 (t2 (2+n*3) b).
Proof.
  intros.
  rewrite Nat.add_comm.
  follow Rsts.
  1: lia.
  follow Rst2.
  1: lia.
  rewrite (Nat.add_comm (n*3) 1).
  cbn.
  finish.
Qed.

Lemma Rsts1_v2 n len0 b:
  n<2^len0 ->
  n mod 3 = 1%nat ->
  S1 len0 n m2 b 0 (2^b-1) -->*
  S1 len0 0 m1 (st2 n b + (n/3*5+2)) 0 (t2 (n+1) b).
Proof.
  intros.
  epose proof (div_mod' n 3 1 H0) as Hn.
  rewrite Hn.
  follow Rsts1.
  1: lia.
  finish.
Qed.

Lemma Rsts2 n len0 b:
  2+n*3<2^len0 ->
  S1 len0 (2+n*3) m2 b 0 (2^b-1) -->*
  S1 len0 0 m0 (st2 (2+n*3) b + (n*5+4)) 0 (t2 (3+n*3) b).
Proof.
  intros.
  rewrite Nat.add_comm.
  follow Rsts.
  1: lia.
  follow Rst2.
  1: lia.
  follow Rst1.
  1: lia.
  rewrite (Nat.add_comm (n*3) 2).
  cbn.
  finish.
Qed.

Lemma Rst1' a0 a b:
  S1 a0 0 m1 a 0 b -->*
  S1 (a0+1+1+a) ((((2^a0-1)*2+1)*2+1)*2^a-1) m2 b 0 (2^b-1).
Proof.
  mid (S1 (a0+1+1+a) ((((2^a0-1)*2+1)*2+1)*2^a-1) m2 b (2^b-1) 0).
  - unfold S1,S0,LC,RC.
    rw_Bin.
    all: try solve_pow2_lt.
    es.
  - mid (S1 (a0+1+1+a) ((((2^a0-1)*2+1)*2+1)*2^a-1) m2 b 0 (2^b-1+0)).
    1: unfold S1; follow Incs0.
    1: solve_pow2_lt.
    1: finish.
    finish.
Qed.

Lemma Rst1'_WF a0 a:
  ((((2^a0-1)*2+1)*2+1)*2^a-1) < 2^(a0+1+1+a).
Proof.
  solve_pow2_lt.
Qed.

Lemma Rst0' a0 a b:
  halts tm (S1 a0 0 m0 a 0 b).
Proof.
  unfold S1,S0,LC,RC.
  rw_Bin.
  all: try solve_pow2_lt.
  solve_halt.
Qed.

Lemma Rsts2H n len0 b:
  n<2^len0 ->
  n mod 3 = 2 ->
  halts tm (S1 len0 n m2 b 0 (2^b-1)).
Proof.
  intros.
  epose proof (div_mod' _ _ _ H0) as Hn.
  rewrite Hn.
  eapply halts_evstep.
  2: apply Rsts2.
  2: lia.
  apply Rst0'.
Qed.

Transparent BinDec.
Lemma init: c0-->* S1 3 7 m2 6 0 63.
Proof.
  unfold S1,S0,LC; cbn.
  solve_init.
Qed.

Lemma t2_mod C a b c d:
  (forall x, t2 (C+x) b mod c = d) ->
  a>=C ->
  t2 a b mod c = d.
Proof.
  intros.
  specialize (H (a-C)).
  applys_eq H.
  repeat (lia || f_equal).
Qed.

Lemma st2_mod C a b c d:
  (forall x, t2 (C+x) b mod c = d) ->
  a>=C ->
  st2 a b mod c = (((st2 C b) mod c) + ((d*(a-C)) mod c)) mod c.
Proof.
  intros Hd Ha.
  rewrite <-Nat.Div0.add_mod.
  replace (st2 a) with (st2 (a-C+C)) by (f_equal; lia).
  induction (a-C).
  - cbn.
    f_equal.
    lia.
  - cbn.
    rewrite Nat.Div0.add_mod.
    rewrite IHn.
    specialize (Hd (S n)).
    replace (C+S n) with (S(n+C)) in Hd by lia.
    cbn[t2] in Hd.
    rewrite Hd.
    rewrite Nat.Div0.add_mod_idemp_l.
    f_equal.
    lia.
Qed.

Lemma mod1 a:
  (a mod 1 = 0)%nat.
Proof.
  epose proof (Nat.mod_upper_bound a 1).
  lia.
Qed.

Notation C := 7%nat.

Ltac le_C a b :=
match a with
| O => idtac
| S ?a0 =>
  match b with
  | O => fail
  | S ?b0 => le_C a0 b0
  end
end.


Lemma t2_S a b: t2 (S a) b = 2^(t2 a b)-1.
Proof. reflexivity. Qed.

Lemma t2_O b: t2 O b = b.
Proof. reflexivity. Qed.

Lemma st2_S a b: st2 (S a) b = st2 a b + t2 (S a) b.
Proof. reflexivity. Qed.

Lemma st2_O b: st2 O b = b.
Proof. reflexivity. Qed.


Ltac rw_mod_1 :=
match goal with
| |- ?G => idtac "rw_mod_1"; idtac G
end;
match goal with
| |- (_ = _) = _ =>
  apply feq2; rw_mod_0
| |- _ mod 1%nat = _ =>
  apply mod1
| |- (t2 ?a ?b) mod ?c = _ =>
  le_C a 7%nat;
  is_nat_const c;
  repeat (rewrite t2_S || rewrite t2_O);
  rw_mod_1
| |- (st2 ?a ?b) mod ?c = _ =>
  le_C a 7%nat;
  is_nat_const c;
  repeat (rewrite st2_S || rewrite st2_O);
  rw_mod_1
| |- (t2 ?a ?b) mod ?c = _ =>
  is_nat_const c;
  etransitivity; [
    apply (t2_mod C);
    [ |shelve];
    intros; cbn[Nat.add];
    repeat (rewrite t2_S || rewrite t2_O);
    rw_mod_1
  | ];
  rw_mod_rec
| |- (st2 ?a ?b) mod ?c = _ =>
  is_nat_const c;
  etransitivity; [
    apply (st2_mod C);
    [ |shelve];
    intros; cbn[Nat.add];
    repeat (rewrite t2_S || rewrite t2_O);
    rw_mod_1
  | ];
  rw_mod_rec
| |- (?a + ?b) mod ?c = _ =>
  is_nat_const c;
  etransitivity; [ apply Nat.Div0.add_mod | ];
  rw_mod_rec
| |- (?a - ?b) mod ?c = _ =>
  is_nat_const c;
  etransitivity; [ apply sub_mod; [ shelve | congruence ] | ];
  rw_mod_rec
| |- (?a * ?b) mod ?c = _ =>
  is_nat_const c;
  etransitivity; [ apply Nat.Div0.mul_mod | ];
  rw_mod_rec
| |- (?a / ?b) mod ?c = _ =>
  idtac "div_mod_comm";
  is_nat_const b;
  is_nat_const c;
  etransitivity; [ eapply div_mod_comm; [ crefl | congruence ] | ];
  rw_mod_rec
| |- (?a ^ ?b) mod ?c = _ =>
  is_nat_const a;
  is_nat_const c;
  (
  (is_nat_const b; idtac "pow_mod_1"; rw_mod_2) +
  ( idtac "pow_mod_2";
    idtac a; idtac b; idtac c;
    etransitivity;
    [ eapply pow_mod;
      [ crefl | | | | | | | | ];
      [ congruence | congruence | | | | | | ];
      [ rw_mod_0 | | | | | ];
      [ rw_mod_0 | | | | ];
      [ rw_mod_0 | | | ];
      [ rw_mod_0 | | ];
      [ shelve | rw_mod_0 ]
    | ];
    rw_mod_rec)
  )
| |- (_ + _ = _) =>
  rw_mod_rec
| |- (_ - _ = _) =>
  rw_mod_rec
| |- (_ * _ = _) =>
  rw_mod_rec
| |- (_ / _ = _) =>
  rw_mod_rec
| |- (_ mod _ = _) =>
  rw_mod_rec
| |- (_ ^ _ = _) =>
  rw_mod_rec
| _ => rw_mod_2
end
with
rw_mod_0 := rw_mod_1
with
rw_mod_rec :=
match goal with
| |- ?G => idtac "rw_mod_rec"; idtac G
end;
etransitivity; [ (apply feq2; rw_mod_0) + reflexivity | ]; rw_mod_2
with
rw_mod_2 :=
match goal with
| |- ?G => idtac "rw_mod_2"; idtac G
end;
etransitivity;
[
match goal with
| |- (_ * 0 = _) =>
  eapply Nat.mul_0_r
| |- (0 * _ = _) =>
  eapply Nat.mul_0_l
| |- (?a * ?b = _) =>
  reflexivity
| |- (?a ^ ?b = _) =>
  reflexivity
| |- ((?a * ?b) mod ?c = _) =>
  no_var a; no_var b; no_var c;
  eapply mul_mod_c; crefl
| |- ((?a ^ ?b) mod ?c = _) =>
  no_var a; no_var b; no_var c;
  eapply pow_mod_c; crefl
| |- (?e = _) =>
  no_var e; crefl
| _ =>
  reflexivity
end
| 
  match goal with
  | |- ?x = _ => idtac "rw_mod_2 ret"; idtac x
  end;
  reflexivity
].

Lemma pow2_gt a:
  a<=2^a-1.
Proof.
  induction a.
  - lia.
  - pose proof (Nat.pow_nonzero 2 a).
    cbn; lia.
Qed.

Lemma t2_ge a b:
  t2 a b >= b.
Proof.
  induction a.
  - cbn; lia.
  - cbn.
    pose proof (pow2_gt (t2 a b)).
    lia.
Qed.

Lemma t2_ge1 a b:
  b >= 1 ->
  t2 a b >= 1.
Proof.
  pose proof (t2_ge a b).
  lia.
Qed.

Ltac R_mod :=
  match goal with
  | |- S1 _ ?a _ _ _ _ -->* _ =>
    eassert (X:_) by (eapply (div_mod' a 3 _); rw_mod_1);
    rewrite X in *;
    clear X
  end.

Ltac rw_mod :=
match goal with
| |- ?e =>
  eassert (e = _) as Hrw by rw_mod_1;
  rewrite Hrw;
  clear Hrw
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
  follow init.
  change 63 with (2^6-1).
  change (S1 3 7) with (S1 3 (1+2*3)).
  follow Rsts1.
  follow Rst1'.
  change (1+2*3) with 7.
  change (2^(3+2)-1) with 31.
  change (2*5+2) with 12.

  epose proof (Rsts1_v2 _ _ _ _) as I.
  eapply evstep_trans.
  1: apply I.
  1: rw_mod; reflexivity.
  clear I.
  follow Rst1'.

  finish.
  }
  apply Rsts2H.
  1: apply Rst1'_WF.
  rw_mod; reflexivity.
  Unshelve.
  all: solve_ge.
  all: repeat
       match goal with
       | |- t2 _ _ >= _ => apply t2_ge1; solve_ge
       end.
  apply Rst1'_WF.
Qed.

End TM63.


Module TM64.

Definition tm := Eval compute in (TM_from_str "1LB0RE_1RC1LE_1RD1RC_1LD0RA_1LF1RD_0LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[0;0;1].
Notation d1 := <[1;1;1].
Notation "l <| r" := (l <{{A}} [0] *> r) (at level 30).
Notation "l |> r" := (l <* <[0] {{A}}> r) (at level 30).

Definition LC l len n := BinDec d0 d1 len n l.

Lemma LC_Inc l len n r:
  S n<2^len ->
  LC l len (S n) <| r -->*
  LC l len n |> r.
Proof.
  intros H.
  eapply progress_evstep.
  apply LBinDec_spec; try assumption.
  es.
Qed.

Definition S0 l len n b :=
  LC (l <* <[0;0]) len n <| [1;1;1;0] *> [1]^^(1+b) *> 0inf.

Opaque BinDec.

Lemma Inc0 l len n b:
  S n<2^len ->
  S0 l len (S n) b -->*
  S0 l len n (3+b).
Proof.
  unfold S0,LC.
  intros.
  follow LC_Inc.
  es.
Qed.

Lemma Incs0 l len n b:
  n<2^len ->
  S0 l len n b -->*
  S0 l len 0 (n*3+b).
Proof.
  gen b.
  induction n; intros.
  1: finish.
  follow Inc0.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Ov1 l len b:
  S0 l (len) 0 (1+b*3) -->+
  S0 (l<*d1<*d0^^len) b (2^b-1) 2.
Proof.
  unfold S0,LC.
  rw_Bin.
  es.
Qed.

Lemma Ov2 l len b:
  S0 l (len) 0 (2+b*3) -->+
  S0 (l<*d1<*d0^^len) b (2^b-1) 0.
Proof.
  unfold S0,LC.
  rw_Bin.
  es.
Qed.

Lemma Ov1Incs l len b:
  S0 l (len) 0 (1+b*3) -->+
  S0 (l<*d1<*d0^^len) b 0 (2+(2^b-1)*3).
Proof.
  follow10 Ov1.
  follow Incs0.
  1: solve_pow2_lt.
  finish.
Qed.

Lemma Ov2Incs l len b:
  S0 l (len) 0 (2+b*3) -->+
  S0 (l<*d1<*d0^^len) b 0 (0+(2^b-1)*3).
Proof.
  follow10 Ov2.
  follow Incs0.
  1: solve_pow2_lt.
  finish.
Qed.

Lemma Ov0 l len b:
  b>=1 ->
  halts tm (S0 l len 0 (0+b*3)).
Proof.
  intros Hb.
  destruct b.
  1: lia.
  unfold S0,LC.
  rw_Bin.
  solve_halt.
Qed.

Transparent BinDec.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
    mid (S0 (0inf<*d1) 3 0 (1+9*3)).
    1: unfold S0,LC; cbn; solve_init.
    follow100 Ov1Incs.
    follow100 Ov2Incs.
    finish.
  }
  eapply Ov0.
  solve_ge.
Qed.

End TM64.


Module TM69.

Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC0RA_1RE0LD_1LC1RB_---1RF_1RB1RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[1;0;0].
Notation d1 := <[1;1;1].
Notation w := <[1;0].
Notation d11 := (w <+ d1 <+ d1).
Notation d01 := (w <+ d0 <+ d1).
Notation d10 := (w <+ d1 <+ d0).
Notation lh := (0inf <* <[1;1]).
Notation "l <| r" := (l <{{D}} [0] *> r) (at level 30).
Notation "l |> r" := (l <* <[1] {{B}}> r) (at level 30).

Definition RC m := [1;0]^^m *> 0inf.

Definition S1 l a b :=
  l <* d10^^a <* <[1;0; 1;0;0; 1;1;1;1;0;1;1;1;1;1] <* w^^(1+b) |> 0inf.

Lemma S1_Inc l a b:
  S1 l a (3+b) -->*
  S1 l (1+a) (b).
Proof.
  es.
Qed.

Lemma S1_Incs n l a b:
  S1 l a (b+n*3) -->*
  S1 l (n+a) b.
Proof.
  rewrite Nat.add_comm.
  gen l a b.
  ind n S1_Inc.
Qed.

Lemma Rst2 l a:
  S1 l a 2 -->*
  l<* d10^^(a+2) <* d01 <| RC 2.
Proof.
  unfold S1,RC.
  es.
Qed.

Lemma Rst0 l a:
  S1 l a 0 -->*
  l<* d10^^(a+2) <* w <* d1 <| RC 2.
Proof.
  unfold S1,RC.
  es.
Qed.

Lemma Rst1 l a:
  halts tm (S1 l a 1).
Proof.
  unfold S1,RC.
  solve_halt.
Qed.

Transparent BinDec.
Lemma init: c0 -->* lh <* d1^^4 <* d11^^2 <| RC (216).
Proof.
  unfold RC; cbn.
  solve_init.
Qed.

Lemma Ov_1 a b c:
  lh <* d1^^a <* d11^^(S b) <| RC (c+7) -->*
  S1 (lh<*d0^^a<*d1<*d0<*d1<*d01^^b) 0 c.
Proof.
  unfold RC.
  execute_with_shift_rule'.
Qed.

Notation hL := (D,[0]).
Notation hR := (B,[1]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].
Definition tm' := flip tm.

Lemma RIncs n m:
  sideRLs tm (hRL^^n) (RC m) (RC (n+m)).
Proof.
  unfold RC.
  induction n.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  simpl_tape; simpl_rotate.
  solve_sideRLs.
Qed.

Lemma Incs [l l' n m]:
  sideRLs tm' (hLR^^n) l l' ->
  l <| RC m -->*
  l' <| RC (n+m).
Proof.
  intros HL.
  apply (sideRLs_concat_1L (RIncs _ _) HL).
Qed.

Lemma segRLs_addmul'' tm a x b h w1 w2:
  segRLs tm (h^^b) [] w1 w2 ->
  segRLs tm (h^^a) h w2 w2 ->
  segRLs tm (h^^(x*a+b)) (h^^x) w1 w2.
Proof.
  epose proof (segRLs_addmul tm a x b O _ _ _) as H.
  rewrite Nat.add_0_r in H.
  apply H.
Qed.

Ltac solve_v1 :=
  intros H;
  eapply segRLs_sideRLs_concat; [|apply H];
  apply segRLs_addmul'';
  solve_segRLs.

Lemma sideRLs_d01 l l' n:
  sideRLs tm' (hLR^^n) l l' ->
  sideRLs tm' (hLR^^(n*4+2)) (l<*d01) (l'<*d11).
Proof.
  solve_v1.
Qed.

Lemma sideRLs_d10 l l' n:
  sideRLs tm' (hLR^^n) l l' ->
  sideRLs tm' (hLR^^(n*4+1)) (l<*d10) (l'<*d11).
Proof.
  solve_v1.
Qed.

Lemma sideRLs_d1 l l' n:
  sideRLs tm' (hLR^^n) l l' ->
  sideRLs tm' (hLR^^(n*2+0)) (l<*d1) (l'<*d1).
Proof.
  solve_v1.
Qed.

Lemma sideRLs_d0 l l' n:
  sideRLs tm' (hLR^^n) l l' ->
  sideRLs tm' (hLR^^(n*2+1)) (l<*d0) (l'<*d1).
Proof.
  solve_v1.
Qed.

Lemma sideRLs_d0s l l' n k:
  sideRLs tm' (hLR^^n) l l' ->
  sideRLs tm' (hLR^^((n+1)*2^k-1)) (l<*d0^^k) (l'<*d1^^k).
Proof.
  intros.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  eapply BC.IncsOvs.
  1: solve_seg.
  1: solve_seg.
  1: solve_seg.
Qed.

Lemma pow4div3_spec k:
  (4^(S k))/3 = (4^k)/3*4+1.
Proof.
  cbn[Nat.pow].
  pose proof (Nat.pow_nonzero 4 k).
  pose proof (pow4_mod3 k).
  replace (4*4^k) with (4^k*3+4^k) by lia.
  rewrite Nat.div_add_l by lia.
  pose proof (Nat.div_mod (4^k) 3).
  lia.
Qed.

Lemma pow4mul2div3_spec k:
  (4^(S k))*2/3 = (4^k)*2/3*4+2.
Proof.
  cbn[Nat.pow].
  pose proof (Nat.pow_nonzero 4 k).
  pose proof (pow4_mod3 k).
  replace (4*4^k*2) with (4^k*2*3+4^k*2) by lia.
  rewrite Nat.div_add_l by lia.
  pose proof (Nat.div_mod (4^k*2) 3).
  assert (4^k*2 mod 3 = 2). {
    rewrite Nat.Div0.mul_mod.
    rewrite H0.
    reflexivity.
  }
  lia.
Qed.

Lemma sideRLs_d01s l l' n k:
  sideRLs tm' (hLR^^n) l l' ->
  sideRLs tm' (hLR^^((n*3+2)*4^k/3)) (l<*d01^^k) (l'<*d11^^k).
Proof.
  replace ((n*3+2)*4^k) with (n*4^k*3+4^k*2) by lia.
  intros H.
  induction k.
  - change (4^0) with 1%nat.
    rewrite Nat.mul_1_r.
    rewrite Nat.div_add_l by lia.
    change (1*2/3) with O.
    rewrite Nat.add_0_r.
    apply H.
  - cbn[Nat.pow].
    cbn[lpow].
    rewrite (Str_app_assoc d01).
    rewrite (Str_app_assoc d11).
    eapply segRLs_sideRLs_concat.
    2: apply IHk.
    do 2 rewrite Nat.div_add_l by lia.
    pose proof (pow4mul2div3_spec k) as Hk.
    cbn[Nat.pow] in Hk.
    rewrite Hk.
    match goal with
    | |- segRLs _ (_^^?a) (_^^?b) _ _ => replace a with (b*4+2) by lia
    end.
    apply segRLs_addmul''; solve_segRLs.
Qed.

Lemma sideRLs_d10s l l' n k:
  sideRLs tm' (hLR^^n) l l' ->
  sideRLs tm' (hLR^^((n*3+1)*4^k/3)) (l<*d10^^k) (l'<*d11^^k).
Proof.
  replace ((n*3+1)*4^k) with (n*4^k*3+4^k) by lia.
  intros H.
  induction k.
  - change (4^0) with 1%nat.
    rewrite Nat.mul_1_r.
    rewrite Nat.div_add_l by lia.
    change (1/3) with O.
    rewrite Nat.add_0_r.
    apply H.
  - cbn[Nat.pow].
    cbn[lpow].
    rewrite (Str_app_assoc d10).
    rewrite (Str_app_assoc d11).
    eapply segRLs_sideRLs_concat.
    2: apply IHk.
    do 2 rewrite Nat.div_add_l by lia.
    pose proof (pow4div3_spec k) as Hk.
    cbn[Nat.pow] in Hk.
    rewrite Hk.
    match goal with
    | |- segRLs _ (_^^?a) (_^^?b) _ _ => replace a with (b*4+1) by lia
    end.
    apply segRLs_addmul''; solve_segRLs.
Qed.

Lemma sideRLs_lh:
  sideRLs tm' (hLR^^0) lh lh.
Proof.
  constructor.
Qed.

Lemma sideRLs_w l l' n:
  sideRLs tm' (hLR^^n) l l' ->
  sideRLs tm' (hLR^^n) (l<*w) (l'<*w).
Proof.
  intros H.
  replace n with (n*1+0) by lia.
  gen H.
  solve_v1.
Qed.

Ltac solve_v2 :=
  repeat
  match goal with
  | |- sideRLs _ _ (w*>_) _ => apply sideRLs_w
  | |- sideRLs _ _ (d1*>_) _ => apply sideRLs_d1
  | |- sideRLs _ _ (d0*>_) _ => apply sideRLs_d0
  | |- sideRLs _ _ (d10*>_) _ => apply sideRLs_d10
  | |- sideRLs _ _ (d01*>_) _ => apply sideRLs_d01
  | |- sideRLs _ _ (d0^^_*>_) _ => apply sideRLs_d0s
  | |- sideRLs _ _ (d01^^_*>_) _ => apply sideRLs_d01s
  | |- sideRLs _ _ (d10^^_*>_) _ => apply sideRLs_d10s
  | |- sideRLs _ _ (lh) _ => apply sideRLs_lh
  end.

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

Lemma ge_le a b:
  a>=b -> b<=a.
Proof. lia. Qed.

Ltac R_sub :=
match goal with
| |- _ <| RC ?m -->* _ => replace m with (m-7+7) by (apply Nat.sub_add; apply ge_le; shelve)
end.

Ltac R_mod :=
match goal with
| |- S1 _ _ ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma Ov_2 {a b c}:
  b>=1 ->
  lh <* d1^^a <* d11^^b <* w <* d1 <| RC (c+7) -->*
  S1 (lh<*d0^^a<*d1<*d0<*d1<*d01^^(b-1)<*w<*d1) 0 c.
Proof.
  intros Hb.
  destruct b as [|b].
  1: lia.
  replace (S b-1) with b by lia.
  unfold RC.
  es.
Qed.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
  follow init.
  change 216 with (2+69*3+7).
  follow Ov_1.
  follow S1_Incs.
  follow Rst2.
  rewrite Nat.add_0_r.
  follow Incs.
  1: solve_v2.
  rw_lpow_add.
  change (69+2+1+1) with 73.
  change (4+1+1+1) with 7.
  change (((0+1)*2^4-1)*2+0) with 30.
  R_sub.
  follow Ov_1.
  R_mod.
  follow S1_Incs.
  follow Rst0.
  rewrite Nat.add_0_r.
  follow Incs.
  1: solve_v2.
  rw_lpow_add.
  R_sub.
  epose proof (Ov_2 _) as I1.
  follow I1. clear I1.
  R_mod.
  follow S1_Incs.
  finish.
  }
  eapply Rst1.
  Unshelve.
  all: solve_ge.
Qed.

End TM69.


Module TM70.

Definition tm := Eval compute in (TM_from_str "1LB1RE_1RC0LA_---1RD_1RE1RB_1LB0RF_1RE0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[1;0;0].
Notation d1 := <[1;1;1].
Notation w := <[1;0].
Notation d11 := (w <+ d1 <+ d1).
Notation d01 := (w <+ d0 <+ d1).
Notation d10 := (w <+ d1 <+ d0).
Notation lh := (0inf <* <[1;1]).
Notation "l <| r" := (l <{{A}} [0] *> r) (at level 30).
Notation "l |> r" := (l <* <[1] {{E}}> r) (at level 30).

Definition RC m := [1;0]^^m *> 0inf.

Definition S1 l a b :=
  l <* d10^^a <* <[1;0; 1;0;0; 1;1;1;1;0;1;1;1;1;1] <* w^^(1+b) |> 0inf.

Lemma S1_Inc l a b:
  S1 l a (3+b) -->*
  S1 l (1+a) (b).
Proof.
  es.
Qed.

Lemma S1_Incs n l a b:
  S1 l a (b+n*3) -->*
  S1 l (n+a) b.
Proof.
  rewrite Nat.add_comm.
  gen l a b.
  ind n S1_Inc.
Qed.

Lemma Rst2 l a:
  S1 l a 2 -->*
  l<* d10^^(a+2) <* d01 <| RC 2.
Proof.
  unfold S1,RC.
  es.
Qed.

Lemma Rst0 l a:
  S1 l a 0 -->*
  l<* d10^^(a+2) <* w <* d1 <| RC 2.
Proof.
  unfold S1,RC.
  es.
Qed.

Lemma Rst1 l a:
  halts tm (S1 l a 1).
Proof.
  unfold S1,RC.
  solve_halt.
Qed.

Transparent BinDec.
Lemma init: c0 -->* lh <* d1^^4 <* d11^^1 <* w <* d1 <| RC (100).
Proof.
  unfold RC; cbn.
  solve_init.
Qed.

Notation hL := (A,[0]).
Notation hR := (E,[1]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].
Definition tm' := flip tm.

Lemma RIncs n m:
  sideRLs tm (hRL^^n) (RC m) (RC (n+m)).
Proof.
  unfold RC.
  induction n.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  simpl_tape; simpl_rotate.
  solve_sideRLs.
Qed.

Lemma Incs [l l' n m]:
  sideRLs tm' (hLR^^n) l l' ->
  l <| RC m -->*
  l' <| RC (n+m).
Proof.
  intros HL.
  apply (sideRLs_concat_1L (RIncs _ _) HL).
Qed.

Lemma segRLs_addmul'' tm a x b h w1 w2:
  segRLs tm (h^^b) [] w1 w2 ->
  segRLs tm (h^^a) h w2 w2 ->
  segRLs tm (h^^(x*a+b)) (h^^x) w1 w2.
Proof.
  epose proof (segRLs_addmul tm a x b O _ _ _) as H.
  rewrite Nat.add_0_r in H.
  apply H.
Qed.

Ltac solve_v1 :=
  intros H;
  eapply segRLs_sideRLs_concat; [|apply H];
  apply segRLs_addmul'';
  solve_segRLs.

Lemma sideRLs_d01 l l' n:
  sideRLs tm' (hLR^^n) l l' ->
  sideRLs tm' (hLR^^(n*4+2)) (l<*d01) (l'<*d11).
Proof.
  solve_v1.
Qed.

Lemma sideRLs_d10 l l' n:
  sideRLs tm' (hLR^^n) l l' ->
  sideRLs tm' (hLR^^(n*4+1)) (l<*d10) (l'<*d11).
Proof.
  solve_v1.
Qed.

Lemma sideRLs_d1 l l' n:
  sideRLs tm' (hLR^^n) l l' ->
  sideRLs tm' (hLR^^(n*2+0)) (l<*d1) (l'<*d1).
Proof.
  solve_v1.
Qed.

Lemma sideRLs_d0 l l' n:
  sideRLs tm' (hLR^^n) l l' ->
  sideRLs tm' (hLR^^(n*2+1)) (l<*d0) (l'<*d1).
Proof.
  solve_v1.
Qed.

Lemma sideRLs_d0s l l' n k:
  sideRLs tm' (hLR^^n) l l' ->
  sideRLs tm' (hLR^^((n+1)*2^k-1)) (l<*d0^^k) (l'<*d1^^k).
Proof.
  intros.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  eapply BC.IncsOvs.
  1: solve_seg.
  1: solve_seg.
  1: solve_seg.
Qed.

Lemma pow4div3_spec k:
  (4^(S k))/3 = (4^k)/3*4+1.
Proof.
  cbn[Nat.pow].
  pose proof (Nat.pow_nonzero 4 k).
  pose proof (pow4_mod3 k).
  replace (4*4^k) with (4^k*3+4^k) by lia.
  rewrite Nat.div_add_l by lia.
  pose proof (Nat.div_mod (4^k) 3).
  lia.
Qed.

Lemma pow4mul2div3_spec k:
  (4^(S k))*2/3 = (4^k)*2/3*4+2.
Proof.
  cbn[Nat.pow].
  pose proof (Nat.pow_nonzero 4 k).
  pose proof (pow4_mod3 k).
  replace (4*4^k*2) with (4^k*2*3+4^k*2) by lia.
  rewrite Nat.div_add_l by lia.
  pose proof (Nat.div_mod (4^k*2) 3).
  assert (4^k*2 mod 3 = 2). {
    rewrite Nat.Div0.mul_mod.
    rewrite H0.
    reflexivity.
  }
  lia.
Qed.

Lemma sideRLs_d01s l l' n k:
  sideRLs tm' (hLR^^n) l l' ->
  sideRLs tm' (hLR^^((n*3+2)*4^k/3)) (l<*d01^^k) (l'<*d11^^k).
Proof.
  replace ((n*3+2)*4^k) with (n*4^k*3+4^k*2) by lia.
  intros H.
  induction k.
  - change (4^0) with 1%nat.
    rewrite Nat.mul_1_r.
    rewrite Nat.div_add_l by lia.
    change (1*2/3) with O.
    rewrite Nat.add_0_r.
    apply H.
  - cbn[Nat.pow].
    cbn[lpow].
    rewrite (Str_app_assoc d01).
    rewrite (Str_app_assoc d11).
    eapply segRLs_sideRLs_concat.
    2: apply IHk.
    do 2 rewrite Nat.div_add_l by lia.
    pose proof (pow4mul2div3_spec k) as Hk.
    cbn[Nat.pow] in Hk.
    rewrite Hk.
    match goal with
    | |- segRLs _ (_^^?a) (_^^?b) _ _ => replace a with (b*4+2) by lia
    end.
    apply segRLs_addmul''; solve_segRLs.
Qed.

Lemma sideRLs_d10s l l' n k:
  sideRLs tm' (hLR^^n) l l' ->
  sideRLs tm' (hLR^^((n*3+1)*4^k/3)) (l<*d10^^k) (l'<*d11^^k).
Proof.
  replace ((n*3+1)*4^k) with (n*4^k*3+4^k) by lia.
  intros H.
  induction k.
  - change (4^0) with 1%nat.
    rewrite Nat.mul_1_r.
    rewrite Nat.div_add_l by lia.
    change (1/3) with O.
    rewrite Nat.add_0_r.
    apply H.
  - cbn[Nat.pow].
    cbn[lpow].
    rewrite (Str_app_assoc d10).
    rewrite (Str_app_assoc d11).
    eapply segRLs_sideRLs_concat.
    2: apply IHk.
    do 2 rewrite Nat.div_add_l by lia.
    pose proof (pow4div3_spec k) as Hk.
    cbn[Nat.pow] in Hk.
    rewrite Hk.
    match goal with
    | |- segRLs _ (_^^?a) (_^^?b) _ _ => replace a with (b*4+1) by lia
    end.
    apply segRLs_addmul''; solve_segRLs.
Qed.

Lemma sideRLs_lh:
  sideRLs tm' (hLR^^0) lh lh.
Proof.
  constructor.
Qed.

Lemma sideRLs_w l l' n:
  sideRLs tm' (hLR^^n) l l' ->
  sideRLs tm' (hLR^^n) (l<*w) (l'<*w).
Proof.
  intros H.
  replace n with (n*1+0) by lia.
  gen H.
  solve_v1.
Qed.

Ltac solve_v2 :=
  repeat
  match goal with
  | |- sideRLs _ _ (w*>_) _ => apply sideRLs_w
  | |- sideRLs _ _ (d1*>_) _ => apply sideRLs_d1
  | |- sideRLs _ _ (d0*>_) _ => apply sideRLs_d0
  | |- sideRLs _ _ (d10*>_) _ => apply sideRLs_d10
  | |- sideRLs _ _ (d01*>_) _ => apply sideRLs_d01
  | |- sideRLs _ _ (d0^^_*>_) _ => apply sideRLs_d0s
  | |- sideRLs _ _ (d01^^_*>_) _ => apply sideRLs_d01s
  | |- sideRLs _ _ (d10^^_*>_) _ => apply sideRLs_d10s
  | |- sideRLs _ _ (lh) _ => apply sideRLs_lh
  end.

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

Lemma ge_le a b:
  a>=b -> b<=a.
Proof. lia. Qed.

Ltac R_sub :=
match goal with
| |- _ <| RC ?m -->* _ => replace m with (m-7+7) by (apply Nat.sub_add; apply ge_le; shelve)
end.

Ltac R_mod :=
match goal with
| |- S1 _ _ ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma Ov_1 a c:
  lh <* d1^^a <* d11^^1 <* w <* d1 <| RC (c+7) -->*
  S1 (lh<*d0^^a<*d1<*d0<*d1<*w<*d1) 0 c.
Proof.
  unfold RC.
  es.
Qed.

Lemma Ov_2 a b c:
  lh <* d1^^a <* w <* d1 <* d11^^(b) <* w <* d1 <| RC (c+7) -->*
  S1 (lh<*d0^^a<*d1<*d1<*d01^^(b)<*w<*d1) 0 c.
Proof.
  unfold S1,RC.
  es.
Qed.

Lemma Ov_3 [a b0 b c]:
  b0>=1 ->
  lh <* d1^^a <* d11^^(b0) <* w <* d1 <* d11^^(b) <* w <* d1 <| RC (c+7) -->*
  S1 (lh<*d0^^a<*d1<*d0<*d1<*d01^^(b0-1)<*w<*d1<*d01^^(b)<*w<*d1) 0 c.
Proof.
  intros Hb0.
  replace b0 with (b0-1+1) by lia.
  replace (b0-1+1-1) with (b0-1) by lia.
  unfold S1,RC.
  es.
Qed.

Lemma Ov_4 [a b0 b1 b c]:
  b0>=1 ->
  lh <* d1^^a <* d11^^(b0) <*w<*d1<*d11^^b1 <*w<*d1<*d11^^(b) <*w<*d1 <| RC (c+7) -->*
  S1 (lh<*d0^^a<*d1<*d0<*d1<*d01^^(b0-1)<*w<*d1<*d01^^b1<*w<*d1<*d01^^(b)<*w<*d1) 0 c.
Proof.
  intros Hb0.
  replace b0 with (b0-1+1) by lia.
  replace (b0-1+1-1) with (b0-1) by lia.
  unfold S1,RC.
  es.
Qed.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: {
  follow init.
  change 100 with (0+31*3+7).
  follow Ov_1.
  follow S1_Incs.
  follow Rst0.
  rewrite Nat.add_0_r.
  follow Incs.
  1: solve_v2.
  rw_lpow_add.
  R_sub.
  follow Ov_2.
  R_mod.
  follow S1_Incs.
  follow Rst0.
  repeat rewrite Nat.add_0_r.
  follow Incs.
  1: solve_v2.
  rw_lpow_add.
  R_sub.
  epose proof (Ov_3 _) as I1.
  follow I1. clear I1.
  repeat rewrite Nat.add_0_r.
  change (((0+1)*2^4-1)*2*2+1) with 61.
  change (4+1+1+1) with 7.
  change (31+2) with 33.
  R_mod.
  follow S1_Incs.
  follow Rst0.
  rewrite Nat.add_0_r.
  follow Incs.
  1: solve_v2.
  rw_lpow_add.
  R_sub.
  epose proof (Ov_4 _) as I1.
  follow I1. clear I1.
  change (33-1) with 32.
  change (7+1+1) with 9.
  R_mod.
  follow S1_Incs.
  finish.
  }
  eapply Rst1.
  Unshelve.
  all: solve_ge.
Qed.

End TM70.


